#include "AntiEmuNanoPass.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <chrono>
#include <cstdint>
#include <cstring>
#include <random>
#include <string>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> AntiEmuNanoEnable("obfaenano", llvm::cl::init(true), llvm::cl::desc("Anti-emulation nanomites pass."));

static constexpr unsigned HarvestDepth = 8;
static constexpr uint64_t HashGolden = 0x9E3779B97F4A7C15ULL;
static constexpr uint64_t HashMix = 0xC6BC279692B5C323ULL;

enum FaultOpcode : unsigned
{
    Hlt,
    Cli,
    Sti,
    Clts,
    Invd,
    Wbinvd,
    Wrmsr,
    Rdmsr,
    Rdpmc,
    Swapgs,
    MovRaxCr0,
    MovRaxCr3,
    MovRaxCr4,
    MovRaxDr0,
    MovRaxDr6,
    MovRaxDr7,
    OpCount,
};

struct RewriteSite
{
    Function* F;
    BasicBlock* FaultBB;
    BasicBlock* TargetBB;
    uint64_t SiteId;
    uint64_t Poll1;
    uint64_t Poll2;
    bool P1FromHarvest;
    bool P2FromHarvest;
    FaultOpcode Opcode;
};

static std::mt19937_64 Rng;
static uint64_t BuildKey = 0;
static std::vector<RewriteSite> Sites;

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga) return false;

    ConstantArray* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;

    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        ConstantStruct* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;

        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;

        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;

        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasAENanoOptIn(Function& f)
{
    return HasAnnotationTag(f, "aenano") || HasAnnotationTag(f, "obfus");
}

static bool HasAENanoOptOut(Function& f)
{
    return HasAnnotationTag(f, "noaenano") || HasAnnotationTag(f, "noobfus");
}

static uint64_t NextAENonce()
{
    uint64_t v;
    do { v = Rng(); } while (v == 0);
    return v;
}

static FaultOpcode PickOpcode()
{
    return (FaultOpcode)(Rng() % (unsigned)OpCount);
}

static uint64_t HashRegs(uint64_t a, uint64_t b)
{
    uint64_t x = a + HashGolden;
    x ^= b;
    x = (x << 23) | (x >> 41);
    x *= HashMix;
    x ^= x >> 32;
    return x;
}

static bool BranchParentIsEHPad(BranchInst* br)
{
    BasicBlock* p = br->getParent();
    return p && p->isEHPad();
}

static bool BranchTargetIsEHPad(BranchInst* br)
{
    for (BasicBlock* succ : br->successors())
        if (succ && succ->isEHPad()) return true;
    return false;
}

static bool BranchTargetIsUnreachableOnly(BranchInst* br)
{
    if (br->getNumSuccessors() != 1) return false;
    BasicBlock* t = br->getSuccessor(0);
    if (!t || t->empty()) return false;
    return t->size() == 1 && isa<UnreachableInst>(t->getTerminator());
}

static bool BranchTargetHasPhi(BranchInst* br)
{
    if (br->getNumSuccessors() != 1) return false;
    BasicBlock* t = br->getSuccessor(0);
    if (!t || t->empty()) return false;
    return isa<PHINode>(&t->front());
}

static void CollectCandidates(Function& f, std::vector<BranchInst*>& out)
{
    for (BasicBlock& bb : f)
    {
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        if (br->isConditional()) continue;
        if (BranchParentIsEHPad(br)) continue;
        if (BranchTargetIsEHPad(br)) continue;
        if (BranchTargetIsUnreachableOnly(br)) continue;
        if (BranchTargetHasPhi(br)) continue;
        out.push_back(br);
    }
}

// trivial values 0 and 1 and all ones are excluded because they would make pollution values collide between sites and fingerprint as bland constants to static analysis
static SmallVector<uint64_t, 2> HarvestDominatingConsts(BranchInst* br, DominatorTree& dt, unsigned maxneeded)
{
    SmallVector<uint64_t, 2> out;
    DenseSet<uint64_t> seen;

    auto trytake = [&](Value* v)
    {
        if (out.size() >= maxneeded) return;
        auto* ci = dyn_cast<ConstantInt>(v);
        if (!ci) return;
        if (ci->getBitWidth() > 64) return;
        uint64_t x = ci->getZExtValue();
        if (x == 0 || x == 1 || x == ~0ULL) return;
        if (!seen.insert(x).second) return;
        out.push_back(x);
    };

    auto scanbb = [&](BasicBlock* bb)
    {
        for (Instruction& i : *bb)
        {
            for (Value* op : i.operands())
            {
                trytake(op);
                if (out.size() >= maxneeded) return;
            }
        }
    };

    scanbb(br->getParent());

    if (out.size() < maxneeded)
    {
        DomTreeNode* node = dt.getNode(br->getParent());
        unsigned depth = 0;
        while (out.size() < maxneeded && node && depth < HarvestDepth)
        {
            node = node->getIDom();
            if (!node) break;
            BasicBlock* bb = node->getBlock();
            if (!bb) break;
            scanbb(bb);
            ++depth;
        }
    }

    return out;
}

static InlineAsm* MakeAsmVoidNoClobber(LLVMContext& c, const char* text)
{
    FunctionType* ft = FunctionType::get(Type::getVoidTy(c), {}, false);
    return InlineAsm::get(ft, text, "~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static InlineAsm* MakeAsmVoidClobber(LLVMContext& c, const char* text, const char* clobbers)
{
    FunctionType* ft = FunctionType::get(Type::getVoidTy(c), {}, false);
    std::string clobstr = clobbers;
    clobstr += ",~{dirflag},~{fpsr},~{flags}";
    return InlineAsm::get(ft, text, clobstr, true, false, InlineAsm::AD_Intel);
}

static InlineAsm* GetFaultAsm(LLVMContext& c, FaultOpcode op)
{
    switch (op)
    {
        case Hlt: return MakeAsmVoidNoClobber(c, "hlt");
        case Cli: return MakeAsmVoidNoClobber(c, "cli");
        case Sti: return MakeAsmVoidNoClobber(c, "sti");
        case Clts: return MakeAsmVoidNoClobber(c, "clts");
        case Invd: return MakeAsmVoidNoClobber(c, "invd");
        case Wbinvd: return MakeAsmVoidNoClobber(c, "wbinvd");
        case Wrmsr: return MakeAsmVoidClobber(c, "wrmsr", "~{eax},~{ecx},~{edx}");
        case Rdmsr: return MakeAsmVoidClobber(c, "rdmsr", "~{eax},~{ecx},~{edx}");
        case Rdpmc: return MakeAsmVoidClobber(c, "rdpmc", "~{eax},~{ecx},~{edx}");
        case Swapgs: return MakeAsmVoidNoClobber(c, "swapgs");
        case MovRaxCr0: return MakeAsmVoidClobber(c, "mov rax, cr0", "~{rax}");
        case MovRaxCr3: return MakeAsmVoidClobber(c, "mov rax, cr3", "~{rax}");
        case MovRaxCr4: return MakeAsmVoidClobber(c, "mov rax, cr4", "~{rax}");
        case MovRaxDr0: return MakeAsmVoidClobber(c, "mov rax, dr0", "~{rax}");
        case MovRaxDr6: return MakeAsmVoidClobber(c, "mov rax, dr6", "~{rax}");
        case MovRaxDr7: return MakeAsmVoidClobber(c, "mov rax, dr7", "~{rax}");
        case OpCount: break;
    }
    llvm_unreachable("bad FaultOpcode");
}

// the "{r10},{r11}" input constraints with hasSideEffects=true pin poll1 and poll2 into r10 and r11 so the subsequent privileged instruction fault captures them in CONTEXT.R10 and CONTEXT.R11 for the VEH dispatcher to read back
static InlineAsm* GetPollAsm(LLVMContext& c)
{
    Type* voidt = Type::getVoidTy(c);
    Type* i64 = Type::getInt64Ty(c);
    FunctionType* polty = FunctionType::get(voidt, {i64, i64}, false);
    return InlineAsm::get(polty, "", "{r10},{r11},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static void EmitSiteRewrite(Function& f, BranchInst* br, DominatorTree& dt)
{
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    BasicBlock* target = br->getSuccessor(0);

    FaultOpcode op = PickOpcode();

    uint64_t poll1 = 0;
    uint64_t poll2 = 0;
    bool p1fromharvest = false;
    bool p2fromharvest = false;

    SmallVector<uint64_t, 2> harvested = HarvestDominatingConsts(br, dt, 2);
    if (harvested.size() >= 1)
    {
        poll1 = harvested[0];
        p1fromharvest = true;
    }
    if (harvested.size() >= 2)
    {
        poll2 = harvested[1];
        p2fromharvest = true;
    }

    if (poll1 == 0) poll1 = NextAENonce();
    if (poll2 == 0 || poll2 == poll1) poll2 = NextAENonce();

    // HashRegs degenerates to a constant when poll1 equals poll2 so reroll until distinct; harvest dedup already guarantees this when both come from harvest, but the random fallback can still collide
    while (poll2 == poll1) poll2 = NextAENonce();

    uint64_t siteid = NextAENonce();

    BasicBlock* faultbb = BasicBlock::Create(c, "Fault", &f, target);

    {
        IRBuilder<> b(faultbb);
        b.CreateCall(GetFaultAsm(c, op));

        // the CreateIndirectBr capacity hint of 1 does not add the destination; addDestination is what registers the CFG edge so the verifier and downstream passes see the real target as a successor
        Constant* targetba = BlockAddress::get(&f, target);
        IndirectBrInst* ibr = b.CreateIndirectBr(targetba, 1);
        ibr->addDestination(target);
    }

    {
        IRBuilder<> bp(br);
        bp.CreateCall(GetPollAsm(c), { ConstantInt::get(i64, poll1), ConstantInt::get(i64, poll2) });
    }

    br->setSuccessor(0, faultbb);

    RewriteSite rs;
    rs.F = &f;
    rs.FaultBB = faultbb;
    rs.TargetBB = target;
    rs.SiteId = siteid;
    rs.Poll1 = poll1;
    rs.Poll2 = poll2;
    rs.P1FromHarvest = p1fromharvest;
    rs.P2FromHarvest = p2fromharvest;
    rs.Opcode = op;
    Sites.push_back(rs);
}

static StructType* GetAENanoEntryType(LLVMContext& c)
{
    return StructType::get(c, { PointerType::get(c, 0), Type::getInt64Ty(c), Type::getInt64Ty(c) }, false);
}

static GlobalVariable* EmitAENanoTable(Module& m, ArrayRef<RewriteSite> sites)
{
    LLVMContext& c = m.getContext();
    StructType* entryt = GetAENanoEntryType(c);
    PointerType* ptrt = PointerType::get(c, 0);
    IntegerType* i64t = Type::getInt64Ty(c);

    SmallVector<Constant*, 4> entries;
    entries.reserve(sites.size() + 1);

    for (const RewriteSite& s : sites)
    {
        Constant* faultba = BlockAddress::get(s.F, s.FaultBB);
        Constant* targetba = BlockAddress::get(s.F, s.TargetBB);
        Constant* targetint = ConstantExpr::getPtrToInt(targetba, i64t);

        uint64_t h = HashRegs(s.Poll1, s.Poll2);
        uint64_t mask = h ^ BuildKey ^ s.SiteId;
        Constant* maskc = ConstantInt::get(i64t, mask);

        Constant* enctarget = ConstantExpr::getAdd(targetint, maskc);
        Constant* siteidc = ConstantInt::get(i64t, s.SiteId);

        entries.push_back(ConstantStruct::get(entryt, { faultba, enctarget, siteidc }));
    }
    entries.push_back(ConstantStruct::get(entryt, { ConstantPointerNull::get(ptrt), ConstantInt::get(i64t, 0), ConstantInt::get(i64t, 0) }));

    ArrayType* arrt = ArrayType::get(entryt, entries.size());
    Constant* init = ConstantArray::get(arrt, entries);

    auto* gv = new GlobalVariable(m, arrt, false, GlobalValue::InternalLinkage, init, "__aenano_table");
    return gv;
}

static Function* GetOrDeclareAddVEH(Module& m)
{
    const char* name = "AddVectoredExceptionHandler";
    if (Function* existing = m.getFunction(name)) return existing;

    LLVMContext& c = m.getContext();
    Type* ptrt = PointerType::get(c, 0);
    Type* i32 = Type::getInt32Ty(c);
    FunctionType* ft = FunctionType::get(ptrt, {i32, ptrt}, false);
    Function* f = Function::Create(ft, GlobalValue::ExternalLinkage, name, &m);
    f->setDLLStorageClass(GlobalValue::DLLImportStorageClass);
    return f;
}

static Value* EmitHashRegsIR(IRBuilder<>& b, Value* a, Value* bv)
{
    LLVMContext& c = b.getContext();
    Type* i64 = Type::getInt64Ty(c);

    Value* x = b.CreateAdd(a, ConstantInt::get(i64, HashGolden), "");
    x = b.CreateXor(x, bv, "");
    Value* xl = b.CreateShl(x, ConstantInt::get(i64, 23), "");
    Value* xh = b.CreateLShr(x, ConstantInt::get(i64, 41), "");
    x = b.CreateOr(xl, xh, "");
    x = b.CreateMul(x, ConstantInt::get(i64, HashMix), "");
    Value* xs = b.CreateLShr(x, ConstantInt::get(i64, 32), "");
    x = b.CreateXor(x, xs, "");
    return x;
}

// CONTEXT offsets are the Windows x64 ABI positions for R10 at 0xC8, R11 at 0xD0 and RIP at 0xF8; the EXCEPTION_POINTERS layout places ExceptionRecord at offset 0 and ContextRecord at offset 8, and ExceptionCode sits at offset 0 of ExceptionRecord so these magic numbers must stay in step with the OS defined structure
static Function* EmitAENanoDispatch(Module& m, GlobalVariable* table, unsigned entriesplussentinel)
{
    const char* name = "__aenano_dispatch";

    LLVMContext& c = m.getContext();
    Type* i8 = Type::getInt8Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrt = PointerType::get(c, 0);
    StructType* entryt = GetAENanoEntryType(c);
    ArrayType* arrt = ArrayType::get(entryt, entriesplussentinel);

    FunctionType* ft = FunctionType::get(i32, {ptrt}, false);
    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, name, &m);
    f->addFnAttr(Attribute::NoUnwind);

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* haveflt = BasicBlock::Create(c, "HaveFault", f);
    BasicBlock* loop = BasicBlock::Create(c, "Loop", f);
    BasicBlock* check = BasicBlock::Create(c, "Check", f);
    BasicBlock* cont = BasicBlock::Create(c, "Cont", f);
    BasicBlock* hit = BasicBlock::Create(c, "Hit", f);
    BasicBlock* miss = BasicBlock::Create(c, "Miss", f);

    Value* ep = f->getArg(0);

    // STATUS_PRIVILEGED_INSTRUCTION 0xC0000096 is the NT status code the Windows kernel delivers on ring 3 CPL violation for every opcode in the pool; gating here filters out unrelated exceptions so we return EXCEPTION_CONTINUE_SEARCH for none ours
    {
        IRBuilder<> b(entry);
        Value* erloc = b.CreateLoad(ptrt, ep, "");
        Value* code = b.CreateLoad(i32, erloc, "");
        Constant* privcode = ConstantInt::get(i32, 0xC0000096u);
        Value* ispriv = b.CreateICmpEQ(code, privcode, "");
        b.CreateCondBr(ispriv, haveflt, miss);
    }

    Value* faultaddr = nullptr;
    {
        IRBuilder<> b(haveflt);
        Value* erloc = b.CreateLoad(ptrt, ep, "");
        Value* addrslot = b.CreateGEP(i8, erloc, ConstantInt::get(i64, 16), "");
        faultaddr = b.CreateLoad(ptrt, addrslot, "");
        b.CreateBr(loop);
    }

    PHINode* iphi = nullptr;
    Value* entptr = nullptr;
    {
        IRBuilder<> b(loop);
        iphi = b.CreatePHI(i64, 2, "");
        iphi->addIncoming(ConstantInt::get(i64, 0), haveflt);
        entptr = b.CreateGEP(arrt, table, { ConstantInt::get(i64, 0), iphi }, "");
        Value* fp = b.CreateLoad(ptrt, entptr, "");
        Value* isend = b.CreateICmpEQ(fp, ConstantPointerNull::get(ptrt), "");
        b.CreateCondBr(isend, miss, check);
    }

    {
        IRBuilder<> b(check);
        Value* fp = b.CreateLoad(ptrt, entptr, "");
        Value* ishit = b.CreateICmpEQ(fp, faultaddr, "");
        b.CreateCondBr(ishit, hit, cont);
    }

    {
        IRBuilder<> b(cont);
        Value* inext = b.CreateAdd(iphi, ConstantInt::get(i64, 1), "");
        iphi->addIncoming(inext, cont);
        b.CreateBr(loop);
    }

    {
        IRBuilder<> b(hit);
        Value* tgtslot = b.CreateGEP(entryt, entptr, { ConstantInt::get(i32, 0), ConstantInt::get(i32, 1) }, "");
        Value* enctgt = b.CreateLoad(i64, tgtslot, "");

        Value* sidslot = b.CreateGEP(entryt, entptr, { ConstantInt::get(i32, 0), ConstantInt::get(i32, 2) }, "");
        Value* sid = b.CreateLoad(i64, sidslot, "");

        Value* ctxslot = b.CreateGEP(i8, ep, ConstantInt::get(i64, 8), "");
        Value* ctx = b.CreateLoad(ptrt, ctxslot, "");

        Value* r10slot = b.CreateGEP(i8, ctx, ConstantInt::get(i64, 0xC8), "");
        Value* r10 = b.CreateLoad(i64, r10slot, "");
        Value* r11slot = b.CreateGEP(i8, ctx, ConstantInt::get(i64, 0xD0), "");
        Value* r11 = b.CreateLoad(i64, r11slot, "");

        Value* h = EmitHashRegsIR(b, r10, r11);
        Constant* bkc = ConstantInt::get(i64, BuildKey);
        Value* hbk = b.CreateXor(h, bkc, "");
        Value* mask = b.CreateXor(hbk, sid, "");
        Value* tgt = b.CreateSub(enctgt, mask, "");

        Value* ripslot = b.CreateGEP(i8, ctx, ConstantInt::get(i64, 0xF8), "");
        b.CreateStore(tgt, ripslot);
        b.CreateRet(ConstantInt::get(i32, (uint32_t)-1));
    }

    {
        IRBuilder<> b(miss);
        b.CreateRet(ConstantInt::get(i32, 0));
    }

    return f;
}

static Function* EmitAENanoInit(Module& m, Function* dispatch)
{
    const char* name = "__aenano_init";
    if (Function* existing = m.getFunction(name)) return existing;

    LLVMContext& c = m.getContext();
    Type* voidt = Type::getVoidTy(c);
    Type* i32 = Type::getInt32Ty(c);
    FunctionType* ft = FunctionType::get(voidt, {}, false);

    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, name, &m);
    f->addFnAttr(Attribute::NoUnwind);

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    IRBuilder<> b(entry);

    Function* addveh = GetOrDeclareAddVEH(m);
    b.CreateCall(addveh, { ConstantInt::get(i32, 1), dispatch });
    b.CreateRetVoid();
    return f;
}

// priority 65535 is the lowest numbered first ctor slot so this runs AFTER any higher priority user ctors in the module; the VEH must be registered before any protected function is called but the addVEH import must have been resolved by the loader first
static bool EmitAENanoPlumbing(Module& m, ArrayRef<RewriteSite> sites)
{
    // skip plumbing emission when the module already has a __aenano_dispatch so reruns of the pass on the same module do not double register the VEH or stack two parallel tables
    if (m.getFunction("__aenano_dispatch")) return false;
    if (sites.empty()) return false;

    GlobalVariable* table = EmitAENanoTable(m, sites);
    Function* dispatch = EmitAENanoDispatch(m, table, (unsigned)sites.size() + 1);
    Function* init = EmitAENanoInit(m, dispatch);

    appendToGlobalCtors(m, init, 65535);

    return true;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (f.getName().starts_with("__aenano_")) return false;

    if (HasAENanoOptOut(f)) return false;
    if (!HasAENanoOptIn(f)) return false;

    DominatorTree dt;
    dt.recalculate(f);

    std::vector<BranchInst*> cands;
    CollectCandidates(f, cands);

    if (cands.empty()) return false;

    for (BranchInst* br : cands) EmitSiteRewrite(f, br, dt);
    return true;
}

bool RunAntiEmuNano(Module& m)
{
    if (!AntiEmuNanoEnable) return false;

    std::random_device rd;
    uint64_t seed = (uint64_t)rd();
    seed ^= (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    seed ^= ((uint64_t)rd()) << 32;
    seed ^= 0x41454E414E4F5F5FULL;
    Rng.seed(seed);

    uint64_t v;
    do { v = Rng(); } while (v == 0);
    BuildKey = v;

    Sites.clear();

    bool mutated = false;
    for (Function& f : m) mutated |= ProcessFunction(f);

    if (!Sites.empty()) mutated |= EmitAENanoPlumbing(m, Sites);

    return mutated;
}

PreservedAnalyses AntiEmuNanoPass::run(Module& m, ModuleAnalysisManager&)
{
    if (!RunAntiEmuNano(m)) return PreservedAnalyses::all();
    return PreservedAnalyses::none();
}