# Usermode Emulation Breaker
Built for LLVM 19.1 - Windows x64 <br> <br>

Usermode applications have these lovely security boundaries to prevent it accessing elevated instructions for kernel purposes. <br>
Symbolic execution environments aren't aware of this, they tend to use emulated environments that support both kernel and usermode processes, as they emulate the instruction execution, not the OS environment. <br>
Thereby using the instructions that will fault on usage, we create a form of exception nanomites that require no registration, we just execute them, fault, continue. <br>
A symbolic executor, Using an emulated backend, will execute it, corrupt the control flow, and continue on. <br>

<img width="406" height="334" alt="image" src="https://github.com/user-attachments/assets/20f02e9d-b37d-4a0a-bac7-67f9bf38ba5e" /> <br>
<img width="233" height="156" alt="image" src="https://github.com/user-attachments/assets/9f8c138b-cdce-4331-93c1-a23ad1389acc" /> <br>
 

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
