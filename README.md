
# Blech Compiler

![](https://github.com/boschresearch/blech/workflows/build%20+%20unit%20tests/badge.svg)

Blech is a language for developing reactive, real-time critical embedded software.
This open source project implements a compiler which translates Blech to C.
More information can be found on the [Blech homepage](https://www.blech-lang.org/).

The software is not ready for production use. It has neither been developed nor
tested for a specific use case. However, the license conditions of the
applicable Open Source licenses allow you to adapt the software to your needs.
Before using it in a safety relevant setting, make sure that the software
fulfills your requirements and adjust it according to any applicable safety
standards (e.g. ISO 26262).

## Quick guide to the Blech compiler

### Build the Blech to C compiler blechc

Clone the project using
```
git clone https://github.com/boschresearch/blech
```
To build the project, you need `.NetCore` installed. Go to the Microsoft website and follow their instructions to install the latest stable `.NetCore` available for your operating system.

Navigate to the folder where you have checked out the Blech project. It should contain the file `Blech.sln`. Now you have choices:
  * For a simple **debug build** run
    ```
    dotnet build
    ```
    This creates `./src/blechc/bin/Debug/netcoreapp3.1/blechc.dll`.
    Use the dotnet command to start the compiler like so
    ```
    dotnet ./src/blechc/bin/Debug/netcoreapp3.1/blechc.dll
    ```
  * For a release build additionally use the `-c Release` option.

  * Finally, for a **self-contained release build**, which is operating system dependent, you need to run `dotnet publish` with a specific runtime identifier like so
    ```
    dotnet publish -c Release -r win-x64
    ```
    For Linux use `linux-x64`, for MacOS use `osx-x64`.

    This creates a folder `./src/blechc/bin/Release/netcoreapp3.1/win-x64/publish` which contains all files needed for execution. The folder as a whole can be moved arbitrarily.
    Inside the folder invoke the binary
    ```
    blechc
    ```
    to run the Blech compiler.

In order to **run the unit tests** execute
```
dotnet test
```
This includes parser, name resolution, type checking and causality checking tests.
If you use VisualStudio 2017 or later, you can open the solution file and build the project from within VisualStudio. You can also run the unit tests provided you have installed the `NUnit3 Test Adapter` plugin.

**Code generation**, however, is tested separately outside this framework. In `./test/blechc` invoke 
```
dotnet run -- codegeneration tmp
```
This (upon first invocation) will interactively create a `config` file, and then compile every file in `codegeneration` to C, compile that to an executable, run it, and compare the resulting trace with the specified trace. In this way we ensure that changes to our backend do not change the behaviour of the generated files.
The batch script `testCodegenerationAll.bat` automates this testing process on Windows. It ensures that the program is executed from the Developer Command Prompt, that generated files from previous runs are deleted and calls the test framework on every folder.

### Use blechc

Assuming you have a binary of the Blech Compiler `blechc` for your operating system, or you have built the Blech project yourself from sources, this sections tells you how to use it.

If the `blechc` binary is in your `$PATH`, you can invoke the compiler by simply writing
```
blechc
```
on the command line interface.
If you do not have a standalone (publish) build and want to use your local Debug (or Release) build, use the `dotnet` command to start the compiler from your blech working directory. 

```
dotnet <path-to>/blech/src/blechc/bin/Debug/netcoreapp3.1/blechc.dll
```


**From here on out we assume ```blechc``` to be a synonym for either call above**

Typical invocations:
  *  ```
     blechc someBlechFile.blc
     ```
     Translates ```someBlechFile.blc``` to C code silently. You will only see output on the command line if there are problems with the translation.
     This will generate a file `blech.c` in the same folder which contains a runnable program. It runs in a main loop and calls the entry point activity of `someBlechFile.blc` 60 times. Furthermore in the subfolder `./blech` two files are generated `someBlechFile.c` and `someBlechFile.h`. They contain the C code and interface declarations respectively.
  *  ```
     blechc -v d someBlechFile.blc
     ```
     Does the same as above but prints out textual representations of intermediate compilation results including: typed syntax tree, control flow graphs and block graphs for activities, C code.
  *  ```
     blechc --dry-run someBlechFile.blc
     ```
     Run through all compilation phases but do not write any C files. This is useful to check for problems without actually touching anything on the file system.


### Compile generated C files

By default the compiler produces a main program in `blech.c` which can be used as a first test. To compile this code you need to include Blech specific C header files. These are located in `<path-to>/blech/src/blechc/include`. 
On Windows C compilation may look like this.
```
mingw32-cc.exe -I. -I<path-to>/blech/src/blechc/include blech.c
```
Note that the current folder `.` is explicitly added as a path to be included.
The resulting executable will run the program for 60 reactions and print the variable evaluations after every reaction in JSON format.

To include the generated C code in your own project inspect `blech.c` for details. In particular, make sure you call the `init` function on initial startup and then `tick` with every reaction.
For programmers familiar with Arduino these correspond to the `setup` and `loop` functions.

## License

The Blech compiler is open-sourced under the Apache-2.0 license. See the 
[LICENSE](LICENSE) file for details.

For a list of other open source components included in the Blech compiler, see the 
file [3rd-party-licenses.txt](3rd-party-licenses.txt).
