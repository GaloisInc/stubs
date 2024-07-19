# Loader

The loader module handles the loading of binaries from a given path. Concretely, this entails reading the file contents to determine the architecture, so that architecture specific definitions like the ABI (Linux is assumed) can be loaded. The core of this is performed by `withBinary`, which supports Arm32, x86_64, and PowerPC (32- and 64-bit), assuming Linux with LLVM's memory model. This function is continuation based, and passes architecture specific values on to the continuation.

The Loader is currently partially dependent on a solver backend. This is due to several components of the supported ABIs being LLVM-dependent and needing constraints over the symbolic backend.
