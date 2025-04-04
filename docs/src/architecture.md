# Architecture

As a project, Stubs can be broken down into several key components. These are:
- The translator, which transforms a Stubs program into a Crucible program. Cabal target: stubs-translator

  stubs-translator is written in an architecture-independent way. There are also additional libraries that instantiate stubs-translator at particular ISAs. Cabal targets: stubs-translator-aarch32, stubs-translator-ppc, stubs-translator-x86
- The wrapper, which transforms Crucible programs into FunctionOverrides to be used in symbolic execution. Cabal target: stubs-wrapper
- The loader, which loads binaries and sets up the proper ABIs necessary for execution. Cabal target: stubs-loader
- The parser, which parses a concrete syntax for Stubs programs. Cabal target: stubs-parser
- Shared data structures, such as FunctionOverride. Cabal target: stubs-common

  stubs-common is written in an architecture-independent way. There are also additional libraries that instantiate stubs-common at particular ISAs. Cabal targets: stubs-common-aarch32, stubs-common-ppc, stubs-common-x86

Thus, a full pipeline, such as the ones used in testing infrastructure, may look something like this:
1. Load the binary, determining architecture specific details. (loader)
2. Parse and process Stubs modules into a set of StubsPrograms. (parser)
3. Translate Stubs programs down into Crucible programs. (translator)
4. Convert Crucible programs into overrides for simulation. (wrapper)
5. Register overrides, setup starting point for simulation.
6. Symbolically execute the program.
