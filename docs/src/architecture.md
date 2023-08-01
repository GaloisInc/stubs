# Architecture

As a project, Stubs can be broken down into several key components. These are: 
- The translator, which transforms a Stubs program into a Crucible program. Cabal target: stubs-translator
- The wrapper, which transforms Crucible programs into FunctionOverrides to be used in symbolic execution Cabal target: stubs-wrapper
- The loader, which loads binaries and sets up the proper ABIs necessary for execution. Cabal target: stubs-loader
- Shared data structures, such as FunctionOverride. Cabal target: stubs-common

Thus, a full pipeline, such as the ones used in testing infrastructure, may look something like this:
1. Load the binary, determining architecture specific details.
2. Translate Stubs programs down into Crucible programs
3. Convert Crucible programs into overrides for simulation.
4. Register overrides, setup starting point for simulation.
5. Symbolically execute the program.