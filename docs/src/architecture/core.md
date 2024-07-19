# Core

The `stubs-common` Cabal target contains definitions that are necessary for several components, or otherwise do not fit into other targets. The most important part of the core is the definition of various ABIs and override components necessary for constructing meaningful, runnable `FunctionOverride` definitions.

## FunctionOverride

The most important concept in core is the `FunctionOverride` type. This type wraps up a function with argument and return types, as well as bindings to auxiliary functions it may call. The core of this is a function taking a symbolic backend, and arguments, and computing the result. Some smart constructors for common construction cases are provided.

In a symbolic execution pipeline, these overrides are packed into the `FunctionABI`, so when a function is called the ABI may cause the override to be invoked instead.

## FunctionABI and SyscallABI

These ABI types are memory-model and arch independent structures defining how to pass values between functions. They consist of functions defining how to retrieve arguments, as well as how to retrieve the return result, and return address.

For testing, the ABIs used assume LLVM and Linux, supporting AArch32 and X86_64.

## BuildFunctionABI and BuildSyscallABI
These types wrap around functions that construct ABI types, based on memory. The loader passes these along to its continuation, as part of its arch/memory specific data.

## Sym

Throughout the pipeline, a symbolic backend, and associated expression builder, are frequently used. Many functions require these to be related, so a `Sym` wraps the two together, satisfying these constraints.
