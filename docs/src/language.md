# Language

As a language, Stubs sits above Crucible, abstracting some architecture specific details in order to allow reusability of overrides whenever possible.
For instance, the `Int` type in Stubs translates down into a bitvector, whose length is architecture dependent.

In terms of semantics, Stubs is essentially a C-like language with modules.

For more details on this relation between Stubs and Crucible, see [Translation](./translation.md).

## Program
The primary unit of compilation for Stubs is a StubsProgram. This consistes of a list of modules, a list of entry points, and a list of init hooks.
The latter two lists indicate functions that are intended to be overridden directly in symbolic execution, and functions to run before execution, respectively.

Init functions are required to have the signature `Unit -> Unit`. Entry points can have arbitrary signatures.

Modules consist of a list of functions, type declarations, and global data declarations. 

Stubs functions consist of a type signature, and a body, which is a list of statements. 
Type declarations define opaque types to be exported to other modules, while global data declarations do the same for shared data.

## Statements and Expressions

The core of Stubs is its statements and expressions, which define the actual allowed operations. 

Legal statements are:
- Variable Assignment (including globals)
- Loops
- If-Then-Else
- Return statements

Legal Expressions are:
- Literals
- Variables
- Argument Variables
- Function calls

**NOTE**: Primitive operations such as addition or comparison are implemented as a Preamble, which allows for architecture specific operations to be used to define these builtins.

## Type System
Stubs has a relatively simple type system, for ease of use as well as ease of translation into Crucible. There are 3 kinds of type, namely:
- Primitves/Builtins, such as Int, Bool, etc.
- Opaque types
- Intrinsic types

### Primitive/Builtin Types
The core of Stubs' type system is a set of builtin types, corresponding to C integer types, and other basic types.

Namely, Stubs has:
- Int, Long, Short (and unsigned variants)
- Bool
- Unit

###  Opaque Types
Modules may declare their own types, which are opaque to other modules reliant on it. For instance, a module may declare a 'Counter' type, which is internally an Int, but to other modules, it is a Counter than can only be used through the interface exposed by its declaring module.

### Intrinsic Types
Intrinsics are similar to Opaque types, but are declared by override modules rather than Stubs-level modules. As override modules (see below) work with Haskell directly, they can return arbitrary Crucible types which may not map to a Stubs type directly. For instance, an override module for memory may define a `Pointer` type, which internally is a bitvector, or a special struct of some kind, but can only be used at the Stubs-level through the override's interface.

### Override Modules
In order to more easily model complex behavior like memory access, file systems, or IO, `OverrideModule`s can be defined in order to model behavior directly as Crucible overrides, allowing arbitrary Haskell to be used. These modules are defined on a per-architecture basis, and are intended to be linked in during translation and execution.