# Language

As a language, Stubs sits above Crucible, abstracting some architecture specific details in order to allow reusability of overrides whenever possible.
For instance, the `Int` type in Stubs translates down into a bitvector, whose length is architecture dependent.

In terms of semantics, Stubs is essentially a C-like language with modules.

For more details on this relation between Stubs and Crucible, see [Translation](./translation.md).

## Program 

A Stubs program consists of a set of modules, and entry points. A single file, such as `ex.stb`, is a module.

A module consists of 4 key components, detailed below: 
- External Declarations 
- Type Declarations
- Global Declarations
- Function Definitions

### External Declarations 

An external declaration is a declaration of the following form: 

```c 
extern TYPE IDENT (PARAMS);
```

A concrete example of this: 

```c 
extern int f(int x);
```

Essentially, these declarations are for functions which are needed for type checking, but do not exist in the source files and will be linked in later.

### Type Declarations

A type declaration has the following form: 

```c 
type IDENT = TYPE;
```

A concrete example:

```c
type counter = int;
```

This declares that within the current module, the type `counter` is known to be an `int`. To other modules, a `counter` is totally opaque.

### Global Declarations

A global declaration has the following form:

```c
TYPE IDENT;
```

With a concrete example: 

```c
int x;
```

This defines a global variable `x`, accessible within and outside of the module. 

### Function Definitions

Lastly, a module can contain function definitions.

For instance:

```c 
fn int f(int x){
    return x;
}

init fn unit k(){
    return ();
}

```

A function consists of its signature, and a list of statements comprising the body. The signature denotes whether or not it is an init hook,whether it is private or not, its return type, and what parameters it takes.
For functions with multiple parameters, each parameter declaration is comma separated, as in C.

## Statements and Expressions

The core of Stubs is its statements and expressions, which define the actual allowed operations. 

Legal statements are:
- Variable Assignment (including globals): `x = 5;`
- Declarations : `int x = 2;`
- Loops: `while b { x = 5; }`
- If-Then-Else `if b { x = 5; } else {x = 6;}`
- Return statements `return true;`

**NOTE**: Semicolons are required, not optional

Legal Expressions are:
- Literals
- Variables
- Function calls
- Tuple expressions 
- Tuple access: `t.0`, where t is some expression evaluating to a tuple. the index can be any unsigned integer, as long as the tuple has a corresponding field.

| Type   | Literal |
|--------|---------|
| int    |   5     |
| short  |   5S    |
| long   |   5L    |
| uint   |   5U    |
| ushort |   5US   |
| ulong  |   5UL   |
| unit   |   ()    |
| bool   | true    |

**NOTE**: Primitive operations such as addition or comparison are implemented as a Preamble, which allows for architecture specific operations to be used to define these builtins.
Thus, 2 + 2 would look like: `plus(2,2)`


### Comprehensive Example
Below is an example module, using several language features.

```c

type num = int;

num t;

fn int f(int y){
    int i = g();
    uint c = 5U;
    while  gt(int(c),0) {
        i = plus(i,i);
    }
    return i;
}

fn num g(){
    return 30;
}

fn bool isThree(int j){
    if eq(j,3) {
        return true;
    } else {
        return false;
    }
}
```

## Type System
Stubs has a relatively simple type system, for ease of use as well as ease of translation into Crucible. There are 3 kinds of type, namely:
- Primitves/Builtins, such as Int, Bool, etc.
- Opaque types
- Intrinsic types
- Tuple/Record types

### Primitive/Builtin Types
The core of Stubs' type system is a set of builtin types, corresponding to C integer types, and other basic types.

Namely, Stubs has:
- int, long, short (and unsigned variants uint,ulong,ushort)
- bool
- unit

**NOTE**: As Stubs aims to be relatively similar to Crucible semantically, higher order functions are not implemented directly in Stubs.

###  Opaque Types
Modules may declare their own types, which are opaque to other modules reliant on it. For instance, a module may declare a `counter` type, which is internally an `int`, but to other modules, it is a `counter` than can only be used through the interface exposed by its declaring module.

### Intrinsic Types
Intrinsics are similar to Opaque types, but are declared by override modules rather than Stubs-level modules. As override modules (see below) work with Haskell directly, they can return arbitrary Crucible types which may not map to a Stubs type directly. For instance, an override module for memory may define a `Pointer` type, which internally is a bitvector, or a special struct of some kind, but can only be used at the Stubs-level through the override's interface. Syntactically, `Pointer` is denoted as `@Pointer`, to distinguish it from an opaque type.

### Tuples 

Custom types exist in the form of tuples, such as `(int,int)` denoting a pair of `int`s. These can be nested, and of abritrary lengths, allowing for complex data to be passed around more 
conveniently.

### Override Modules
In order to more easily model complex behavior like memory access, file systems, or IO, `OverrideModule`s can be defined in order to model behavior directly as Crucible overrides, allowing arbitrary Haskell to be used. These modules are defined on a per-architecture basis, and are intended to be linked in during translation and execution.