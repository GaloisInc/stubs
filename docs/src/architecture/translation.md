# Translation

Stubs translates down into Crucible code, in order to use Crucible's simulator for execution, while abstracting architecture specific information from Crucible.

At a high level, a `StubsProgram` is translated into `CrucibleProgram`s, which contains the actual CFGs needed for execution, along with data required for linking in preamble functions, override modules, and defining an entry point. This translation can be broken down into several steps:
- Collect Intrinsic type definitions from all overrides, to put into the translation environment. This is needed so that modules using these types are able to not only type check, but also be translated properly into Crucible types.
- Collect all override definitions, to be passed along to the resulting `CrucibleProgram` for future linking. The generated function handles are collected for code generation, along with  the Stubs-level type signature for type checking at call sites.
- Handles are generated for all preamble functions, to be used in code generation. A matching Stubs-level type signature is paired with each handle, for type checking. This process naturally appears similar to the override definition processing above.
- Core safety checks are performed, namely that Opaque types are respected (see type checking, further down), and no signatures are missing.
- All global variables are declared, as during code generation they are assumed to exist.
- Modules are topologically sorted, as function handles produced in translating one module may need to be used in other modules. Function handles uniquely identify a function in Crucible, so the handles must be kept if the function is called in a different module. For simplicity, all are kept in a list, and translation of modules is a fold operation that accumulates these, as well as the translated modules, and type declarations.
- Translation artifacts are wrapped into `CrucibleProgram` objects, and returned.

Note: A `StubsProgram` can have several entry points, whereas a `CrucibleProgram` has exactly one. Thus, a `StubsProgram` can translate into several `CrucibleProgram`s.

## The Relationship Between Stubs and Crucible 

Stubs abstracts away some architecture specific information that would be necessary if everything was written directly in Crucible syntax. Stubs also adds some higher level features like opaque types and modules. To facilitate this, Stubs defines its own language, with its own type system. As Stubs is translated down into Crucible, there is necessarily a relationship between Stubs and Crucible expressions and types.

Each architecture supported by Stubs defines a set of core definitions needed for translation. This includes a type translation for primitive Stubs types into Crucible types, as well as for literals of these primitive types. Some type information can be ascertained at the Stubs level, though some constructs require Crucible-level type checking, due to opaque types.

## The Translation Environment

Translation at the top level sits in the `IO` monad, but the core translation (that of functions) occurs in the `StubsM` monad, which is a specialization of Crucible's `Generator` monad, which is a State monad built on top of `IO`. This monad contains a `StubsState`, which includes:
- Type mappings for Opaque and Intrinsic types
- Architecture address width info
- Expected return type (as a Stubs type)
- Defined variables and globals
- Parameter atoms (Crucible generates these)
- "Known" function handles (Previously translated, or defined in the same module)


## Module and Function Translation

Module translation is essentially translation of each function, so the 'meat' of this section focuses on function translation.

Firstly, Crucible function handles are generated for each function declared, and associated with the function. These handles, preamble handles, override handles, and previously translated function handles are combined, and stored in the environment, so that function calls can access them. Then, the functions are translated.

### Function Translation

First, argument and return types in the signature are translated into corresponding Crucible types. Parameters are translated into `StubAtom` objects, which are Crucible atoms + a Stubs type, so argument literals can be type checked. The environment is constructed as discussed above, and the statements comprising the body are translated. Inside of the body of the translated Crucible function, a final statement throwing an error is added, as there is no enforcement of a return statement ever actually occuring. This is to simplify the handling of early returns, as they don't need any special handling with this. 

## Statement and Expression Translation

Each statement in the Stubs language is simple enough to directly map to a Crucible statement, so the bulk of the interesting work is done by the expression translation, as well
as the type translation and checking.

Translation of literal expressions is handled by `translateLit`, an architecture-specific function, as the corresponding Crucible type for each Stubs type is architecture dependent. 

For variables, and global variables, the expressions are first type checked, and then if this succeeds, a lookup occurs to determine if the variable exists. If it doesn't, and it is a global, an error occurs, as all known globals were defined before translating any modules. If it is a local variable, it is defined, and added to the state, then initialized. If the variable exists, a corresponding update statement is generated.

Argument literals work similarly to variables. First, the argument must exist, and the corresponding StubsAtom is then used in typechecking against the literal's declared type. If everything is correct, the atom is used as the translated expression.

Function calls are slightly more complex as they must be type checked. Firstly, the environment is checked to determine if the function called actually exists. If it does, the declared signature is checked against the call itself, which includes an expected return type for this reason. If everything checks out, a Crucible function call is generated with the proper handle.

## Type Checking, and Type Translation

Throughout the translation, expressions are type checked against environment information to ensure correctness and consistency throughout translation. Every Stubs type has a corresponding Crucible type, although there are some types which make things more complicated, namely Opaque types.

Essentially, any module can define a custom type declaration, introducing an Opaque type, and mapping it to a Stubs type. Inside of the module, the type it aliases, and the alias itself can be used interchangeably, but other modules do not have access to this definition, which makes type checking, and type translation, more interesting than simple equivalence. In the presence of opaque types, the easiest way to check this is to translate all types down to Crucible types, and then check equivalence. This is also necessary as opaque types do not have a Crucible equivalent concept, so the translation step needs to replace them with the proper Crucible type. As type checking happens at the Crucible level, the fact that a type's 'opaqueness' is enforced needs to be handled as a separate pass, before translation. 

Besides opaque types, Stubs has a notion of Intrinsic types, which are introduced by special OverrideModules. These intrinsic types are like opaque types, except that they map directly to a Crucible type rather than a Stubs type. Though an intrinsic type works similarly to an opaque type, the Crucible type may not have an equivalent Stubs type, so some issues of opaqueness may be ignored safely.