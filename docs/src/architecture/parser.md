## Parser

The parser implements a C-like concrete syntax for Stubs, allowing for more convenient development.

The literal parsing steps are done using [Alex](https://haskell-alex.readthedocs.io/en/latest/index.html) and [Happy](https://haskell-happy.readthedocs.io/en/latest/index.html), which are similar to `lex` and `yacc`, but for Haskell.

At a high level, the parser expects a list of files to compile (each being a module), and a list of entry points in those modules (meta data needed by the full Stubs program). The parser generates a simple AST, with less restrictions than the lower level AST we translate down into Crucible. Thus, after parsing, this 'weaker' AST is lowered into the more precise AST, handling cases such as global or local variables, and type-checking.

To perform this lowering, a simple monad, `StubsLowerM` is used. This is essentially a state monad with exceptions, as variable and type context is necessary for lowering.
The lowering is able to catch several bugs, such as using undeclared variables, or assigning to parameters (immutable in Stubs).