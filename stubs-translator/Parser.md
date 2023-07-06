## Notes on a Parser 
In the AST design (hence referred to as Stubs), some liberties have been taken in assuming what will be handled by a parser, allowing for simpler translation into Crucible.

This document is intended to collect and document these assumptions, such that future parser development handles these adequately.

### Type Conversion
Stubs has a couple of integer types, including both signed and unsigned. While at the AST level their contents may be equivalent, they are distinct types 
and so explicit conversion functions are defined as part of a preamble. We expect a parser to handle the conversions implicitly for ease of use where applicable.

### Variables
At the AST level it is possible to use variables not previously declared, which is an error during translation. A parser could prevent this error in its entirety.

Additionally, variables have effectively dynamic scoping during translation, whereas static scoping is a more common scoping mechanism. A parser could solve this 
by introducing different variable names in order to recover static scoping.

### Functions 
Calling a function is an expression, and so for functions that have no useful return (effectful functions), the easiest way to use this is to assign the result to some dummy variable.
Syntactic sugar for a function call statement would be useful.