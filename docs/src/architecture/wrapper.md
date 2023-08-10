# Wrapper

The Wrapper handles the translation of `CrucibleProgram` objects, produced by the Stubs translator, into `FunctionOverrides`, which are used in symbolic exection.

This takes a program's entry point and sets the corresponding CFG as the entry to the override, and adds all the function bindings for other functions as auxiliary code.

The wrapper also handles translation of init hooks into `FunctionOverrides `, provided that the signature is correct (Init hooks must take no arguments and return unit).