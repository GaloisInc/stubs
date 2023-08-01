# Key Typeclasses

Throughout the pipeline, constraints over the architecture and memory model are needed to ensure the translation and execution are well-defined. These are explained below.

**Preamble**

The `Preamble` type class requires that an architecture defines preamble-specific functions for the architecture, such as `plus`, or type casts. 

**StubsArch**

The `StubsArch` type class defines functions and type families necessary for translation. This includes how Stubs types map into Crucible types, the widths of integer types, and how to translate literals and type reprs.

**OverrideArch**

This type class defines a list of architecture specific override modules that a `StubsProgram` is able to use.