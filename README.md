# Stubs

The Stubs project provides a simple programming language that is amenable to symbolic execution, along with infrastructure for calling Stubs functions during symbolic execution of binaries with [macaw-symbolic][macaw-symbolic]. The primary intended use-cases are:

- Providing models for external functions
- Overriding complex functions with simpler models

This repository contains components needed by the Stubs definition language, including a parser, ABI wrapper, translator, binary loader, and symbolic execution infrastructure.

See the `docs/` folder for a detailed explanation of the language and various components. The overview documentation is written in Markdown, using `mdbook`. Build HTML with:

```
cd doc/
mdbook build
```

[macaw-symbolic]: https://github.com/GaloisInc/macaw/tree/master/symbolic