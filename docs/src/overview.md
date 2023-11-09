# Overview

The Stubs project provides a simple programming language that is amenable to symbolic execution, along with infrastructure for calling Stubs functions during symbolic execution of binaries with [macaw-symbolic][macaw-symbolic]. The primary intended use-cases are:

- Providing models for external functions
- Overriding complex functions with simpler models

This documentation is intended to provide comprehensive documentation of the Stubs language, and infrastructure necessary to produce and execute overrides for binaries using the language. While much of the project has Haddock comments for specific structures and important functions, this document is intended to focus on more of the "big picture," namely how components fit together, and explanations of key design decisions. 