# Simple id Override

This example shows a definition for a simple override that defines a function `f`, which is an identity function for an integer.

```haskell
SA.StubsProgram {
    SA.stubsEntryPoints=["f"],
    SA.stubsModules=[SA.mkStubsModule "core" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="f",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return  (SA.StubsArg 0 SA.StubsIntRepr)]
        }
    ] [] []]
,SA.stubsInitFns = []}
```