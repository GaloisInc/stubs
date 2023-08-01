# Opaque type Example

This example consists of two modules, one which defines a `Counter` type, with several operations, and one that utilizes this type.

```haskell
SA.StubsProgram {
        SA.stubsEntryPoints=["f"],
        SA.stubsModules=[
            SA.mkStubsModule "counter" [
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsAliasRepr counter
                    },
                    SA.stubFnBody=[SA.Return $  SA.LitExpr $ SA.IntLit 0]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=SA.StubsAliasRepr counter
                    },
                    SA.stubFnBody=[SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr )]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="as_int",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)]}
        ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [],
            SA.mkStubsModule "core" [
                SA.SomeStubsFunction
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="f",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return (SA.AppExpr "as_int" (Ctx.extend Ctx.empty (SA.AppExpr "inc" (Ctx.extend Ctx.empty (SA.AppExpr "init" Ctx.empty (SA.StubsAliasRepr counter))) (SA.StubsAliasRepr counter))) SA.StubsIntRepr)]
                    }
            ] [] []
        ],
        SA.stubsInitFns = []   }
```