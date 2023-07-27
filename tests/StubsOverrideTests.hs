{-# LANGUAGE OverloadedStrings #-}

-- Tests where Stubs programs are used to override parts of a binary
module StubsOverrideTests(overrideTests) where
import Test.Tasty
import qualified Stubs.AST as SA
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized
import qualified Pipeline as STP
import qualified Data.Parameterized as P
import Test.Tasty.HUnit

-- test generator
genCoreTestIO :: IO [SA.StubsProgram] -> FilePath -> TestName -> Integer -> TestTree
genCoreTestIO iprog path tag exp = testCase tag $ do
    sprog <- iprog
    i <- STP.corePipeline path sprog
    case i of
        Just n -> assertEqual "Unexpected value returned" exp n
        Nothing -> assertFailure "Failed to get return value"


overrideTests = [corePipelinePreambleTest,corePipelineOpaqueTest,corePipelineModuleTest,corePipelineMultipleOverrideTest,corePipelineGlobalTest,corePipelineGlobalITest,mallocOvTest]

corePipelinePreambleTest :: TestTree
corePipelinePreambleTest = testCase "Core Pipeline Preamble Check" $ do
    i <- STP.corePipeline "./tests/test-data/a.out" sProgs
    case i of
        Just n -> assertEqual "Unexpected value returned" n 20
        Nothing -> assertFailure "Failed to get return value"
    where
        sProgs =  [SA.StubsProgram {
    SA.stubsEntryPoints=["f"],
    SA.stubsModules=[SA.mkStubsModule "core" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="f",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.LitExpr $ SA.IntLit 4))  SA.StubsIntRepr)]
        }
    ] [] []]
,SA.stubsInitFns = []}]

corePipelineModuleTest :: TestTree
corePipelineModuleTest = testCase "Core Pipeline Module Check" $ do
    i <- STP.corePipeline "./tests/test-data/a.out" sProgs
    case i of
        Just n -> assertEqual "Unexpected value returned" n 20
        Nothing -> assertFailure "Failed to get return value"
    where
        sProgs =  [SA.StubsProgram {
    SA.stubsEntryPoints=["f"],
    SA.stubsModules=[SA.mkStubsModule "core" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="f",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return (SA.AppExpr "g" (Ctx.extend  Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)))  SA.StubsIntRepr)]
        }
    ] [] [],
    SA.mkStubsModule "internal" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="g",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.LitExpr $ SA.IntLit 4))  SA.StubsIntRepr)]
        }
    ] [] []
    ]
,SA.stubsInitFns = []}]

corePipelineOpaqueTest :: TestTree
corePipelineOpaqueTest = genCoreTestIO (do
        Some counter <- return $ someSymbol "Counter"
        return [SA.StubsProgram {
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
        SA.stubsInitFns = []   }]
    ) "./tests/test-data/a.out" "Core Pipeline Opaque Check" 1

mallocOvTest :: TestTree
mallocOvTest = testCase "Malloc Intrinsic Test" $ do
    Some ptr <- return $ P.someSymbol "Pointer"
    let sprog = SA.StubsProgram {
        SA.stubsEntryPoints=["f"],
        SA.stubsModules=[
            SA.mkStubsModule "internal" [
                SA.SomeStubsFunction SA.StubsFunction {
                    SA.stubFnSig= SA.StubsSignature {
                        SA.sigFnName="f",
                        SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                        SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Assignment (SA.StubsVar "_" (SA.StubsIntrinsicRepr ptr)) (SA.AppExpr "malloc" (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 5)) (SA.StubsIntrinsicRepr ptr)), SA.Return (SA.LitExpr $ SA.IntLit 20)]
                }
            ] [] []
        ],
        SA.stubsInitFns = []
    }
    i <- STP.corePipeline "./tests/test-data/a.out" [sprog] --[STI.BuildOverrideModule (\_ -> mallocOv ptr)]
    case i of
        Just n -> assertEqual "Unexpected value returned" n 20
        Nothing -> assertFailure "Failed to get return value"


corePipelineGlobalTest :: TestTree
corePipelineGlobalTest = genCoreTestIO (do
        Some counter <- return $ someSymbol "Counter"
        return [
            SA.StubsProgram{
                SA.stubsEntryPoints=["f","g","j"],
                SA.stubsModules=[
                    SA.mkStubsModule "counter" [
                    SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 0),SA.Return $  SA.LitExpr SA.UnitLit]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr),SA.Return $  SA.LitExpr SA.UnitLit]},

            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="get",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr]}

                ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl "i" (SA.StubsAliasRepr counter))],
                SA.mkStubsModule "core" [
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="j",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsUnitRepr
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "init" Ctx.empty SA.StubsUnitRepr ), SA.Return $ SA.LitExpr SA.UnitLit]
                        },
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="g",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsIntRepr
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr ), SA.Return $ SA.LitExpr $ SA.IntLit 9]
                        },
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="f",
                                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                                SA.sigFnRetTy=SA.StubsIntRepr
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr ), SA.Return (SA.AppExpr "get" Ctx.empty SA.StubsIntRepr )]
                        }
                ] [] []
                ],
                SA.stubsInitFns = []
            }
            ]
    ) "./tests/test-data/mult.out" "Core Pipeline Global Data" 2

corePipelineGlobalITest :: TestTree
corePipelineGlobalITest = genCoreTestIO (do
        Some counter <- return $ someSymbol "Counter"
        return [
            SA.StubsProgram{
                SA.stubsEntryPoints=["f","g","j"],
                SA.stubsModules=[
                    SA.mkStubsModule "counter" [
                    SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 0),SA.Return $  SA.LitExpr SA.UnitLit]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr),SA.Return $  SA.LitExpr SA.UnitLit]},

            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="get",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr]}

                ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl "i" (SA.StubsAliasRepr counter))],
                SA.mkStubsModule "core" [
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="j",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsUnitRepr
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "init" Ctx.empty SA.StubsUnitRepr ), SA.Return $ SA.LitExpr SA.UnitLit]
                        },
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="g",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsIntRepr
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr ), SA.Return $ SA.LitExpr $ SA.IntLit 9]
                        },
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="f",
                                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                                SA.sigFnRetTy=SA.StubsIntRepr
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr ), SA.Return (SA.AppExpr "get" Ctx.empty SA.StubsIntRepr )]
                        }
                ] [] []
                ],
                SA.stubsInitFns = []
            }
            ]
    ) "./tests/test-data/mult_i.out" "Core Pipeline Global Data (with intermediate variable return)" 2

corePipelineMultipleOverrideTest :: TestTree
corePipelineMultipleOverrideTest = genCoreTestIO (do
    return [SA.StubsProgram{
        SA.stubsEntryPoints=["f","g"],
        SA.stubsModules=[
            SA.mkStubsModule "core" [
                SA.SomeStubsFunction
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="f",
                                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                                SA.sigFnRetTy=SA.StubsIntRepr
                            },
                        SA.stubFnBody=[SA.Return (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr) )]
                    },
                SA.SomeStubsFunction
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="g",
                                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                                SA.sigFnRetTy=SA.StubsIntRepr
                            },
                        SA.stubFnBody=[SA.Return (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr) )]
                    }
            ] [] []
        ],
        SA.stubsInitFns=[]
    }]
    ) "./tests/test-data/two.out" "Core Pipeline with multiple overrides (no sharing)" 2

