{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}

{-|
Description: Core ABI Wrapper Module 

Generally, this module, and cabal target, focuses on loading translated Stubs into overrides for use in symbolic execution or analysis.
-}
module Stubs.Wrapper (
    loadParsedPrograms,
    crucibleProgramToFunctionOverride,
    genInitHooks,
    genInitOvHooks
) where

import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Memory as DMM

import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.CFG.SSAConversion as LCCS
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Types as LCT

import qualified Stubs.FunctionOverride as SF
import qualified Stubs.FunctionOverride.ArgumentMapping as SFA
import qualified Stubs.FunctionOverride.Extension.Types as SFT

import qualified Stubs.Wrapper.Exception as SWE

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.String as DS
import qualified Data.Parameterized.Context as Ctx
import qualified System.FilePath as FP
import qualified Control.Monad.Catch as CMC

import           Data.Parameterized.Some ( Some(..) )
import qualified Data.List.NonEmpty as NEL
import           Control.Monad.IO.Class
import Data.Word
import qualified Stubs.Translate as ST
import qualified Stubs.Preamble as SPR
import qualified Stubs.Translate.Core as STC
import qualified Data.Text as DT
import qualified Stubs.AST as SA

-- | Inherited from Ambient : Turn crucible-syntax Parsed Programs into overrides
loadParsedPrograms :: forall ext sym arch w . (ext ~ DMS.MacawExt arch, DMM.MemWidth w) => [(FilePath,LCSC.ParsedProgram ext)] -> [WF.FunctionName] -> [(FilePath, Word64,WF.FunctionName)] -> IO (SFT.CrucibleSyntaxOverrides w () sym arch)
loadParsedPrograms pathProgs startupOverrides funAddrOverrides = do
  overrides <- traverse (uncurry parsedProgToFunctionOverride) pathProgs
  let ovmap = Map.fromList $ map (\sov@(SF.SomeFunctionOverride ov) -> (SF.functionName ov, sov)) overrides
  startupOvs <- traverse (\funName ->
                           case Map.lookup funName ovmap of
                             Just ov -> validateStartupOverride ov
                             Nothing -> CMC.throwM $ SWE.StartupOverrideNameNotFound funName)
                         startupOverrides
  funAddrOvs <- traverse (\(bin, addr, funName) ->
                           let addrMemWord = fromIntegral addr in
                           case Map.lookup funName ovmap of
                             -- NOTE: We construct a singleton here because
                             -- crucible syntax overrides cannot currently call
                             -- into parent overrides.
                             Just ov -> pure ( SF.AddrInBinary addrMemWord bin
                                             , ov NEL.:| [] )
                             Nothing -> CMC.throwM $ SWE.FunctionAddressOverridesNameNotFound
                                          bin addrMemWord funName)
                         funAddrOverrides
  return SFT.CrucibleSyntaxOverrides {
    SFT.csoAddressOverrides = Map.fromList funAddrOvs
    , SFT.csoStartupOverrides = startupOvs
    , SFT.csoNamedOverrides = overrides
  }
  where
    validateStartupOverride ::
      SF.SomeFunctionOverride p sym arch ->
      IO (SF.FunctionOverride p sym Ctx.EmptyCtx arch LCT.UnitType)
    validateStartupOverride (SF.SomeFunctionOverride ov)
      | Just WI.Refl <- WI.testEquality (SF.functionArgTypes ov) Ctx.Empty
      , Just WI.Refl <- WI.testEquality (SF.functionReturnType ov) LCT.UnitRepr
      = pure ov
      | otherwise
      = CMC.throwM $ SWE.StartupOverrideUnexpectedType $ SF.functionName ov

-- | Given a symbolic backend, and a CrucibleProgram, generate a corresponding override
crucibleProgramToFunctionOverride ::  (STC.StubsArch arch, SPR.Preamble arch) =>STC.Sym sym -> ST.CrucibleProgram arch -> IO (SF.SomeFunctionOverride p sym arch)
crucibleProgramToFunctionOverride sym prog = do
    -- Translate preambles into bindings
    let wrappedPre = ST.crFnHandleMap prog
    let preambleBindings = map (wrappedPreambleToBinding sym) wrappedPre
    -- Haskell Overrides to bindings 
    let wrappedHovs = ST.crOvHandleMap prog
    let ovBindings = map (wrappedOverrideToBinding sym) wrappedHovs

    -- Get entry point of override
    case List.partition (isEntryPoint (ST.crEntry prog)) (ST.crCFGs prog) of
      ([LCSC.ACFG argTypes retType cfg], aux) -> do
              let e = WF.functionNameFromText $ DT.pack $ ST.crEntry prog
              let argMap = SFA.bitvectorArgumentMapping argTypes
                  (ptrTypes, ptrTypeMapping) = SFA.pointerArgumentMappping argMap
                  retRepr = SFA.promoteBVToPtr retType
              -- Turn aux cfgs into bindings
              let auxBindings = map acfgToFnBinding aux
              -- Make core override    
              case LCCS.toSSA cfg of
                LCCC.SomeCFG ssaCFG -> return $ SF.SomeFunctionOverride (SF.FunctionOverride {
                    SF.functionName=e,
                    SF.functionGlobals=mempty,
                    SF.functionExterns=mempty,
                    SF.functionArgTypes=ptrTypes,
                    SF.functionReturnType=retRepr,
                    SF.functionAuxiliaryFnBindings=preambleBindings++ovBindings++auxBindings, --Should have preamble + aux fns here
                    SF.functionForwardDeclarations=mempty,
                    SF.functionOverride= \bak args _ _ -> do --will bak as an arg be an issue? this needs to be the same bak
                        pointerArgs <- liftIO $ SFA.buildFunctionOverrideArgs bak argMap ptrTypeMapping args
                        userRes <- LCS.callCFG ssaCFG (LCS.RegMap pointerArgs)
                        SF.OverrideResult [] . LCS.regValue <$> liftIO (SFA.convertBitvector bak retRepr userRes)
                  })
      _ -> fail "Could not find entry point"

-- | Generate overrides for functions marked as init hooks - these are intended to run before symbolic execution of a binary
-- All init hooks have the signature Unit -> Unit
genInitHooks ::(STC.StubsArch arch, SPR.Preamble arch) =>STC.Sym sym -> ST.CrucibleProgram arch -> IO [SF.FunctionOverride p sym Ctx.EmptyCtx arch LCT.UnitType ]
genInitHooks sym prog = do 
      -- Translate preambles into bindings
      let wrappedPre = ST.crFnHandleMap prog
      let preambleBindings = map (wrappedPreambleToBinding sym) wrappedPre
       -- Haskell Overrides to bindings 
      let wrappedHovs = ST.crOvHandleMap prog
      let ovBindings = map (wrappedOverrideToBinding sym) wrappedHovs
      let (inits, _) = List.partition (isInitPoint (ST.crInit prog)) (ST.crCFGs prog) 
      mapM (acfgToInitOverride preambleBindings ovBindings) inits

-- | Similar to genInitHooks, but for init hooks of override modules
genInitOvHooks :: (STC.StubsArch arch, SPR.Preamble arch) =>STC.Sym sym -> ST.CrucibleProgram arch -> IO [SF.FunctionOverride p sym Ctx.EmptyCtx arch LCT.UnitType]
genInitOvHooks sym prog = do 
    let (inits, _) = List.partition (isInitOv (ST.crOvInits prog)) (ST.crOvHandleMap prog)
    mapM (wrappedOverrideToInitOv sym) inits

acfgToInitOverride ::  (STC.StubsArch arch, SPR.Preamble arch) =>  [LCS.FnBinding p sym (DMS.MacawExt arch)] -> [LCS.FnBinding p sym (DMS.MacawExt arch)] -> LCSC.ACFG (DMS.MacawExt arch) -> IO  (SF.FunctionOverride p sym Ctx.EmptyCtx arch LCT.UnitType)
acfgToInitOverride preambleBindings ovBindings (LCSC.ACFG Ctx.Empty LCT.UnitRepr cfg) = do 
  let name = LCF.handleName (LCCR.cfgHandle cfg)
  let argMap = SFA.bitvectorArgumentMapping Ctx.Empty
      (ptrTypes, ptrTypeMapping) = SFA.pointerArgumentMappping argMap
      retRepr = SFA.promoteBVToPtr LCT.UnitRepr
  case LCCS.toSSA cfg of
                LCCC.SomeCFG ssaCFG -> return $ (SF.FunctionOverride {
                    SF.functionName=name,
                    SF.functionGlobals=mempty,
                    SF.functionExterns=mempty,
                    SF.functionArgTypes=ptrTypes,
                    SF.functionReturnType=retRepr,
                    SF.functionAuxiliaryFnBindings=preambleBindings++ovBindings, --Should have preamble + overrides here
                    SF.functionForwardDeclarations=mempty,
                    SF.functionOverride= \bak args _ _ -> do 
                        pointerArgs <- liftIO $ SFA.buildFunctionOverrideArgs bak argMap ptrTypeMapping args
                        userRes <- LCS.callCFG ssaCFG (LCS.RegMap pointerArgs)
                        SF.OverrideResult [] . LCS.regValue <$> liftIO (SFA.convertBitvector bak retRepr userRes)
                  })
acfgToInitOverride _ _ (LCSC.ACFG _ _ cfg)= fail ("Attempted to generate init override with invalid signature: " ++ show (LCCR.cfgHandle cfg))

wrappedOverrideToInitOv :: (STC.StubsArch arch, SPR.Preamble arch) => STC.Sym sym -> ST.SomeWrappedOverride arch -> IO  (SF.FunctionOverride p sym Ctx.EmptyCtx arch LCT.UnitType)
wrappedOverrideToInitOv sym (ST.SomeWrappedOverride (ST.WrappedOverride ovf (STC.StubHandle Ctx.Empty SA.StubsUnitRepr n))) = do 
    let argMap = SFA.bitvectorArgumentMapping Ctx.Empty
        (ptrTypes, ptrTypeMapping) = SFA.pointerArgumentMappping argMap
        retRepr = SFA.promoteBVToPtr LCT.UnitRepr
    return (SF.FunctionOverride {
                    SF.functionName=LCF.handleName n,
                    SF.functionGlobals=mempty,
                    SF.functionExterns=mempty,
                    SF.functionArgTypes=ptrTypes,
                    SF.functionReturnType=retRepr,
                    SF.functionAuxiliaryFnBindings=[], --Should have preamble + overrides here
                    SF.functionForwardDeclarations=mempty,
                    SF.functionOverride= \bak args _ _ -> do 
                        pointerArgs <- liftIO $ SFA.buildFunctionOverrideArgs bak argMap ptrTypeMapping args
                        userRes <- LCS.callOverride n (ovf sym) (LCS.RegMap pointerArgs)
                        SF.OverrideResult [] . LCS.regValue <$> liftIO (SFA.convertBitvector bak retRepr userRes)
                  })

wrappedOverrideToInitOv _ (ST.SomeWrappedOverride (ST.WrappedOverride a (STC.StubHandle _ _ n))) = fail ("Attempted to generate init override with invalid signature: " ++ (show $ LCF.handleName n))


-- | Convert a 'LCSC.ParsedProgram' at a the given 'FilePath' to a function
-- override.
parsedProgToFunctionOverride ::
  ( ext ~ DMS.MacawExt arch ) =>
  String ->
  LCSC.ParsedProgram ext ->
  IO (SF.SomeFunctionOverride () sym arch)
parsedProgToFunctionOverride path parsedProg = do
  let fnName = DS.fromString $ FP.takeBaseName path
  let globals = LCSC.parsedProgGlobals parsedProg
  let externs = LCSC.parsedProgExterns parsedProg
  let (matchCFGs, auxCFGs) = List.partition (isEntryPoint path)
                                            (LCSC.parsedProgCFGs parsedProg)
  let fwdDecs = LCSC.parsedProgForwardDecs parsedProg
  case matchCFGs of
    [] -> CMC.throwM (SWE.CrucibleSyntaxFunctionNotFound fnName path)
    [acfg] ->
      return $ acfgToFunctionOverride fnName globals externs fwdDecs auxCFGs acfg
    _ ->
      -- This shouldn't be possible.  Multiple functions with the same name
      -- should have already been caught by crucible-syntax.
      CMC.throwM $ SWE.DuplicateNamesInCrucibleOverride path fnName

-- | Does a function have the same name as the @.cbl@ file in which it is
-- defined?
isEntryPoint :: String -> LCSC.ACFG ext -> Bool
isEntryPoint path acfg =
  acfgHandleName acfg == DS.fromString path

isInitPoint :: [String] -> LCSC.ACFG ext -> Bool 
isInitPoint initNames acfg = List.elem (show $ acfgHandleName acfg) initNames

isInitOv :: [String] -> ST.SomeWrappedOverride arch -> Bool 
isInitOv initNames (ST.SomeWrappedOverride (ST.WrappedOverride o (STC.StubHandle _ _ hdl) )) = List.elem (show $ LCF.handleName hdl) initNames

-- | Retrieve the 'WF.FunctionName' in the handle in a 'LCSC.ACFG'.
acfgHandleName :: LCSC.ACFG ext -> WF.FunctionName
acfgHandleName (LCSC.ACFG _ _ g) = LCF.handleName (LCCR.cfgHandle g)

-- Convert an ACFG to a FunctionOverride
acfgToFunctionOverride
  :: ( ext ~ DMS.MacawExt arch )
  => WF.FunctionName
  -> Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
  -- ^ GlobalVars used in function override
  -> Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
  -- ^ Externs declared in the override
  -> Map.Map WF.FunctionName LCF.SomeHandle
  -- ^ Forward declarations declared in the override
  -> [LCSC.ACFG ext]
  -- ^ The ACFGs for auxiliary functions
  -> LCSC.ACFG ext
  -> SF.SomeFunctionOverride () sym arch
acfgToFunctionOverride name globals externs fwdDecs auxCFGs (LCSC.ACFG argTypes retType cfg) =
  let argMap = SFA.bitvectorArgumentMapping argTypes
      (ptrTypes, ptrTypeMapping) = SFA.pointerArgumentMappping argMap
      retRepr = SFA.promoteBVToPtr retType
  in case LCCS.toSSA cfg of
       LCCC.SomeCFG ssaCfg ->
         SF.SomeFunctionOverride $ SF.FunctionOverride
         { SF.functionName = name
         , SF.functionGlobals = globals
         , SF.functionExterns = externs
         , SF.functionArgTypes = ptrTypes
         , SF.functionReturnType = retRepr
         , SF.functionAuxiliaryFnBindings = map acfgToFnBinding auxCFGs
         , SF.functionForwardDeclarations = fwdDecs
           -- Note that we do not use the GetVarArg callback below since syntax
           -- overrides do not have a mechanism for variadic arguments. See
           -- Note [Varargs] in Ambient.FunctionOverride.
         , SF.functionOverride = \bak args _getVarArg _parents -> do
             -- Translate any arguments that are LLVMPointers but should be Bitvectors into Bitvectors
             --
             -- This generates side conditions asserting that the block ID is zero
             pointerArgs <- liftIO $ SFA.buildFunctionOverrideArgs bak argMap ptrTypeMapping args
             userRes <- LCS.callCFG ssaCfg (LCS.RegMap pointerArgs)
             -- Convert any BV returns from the user override to LLVMPointers
             SF.OverrideResult [] . LCS.regValue <$> liftIO (SFA.convertBitvector bak retRepr userRes)
         }

-- | Convert an 'LCSC.ACFG' to a 'LCS.FnBinding'.
acfgToFnBinding :: forall sym ext p. LCSC.ACFG ext -> LCS.FnBinding p sym ext
acfgToFnBinding (LCSC.ACFG _ _ g) =
  case LCCS.toSSA g of
    LCCC.SomeCFG ssa ->
      LCS.FnBinding (LCCR.cfgHandle g)
                    (LCS.UseCFG ssa (LCAP.postdomInfo ssa))

wrappedPreambleToBinding :: STC.Sym sym -> ST.SomePreambleOverride arch -> LCS.FnBinding p sym (DMS.MacawExt arch) 
wrappedPreambleToBinding (STC.Sym _ bak) (ST.SomePreambleOverride (ST.PreambleOverride ovf (STC.StubHandle _ _ hdl) )) = LCS.FnBinding hdl (LCS.UseOverride (ovf bak))

wrappedOverrideToBinding :: STC.Sym sym -> ST.SomeWrappedOverride arch -> LCS.FnBinding p sym (DMS.MacawExt arch) 
wrappedOverrideToBinding sym (ST.SomeWrappedOverride (ST.WrappedOverride ovf (STC.StubHandle _ _ hdl))) = LCS.FnBinding hdl (LCS.UseOverride (ovf sym))