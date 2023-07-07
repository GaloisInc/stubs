{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Stubs.Wrapper (
    loadParsedPrograms,
    loadStubsPrograms,
    crucibleProgToParsedProg
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
import qualified Data.Parameterized.Nonce as PN

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
import qualified Stubs.AST as SA
import qualified Stubs.Translate as ST
import qualified Stubs.Preamble as SPR
import qualified Stubs.Translate.Core as STC

crucibleProgToParsedProg :: ST.CrucibleProgram arch -> LCSC.ParsedProgram (DMS.MacawExt arch) 
crucibleProgToParsedProg ST.CrucibleProgram{ST.crCFGs=cfgs, ST.crGlobals= glbls, ST.crExterns=externs, ST.crFwdDecs=fwds} = LCSC.ParsedProgram {
  LCSC.parsedProgCFGs= cfgs,
  LCSC.parsedProgExterns=externs,
  LCSC.parsedProgForwardDecs=fwds,
  LCSC.parsedProgGlobals=glbls
}

stubsProgramToOverride :: forall ext p sym arch. (ext ~ DMS.MacawExt arch, STC.StubsArch arch, SPR.Preamble arch) => SA.StubsProgram -> IO [SF.SomeFunctionOverride p sym arch]
stubsProgramToOverride prog = do 
  hAlloc <- LCF.newHandleAllocator
  Some ng <- PN.newIONonceGenerator
  crucProgs <- ST.translateProgram ng hAlloc prog
  mapM (\crucProg -> parsedProgToFunctionOverride (ST.crEntry crucProg) (crucibleProgToParsedProg crucProg)) crucProgs

loadStubsPrograms :: forall ext p sym arch w . (ext ~ DMS.MacawExt arch, STC.StubsArch arch,SPR.Preamble arch) => [SA.StubsProgram] -> IO (SFT.CrucibleSyntaxOverrides w p sym arch)
loadStubsPrograms progs = do 
  overrides <- mapM stubsProgramToOverride progs 
  return SFT.CrucibleSyntaxOverrides {
    SFT.csoAddressOverrides = Map.empty
    , SFT.csoStartupOverrides = []
    , SFT.csoNamedOverrides = concat overrides
  }


loadParsedPrograms :: forall ext p sym arch w . (ext ~ DMS.MacawExt arch, DMM.MemWidth w) => [(FilePath,LCSC.ParsedProgram ext)] -> [WF.FunctionName] -> [(FilePath, Word64,WF.FunctionName)] -> IO (SFT.CrucibleSyntaxOverrides w p sym arch)
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

-- | Convert a 'LCSC.ParsedProgram' at a the given 'FilePath' to a function
-- override.
parsedProgToFunctionOverride ::
  ( ext ~ DMS.MacawExt arch ) =>
  String ->
  LCSC.ParsedProgram ext ->
  IO (SF.SomeFunctionOverride p sym arch)
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
  -> SF.SomeFunctionOverride p sym arch
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
             SF.OverrideResult [] <$> LCS.regValue <$> liftIO (SFA.convertBitvector bak retRepr userRes)
         }

-- | Convert an 'LCSC.ACFG' to a 'LCS.FnBinding'.
acfgToFnBinding :: forall p sym ext. LCSC.ACFG ext -> LCS.FnBinding p sym ext
acfgToFnBinding (LCSC.ACFG _ _ g) =
  case LCCS.toSSA g of
    LCCC.SomeCFG ssa ->
      LCS.FnBinding (LCCR.cfgHandle g)
                    (LCS.UseCFG ssa (LCAP.postdomInfo ssa))