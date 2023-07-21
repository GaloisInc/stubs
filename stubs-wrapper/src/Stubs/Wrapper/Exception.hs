{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}

{-| Module for wrapper related exceptions -}
module Stubs.Wrapper.Exception 
    (StubsLoaderException(..))
where

import qualified Control.Exception as X
import qualified What4.FunctionName as WF
import qualified Data.Macaw.Memory as DMM

data StubsLoaderException where 
    CrucibleSyntaxFunctionNotFound :: WF.FunctionName -> FilePath -> StubsLoaderException
    DuplicateNamesInCrucibleOverride :: FilePath -> WF.FunctionName -> StubsLoaderException
    FunctionAddressOverridesNameNotFound :: DMM.MemWidth w => FilePath -> DMM.MemWord w -> WF.FunctionName -> StubsLoaderException
    StartupOverrideNameNotFound :: WF.FunctionName -> StubsLoaderException
    StartupOverrideUnexpectedType :: WF.FunctionName -> StubsLoaderException

deriving instance Show StubsLoaderException
instance X.Exception StubsLoaderException