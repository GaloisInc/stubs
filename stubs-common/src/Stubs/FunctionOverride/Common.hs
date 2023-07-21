{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Stubs.FunctionOverride.Common
  ( mkFunctionNameGlobMaps
  ) where

import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified What4.FunctionName as WF

import qualified Stubs.Extensions as AE
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.Memory as AM
import qualified Stubs.Memory as SM

-- | Compute a pair of maps, where the first element contains a mapping from
-- function names to overrides, and the second element contains a mapping from
-- global names to global variables. This is ultimately used in service of
-- building a 'AF.FunctionABI'.
mkFunctionNameGlobMaps ::
    forall arch sym w p.
     ( DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , p ~ AE.AmbientSimulatorState sym arch
     )
  => [AF.SomeFunctionOverride p sym arch]
  -- ^ Overrides for functions with particular names
  -> [Some LCS.GlobalVar]
  -- ^ Additional global variables to register for simulation
  -> [AF.SomeFunctionOverride p sym arch]
  -- ^ Specialized overrides
  -> ( Map.Map WF.FunctionName (NEL.NonEmpty (AF.SomeFunctionOverride p sym arch))
     , Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
     )
  -- ^ A pair where the first element contains a mapping from function names to
  -- overrides, and the second element contains a mapping from global names to
  -- global variables.
mkFunctionNameGlobMaps  namedOvs otherGlobs specializedOvs =
    (nameMap, globMap)
  where
    nameMap =
      Map.fromListWith
        (<>)
        [ (AF.functionName fo, sfo NEL.:| [])
        | sfo@(AF.SomeFunctionOverride fo) <-
            customNamedOvs ++ namedOvs
        ]

    globMap = otherGlobMap `Map.union` functionGlobMap

    otherGlobMap =
      Map.fromList
        [ (LCSA.GlobalName (LCS.globalName glob), sg)
        | sg@(Some glob) <- otherGlobs
        ]

    functionGlobMap =
      Map.unions
        [ AF.functionGlobals fo
        | AF.SomeFunctionOverride fo <-
            customNamedOvs ++ namedOvs
        ]

    -- NOTE: The order of elements in customNamedOvs is important.  See @Note
    -- [Override Specialization Order]@ for more information.
    customNamedOvs = specializedOvs

{-
Note [Override Specialization Order]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The order in which overrides appear in @mkFunctionNameGlobMaps@ determines the
hierarchy of overrides that specialize or refine other overrides.  In the event
that multiple overrides in this list have the same name, the verifier will
treat overrides later in the list as children of overrides earlier in the list.
Child overrides receive a list of their parents on invocation and may
optionally call into parent overrides.

We chose this design for the flexibility it provides.  It allows specialized
child overrides to insert computation before and/or after calling into parent
overrides.  It also allows child overrides to completely replace parent
overrides by simply not calling into the parent override.

For example, a child override may call into a parent override, then modify
register state to capture a side effect to a caller saved register (such as in
our specialized @sprintf@ override in
'Ambient.FunctionOverride.X86_64.Linux.Specialized').
-}
