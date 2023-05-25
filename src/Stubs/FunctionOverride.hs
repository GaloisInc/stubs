{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.FunctionOverride (
    FunctionOverride(..)
  , OverrideResult(..)
  , mkFunctionOverride
  , mkVariadicFunctionOverride
  , mkVariadicSpecializedFunctionOverride
  , syscallToFunctionOverride
  , GetVarArg(..)
  , SomeFunctionOverride(..)
  , FunctionOverrideHandle
  , FunctionAddrLoc(..)
  , FunctionABI(..)
  , BuildFunctionABI(..)
  , FunctionOverrideContext(..)
  ) where

import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Memory as AM
import qualified Stubs.Syscall as AS

-------------------------------------------------------------------------------
-- Function Call Overrides
-------------------------------------------------------------------------------

-- | OverrideResult holds the register updates and return value from an
-- override
data OverrideResult sym arch ret = OverrideResult
  { regUpdates :: [( DMC.ArchReg arch (DMT.BVType (DMC.ArchAddrWidth arch))
                   , LCLM.LLVMPtr sym (DMC.ArchAddrWidth arch) )]
  -- ^ Registers to update.  An assoc list from registers to the values they
  -- should be updated to contain.  If a key in the assoc list appears twice,
  -- the later updates will clobber the earlier ones.
  , result :: LCS.RegValue sym ret
  -- ^ Return value from the override.
  }

-- | FunctionOverride captures an override and type information about how to
-- call it
data FunctionOverride p sym args arch ret =
  FunctionOverride
    { functionName :: WF.FunctionName
    -- ^ Name of the function
    , functionGlobals :: Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
    -- ^ Global variables the function uses
    , functionExterns :: Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
    -- ^ Externs associated with a syntax override that must be inserted into
    --   the symbolic global state before invoking the override.
    --   See @Wrinkle: Externs@ in @Note [Resolving forward declarations]@ in
    --   "Ambient.FunctionOverride.Overrides.ForwardDeclarations".
    , functionArgTypes :: LCT.CtxRepr args
    -- ^ Types of the arguments to the function
    , functionReturnType :: LCT.TypeRepr ret
    -- ^ Return type of the function
    , functionAuxiliaryFnBindings :: [LCS.FnBinding p sym (DMS.MacawExt arch)]
    -- ^ Bindings for every auxiliary function that is called
    --   from the 'functionOverride' but does not have a
    --   'FunctionOverride' of its own. This is primarily
    --   intended for local functions that are not meant to be
    --   invoked from other functions besides the one being
    --   overridden.
    --
    --   Currently, the sole use case for this feature is to
    --   support @<name>.cbl@ files that define functions
    --   besides ones named @<name>@. While these functions
    --   cannot be invoked directly from machine code
    --   simulation, they can be invoked by syntax overrides, so
    --   we must register them in the simulator.
    --
    --   Note that it is OK for multiple auxiliary functions
    --   across different 'FunctionOverrides' files to have the
    --   same name. This is because the simulator looks up
    --   functions by their handle, not by their name, and since
    --   handles are uniquely identified in Crucible, different
    --   auxiliary functions with the same name won't conflict
    --   with each other.
    , functionForwardDeclarations ::
        Map.Map WF.FunctionName LCF.SomeHandle
    -- ^ Forward declarations associated with a syntax override
    --   that must be registered before invoking the override.
    --   See @Note [Resolving forward declarations]@ in
    --   "Ambient.FunctionOverride.Overrides.ForwardDeclarations".
    , functionOverride
        :: forall bak solver scope st fs
         . ( LCB.IsSymBackend sym bak
           , sym ~ WE.ExprBuilder scope st fs
           , bak ~ LCBO.OnlineBackend solver scope st fs
           , WPO.OnlineSolver solver
           )
        => bak
        -> Ctx.Assignment (LCS.RegEntry sym) args
        -- Known arguments to function
        -> GetVarArg sym
        -- Variadic arguments to function
        -> [ SomeFunctionOverride p sym arch ]
        -- ^ Parent overrides
        -> (forall rtp args' ret'. LCS.OverrideSim p sym (DMS.MacawExt arch) rtp args' ret' (OverrideResult sym arch ret))
    -- ^ Override capturing behavior of the function
    }

-- | A smart constructor for 'FunctionOverride' for the common case when:
--
-- * There are no global variables.
--
-- * No externs are used.
--
-- * The argument and result types are statically known.
--
-- * No auxiliary function bindings are used.
--
-- * No forward declarations are used.
--
-- * The override does not make use of variadic arguments (see
--   @Note [Varargs]@).
mkFunctionOverride ::
  ( LCT.KnownRepr LCT.CtxRepr args
  , LCT.KnownRepr LCT.TypeRepr ret
  ) =>
  WF.FunctionName ->
  (forall bak solver scope st fs
     . ( LCB.IsSymBackend sym bak
       , sym ~ WE.ExprBuilder scope st fs
       , bak ~ LCBO.OnlineBackend solver scope st fs
       , WPO.OnlineSolver solver
       )
    => bak
    -> Ctx.Assignment (LCS.RegEntry sym) args
    -> (forall rtp args' ret'. LCS.OverrideSim p sym (DMS.MacawExt arch) rtp args' ret' (LCS.RegValue sym ret))) ->
  FunctionOverride p sym args arch ret
mkFunctionOverride name ov =
  mkVariadicFunctionOverride name $ \bak args _getVarArg -> ov bak args

-- | Like 'mkFunctionOverride', but where the function override can make use of
-- variadic arguments (see @Note [Varargs]@).
mkVariadicFunctionOverride ::
  ( LCT.KnownRepr LCT.CtxRepr args
  , LCT.KnownRepr LCT.TypeRepr ret
  ) =>
  WF.FunctionName ->
  (forall bak solver scope st fs
     . ( LCB.IsSymBackend sym bak
       , sym ~ WE.ExprBuilder scope st fs
       , bak ~ LCBO.OnlineBackend solver scope st fs
       , WPO.OnlineSolver solver
       )
    => bak
    -> Ctx.Assignment (LCS.RegEntry sym) args
    -> GetVarArg sym
    -> (forall rtp args' ret'. LCS.OverrideSim p sym (DMS.MacawExt arch) rtp args' ret' (LCS.RegValue sym ret))) ->
  FunctionOverride p sym args arch ret
mkVariadicFunctionOverride name ov = FunctionOverride
  { functionName = name
  , functionGlobals = Map.empty
  , functionExterns = Map.empty
  , functionArgTypes = LCT.knownRepr
  , functionReturnType = LCT.knownRepr
  , functionAuxiliaryFnBindings = []
  , functionForwardDeclarations = Map.empty
  , functionOverride = \bak args getVarArg _parents -> OverrideResult [] <$> ov bak args getVarArg
  }

-- | Like 'mkVariadicFunctionOverride', but where the function override can
-- make use of parent override implementations.
mkVariadicSpecializedFunctionOverride ::
  ( LCT.KnownRepr LCT.CtxRepr args
  , LCT.KnownRepr LCT.TypeRepr ret
  ) =>
  WF.FunctionName ->
  (forall bak solver scope st fs
     . ( LCB.IsSymBackend sym bak
       , sym ~ WE.ExprBuilder scope st fs
       , bak ~ LCBO.OnlineBackend solver scope st fs
       , WPO.OnlineSolver solver
       )
    => bak
    -> Ctx.Assignment (LCS.RegEntry sym) args
    -> GetVarArg sym
    -> [ SomeFunctionOverride p sym arch ]
    -> (forall rtp args' ret'. LCS.OverrideSim p sym (DMS.MacawExt arch) rtp args' ret' (OverrideResult sym arch ret))) ->
  FunctionOverride p sym args arch ret
mkVariadicSpecializedFunctionOverride name ov = FunctionOverride
  { functionName = name
  , functionGlobals = Map.empty
  , functionExterns = Map.empty
  , functionArgTypes = LCT.knownRepr
  , functionReturnType = LCT.knownRepr
  , functionAuxiliaryFnBindings = []
  , functionForwardDeclarations = Map.empty
  , functionOverride = ov
  }

-- | Convert a 'AS.Syscall' override to a 'FunctionOverride' with the same
-- semantics. Note that this override will not perform any error-checking on
-- the value returned by the syscall. (See #144.)
syscallToFunctionOverride ::
  FunctionOverrideContext arch sym ->
  -- ^ In what context is this override being run?
  AS.Syscall p sym args (DMS.MacawExt arch) ret ->
  FunctionOverride p sym args arch ret
syscallToFunctionOverride fovCtx syscallOv = FunctionOverride
  { functionName = name
  , functionGlobals = Map.empty
  , functionExterns = Map.empty
  , functionArgTypes = AS.syscallArgTypes syscallOv
  , functionReturnType = AS.syscallReturnType syscallOv
  , functionAuxiliaryFnBindings = []
  , functionForwardDeclarations = Map.empty
  , functionOverride = \bak args _getVarArg _parents -> do
      OverrideResult [] <$> AS.syscallOverride syscallOv bak args
  }
  where
    name = AS.syscallName syscallOv

-- | Given a type, retrieve the value of a variadic argument in a function
-- override, as well a callback for retrieving the next variadic argument.
-- This is monadic since there is a possibility that the variadic argument must
-- be loaded from the stack. See @Note [Varargs]@.
newtype GetVarArg sym = GetVarArg
  ( forall tp.
    LCT.TypeRepr tp ->
    IO (LCS.RegEntry sym tp, GetVarArg sym)
  )

data SomeFunctionOverride p sym arch =
  forall args ret . SomeFunctionOverride (FunctionOverride p sym args arch ret)

-- | A 'LCF.FnHandle' for a function override.
type FunctionOverrideHandle arch =
  LCF.FnHandle
    (LCT.EmptyCtx LCT.::> LCT.StructType (DMS.MacawCrucibleRegTypes arch))
    (LCT.StructType (DMS.MacawCrucibleRegTypes arch))

-- | Where is a function's address located?
data FunctionAddrLoc w
  = AddrInBinary (DMC.MemWord w) FilePath
    -- ^ The function address is located in a binary at the given 'FilePath'.
    --
    -- By convention, the 'FilePath' is the name of the binary, not its full
    -- path. This convention is convenient for a couple of reasons:
    --
    -- * When displaying the binary via the @list-overrides@ command, it
    --   results in more compact output.
    --
    -- * When specifying function address overrides in an @overrides.yaml@
    --   file, users need only write down the file name. We could,
    --   theoretically, require users to write down full paths, but this would
    --   (1) be more annoying and (2) make the @overrides.yaml@ file less
    --   portable.
  | AddrFromKernel (DMC.MemWord w)
    -- ^ The function address is provided by the kernel itself. See
    --   @Note [AArch32 and TLS]@ in "Ambient.FunctionOverride.AArch32.Linux"
    --   for one application of this.
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Function Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the FunctionCall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data FunctionABI arch sym p =
  FunctionABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the function call. See Note [Passing arguments to functions].
    functionIntegerArguments
      :: forall bak atps
       . LCB.IsSymBackend sym bak
      => bak
      -> LCT.CtxRepr atps
      -- Types of arguments
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Argument register values
      -> LCLM.MemImpl sym
      -- The memory state at the time of the function call
      -> IO (Ctx.Assignment (LCS.RegEntry sym) atps, GetVarArg sym)
      -- A pair containing the function argument values and a callback for
      -- retrieving variadic arguments.

    -- The registers used to pass integer arguments to functions.
  , functionIntegerArgumentRegisters
      :: [DMC.ArchReg arch (DMT.BVType (DMC.ArchAddrWidth arch))]

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , functionIntegerReturnRegisters
     :: forall bak t r args rtp mem
      . LCB.IsSymBackend sym bak
     => bak
     -> DMS.GenArchVals mem arch
     -- Architecture-specific information
     -> LCT.TypeRepr t
     -- Function return type
     -> OverrideResult sym arch t
     -- Function's return value
     -> LCS.RegValue sym (DMS.ArchRegStruct arch)
     -- Argument register values from before function execution
     -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
     -- OverrideSim action with return type matching system return register
     -- type

    -- If the return address for the function being called can be determined,
    -- then return Just that address. Otherwise, return Nothing. Some ABIs
    -- store this information directly in a register, while other ABIs store
    -- this information on the stack, so we provide both registers and the stack
    -- as arguments.
  , functionReturnAddr
      :: forall bak solver scope st fs mem
       . ( LCB.IsSymBackend sym bak
         , sym ~ WE.ExprBuilder scope st fs
         , bak ~ LCBO.OnlineBackend solver scope st fs
         , WPO.OnlineSolver solver
         )
      => bak
      -> DMS.GenArchVals mem arch
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Registers for the given architecture
      -> LCLM.MemImpl sym
      -- The memory state at the time of the function call
      -> IO (Maybe (DMC.MemWord (DMC.ArchAddrWidth arch)))

    -- A mapping of function addresses to overrides. This is utilized for two
    -- purposes:
    --
    -- * User-provided overrides at particular addresses, as specified in an
    --   @overrides.yaml@ file.
    --
    -- * Kernel-provided user helpers that are reachable from user space
    --   at fixed addresses in kernel memory. In particular, see
    --   Note [AArch32 and TLS] in Ambient.FunctionOverride.AArch32.Linux for
    --   how this is used to implement TLS for AArch32 binaries.
    --
    -- Note that if a function's address has an override in this map, that will
    -- always take precedence over any overrides for functions of the same name
    -- in 'functionNameMapping'.  The values of the mapping are nonempty lists
    -- to ensure that at least one override actually exists for each key in the
    -- map.
    --
    -- See @Note [NonEmpty List Override Mapping Values]@ for information on
    -- why the values for the mapping are nonempty lists.
  , functionAddrMapping
     :: Map.Map (FunctionAddrLoc (DMC.ArchAddrWidth arch))
                (NEL.NonEmpty (SomeFunctionOverride p sym arch))

    -- A mapping from function names to overrides.
    --
    -- See @Note [NonEmpty List Override Mapping Values]@ for information on
    -- why the values for the mapping are nonempty lists.
  , functionNameMapping
     :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
     => Map.Map WF.FunctionName
                (NEL.NonEmpty (SomeFunctionOverride p sym arch))

    -- A mapping from global names to global variables.
  , functionGlobalMapping
     :: Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
  }

-- A function to construct a FunctionABI with memory access
newtype BuildFunctionABI arch sym p = BuildFunctionABI (
       forall mem
     . FunctionOverrideContext arch sym
    -- In what context are the function overrides are being run?
    -> LCLS.LLVMFileSystem (DMC.ArchAddrWidth arch)
    -- File system to use in overrides
    -> AM.InitialMemory sym (DMC.ArchAddrWidth arch)
    -> DMS.GenArchVals mem arch
    -- Architecture-specific information
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) String
    -- ^ Mapping from unsupported relocation addresses to the names of the
    -- unsupported relocation types.
    -> Map.Map (FunctionAddrLoc (DMC.ArchAddrWidth arch))
               (NEL.NonEmpty (SomeFunctionOverride p sym arch))
    -- Overrides for functions at particular addresses
    -> [ SomeFunctionOverride p sym arch ]
    -- Overrides for functions with particular names
    -> [ Some LCS.GlobalVar ]
    -- Additional global variables to register for simulation
    -> FunctionABI arch sym p
  )

-- | In what context are we running a function override? This tracked because
-- some function overrides (e.g., @get-global-pointer-named@) can only be run in
-- a 'VerifyContext', which has access to information about binaries.
data FunctionOverrideContext arch sym where
  -- | A function override is being ran from the @list-overrides@ command, which
  -- runs independently of any binary.
  TestContext :: FunctionOverrideContext arch sym

{-
Note [Passing arguments to functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Under most circumstances, a function's arguments will be passed by way of
registers. Extracting argument values from registers is a relatively
straightforward process of looking up the appropriate entry in the register
assignment that is passed to `functionIntegerArguments` in a `FunctionABI`.

If a function has a sufficiently large number of arguments, however, the
arguments that cannot be put into registers will instead be stored on the
stack. Extracting argument values from the stack is a slightly more involved
process, since it requires reading values from memory. The
A.FunctionOverride.StackArguments.loadStackArgument function takes care of most
of these fiddly details. The remaining fiddly detail is determining _which_
stack entries to read, since this varies depending on the calling convention.
For instance, the System V x86_64 ABI puts the first stack argument at
8(%rsp), since 0(%rsp) is reserved for the callee's function address. On the
other hand, the AArch32 calling convention puts the first stack argument at
[sp, #0]. These ABI-specific details are handled in each `FunctionABI`'s
implementation of `functionIntegerArguments`.

At present, we only support integer arguments whose size matches the size of
a pointer on the given architecture. Notably, we do not support any of the
following:

* Floating-point arguments
* Struct arguments. These complicate matters due to the fact that struct values
  can be split up into multiple registers or stack values depending on the size
  of the struct.
* Eight-byte values of 32-bit architectures

Note [Varargs]
~~~~~~~~~~~~~~
Various C functions accept variadic arguments (or varargs for short), e.g.,

  int sprintf(char *str, const char *format, ...);

Here, the `...` represents zero or more arguments of possibly differing types.
At the machine code level, however, there is no distinction between varargs and
the arguments that come before them. If a C program calls
sprintf(out, "%d %s", 42, "abc"), then at the machine code level, the sprintf
function will be called with all of its arguments placed in registers. If
sprintf is called with even more arguments, then some of those arguments may be
spilled to the stack. (See Note [Passing arguments to functions] for more
about how stack arguments work.)

While varargs are not particularly remarkable at the machine level, they pose
an interesting challenge for function overrides. For instance, we have a
built-in override for sprintf, and we would like to only define the override
once such that it works with any numbers of arguments. However, we do not know
in advance how many arguments sprintf will be given. When running the built-in
override for sprintf, we need to be able to load additional arguments on demand
based on the contents of the format string.

Our solution to this problem is to pass a GetVarArg callback to the type of
`functionOverride`, where GetVarArg is defined as:

  newtype GetVarArg sym = GetVarArg
    ( forall tp.
      LCT.TypeRepr tp ->
      IO (LCS.RegEntry sym tp, GetVarArg sym)
    )

Given a type, this callback will return a pair containing (1) the vararg value
of that type, and (2) another callback for loading the next vararg. The design
of GetVarArg is very similar to that of C's va_arg macro, which also loads
arguments one at a time in a type-directed fashion. In the case of the sprintf
example, the sprintf override can invoke GetVarArg as many times as needed
based on the contents of the format string.

The Ambient.Override.buildArgumentAssignment function is responsible for
implementing the GetVarArg callback that is passed to `functionOverride`. This
function takes a set of known (i.e., non-variadic) argument types and matches
them up to register or stack values as appropriate. The argument values that
are left over (let's call this the "vararg list") are then used to implement a
GetVarArg callback. Each time you invoke GetVarArg, it will pop off a value
from the vararg list and return a pair containing that value and another
GetVarArg callback that uses the remainder of the vararg list. Because there
could be an arbitrary number of variadic arguments, the vararg list is an
infinite list. After exhausing the register values, the vararg list will
read from the stack at higher and higher offsets.

As a concrete example, let's suppose you invoke the sprintf function override
on AArch32 like so:

  sprintf(out, "%d %s %d", 42, "abc", 27);

When invoking buildArgumentAssignment, the first two arguments will immediately
be paired up with registers (r0 and r1 on AArch32), since they are non-variadic
arguments. The remaining arguments are variadic, so they will be taken from a
vararg list that looks like this:

  {r3, r4, [sp, #0], [sp #4], [sp #8], [sp #12], ...}

Here, the first two entries (r3 and r4) are registers, and all other entries
are different offsets into the stack pointer (sp). The sprintf override will
call GetVarArg three times, causing the first three entries to be read for
their values. That is all the arguments that this particular example needs,
but the same approach would work for an even greater number of arguments, since
the vararg list is infinite.

Some follow-up observations about the verifier's implementation of varargs:

* Although buildArgumentAssignment always returns a GetVarArg callback, not
  all call sites of buildArgumentAssignment actually make use of it. For
  instance, syscall overrides use buildArgumentAssignment solely for register
  arguments, and no system call uses variadic arguments.

* Similarly, although the type of `functionOverride` always includes a
  GetVarArg callback, most function overrides don't actually use it. For
  instance, syntax overrides never make use of the GetVarArg callback since
  they do not have a mechanism for handling varargs.

* What happens if a .cbl file `declare`s a built-in override for a variadic
  function like sprintf? We permit this, but we only permit the `declare`d
  type to contain the non-variadic arguments. For instance, the `delcare`d
  type of `sprintf` must be:

    (declare @sprintf ((str Pointer) (format Pointer)) Int)

  Attempting to `declare` it with any more argument types will result in a type
  error. This is admittedly pretty limiting, but designing a way to robustly
  handle varargs at the syntax override level will take some thought and
  effort. We will wait for someone to complain about this before initiating
  that effort.

Note [NonEmpty List Override Mapping Values]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We use NonEmpty lists as values in the address-to-override and
name-to-override mappings to provide a heirarchy of overrides.  The overrides
towards the front of each list are refinements of those towards the back of
each list.  When the verifier reaches a function to dispatch an override for,
it executes the override at the head of the list and passes the tail of the
list to the override.  This override may then optionally call into the next
override in the list, and so on.  We use this functionality to implement
specialized overrides which perform additional work before or after the
execution of a more generic override.

We require that each list is nonempty to ensure that at least one override
exists for every key.
-}
