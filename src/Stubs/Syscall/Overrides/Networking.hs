{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.Syscall.Overrides.Networking
  ( networkOverrides
  , buildAcceptOverride
  , callAccept
  , buildBindOverride
  , callBind
  , buildConnectOverride
  , callConnect
  , buildListenOverride
  , callListen
  , buildRecvOverride
  , callRecv
  , buildSendOverride
  , callSend
  , buildSocketOverride
  , callSocket
  ) where


import           Control.Lens ( (%=) )
import qualified Control.Lens as Lens
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import           Data.Word ( Word16 )
import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.SymIO as LCSy
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.ProgramLoc as WP

import qualified Stubs.Exception as AE
import qualified Stubs.Extensions as AExt
import           Stubs.Syscall
import           Stubs.Syscall.Overrides.Networking.Types
import qualified Stubs.Memory as AM
import           Stubs.Override
import qualified Stubs.Panic as AP
import qualified Stubs.Syscall.Overrides.SymIO as ASOS
import qualified Stubs.Verifier.Concretize as AVC

{-
Note [The networking story]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
The verifier has limited support for socket I/O. The verifier defines enough
overrides (see `networkOverrides`) to simulate basic socket server and client
programs. These overrides emulate socket connections by opening specific files
on the symbolic filesystem.

When a program invokes socket(domain, type, protocol), the following file will
be opened:

  /network/<domain_macro>/<type_macro>/socket

Where:

* <domain_macro> is the name of the C macro that corresponds to the `domain`
  value passed to socket(). For example, a `domain` value of 2 corresponds to
  the AF_INET macro, so that would result in /network/AF_INET/...

* <type_macro> is the name of the C macro that corresponds to the `type` value
  passed to socket(). For example, a `type` value of 1 corresponds to the
  SOCK_STREAM macro, so that would reult in /network/.../SOCK_STREAM/...

For servers, the contents of this .../socket file don't matter that much. For
clients, this file is used for network communication, so
`read`ing/`recv`ing from this file simulates receiving a message from the
server, and `send`ing/`write`ing to this file simulates sending a message to
the server.

When a program invokes accept(sockfd, addr, addrlen), a file will be opened at
a path depending on the socket domain:

* If it is an AF_UNIX socket, the following file will be opened:

    <sun_path>/<seq_num>

  Where:

  * <sun_path> is the value in the `sun_path` field of the `sockaddr_un` struct
    passed to bind() when binding the socket.

  * <seq_num> indicates the order in which each call to accept() was made. For
    example, the first accept() call will be given a <seq_num> of 0, the second
    accept() call will be given a <seq_num> of 1, etc.

* If it is an AF_INET or AF_INET6 socket, the  following file will be opened:

    /network/<domain_macro>/<type_macro>/<port>/<seq_num>

  Where:

  * <domain_macro> and <type_macro> are the same values as in the socket() case.
    <port> is the same value that was passed to bind() when assigning a name to
    the socket. (We'll describe how the verifier looks up these values in a bit.)

  * <seq_num> indicates the order in which each call to accept() was made.

These overrides use a crucible-symio LLVMFileSystem under the hood to track
these files. One limitation of an LLVMFileSystem is that there isn't a simple
way to associate extra metadata with each file. That is to say, after socket()
returns a file descriptor, there isn't an easy way to use that file descriptor
to look up its file path, port number, the number of connections etc. One might
be tempted to pass around a GlobalVar containing this metadata, but it's not
obvious what CrucibleType such a GlobalVar would have, since we would need some
kind of map-like structure.

Our solution to this problem is to add a `serverSocketFDs` field to the
AmbientSimulatorState, which is passed around across all overrides. This
contains a map of file descriptors to ServerSocketInfo, which is a collection of
metadata that gradually gets filled in after calls to socket() and bind().
This is not a perfect solution (more on this in a bit), but it is sufficient to
handle the kinds of network programs we are targeting.

Note that this metadata is only needed in service of figuring out the name of
the filepath that accept() opens, which is only needed for servers. Clients do
not need to invoke accept(), which is why there is not a corresponding
ClientSocketInfo data type.

There are a variety of limitations surrounding how this works to be aware of:

* AmbientSimulatorState is passed around in the `personality` of each
  OverrideSim, which does not participate in branching and merging. One could
  imagine a program for which this is problematic (e.g., a socket that
  conditionally gets created depeneding on the value of symbolic data), but we
  do not anticipate this being an issue in practice.

* Because the names of crucible-symio filepaths must be concrete, a socket's
  domain, type, and path (for AF_UNIX sockets) or port number (for AF_INET{6}
  sockets) must all be concrete, since they all appear in filepath names.
  Again, we do not anticipate many programs in the wild will try to make this
  information symbolic. The file descriptor for each socket must also be
  concrete, but since crucible-symio always allocates concrete file descriptors
  anyway, this requirement is easily satisfied.

* The domain value passed to socket() must be listed in the `socketDomainMap`.
  We could, in theory, support other forms of communication, but we do not do so
  at present.

* The type value passed to socket() must be listed in the `socketTypeMap`.
  We could, in theory, support other forms of communication semantics, but we
  do not do so at present.

* Because crucible-symio's open() implementation does not support creating new
  files (see https://github.com/GaloisInc/crucible/issues/803), all of the
  files under the /network directory must be specified ahead of time in the
  initial symbolic filesystem.

* The accept() override, unlike the syscall it models, completely ignores the
  addr and addrlen arguments. To model accept() more faithfully, it should fill
  in these arguments with information about the peer socket address. See #77.
-}

-- | All of the socket I/O–related overrides, packaged up for your
-- convenience.
networkOverrides :: ( LCLM.HasLLVMAnn sym
                    , LCLM.HasPtrWidth w
                    , DMC.MemWidth w
                    , w ~ DMC.ArchAddrWidth arch
                    )
                 => LCLS.LLVMFileSystem w
                 -> AM.InitialMemory sym w
                 -- ^ Initial memory state for symbolic execution
                 -> Map.Map (DMC.MemWord w) String
                 -- ^ Mapping from unsupported relocation addresses to the names of the
                 -- unsupported relocation types.
                 -> [SomeSyscall (AExt.AmbientSimulatorState sym arch) sym ext]
networkOverrides fs initialMem unsupportedRelocs =
  [ SomeSyscall (buildAcceptOverride fs)
  , SomeSyscall (buildBindOverride fs initialMem unsupportedRelocs)
  , SomeSyscall buildConnectOverride
  , SomeSyscall buildListenOverride
  , SomeSyscall (buildRecvOverride fs memVar)
  , SomeSyscall (buildSendOverride fs memVar)
  , SomeSyscall (buildSocketOverride fs)
  ]
  where
    memVar = AM.imMemVar initialMem

buildAcceptOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => LCLS.LLVMFileSystem w
                    -> Syscall (AExt.AmbientSimulatorState sym arch) sym
                               (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                             Ctx.::> LCLM.LLVMPointerType w
                                             Ctx.::> LCLM.LLVMPointerType w) ext
                               (LCLM.LLVMPointerType w)
buildAcceptOverride fs =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "accept" $ \bak args ->
    Ctx.uncurryAssignment (callAccept fs bak) args

-- | Override for the @accept(2)@ syscall. This function looks up the metadata
-- associated with the socket file descriptor argument, allocates a new socket
-- file with a unique name, and records this information in the
-- 'AE.AmbientSimulatorState'. See Note @[The networking story]@ for the full
-- details.
callAccept :: forall sym bak arch w p solver scope st fs ext r args ret
            . ( LCB.IsSymBackend sym bak
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , WPO.OnlineSolver solver
              , LCLM.HasPtrWidth w
              , w ~ DMC.ArchAddrWidth arch
              , p ~ AExt.AmbientSimulatorState sym arch
              )
           => LCLS.LLVMFileSystem w
           -> bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                              (LCS.RegValue sym (LCLM.LLVMPointerType w))
callAccept fs bak sockfd _addr _addrlen = do
  sockfdInt <- liftIO $ networkConstantBVPtrToInteger bak "accept" AE.FDArgument (LCS.regValue sockfd)
  serverSocketFDs <- Lens.use (LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs)
  fd <-
    case Map.lookup sockfdInt serverSocketFDs of
      Just (Some ssi@(ServerSocketInfo { serverSocketAddress = Just sockAddr })) -> do
        let connectionFilePath =
              case serverSocketDomain ssi of
                AF_UNIX_Repr  -> acceptAFUnixFilePath sockAddr ssi
                AF_INET_Repr  -> acceptAFInetFilePath sockAddr ssi
                AF_INET6_Repr -> acceptAFInetFilePath sockAddr ssi
        connectionFileLit <- liftIO $ WI.stringLit sym $ WI.Char8Literal $ BSC.pack connectionFilePath
        LCSy.openFile (LCLS.llvmFileSystem fs) connectionFileLit $ \res -> do
          case res of
            Left LCSy.FileNotFound -> returnIOError
            Right fileHandle -> do
              let sockNextConn = serverSocketNextConnection ssi
              LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
                Map.insert sockfdInt (Some (ssi{ serverSocketNextConnection = sockNextConn + 1 }))
              LCLS.allocateFileDescriptor fs fileHandle
      _ -> returnIOError
  liftIO $ bvToPtr sym fd ?ptrWidth
  where
    sym = LCB.backendGetSym bak

buildBindOverride :: ( LCLM.HasPtrWidth w
                     , LCLM.HasLLVMAnn sym
                     , DMC.MemWidth w
                     , w ~ DMC.ArchAddrWidth arch
                     )
                  => LCLS.LLVMFileSystem w
                  -> AM.InitialMemory sym w
                  -- ^ Initial memory state for symbolic execution
                  -> Map.Map (DMC.MemWord w) String
                  -- ^ Mapping from unsupported relocation addresses to the names of the
                  -- unsupported relocation types.
                  -> Syscall (AExt.AmbientSimulatorState sym arch) sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w) ext
                             (LCLM.LLVMPointerType w)
buildBindOverride fs initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "bind" $ \bak args ->
    Ctx.uncurryAssignment (callBind fs initialMem unsupportedRelocs bak) args

-- | Override for the @bind(2)@ syscall. This function reads the port number from
-- the @addr@ struct, ensures that it is concrete, and records it for later
-- calls to @accept()@. See Note @[The networking story]@ for the full details.
callBind :: forall sym bak arch w p solver scope st fs ext r args ret
          . ( LCB.IsSymBackend sym bak
            , sym ~ WE.ExprBuilder scope st fs
            , bak ~ LCBO.OnlineBackend solver scope st fs
            , WPO.OnlineSolver solver
            , LCLM.HasLLVMAnn sym
            , LCLM.HasPtrWidth w
            , DMC.MemWidth w
            , w ~ DMC.ArchAddrWidth arch
            , p ~ AExt.AmbientSimulatorState sym arch
            )
         => LCLS.LLVMFileSystem w
         -> AM.InitialMemory sym w
         -- ^ Initial memory state for symbolic execution
         -> Map.Map (DMC.MemWord w) String
         -- ^ Mapping from unsupported relocation addresses to the names of the
         -- unsupported relocation types.
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.OverrideSim p sym ext r args ret
                            (LCS.RegValue sym (LCLM.LLVMPointerType w))
callBind _fs initialMem unsupportedRelocs bak sockfd addr _addrlen = do
  sockfdInt <- liftIO $ networkConstantBVPtrToInteger bak "bind" AE.FDArgument (LCS.regValue sockfd)
  serverSocketFDs <- Lens.use (LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs)
  ec <- case Map.lookup sockfdInt serverSocketFDs of
          Just (Some ssi) -> do
            () <- case serverSocketDomain ssi of
                    AF_UNIX_Repr  -> bindUnix sockfdInt ssi
                    AF_INET_Repr  -> bindInet sockfdInt ssi
                    AF_INET6_Repr -> bindInet sockfdInt ssi
            returnIOSuccess
          Nothing -> returnIOError
  liftIO $ bvToPtr sym ec ?ptrWidth
  where
    sym = LCB.backendGetSym bak
    memVar = AM.imMemVar initialMem

    -- For AF_UNIX sockets, we bind the socket to a path name.
    bindUnix ::
      Integer ->
      ServerSocketInfo AF_UNIX ->
      LCS.OverrideSim p sym ext r args ret ()
    bindUnix sockfdInt ssi = do
      mem <- LCS.readGlobal memVar
      portPath <- loadSockaddrUnPath bak mem initialMem unsupportedRelocs (LCS.regValue addr)
      LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
        Map.insert sockfdInt (Some (ssi{ serverSocketAddress = Just portPath }))

    -- For AF_INET(6) sockets, we bind the socket to a port number.
    bindInet ::
      forall domain.
      (SocketAddress domain ~ Word16) =>
      Integer ->
      ServerSocketInfo domain ->
      LCS.OverrideSim p sym ext r args ret ()
    bindInet sockfdInt ssi = do
      mem <- LCS.readGlobal memVar
      portBV <- liftIO $ loadSockaddrInPort bak mem (LCS.regValue addr)
      portInt <- liftIO $ fmap BVS.asUnsigned
                        $ networkConstantBV bak "bind" AE.PortArgument (WI.knownNat @16) portBV
      LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
        Map.insert sockfdInt (Some (ssi{ serverSocketAddress = Just (fromInteger portInt) }))

-- | This function digs through the memory in a pointer to a @sockaddr_in@
-- struct (for @AF_INET@ connections) or a @sockaddr_in6@ struct (for
-- @AF_INET6@ connections) and loads the port number out of it, which is the
-- only information that we care about in the verifier. Note that the port
-- number's bytes will be represented in network order, not host order, so you
-- may want to byteswap it for debugging purposes.
loadSockaddrInPort ::
     ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     )
  => bak
  -> LCLM.MemImpl sym
  -> LCLM.LLVMPtr sym w
  -> IO (WI.SymBV sym 16)
loadSockaddrInPort bak mem sockaddrInPtr = do
  let sym = LCB.backendGetSym bak
  let -- The size of the @sa_family_t@ type in bytes. While
      -- https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_socket.h.html
      -- requires @sa_family_t@ to be an unsigned integer, it does not specify
      -- what size it should have. As a result, the size could potentially be
      -- different across different OS/architecture configurations.
      --
      -- Fortunately, @sa_family_t@ is two bytes in all of the configurations
      -- that the verifier currently supports, so we have opted to hard-code
      -- this information for the time being. We should eventually move towards
      -- a design that avoids this hard-coding—see #75.
      saFamilyTLenBytes = BVS.mkBV ?ptrWidth 2
  bvSaFamilyTLenBytes <- WI.bvLit sym ?ptrWidth saFamilyTLenBytes
  let ?memOpts = overrideMemOptions
  -- At what offset into the struct should we load to get the port number?
  -- Here are the definitions of @sockaddr_in@ and @sockaddr_in6@,
  -- respectively, for reference:
  --
  -- @
  -- struct sockaddr_in {
  --     sa_family_t    sin_family;
  --     in_port_t      sin_port;
  --     struct in_addr sin_addr;
  -- };
  --
  -- struct sockaddr_in6 {
  --     sa_family_t     sin6_family;
  --     in_port_t       sin6_port;
  --     uint32_t        sin6_flowinfo;
  --     struct in6_addr sin6_addr;
  --     uint32_t        sin6_scope_id;
  -- };
  -- @
  --
  -- Conveniently, the field of type @in_port_t@ is always the second field,
  -- and it always follows a field of type @sa_family_t@. Therefore, we use the
  -- size of @sa_family_t@ to compute the offset.
  sockaddrInPortPtr <- LCLM.doPtrAddOffset bak mem sockaddrInPtr bvSaFamilyTLenBytes
  let -- The size of the @in_port_t@ type in bits. The size of this type
      -- appears to be standardized across all implementations. See, e.g.,.
      -- https://pubs.opengroup.org/onlinepubs/009695399/basedefs/netinet/in.h.html,
      -- which says that @in_port_t@ should always be equivalent to @uint16_t@.
      inPortTLenBits = WI.knownNat @16
      inPortTLenBytes = LCLB.bitsToBytes $ WI.intValue $ inPortTLenBits
  v <- LCLM.doLoad bak mem sockaddrInPortPtr (LCLM.bitvectorType inPortTLenBytes)
                   (LCLM.LLVMPointerRepr inPortTLenBits) LCLD.noAlignment
  LCLM.projectLLVM_bv bak v

-- | This function digs through the memory in a pointer to a @sockaddr_un@
-- struct and loads the @sun_path@ out of it, which is the only information
-- that we care about in the verifier.
loadSockaddrUnPath ::
     ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , p ~ AExt.AmbientSimulatorState sym arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     )
  => bak
  -> LCLM.MemImpl sym
  -> AM.InitialMemory sym w
  -> Map.Map (DMC.MemWord w) String
  -> LCLM.LLVMPtr sym w
  -> LCS.OverrideSim p sym ext r args ret BS.ByteString
loadSockaddrUnPath bak mem initialMem unsupportedRelocs sockaddrUnPtr = do
  let sym = LCB.backendGetSym bak
  let -- See the comments above @saFamilyTLenBytes@ in 'loadSockaddrInPort'
      -- for why we use 2 here.
      saFamilyTLenBytes = BVS.mkBV ?ptrWidth 2
  bvSaFamilyTLenBytes <- liftIO $ WI.bvLit sym ?ptrWidth saFamilyTLenBytes
  let ?memOpts = overrideMemOptions
  -- Here is the definition of @sockaddr_un@:
  --
  -- @
  -- struct sockaddr_un {
  --     sa_family_t sun_family;               /* AF_UNIX */
  --     char        sun_path[108];            /* Pathname */
  -- };
  -- @
  --
  -- Just as with @sockaddr_in@, the information we care about is the second
  -- field, which follows a field of type @sa_family_t@. Therefore, we use the
  -- size of @sa_family_t@ to compute the offset.
  sockaddrUnPathPtr <- liftIO $ LCLM.doPtrAddOffset bak mem sockaddrUnPtr bvSaFamilyTLenBytes
  let sockaddrUnPathReg = LCS.RegEntry { LCS.regType = LCLM.PtrRepr, LCS.regValue = sockaddrUnPathPtr }
  -- Note that the maximum size of @sun_path@ is 108 characters, which is why
  -- we pass @Just 108@ here.
  unPathBytes <- AExt.loadConcreteString bak mem initialMem unsupportedRelocs sockaddrUnPathReg (Just 108)
  pure $ BS.pack unPathBytes

buildConnectOverride :: ( LCLM.HasPtrWidth w
                        , w ~ DMC.ArchAddrWidth arch
                        )
                     => Syscall (AExt.AmbientSimulatorState sym arch) sym
                                (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                              Ctx.::> LCLM.LLVMPointerType w
                                              Ctx.::> LCLM.LLVMPointerType w) ext
                                (LCLM.LLVMPointerType w)
buildConnectOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "connect" $ \bak args ->
    Ctx.uncurryAssignment (callConnect bak) args


-- | Override for the @connect(2)@ syscall. This implementation is very simple, as
-- it only checks to see if the socket file descriptor argument has previously
-- been registered. If it has, it will return 0, indicating success. If not, it
-- will return -1, indicating failure.
--
-- Like @bind@, the @connect@ syscall also takes an @addr@ argument. However,
-- we never need to examine what port it uses, since this override always
-- assumes that the connection was successfully initiated (FD registration
-- notwithstanding).
callConnect :: ( LCB.IsSymBackend sym bak
               , sym ~ WE.ExprBuilder scope st fs
               , bak ~ LCBO.OnlineBackend solver scope st fs
               , WPO.OnlineSolver solver
               , LCLM.HasPtrWidth w
               , w ~ DMC.ArchAddrWidth arch
               )
            => bak
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                               (LCS.RegValue sym (LCLM.LLVMPointerType w))
callConnect bak sockfd _addr _addrlen = checkSocketFDInUse bak "connect" sockfd

buildListenOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => Syscall (AExt.AmbientSimulatorState sym arch) sym
                               (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                             Ctx.::> LCLM.LLVMPointerType w) ext
                               (LCLM.LLVMPointerType w)
buildListenOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "listen" $ \bak args ->
    Ctx.uncurryAssignment (callListen bak) args

-- | Override for the @listen(2)@ syscall. This implementation is very simple, as
-- it only checks to see if the socket file descriptor argument has previously
-- been registered. If it has, it will return 0, indicating success. If not, it
-- will return -1, indicating failure.
callListen :: ( LCB.IsSymBackend sym bak
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , WPO.OnlineSolver solver
              , LCLM.HasPtrWidth w
              , w ~ DMC.ArchAddrWidth arch
              )
           => bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                              (LCS.RegValue sym (LCLM.LLVMPointerType w))
callListen bak sockfd _backlog = checkSocketFDInUse bak "listen" sockfd

-- | Check if the socket file descriptor argument has previously been
-- registered. If so, return 0, indicating success. If not, return -1,
-- indicating failure.
--
-- This function is the workhorse for the @connect@ and @listen@ overrides.
checkSocketFDInUse :: ( LCB.IsSymBackend sym bak
                      , sym ~ WE.ExprBuilder scope st fs
                      , bak ~ LCBO.OnlineBackend solver scope st fs
                      , WPO.OnlineSolver solver
                      , LCLM.HasPtrWidth w
                      , w ~ DMC.ArchAddrWidth arch
                      )
                   => bak
                   -> T.Text
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                   -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                                      (LCS.RegValue sym (LCLM.LLVMPointerType w))
checkSocketFDInUse bak fnName sockfd = do
  let sym = LCB.backendGetSym bak
  sockfdInt <- liftIO $ networkConstantBVPtrToInteger bak fnName AE.FDArgument (LCS.regValue sockfd)
  serverSocketFDs <- Lens.use (LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs)
  ec <- if Map.member sockfdInt serverSocketFDs
        then returnIOSuccess
        else returnIOError
  liftIO $ bvToPtr sym ec ?ptrWidth

buildRecvOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> Syscall p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                 Ctx.::> LCLM.LLVMPointerType w
                                                 Ctx.::> LCLM.LLVMPointerType w
                                                 Ctx.::> LCLM.LLVMPointerType w) ext
                                   (LCLM.LLVMPointerType w)
buildRecvOverride fs memVar =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "recv" $ \bak args ->
    Ctx.uncurryAssignment (callRecv fs memVar bak) args

-- | Override for the @recv(2)@ syscall. For now, we treat it identically to
-- @read@, ignoring the @flags@ argument entirely.
callRecv :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callRecv fs memVar bak sockfd buf len _flags =
  ASOS.callRead fs memVar bak sockfd buf len

buildSendOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> Syscall p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                 Ctx.::> LCLM.LLVMPointerType w
                                                 Ctx.::> LCLM.LLVMPointerType w
                                                 Ctx.::> LCLM.LLVMPointerType w) ext
                                   (LCLM.LLVMPointerType w)
buildSendOverride fs memVar =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "send" $ \bak args ->
    Ctx.uncurryAssignment (callSend fs memVar bak) args

-- | Override for the @send(2)@ syscall. For now, we treat it identically to
-- @write@, ignoring the @flags@ argument entirely.
callSend :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSend fs memVar bak sockfd buf len _flags =
  ASOS.callWrite fs memVar bak sockfd buf len

buildSocketOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => LCLS.LLVMFileSystem w
                    -> Syscall (AExt.AmbientSimulatorState sym arch) sym
                               (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                             Ctx.::> LCLM.LLVMPointerType w
                                             Ctx.::> LCLM.LLVMPointerType w) ext
                               (LCLM.LLVMPointerType w)
buildSocketOverride fs =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "socket" $ \bak args ->
    Ctx.uncurryAssignment (callSocket fs bak) args

-- | Override for the @socket(2)@ syscall. This checks to see if the appropriate
-- arguments are concrete, and if so, open a file with the appropriate name
-- representing the socket. See Note @[The networking story]@ for the full
-- details.
callSocket :: ( LCB.IsSymBackend sym bak
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , WPO.OnlineSolver solver
              , LCLM.HasPtrWidth w
              , w ~ DMC.ArchAddrWidth arch
              )
           => LCLS.LLVMFileSystem w
           -> bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                              (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSocket fs bak domainReg typeReg _protocol = do
  let sym = LCB.backendGetSym bak
  domainInt <- liftIO $ networkConstantBVPtrToInteger bak "socket" AE.DomainArgument (LCS.regValue domainReg)
  domain <-
    case Map.lookup domainInt socketDomainMap of
      Just d  -> pure d
      Nothing -> CMC.throwM $ AE.UnsupportedSocketArgument AE.DomainArgument domainInt
  Some domainRepr <- pure $ toSocketDomainRepr domain
  typeInt <- liftIO $ networkConstantBVPtrToInteger bak "socket" AE.TypeArgument (LCS.regValue typeReg)
  typ <-
    case Map.lookup typeInt socketTypeMap of
      Just t  -> pure t
      Nothing -> CMC.throwM $ AE.UnsupportedSocketArgument AE.TypeArgument typeInt
  let ssi = ServerSocketInfo
              { serverSocketDomain = domainRepr
              , serverSocketType = typ
              , serverSocketAddress = Nothing
              , serverSocketNextConnection = 0
              }
  socketFileLit <- liftIO $ WI.stringLit sym $ WI.Char8Literal $ BSC.pack
                          $ socketFilePath ssi
  fd <- LCSy.openFile (LCLS.llvmFileSystem fs) socketFileLit $ \res -> do
    case res of
      Left LCSy.FileNotFound -> returnIOError
      Right fileHandle -> do
        fd <- LCLS.allocateFileDescriptor fs fileHandle
        fdBV <- case WI.asBV fd of
          Just fdBV -> pure fdBV
          Nothing -> AP.panic AP.FunctionOverride "callSocket"
                              ["allocateFileDescriptor should return a concrete FD"]
        LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
          Map.insert (BVS.asUnsigned fdBV) (Some ssi)
        pure fd
  liftIO $ bvToPtr sym fd ?ptrWidth

-- | A map of socket domains that the verifier supports. The keys are the
-- values of the corresponding C macros, with each key mapping to the name of
-- the macro.
--
-- Note that there is no guarantee that the values of these macros will be the
-- same in every OS/architecture configuration. At the moment, the values
-- happen to be the same in all of the configurations that the verifier
-- supports, so we have opted to hard-code the values for the time being. We
-- should eventually move towards a design that avoids this
-- hard-coding—see #75.
socketDomainMap :: Map.Map Integer SocketDomain
socketDomainMap = Map.fromList
  [ (1,  AF_UNIX)
  , (2,  AF_INET)
  , (10, AF_INET6)
  ]

-- | A map of socket types that the verifier supports. The keys are the
-- values of the corresponding C macros, with each key mapping to the name of
-- the macro.
--
-- Note that there is no guarantee that the values of these macros will be the
-- same in every OS/architecture configuration. At the moment, the values
-- happen to be the same in all of the configurations that the verifier
-- supports, so we have opted to hard-code the values for the time being. We
-- should eventually move towards a design that avoids this
-- hard-coding—see #75.
socketTypeMap :: Map.Map Integer SocketType
socketTypeMap = Map.fromList
  [ (1, SOCK_STREAM)
  , (2, SOCK_DGRAM)
  , (5, SOCK_SEQPACKET)
  ]

-- | Concretize a symbolic bitvector representing the argument to a
-- networking-related function override. If the bitvector is truly symbolic,
-- throw an appropriate exception.
networkConstantBV ::
     ( LCB.IsSymBackend sym bak
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , 1 WI.<= w
     )
  => bak
  -> T.Text
     -- ^ The name of the function being overriden. Only used for exception
     -- message purposes.
  -> AE.NetworkFunctionArgument
     -- ^ The sort of argument the 'WI.SymBV' represents. Only used for
     -- exception message purposes.
  -> WI.NatRepr w
     -- ^ The width of the bitvector.
  -> WI.SymBV sym w
     -- ^ The symbolic bitvector.
  -> IO (BVS.BV w)
networkConstantBV bak fnName fnArg w symBV = do
  let sym = LCB.backendGetSym bak
  loc <- WI.getCurrentProgramLoc sym

  -- NB: It's not enough to just use asBV here, as it's possible for these
  -- values to get spilled onto the stack. We need the power of an online
  -- solver connection in the general case.
  res <- AVC.resolveSymBVAs bak w symBV
  case res of
    Right bv -> pure bv
    Left AVC.SolverUnknown ->
      CMC.throwM $ AE.ConcretizationFailedUnknown loc target
    Left AVC.UnsatInitialAssumptions ->
      AP.panic AP.FunctionOverride "constantBV"
        ["Initial assumptions are unsatisfiable at " ++ show (PP.pretty (WP.plSourceLoc loc))]
    Left AVC.MultipleModels ->
      CMC.throwM $ AE.ConcretizationFailedSymbolic loc target
  where
    target = AE.NetworkFunction fnName fnArg

-- | Like 'networkConstantBV', but where:
--
-- * The argument is an 'LCLM.LLVMPtr' instead of a 'WI.SymBV'.
--
-- * The returned value is converted directly to an 'Integer'.
networkConstantBVPtrToInteger ::
     ( LCB.IsSymBackend sym bak
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , 1 WI.<= w
     )
  => bak
  -> T.Text
  -> AE.NetworkFunctionArgument
  -> LCLM.LLVMPtr sym w
  -> IO Integer
networkConstantBVPtrToInteger bak fnName fnArg ptr = do
  ptrBV <- LCLM.projectLLVM_bv bak ptr
  bv <- networkConstantBV bak fnName fnArg (LCLM.ptrWidth ptr) ptrBV
  pure $ BVS.asUnsigned bv

-- | Return 0, indicating success.
returnIOSuccess :: LCB.IsSymInterface sym
                => LCS.OverrideSim p sym ext r args ret (WI.SymBV sym 32)
returnIOSuccess = do
  sym <- LCS.getSymInterface
  liftIO $ WI.bvLit sym (WI.knownNat @32) (BVS.zero (WI.knownNat @32))

-- | Return 1, indiciating failure.
returnIOError :: LCB.IsSymInterface sym
              => LCS.OverrideSim p sym ext r args ret (WI.SymBV sym 32)
returnIOError = do
  sym <- LCS.getSymInterface
  liftIO $ WI.bvLit sym (WI.knownNat @32) (BVS.mkBV (WI.knownNat @32) (-1))
