{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Stubs.Syscall.Overrides.Networking.Types
  ( -- * @ServerSocketInfo@ and friends
    ServerSocketInfo(..)
  , SocketDomain(..)
  , type AF_UNIX
  , type AF_INET
  , type AF_INET6
  , SocketDomainRepr(..)
  , fromSocketDomainRepr
  , toSocketDomainRepr
  , SocketAddress
  , SocketType(..)
    -- * Socket file path conventions
  , socketFilePath
  , acceptAFUnixFilePath
  , acceptAFInetFilePath
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.Kind ( Type )
import           Data.Parameterized.Some ( Some(..) )
import           Data.Word ( Word16 )
import qualified System.FilePath as FP

-- See Note [The networking story] in
-- Ambient.Syscall.Overrides.Networking for a high-level overview of
-- how these data types are used to model network IO.

-- | A collection of metadata about sockets that is useful for server programs
-- (i.e., programs that call @accept()@).
data ServerSocketInfo (domain :: SocketDomain) = ServerSocketInfo
  { serverSocketDomain :: SocketDomainRepr domain
    -- ^ The socket's domain as specified by the first argument to the
    -- @socket()@ syscall.
  , serverSocketType :: SocketType
    -- ^ The socket's type as specified by the second argument to the
    -- @socket()@ syscall.
  , serverSocketAddress :: Maybe (SocketAddress domain)
    -- ^ If this socket has been assigned via @bind()@, this is
    -- @'Just' addr@. If not, this is 'Nothing'. The type of @addr@ depends on
    -- the socket domain—see the Haddocks for 'SocketAddress'.
  , serverSocketNextConnection :: Word
    -- ^ The number to use for the socket file allocated by the next call to
    -- @accept()@.
  }
deriving instance Show (SocketAddress domain) => Show (ServerSocketInfo domain)

-- | All of the socket domains that the verifier currently supports. In
-- addition to being used at the value level, this is also used at the type
-- level to compute the type of the 'SocketAddress', which depends on the
-- domain.
data SocketDomain
  = AF_UNIX
  | AF_INET
  | AF_INET6
  deriving Show

type AF_UNIX  = 'AF_UNIX
type AF_INET  = 'AF_INET
type AF_INET6 = 'AF_INET6

-- | A singleton type for 'SocketDomain'.
data SocketDomainRepr domain where
  AF_UNIX_Repr  :: SocketDomainRepr AF_UNIX
  AF_INET_Repr  :: SocketDomainRepr AF_INET
  AF_INET6_Repr :: SocketDomainRepr AF_INET6
deriving instance Show (SocketDomainRepr domain)

-- | Obtain a 'SocketDomain' from its corresponding singleton.
fromSocketDomainRepr :: SocketDomainRepr domain -> SocketDomain
fromSocketDomainRepr AF_UNIX_Repr  = AF_UNIX
fromSocketDomainRepr AF_INET_Repr  = AF_INET
fromSocketDomainRepr AF_INET6_Repr = AF_INET6

-- | Convert a singleton to its corresponding singleton.
toSocketDomainRepr :: SocketDomain -> Some SocketDomainRepr
toSocketDomainRepr AF_UNIX  = Some AF_UNIX_Repr
toSocketDomainRepr AF_INET  = Some AF_INET_Repr
toSocketDomainRepr AF_INET6 = Some AF_INET6_Repr

-- | The type of address corresponding to a particular socket domain.
type family SocketAddress (domain :: SocketDomain) :: Type where
  SocketAddress AF_UNIX  = BS.ByteString -- A file path (`sun_path`)
  SocketAddress AF_INET  = Word16        -- A port number (`sin_addr`)
  SocketAddress AF_INET6 = Word16        -- A port number (`sin6_addr`)

-- | All of the socket types that the verifier currently supports.
data SocketType
  = SOCK_STREAM
  | SOCK_DGRAM
  | SOCK_SEQPACKET
  deriving Show

-- These functions implement the file path conventions described in
-- Note [The networking story] in
-- Ambient.Syscall.Overrides.Networking.

-- | In our @socket()@ override, the returned socket file descriptor is modeled
-- with a file located at @/network/<domain_macro>/<type_macro>/socket@.
socketFilePath :: ServerSocketInfo domain -> FilePath
socketFilePath ssi = mkSocketPathPrefix ssi FP.</> "socket"

-- | In our @accept()@ override, @AF_UNIX@ sockets are modeled with files
-- located at @<sun_path>/<seq_num>@.
acceptAFUnixFilePath ::
  BS.ByteString ->
  ServerSocketInfo AF_UNIX ->
  FilePath
acceptAFUnixFilePath sockPath
    (ServerSocketInfo
       { serverSocketNextConnection = sockNextConn
       }) =
  BSC.unpack sockPath FP.</> show sockNextConn

-- | In our @accept()@ override, @AF_INET(6)@ sockets are modeled with files
-- located at @/network/<domain_macro>/<type_macro>/<port>/<seq_num>@.
--
-- NB: while @domain@ is universally quantified here, it only makes sense
-- to instantiate it at @AF_INET@ or @AF_INET6@.
acceptAFInetFilePath ::
  Word16 ->
  ServerSocketInfo domain ->
  FilePath
acceptAFInetFilePath sockPort
    ssi@(ServerSocketInfo
           { serverSocketNextConnection = sockNextConn
           }) =
  mkSocketPathPrefix ssi FP.</> show sockPort FP.</> show sockNextConn

-- | Construct a @/network/<domain_macro>/<type_macro>@ file path for a socket.
-- This is shared in common between 'socketFilePath' and 'acceptAFInetPath'.
mkSocketPathPrefix :: ServerSocketInfo domain -> FilePath
mkSocketPathPrefix (ServerSocketInfo
                      { serverSocketDomain = domainRepr
                      , serverSocketType = typ
                      }) =
  "/network" FP.</> show (fromSocketDomainRepr domainRepr) FP.</> show typ
