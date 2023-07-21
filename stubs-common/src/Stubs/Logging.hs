{-| Description: A small module for collecting common logging definitions

-}
module Stubs.Logging (emptyLogger) where 
import qualified Lumberjack as LJ
import qualified Stubs.Diagnostic as SD

logShim:: SD.Diagnostic -> IO ()
logShim _ = return ()

emptyLogger :: LJ.LogAction IO SD.Diagnostic
emptyLogger = LJ.LogAction logShim