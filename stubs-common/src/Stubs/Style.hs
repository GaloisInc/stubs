module Stubs.Style (
      ANSI.AnsiStyle
    , Style(..)
    , plain, success, failure, keyword, emph
    , toAnsi, toAnsiDark
    , hPutDocAnsi
    ) where

import qualified Prettyprinter.Render.Terminal as ANSI
import qualified Prettyprinter as PP
import qualified System.IO as IO

{-
To handle future rendering needs, we tag Docs with semantic Style tags.
These annotations are reinterpreted via reannotation functions
into tags that indicate how to render text to some particular I/O handle.

To log text in an existing style:
- Add Style annotations to `ppDiagnostic` in Ambient.Diagnostic
  (see convenience functions at the bottom of this file).

To add a new style:
- Extend the Style datatype.
- Write a convenience function.
- Extend each reannotation function in this file (e.g. `toAnsi`).
- Extend the 'pretty' or equivalent annotation function as desired
  (e.g. `ppDiagnostic` in Ambient.Diagnostic).

To add a new rendering function:
- Define a new reannotation function in this file (e.g. `toAnsi`)
  to the rendering annotation.
- Use this to define a new convenience function in this file
  (e.g. `hPutDocAnsi`) to output a Doc Style.
-}

-- | Semantic Style datatype; can be reannotated to various concrete rendering styles.
data Style = Plain | Success | Failure | Keyword | Emph



-- | Reannotation function for ANSI terminals.
toAnsi :: Style -> ANSI.AnsiStyle
toAnsi Plain = ANSI.color ANSI.Black <> ANSI.bgColor ANSI.White
toAnsi Success = ANSI.colorDull ANSI.Green <> toAnsi Plain
toAnsi Failure = ANSI.colorDull ANSI.Red <> toAnsi Plain
toAnsi Keyword = ANSI.colorDull ANSI.Blue <> toAnsi Plain
toAnsi Emph = ANSI.italicized <> toAnsi Plain

-- | Alternate reannotation function for ANSI with a dark bg scheme.
toAnsiDark :: Style -> ANSI.AnsiStyle
toAnsiDark Plain = ANSI.color ANSI.White <> ANSI.bgColor ANSI.Black
toAnsiDark Success = ANSI.color ANSI.Green <> toAnsiDark Plain
toAnsiDark Failure = ANSI.color ANSI.Red <> toAnsiDark Plain
toAnsiDark Keyword = ANSI.color ANSI.Blue <> toAnsiDark Plain
toAnsiDark Emph = ANSI.italicized <> toAnsiDark Plain

-- Convenience functions

plain, success, failure, keyword, emph :: PP.Doc Style -> PP.Doc Style
plain = PP.annotate Plain
success = PP.annotate Success
failure = PP.annotate Failure
keyword = PP.annotate Keyword
emph = PP.annotate Emph

-- | Prints a Style-annotated Doc to a given handle.
hPutDocAnsi :: IO.Handle -> PP.Doc Style -> IO ()
hPutDocAnsi hdl doc = ANSI.hPutDoc hdl (PP.reAnnotate toAnsi doc)