{-# OPTIONS_GHC -Wall #-}

-- | Core literals as JavaScript source (@docs/m1a-js-on-core.md@ §J4).
--
-- Core holds characters and numbers, not the source they were written as: C2
-- made 'Core.AST.Text' real characters on purpose, and a @Float@ is a 'Double'.
-- Whatever reads Core therefore has to write JavaScript literals rather than
-- paste them, and this is the one place that does — @Generate.FromCore@ on the
-- way to @Opt@, and "Generate.CoreJS" on the way straight to JavaScript.
--
-- __Deliberately not `Gren.String`'s encoder.__ That is the function whose
-- surrogate-pair boundary was off by one — @docs\/upstream\/@
-- @compiler-u-ffff-becomes-a-surrogate-pair.md@, upstream as @compiler#384@ —
-- and §J4 asked for this one to be written from the specification instead, so
-- that the fork keeps the fix by construction rather than by remembering to
-- port it. There is no arithmetic here to be off by one: a character that does
-- not have to be escaped is written as itself.
module Generate.JavaScript.Literal
  ( string,
    float,
  )
where

import Data.Utf8 qualified as Utf8
import Gren.Float qualified as EF
import Gren.String qualified as ES

-- | Characters as the body of a JavaScript string literal.
--
-- `Generate.JavaScript.Builder` writes a string between __single__ quotes, so
-- that is the quote to escape; a double quote goes out as itself, which is what
-- `Parse.String` does when it builds one of these from source.
--
-- Escaped: the quote, the backslash, the C0 controls, DEL, and U+2028 and
-- U+2029, which JavaScript before ES2019 treats as line terminators inside a
-- string literal. __Everything else goes out as itself, in UTF-8__, astral
-- characters included — the output is a UTF-8 file and a JavaScript string
-- literal may hold any character but those.
string :: [Char] -> ES.String
string = Utf8.fromChars . concatMap escape
  where
    escape c =
      case c of
        '\'' -> "\\'"
        '\\' -> "\\\\"
        '\n' -> "\\n"
        '\r' -> "\\r"
        '\t' -> "\\t"
        _
          | code < 0x20 || code == 0x7F || code == 0x2028 || code == 0x2029 ->
              "\\u" ++ pad (hex code)
          | otherwise -> [c]
      where
        code = fromEnum c

    pad h = replicate (4 - length h) '0' ++ h

    hex 0 = "0"
    hex n = go n ""
      where
        go 0 acc = acc
        go m acc = go (m `div` 16) (digit (m `mod` 16) : acc)
        digit d = if d < 10 then toEnum (fromEnum '0' + d) else toEnum (fromEnum 'a' + d - 10)

-- | A `Double` as JavaScript source.
--
-- A `Gren.Float` is the digits as they were written and Core holds the value, so
-- the digits have to be written again. Haskell's `show` produces the shortest
-- decimal that reads back as the same `Double`, and every form it produces —
-- @1.0@, @1.0e-2@, @Infinity@, @NaN@ — is also valid JavaScript.
float :: Double -> EF.Float
float = Utf8.fromChars . show
