{-# LANGUAGE OverloadedStrings #-}

module Reporting.Error.Literal
  ( Error (..),
    regionOf,
    toReport,
  )
where

import Data.Name qualified as Name
import Reporting.Annotation qualified as A
import Reporting.Doc qualified as D
import Reporting.Render.Code qualified as Code
import Reporting.Report qualified as Report

-- | A numeric literal outside the range of the type it has (D63,
-- @syntax.md@ S5).
--
-- The type is a @Basics@ name rather than a @Can.Type@ because that is all the
-- check has and all the message needs: every numeric type is declared in
-- @Basics@ (D148), so the name identifies it, and a range is a property of the
-- name alone.
data Error
  = OutOfRange A.Region Integer Name.Name Integer Integer
  | -- | A literal pattern whose type is a variable (D172).
    PatternAtVariable A.Region Integer
  | -- | A literal pattern at @Float@ or @Float32@ (D172).
    PatternAtFloat A.Region Integer Name.Name

regionOf :: Error -> A.Region
regionOf err =
  case err of
    OutOfRange region _ _ _ _ -> region
    PatternAtVariable region _ -> region
    PatternAtFloat region _ _ -> region

toReport :: Code.Source -> Error -> Report.Report
toReport source err =
  case err of
    OutOfRange region value tipe low high ->
      Report.Report "NUMBER OUT OF RANGE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "This number does not fit in the type it has here:",
            D.stack
              [ D.reflow $
                  "It is "
                    ++ show value
                    ++ ", and "
                    ++ article (Name.toChars tipe)
                    ++ " `"
                    ++ Name.toChars tipe
                    ++ "` holds the numbers from "
                    ++ show low
                    ++ " to "
                    ++ show high
                    ++ ".",
                D.toSimpleNote $
                  if isNarrow tipe
                    then
                      "Arithmetic wraps at a type's width and a literal does not: writing a number\
                      \ that cannot be one is a mistake, and wrapping it silently would hide which\
                      \ mistake it was. If you meant a bit pattern, write the value it has at this\
                      \ width: 255u8 is the byte 0xFF, and -1i8 is the same eight bits read as\
                      \ signed. If you meant the number, an `Int` holds it."
                    else
                      "Arithmetic wraps at a type's width and a literal does not: writing a number\
                      \ that cannot be one is a mistake, and wrapping it silently would hide which\
                      \ mistake it was. If you meant the number, one of the wider types will hold\
                      \ it -- `Int64`, `UInt32` and `UInt64` are there for that, and a literal can\
                      \ say so with a suffix: 42i64, 42u32, 42u64."
              ]
          )
    PatternAtVariable region value ->
      Report.Report "NUMBER PATTERN AT A TYPE VARIABLE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "This pattern is a number, and the value it is matched against can be more than one numeric type:",
            D.stack
              [ D.reflow $
                  "A pattern is compared with the value exactly, and `"
                    ++ show value
                    ++ "` is a different value at an `Int` than at an `Int64` or a `Float`, so which one this\
                       \ pattern means would depend on who calls it.",
                D.toSimpleNote $
                  "Compare with `==` instead, which works at every numeric type once the annotation\
                  \ says the type has `Eq`. Or give the value a specific type, and the pattern\
                  \ will have that one."
              ]
          )
    PatternAtFloat region value tipe ->
      Report.Report "NUMBER PATTERN AT A FLOAT" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "This pattern is a number, and the value it is matched against is "
                ++ article (Name.toChars tipe)
                ++ " `"
                ++ Name.toChars tipe
                ++ "`:",
            D.stack
              [ D.reflow $
                  "Only the integer types can be matched against a number. A float is rarely exactly\
                  \ anything, and `-0.0` and `NaN` each break half of what `"
                    ++ show value
                    ++ " ->` would promise.",
                D.toSimpleNote $
                  "Compare with `==` if an exact value is what you mean, or use `round` or `truncate`\
                  \ first if you meant a whole number."
              ]
          )

-- | @Int@ and @Int64@ take "an"; @UInt32@ and @UInt64@ take "a", because they
-- are read out as "you-int". @Float@ and @Float32@ take "a".
article :: [Char] -> [Char]
article name =
  case name of
    'I' : _ -> "an"
    _ -> "a"

-- | D342's four, whose out-of-range literal is more often a bit pattern written
-- as its unsigned value than a number that needed a wider type
-- (@docs\/m1b-narrow-int.md@ §NI8).
isNarrow :: Name.Name -> Bool
isNarrow tipe =
  tipe `elem` [Name.int8, Name.uint8, Name.int16, Name.uint16]
