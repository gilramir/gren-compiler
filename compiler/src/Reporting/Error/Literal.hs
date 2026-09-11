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

regionOf :: Error -> A.Region
regionOf (OutOfRange region _ _ _ _) = region

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
                  "Arithmetic wraps at a type's width and a literal does not: writing a number\
                  \ that cannot be one is a mistake, and wrapping it silently would hide which\
                  \ mistake it was. If you meant the number, one of the wider types will hold\
                  \ it -- `Int64`, `UInt32` and `UInt64` are there for that, and a literal can\
                  \ say so with a suffix: 42i64, 42u32, 42u64."
              ]
          )

-- | @Int@ and @Int64@ take "an"; @UInt32@ and @UInt64@ take "a", because they
-- are read out as "you-int".
article :: [Char] -> [Char]
article name =
  case name of
    'I' : _ -> "an"
    _ -> "a"
