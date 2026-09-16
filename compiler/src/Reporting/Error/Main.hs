{-# LANGUAGE OverloadedStrings #-}

module Reporting.Error.Main
  ( Error (..),
    toReport,
  )
where

import AST.Canonical qualified as Can
import Data.List qualified as List
import Data.Name qualified as Name
import Reporting.Annotation qualified as A
import Reporting.Doc qualified as D
import Reporting.Error.Canonicalize qualified as E
import Reporting.Render.Code qualified as Code
import Reporting.Render.Type qualified as RT
import Reporting.Render.Type.Localizer qualified as L
import Reporting.Report qualified as Report

-- ERROR

data Error
  = BadType A.Region Can.Type [String]
  | BadCycle A.Region Name.Name [Name.Name]
  | BadFlags A.Region Can.Type E.InvalidPayload
  | -- | A @main : Task e a@ that is not a @Task Never {}@ (D72): whether @e@ is
    -- the wrong type, and whether @a@ is.
    BadTask A.Region Can.Type Bool Bool

-- TO REPORT

toReport :: L.Localizer -> Code.Source -> Error -> Report.Report
toReport localizer source err =
  case err of
    BadType region tipe allowed ->
      Report.Report "BAD MAIN TYPE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( "I cannot handle this type of `main` value:",
            D.stack
              [ "The type of `main` value I am seeing is:",
                D.indent 4 $ D.dullyellow $ RT.canToDoc localizer RT.None tipe,
                D.reflow $ "But I only know how to handle these types: " ++ List.intercalate ", " allowed
              ]
          )
    BadCycle region name names ->
      Report.Report "BAD MAIN" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( "A `main` definition cannot be defined in terms of itself.",
            D.stack
              [ D.reflow $
                  "It should be a boring value with no recursion. But\
                  \ instead it is involved in this cycle of definitions:",
                D.cycle 4 name names
              ]
          )
    BadTask region tipe badErr badAnswer ->
      Report.Report "BAD MAIN TYPE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( "A `main` task must be a `Task Never {}`, and this one is not:",
            D.stack $
              [ D.indent 4 $ D.dullyellow $ RT.canToDoc localizer RT.None tipe
              ]
                ++ [ D.reflow $
                       "Its error type is not `Never`, so it can fail, and a failure\
                       \ would have nowhere to go: `main` is the end of the program.\
                       \ Handle the error before it gets there, with `Task.onError`:"
                   | badErr
                   ]
                ++ [ D.indent 4 $
                       D.vcat
                         [ "main =",
                           "    run",
                           "        |> Task.onError (\\error -> Console.writeErr (inspect error ++ \"\\n\"))"
                         ]
                   | badErr
                   ]
                ++ [ D.reflow $
                       "Its answer is not `{}`. Nothing receives what `main` completes\
                       \ with, so say that it is thrown away, with `Task.map (\\_ -> {})`."
                   | badAnswer
                   ]
          )
    BadFlags region _badType invalidPayload ->
      let formatDetails (aBadKindOfThing, butThatIsNoGood) =
            Report.Report "BAD FLAGS" region [] $
              Code.toSnippet
                source
                region
                Nothing
                ( D.reflow $
                    "Your `main` program wants " ++ aBadKindOfThing ++ " from JavaScript.",
                  butThatIsNoGood
                )
       in formatDetails $
            case invalidPayload of
              E.ExtendedRecord ->
                ( "an extended record",
                  D.reflow $
                    "But the exact shape of the record must be known at compile time. No type variables!"
                )
              E.Function ->
                ( "a function",
                  D.reflow $
                    "But if I allowed functions from JS, it would be possible to sneak\
                    \ side-effects and runtime exceptions into Gren!"
                )
              E.TypeVariable name ->
                ( "an unspecified type",
                  D.reflow $
                    "But type variables like `"
                      ++ Name.toChars name
                      ++ "` cannot be given as flags.\
                         \ I need to know exactly what type of data I am getting, so I can guarantee that\
                         \ unexpected data cannot sneak in and crash the Gren program."
                )
              E.UnsupportedType name ->
                ( "a `" ++ Name.toChars name ++ "` value",
                  D.stack
                    [ D.reflow $ "I cannot handle that. The types that CAN be in flags include:",
                      D.indent 4 $
                        D.reflow $
                          "Ints, Floats, Bools, Strings, Bytes, Maybes, Arrays,\
                          \ records, and JSON values.",
                      D.reflow $
                        "Since JSON values can flow through, you can use JSON encoders and decoders\
                        \ to allow other types through as well. More advanced users often just do\
                        \ everything with encoders and decoders for more control and better errors."
                    ]
                )
