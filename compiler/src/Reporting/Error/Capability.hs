{-# LANGUAGE OverloadedStrings #-}

module Reporting.Error.Capability
  ( C.Error (..),
    toReport,
  )
where

import Data.Name qualified as Name
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Nitpick.Capability qualified as C
import Reporting.Doc qualified as D
import Reporting.Render.Code qualified as Code
import Reporting.Report qualified as Report

toReport :: Code.Source -> C.Error -> Report.Report
toReport source err =
  case err of
    C.MintedByDependency region (ModuleName.Canonical declaring home) name pkg ->
      Report.Report "CAPABILITY IN A DEPENDENCY" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "This is `"
                ++ Name.toChars home
                ++ "."
                ++ Name.toChars name
                ++ "`, which mints a capability, and `"
                ++ Pkg.toChars pkg
                ++ "` is a package, not the application:",
            D.stack
              [ D.reflow $
                  "Only the application, and `"
                    ++ Pkg.toChars declaring
                    ++ "` itself, may use it. A capability is the application's to\
                       \ hand out, so that what a dependency can reach is written in\
                       \ the types of the functions it exposes.",
                D.reflow $
                  "Take the capability as an argument instead, and let the application\
                  \ pass it in."
              ]
          )
