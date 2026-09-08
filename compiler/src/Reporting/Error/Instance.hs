{-# LANGUAGE OverloadedStrings #-}

-- | What can go wrong when a class-method call is resolved to an instance
-- (@docs/m1b-classes.md@ §G23).
--
-- Two things can, and they are different questions rather than two spellings
-- of one. __No instance__ is a fact about the program: the type at the use
-- site is settled and nothing declares an instance for it, and no later phase
-- will change that. __Not resolved__ is a fact about this compiler: the type
-- at the use site is still a variable, so the call needs a witness passed in
-- rather than an instance picked here, and that is verb 6's.
module Reporting.Error.Instance
  ( Error (..),
    toReport,
  )
where

import AST.Canonical qualified as Can
import Data.Name qualified as Name
import Reporting.Annotation qualified as A
import Reporting.Doc qualified as D
import Reporting.Render.Code qualified as Code
import Reporting.Render.Type qualified as RT
import Reporting.Render.Type.Localizer qualified as L
import Reporting.Report qualified as Report

-- ERROR

data Error
  = -- | The class, the method, and what its class parameter turned out to be.
    NoInstance A.Region Can.Class Name.Name Can.Type
  | -- | The same, when what it turned out to be is a type variable.
    NotResolved A.Region Can.Class Name.Name Name.Name

-- TO REPORT

toReport :: L.Localizer -> Code.Source -> Error -> Report.Report
toReport localizer source err =
  case err of
    NoInstance region (Can.Class _ className) methodName tipe ->
      Report.Report "NO INSTANCE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "`"
                ++ Name.toChars methodName
                ++ "` is a method of the `"
                ++ Name.toChars className
                ++ "` class, and here it is used at this type:",
            D.stack
              [ D.indent 4 $ D.dullyellow $ RT.canToDoc localizer RT.None tipe,
                D.reflow $
                  "There is no `instance "
                    ++ Name.toChars className
                    ++ "` for it, so there is no definition for this call to use."
              ]
          )
    NotResolved region (Can.Class _ className) methodName param ->
      Report.Report "UNRESOLVED CLASS METHOD" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "`"
                ++ Name.toChars methodName
                ++ "` is a method of the `"
                ++ Name.toChars className
                ++ "` class, and here it is used at the type variable `"
                ++ Name.toChars param
                ++ "`:",
            D.reflow
              "I pick the instance from the type at the call, so the type has to be a\
              \ specific one by the time I get here. Calling a method at a variable means\
              \ passing the instance in instead, and I cannot do that in this version."
          )
