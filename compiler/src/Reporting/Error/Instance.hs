{-# LANGUAGE OverloadedStrings #-}

-- | What can go wrong when a constraint is discharged
-- (@docs/m1b-classes.md@ §G23, §G26).
--
-- Three things can, and they are three different questions rather than three
-- spellings of one.
--
-- __No instance__ is a fact about the program: the type the constraint has to
-- hold at is settled and nothing declares an instance for it, and no later
-- phase will change that.
--
-- __Not constrained__ is a fact about the /signature/: the constraint is at a
-- type variable, and the definition it is written in does not say that variable
-- has an instance. The fix is in the source and the message says where.
--
-- __A method's own context__ is a fact about this compiler: §G21.1 lets a
-- method's signature name a second class, and nothing passes a witness for one
-- yet.
module Reporting.Error.Instance
  ( Error (..),
    Wanted (..),
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

-- | What was being used when the constraint turned up, so that a message can
-- open with the thing the author wrote rather than with the constraint.
data Wanted
  = ForMethod Name.Name
  | ForValue Name.Name

data Error
  = -- | The class, the type it has to hold at, and the chain of instances being
    -- discharged to get there.
    NoInstance A.Region Wanted Can.Class Can.Type [(Can.Class, Can.Type)]
  | -- | The same, when the type is a variable nothing constrains.
    NotConstrained A.Region Wanted Can.Class Name.Name [(Can.Class, Can.Type)]
  | -- | A class method whose own signature names a second class.
    MethodContext A.Region Name.Name Can.Class Can.Class

-- TO REPORT

toReport :: L.Localizer -> Code.Source -> Error -> Report.Report
toReport localizer source err =
  case err of
    NoInstance region wanted (Can.Class _ className) tipe because ->
      Report.Report "NO INSTANCE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( introduction wanted className,
            D.stack $
              chain localizer className tipe because
                ++ [ D.reflow $
                       "There is no `instance "
                         ++ Name.toChars className
                         ++ "` for it, so there is no definition for this "
                         ++ (case wanted of ForMethod _ -> "call to use."; ForValue _ -> "to use.")
                   ]
          )
    NotConstrained region wanted (Can.Class _ className) var because ->
      Report.Report "UNCONSTRAINED TYPE VARIABLE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( case because of
              -- The direct case has nothing to show that the sentence does not
              -- already say, so it says it rather than pointing at a variable
              -- on a line of its own.
              [] -> atVariable wanted className var
              _ -> introduction wanted className,
            D.stack $
              (case because of [] -> []; _ -> chain localizer className (Can.TVar var) because)
                ++ [ D.reflow $
                       "I pick an instance from the type, and `"
                         ++ Name.toChars var
                         ++ "` does not say which one. Writing `"
                         ++ Name.toChars className
                         ++ " "
                         ++ Name.toChars var
                         ++ " =>` in the signature of the definition this is in says that the\
                            \ caller supplies it."
                   ]
          )
    MethodContext region methodName (Can.Class _ className) (Can.Class _ other) ->
      Report.Report "UNSUPPORTED METHOD SIGNATURE" region [] $
        Code.toSnippet
          source
          region
          Nothing
          ( D.reflow $
              "`"
                ++ Name.toChars methodName
                ++ "` is a method of the `"
                ++ Name.toChars className
                ++ "` class, and its signature is constrained by `"
                ++ Name.toChars other
                ++ "` as well:",
            D.reflow
              "I pass one instance to a method — the one its own class picks — and I cannot\
              \ pass a second yet. Declaring the method without that constraint, or in a\
              \ class that already has it, is the way around it in this version."
          )

-- | The same, when what the constraint is at is a variable and nothing else
-- needs saying.
atVariable :: Wanted -> Name.Name -> Name.Name -> D.Doc
atVariable wanted className var =
  D.reflow $
    ( case wanted of
        ForMethod methodName ->
          "`" ++ Name.toChars methodName ++ "` is a method of the `" ++ Name.toChars className ++ "` class, and here it is used"
        ForValue valueName ->
          "`" ++ Name.toChars valueName ++ "` needs an `instance " ++ Name.toChars className ++ "`, and here it is used"
    )
      ++ " at the type variable `"
      ++ Name.toChars var
      ++ "`:"

introduction :: Wanted -> Name.Name -> D.Doc
introduction wanted className =
  case wanted of
    ForMethod methodName ->
      D.reflow $
        "`"
          ++ Name.toChars methodName
          ++ "` is a method of the `"
          ++ Name.toChars className
          ++ "` class, and here it is used at this type:"
    ForValue valueName ->
      D.reflow $
        "`"
          ++ Name.toChars valueName
          ++ "` needs an `instance "
          ++ Name.toChars className
          ++ "`, and here it is used at this type:"

-- | The type the constraint is at, and how it got there.
--
-- An empty chain is the direct case and prints one type. A chain means an
-- instance was found and its own context could not be discharged, which is a
-- different fact and reads as one: @Eq (Array (Int -> Int))@ has an instance
-- and @Eq (Int -> Int)@ is why it does not help.
chain :: L.Localizer -> Name.Name -> Can.Type -> [(Can.Class, Can.Type)] -> [D.Doc]
chain localizer className tipe because =
  case because of
    [] ->
      [D.indent 4 $ D.dullyellow $ RT.canToDoc localizer RT.None tipe]
    (Can.Class _ outerName, outer) : _ ->
      [ D.indent 4 $ D.dullyellow $ RT.canToDoc localizer RT.None outer,
        D.reflow $
          "There is an `instance "
            ++ Name.toChars outerName
            ++ "` for that, and using it means also having:",
        D.indent 4 $
          D.dullyellow $
            D.fromChars (Name.toChars className ++ " ") <> RT.canToDoc localizer RT.App tipe
      ]
