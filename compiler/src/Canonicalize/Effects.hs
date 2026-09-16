{-# OPTIONS_GHC -Wall #-}

-- | An @effect module@ or a @port@ is refused (@m1b-source.md@ §SO19).
--
-- Effect managers and ports left with @Platform@, @Cmd@ and @Sub@, and nothing
-- after canonicalization has a place for either. The parser still takes both
-- until the syntax leaves (§SO17.2's 6c), so this is where a program that
-- declares one is told what replaces it.
module Canonicalize.Effects
  ( refuse,
  )
where

import AST.Source qualified as Src
import Reporting.Annotation qualified as A
import Reporting.Error.Canonicalize qualified as Error
import Reporting.Result qualified as Result

refuse :: Src.Effects -> Result.Result i w Error.Error ()
refuse effects =
  case effects of
    Src.NoEffects ->
      Result.ok ()
    Src.Ports ports _ ->
      case fmap snd ports of
        Src.Port (A.At region name) _ : _ ->
          Result.throw (Error.PortDeclaration region name)
        [] ->
          Result.ok ()
    Src.Manager region _ _ ->
      Result.throw (Error.EffectModule region)
