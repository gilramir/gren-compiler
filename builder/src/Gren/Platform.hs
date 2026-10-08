module Gren.Platform
  ( Platform (..),
    --
    compatible,
    --
    encode,
    decoder,
    fromChars,
    toChars,
  )
where

import Data.Binary (Binary, get, getWord8, put, putWord8)
import Data.Utf8 qualified as Utf8
import Json.Decode qualified as D
import Json.Encode qualified as E

-- | @Host@ is a library a C, Go or Python program loads (geng-lang
-- @m3-embed.md@ D619): an application with no @main@, whose exports are the
-- values the one module it is built from exposes. It is a platform rather
-- than @Common@ told otherwise, as @beam@ and @os@ are told @Node@, because the
-- backend's answer differs: its roots are those values, each held to what can
-- cross to C ('Generate.checkRoots').
data Platform
  = Common
  | Browser
  | Node
  | Host
  deriving (Show, Eq)

-- COMPATIBILITY

compatible :: Platform -> Platform -> Bool
compatible rootPlatform comparison =
  rootPlatform == comparison || comparison == Common

-- JSON

encode :: Platform -> E.Value
encode platform =
  case platform of
    Common -> E.chars "common"
    Browser -> E.chars "browser"
    Node -> E.chars "node"
    Host -> E.chars "host"

decoder :: a -> D.Decoder a Platform
decoder badPlatformError =
  do
    platformStr <- D.string
    case fromChars $ Utf8.toChars platformStr of
      Just platform -> D.succeed platform
      Nothing -> D.failure badPlatformError

fromChars :: [Char] -> Maybe Platform
fromChars value =
  case value of
    "common" -> Just Common
    "browser" -> Just Browser
    "node" -> Just Node
    "host" -> Just Host
    _ -> Nothing

toChars :: Platform -> [Char]
toChars value =
  case value of
    Common -> "common"
    Browser -> "browser"
    Node -> "node"
    Host -> "host"

-- BINARY

instance Binary Platform where
  put platform =
    case platform of
      Common -> putWord8 0
      Browser -> putWord8 1
      Node -> putWord8 2
      Host -> putWord8 3

  get =
    do
      n <- getWord8
      case n of
        0 -> return Common
        1 -> return Browser
        2 -> return Node
        3 -> return Host
        _ -> fail "binary encoding of Platform was corrupted"
