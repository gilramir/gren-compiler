{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}

module Gren.Package
  ( Name,
    isKernel,
    isFirstParty,
    isValid,
    toChars,
    toFilePath,
    toJsonString,
    escapedSegments,
    toUtf8,
    fromUtf8,
    --
    application,
    kernel,
    core,
    browser,
    node,
    beam,
    url,
    --
    suggestions,
    --
    decoder,
    encode,
    keyDecoder,
    --
    parser,
  )
where

import Data.Binary (Binary, get, put)
import Data.Char qualified as Char
import Data.Coerce qualified as Coerce
import Data.Kind (Type)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Data.Word (Word8)
import Foreign.Ptr (Ptr, minusPtr, plusPtr)
import Json.Decode qualified as D
import Json.Encode qualified as E
import Json.String qualified as Json
import Parse.Primitives (Col, Row)
import Parse.Primitives qualified as P
import System.FilePath (joinPath)

-- PACKAGE NAMES

-- | A package identifier (@packaging.md@ K7, D76): a URL path — the host, then
-- the path to the package within its repository — or @core@, the one package
-- the toolchain distributes.
--
-- It was an author and a project, which is Gren's shape and GitHub's, and it is
-- one string now because nothing about an identifier divides it in two: a
-- package below a repository's root has as many parts as its path does (D295).
newtype Name = Name (Utf8.Utf8 IDENTIFIER)
  deriving (Eq, Ord)

data IDENTIFIER

instance Show Name where
  show = show . toChars

-- HELPERS

-- | Whether a package may hold kernel code, write @infix@ declarations and
-- reach a kernel module without importing it. Only @core@ does any of them
-- since the splicer's other clients left (D45); it was every package @gren-lang@
-- authors.
isKernel :: Name -> Bool
isKernel name =
  name == core

-- | Whether a package may declare classes and instances (`classes.md` §8.3).
--
-- @core@, and a package whose identifier begins with
-- @github.com/geng-language/@, the first-party prefix D289 settles. It is kept
-- apart from 'isKernel' because the two mean different things: a first-party
-- package is an ordinary hosted package that D59's class gate admits until D10
-- opens, and it holds no kernel code.
--
-- §8.4 gates classes and instances __together__, and the gate lifts when D10
-- opens rather than when any verb lands.
isFirstParty :: Name -> Bool
isFirstParty name =
  name == core || List.isPrefixOf firstPartyPrefix (toChars name)

firstPartyPrefix :: String
firstPartyPrefix =
  "github.com/geng-language/"

toChars :: Name -> String
toChars (Name identifier) =
  Utf8.toChars identifier

-- | Where a package's artifacts sit below a cache directory: one directory per
-- path element, so @core@ is @core@ and @github.com/x/y@ is @github.com/x/y@.
toFilePath :: Name -> FilePath
toFilePath name =
  joinPath (splitSegments (toChars name))

-- | The identifier's bytes, as whatever string type the caller keeps: the wire
-- format's string table holds them beside every other name.
toUtf8 :: Name -> Utf8.Utf8 (t :: Type)
toUtf8 (Name identifier) =
  Coerce.coerce identifier

-- | A name read back from somewhere that already holds one, which is the Core
-- wire format. It is not checked with 'isValid', because 'application' and
-- 'kernel' are names Core carries and no manifest may write.
fromUtf8 :: Utf8.Utf8 (t :: Type) -> Name
fromUtf8 bytes =
  Name (Coerce.coerce bytes)

toJsonString :: Name -> Json.String
toJsonString (Name identifier) =
  Coerce.coerce identifier

-- | The identifier's path elements, each escaped so that what is left is
-- letters, digits and underscores: @_@ is @_u@, @.@ is @_d@ and @-@ is @_h@
-- (D296). The escape is injective within an element, and an escaped element
-- has no character a separator could be, so a generated name joins them with
-- whatever separator its language allows and stays injective: the JavaScript
-- one with @$@, a dump file with @-@ and the C spike with @_s@.
escapedSegments :: Name -> [String]
escapedSegments name =
  map (concatMap escape) (splitSegments (toChars name))
  where
    escape c =
      case c of
        '_' -> "_u"
        '.' -> "_d"
        '-' -> "_h"
        _ -> [c]

splitSegments :: String -> [String]
splitSegments chars =
  case break (== '/') chars of
    (segment, []) -> [segment]
    (segment, _ : rest) -> segment : splitSegments rest

-- | Whether a string is an identifier a manifest may write (K7): @core@, or a
-- host with a dot in it, lower-case, then one or more path elements, with no
-- scheme, no empty element, no @.@ or @..@ element and no trailing slash.
--
-- An element is ASCII letters, digits, @.@, @_@ and @-@, and does not begin or
-- end with a dot, which is Go's module path rule less the tilde. Those are the
-- characters 'escapedSegments' has an escape for.
isValid :: String -> Bool
isValid chars =
  chars == "core"
    || case splitSegments chars of
      host : path@(_ : _) -> isHost host && all isElement path
      _ -> False

isHost :: String -> Bool
isHost host =
  elem '.' host
    && all (\c -> Char.isAsciiLower c || Char.isDigit c || c == '.' || c == '-') host
    && not (List.isInfixOf ".." host)
    && notAtEitherEnd '.' host
    && notAtEitherEnd '-' host

isElement :: String -> Bool
isElement element =
  not (null element)
    && all (\c -> Char.isAsciiLower c || Char.isAsciiUpper c || Char.isDigit c || c == '.' || c == '_' || c == '-') element
    && notAtEitherEnd '.' element

notAtEitherEnd :: Char -> String -> Bool
notAtEitherEnd c chars =
  not (List.isPrefixOf [c] chars) && not (List.isSuffixOf [c] chars)

-- COMMON PACKAGE NAMES

fromChars :: String -> Name
fromChars chars =
  Name (Utf8.fromChars chars)

-- | The name an application's own modules are compiled under. An application
-- has no identifier (K8), so this is not one: it has no dot, and no manifest can
-- write it, which is what keeps it from ever naming a real package.
application :: Name
application =
  fromChars "app"

-- | The pseudo-package the kernel's names live under, which leaves with the
-- splicer. It has no dot either.
kernel :: Name
kernel =
  fromChars "kernel"

core :: Name
core =
  fromChars "core"

browser :: Name
browser =
  fromChars "github.com/geng-language/browser"

node :: Name
node =
  fromChars "github.com/geng-language/node"

-- | The @beam@ package, whose @Beam.Server@ and @Beam.Worker@ the build
-- roots by (D414).
beam :: Name
beam =
  fromChars "github.com/geng-language/beam"

url :: Name
url =
  fromChars "github.com/geng-language/url"

-- PACKAGE SUGGESTIONS

-- | Modules a missing import is likely to have meant, and the package to install
-- for each. @core@'s modules are not in it: @core@ is never installed, so a
-- @core@ module that cannot be found is not one a suggestion could supply.
suggestions :: Map.Map Name.Name Name
suggestions =
  Map.fromList
    [ "Browser" ==> browser,
      "File" ==> browser,
      "File.Download" ==> browser,
      "File.Select" ==> browser,
      "Html" ==> browser,
      "Html.Attributes" ==> browser,
      "Html.Events" ==> browser,
      "Http" ==> browser,
      "Url.Parser" ==> url,
      "Url" ==> url
    ]

(==>) :: [Char] -> Name -> (Name.Name, Name)
(==>) moduleName package =
  (Utf8.fromChars moduleName, package)

-- BINARY

instance Binary Name where
  get = fmap Name Utf8.getVeryLong
  put (Name identifier) = Utf8.putVeryLong identifier

-- JSON

decoder :: D.Decoder (Row, Col) Name
decoder =
  D.customString parser (,)

encode :: Name -> E.Value
encode name =
  E.chars (toChars name)

keyDecoder :: (Row -> Col -> x) -> D.KeyDecoder x Name
keyDecoder toError =
  let keyParser =
        P.specialize (\(r, c) _ _ -> toError r c) parser
   in D.KeyDecoder keyParser toError

-- PARSER

-- | Every character an identifier may hold, then 'isValid' over the lot. A
-- string that is not an identifier is refused at its end, which is where the
-- decoder's report points.
parser :: P.Parser (Row, Col) Name
parser =
  P.Parser $ \(P.State src pos end indent row col) cok _ cerr eerr ->
    let !newPos = chompIdentifier pos end
        !len = minusPtr newPos pos
        !newCol = col + fromIntegral len
     in if len == 0
          then eerr row col (,)
          else
            let !identifier = Utf8.fromPtr pos newPos
             in if isValid (Utf8.toChars identifier)
                  then cok (Name identifier) (P.State src newPos end indent row newCol)
                  else cerr row newCol (,)

chompIdentifier :: Ptr Word8 -> Ptr Word8 -> Ptr Word8
chompIdentifier pos end =
  if pos < end && isIdentifierByte (P.unsafeIndex pos)
    then chompIdentifier (plusPtr pos 1) end
    else pos

isIdentifierByte :: Word8 -> Bool
isIdentifierByte word =
  0x61 {-a-} <= word && word <= 0x7A {-z-}
    || 0x41 {-A-} <= word && word <= 0x5A {-Z-}
    || 0x30 {-0-} <= word && word <= 0x39 {-9-}
    || word == 0x2E {-.-}
    || word == 0x2F {-/-}
    || word == 0x5F {-_-}
    || word == 0x2D {---}
