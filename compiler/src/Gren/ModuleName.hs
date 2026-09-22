{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnboxedTuples #-}

module Gren.ModuleName
  ( Raw,
    toChars,
    toFilePath,
    toHyphenPath,
    --
    encode,
    decoder,
    keyDecoder,
    parser,
    --
    Canonical (..),
    basics,
    bitwise,
    bytes,
    bytesTransient,
    arrayTransient,
    source,
    process,
    taskInternal,
    taskModule,
    char,
    string,
    maybe,
    result,
    array,
    dict,
    platform,
    cmd,
    sub,
    debug,
    inspect,
    inbound,
    virtualDom,
    jsonDecode,
    jsonEncode,
    jsonValue,
  )
where

import Control.Monad (liftM2)
import Data.Binary (Binary (..))
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Data.Word (Word8)
import Foreign.Ptr (Ptr, minusPtr, plusPtr)
import Gren.Package qualified as Pkg
import Json.Decode qualified as D
import Json.Encode qualified as E
import Parse.Primitives (Col, Row)
import Parse.Primitives qualified as P
import Parse.Variable qualified as Var
import System.FilePath qualified as FP
import Prelude hiding (maybe)

-- RAW

type Raw = Name.Name

toChars :: Raw -> String
toChars =
  Name.toChars

toFilePath :: Raw -> FilePath
toFilePath name =
  map (\c -> if c == '.' then FP.pathSeparator else c) (Name.toChars name)

toHyphenPath :: Raw -> FilePath
toHyphenPath name =
  map (\c -> if c == '.' then '-' else c) (Name.toChars name)

-- JSON

encode :: Raw -> E.Value
encode =
  E.name

decoder :: D.Decoder (Row, Col) Raw
decoder =
  D.customString parser (,)

keyDecoder :: (Row -> Col -> x) -> D.KeyDecoder x Raw
keyDecoder toError =
  let keyParser =
        P.specialize (\(r, c) _ _ -> toError r c) parser
   in D.KeyDecoder keyParser toError

-- PARSER

parser :: P.Parser (Row, Col) Raw
parser =
  P.Parser $ \(P.State src pos end indent row col) cok _ cerr eerr ->
    let (# isGood, newPos, newCol #) = chompStart pos end col
     in if isGood && minusPtr newPos pos < 256
          then
            let !newState = P.State src newPos end indent row newCol
             in cok (Utf8.fromPtr pos newPos) newState
          else
            if col == newCol
              then eerr row newCol (,)
              else cerr row newCol (,)

chompStart :: Ptr Word8 -> Ptr Word8 -> Col -> (# Bool, Ptr Word8, Col #)
chompStart pos end col =
  let !width = Var.getUpperWidth pos end
   in if width == 0
        then (# False, pos, col #)
        else chompInner (plusPtr pos width) end (col + 1)

chompInner :: Ptr Word8 -> Ptr Word8 -> Col -> (# Bool, Ptr Word8, Col #)
chompInner pos end col =
  if pos >= end
    then (# True, pos, col #)
    else
      let !word = P.unsafeIndex pos
          !width = Var.getInnerWidthHelp pos end word
       in if width == 0
            then
              if word == 0x2E {-.-}
                then chompStart (plusPtr pos 1) end (col + 1)
                else (# True, pos, col #)
            else chompInner (plusPtr pos width) end (col + 1)

-- CANONICAL

data Canonical = Canonical
  { _package :: !Pkg.Name,
    _module :: !Name.Name
  }
  deriving (Show)

-- INSTANCES

instance Eq Canonical where
  (==) (Canonical pkg1 name1) (Canonical pkg2 name2) =
    name1 == name2 && pkg1 == pkg2

instance Ord Canonical where
  compare (Canonical pkg1 name1) (Canonical pkg2 name2) =
    case compare name1 name2 of
      LT -> LT
      EQ -> compare pkg1 pkg2
      GT -> GT

instance Binary Canonical where
  put (Canonical a b) = put a >> put b
  get = liftM2 Canonical get get

-- CORE

basics :: Canonical
basics = Canonical Pkg.core Name.basics

-- | Where `Bits` is declared (D145): its methods are named @and@, @or@ and
-- @xor@, and those are `Basics`'s `Bool` operations.
bitwise :: Canonical
bitwise = Canonical Pkg.core Name.bitwise

char :: Canonical
char = Canonical Pkg.core Name.char

string :: Canonical
string = Canonical Pkg.core Name.string

maybe :: Canonical
maybe = Canonical Pkg.core Name.maybe

result :: Canonical
result = Canonical Pkg.core Name.result

array :: Canonical
array = Canonical Pkg.core Name.array

dict :: Canonical
dict = Canonical Pkg.core Name.dict

platform :: Canonical
platform = Canonical Pkg.core Name.platform

cmd :: Canonical
cmd = Canonical Pkg.core "Platform.Cmd"

sub :: Canonical
sub = Canonical Pkg.core "Platform.Sub"

debug :: Canonical
debug = Canonical Pkg.core Name.debug

-- | `Inspect`, which declares the class of the same name and is default-imported
-- so that `inspect` is in scope everywhere (§G43).
inspect :: Canonical
inspect = Canonical Pkg.core Name.inspectModule

-- | `Inbound`, whose class checks a term only Erlang could have supplied
-- (geng-lang `m2-interop.md` D419, D422). Not default-imported.
inbound :: Canonical
inbound = Canonical Pkg.core Name.inboundModule

bytes :: Canonical
bytes = Canonical Pkg.core "Bytes"

-- | Where the bytes transient's type is declared, with the @bt_@ bindings: a
-- module @core@ does not expose, which @Bytes@ and @Bytes.Encode@ both import
-- (@m1b-bytes-prim.md@ D233, after D221's @Json.Value@).
bytesTransient :: Canonical
bytesTransient = Canonical Pkg.core "Bytes.Transient"

-- | Where the array transient's type is declared, with the @tr_@ bindings that
-- do not mention @Array@: a module @core@ does not expose, which @Array@ and
-- @Array.Builder@ both import (@m1b-arr-prim.md@ D240).
arrayTransient :: Canonical
arrayTransient = Canonical Pkg.core "Array.Transient"

-- | D71's mailbox (@ffi.md@ F4), the pull-based replacement for @Sub@. Unlike
-- the two transients this one is __exposed__ (D253): @portable-core.md@ P2
-- keeps @Source@ in @core@, and its whole purpose is to be named in the
-- signature of every extern that emits events.
source :: Canonical
source = Canonical Pkg.core "Source"

-- | Where @Process.Id@ is declared, the type @task_spawn@ answers and @task_kill@
-- takes (D283).
process :: Canonical
process = Canonical Pkg.core "Process"

-- | Where a @Task@'s type is declared: a module @core@ does not expose, because
-- @Platform@ — which declared it until close-out item 4 — and @Task@ import each
-- other (@m1b-source.md@ §SO11), exactly as the two transients' modules exist.
taskInternal :: Canonical
taskInternal = Canonical Pkg.core "Task.Internal"

-- | The module a reader writes when they mean a @Task@, which is what an error
-- message says rather than 'taskInternal'.
taskModule :: Canonical
taskModule = Canonical Pkg.core Name.task

-- HTML

virtualDom :: Canonical
virtualDom = Canonical Pkg.browser Name.virtualDom

-- JSON

jsonDecode :: Canonical
jsonDecode = Canonical Pkg.core "Json.Decode"

jsonEncode :: Canonical
jsonEncode = Canonical Pkg.core "Json.Encode"

-- | Where `Json.Encode.Value` is defined: an alias of `Json.Value.Value`, in a
-- module `core` does not expose, so that no program reaches its constructors
-- (`m1b-json.md` D212, D221).
jsonValue :: Canonical
jsonValue = Canonical Pkg.core "Json.Value"
