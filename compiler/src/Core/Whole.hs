{-# OPTIONS_GHC -Wall #-}

-- | What a build is, besides its modules: the whole-program message the wire
-- carries beside a @Module@ (D378, @m2-seam.md@ §DS5 item 4).
--
-- __This is not the linked 'Core.Program.Program'__, which @m1a-wire.md@ §B5
-- says is not serialized and still is not: the link is derived from the
-- modules, these roots and a @Backend@, and the @Backend@ half is the build
-- system's knowledge that C16 keeps out of the IR. What is here is the
-- question the link answers from.
--
-- The runtime is Core's own enum rather than 'Gren.Platform.Platform' for the
-- same reason: @Platform@ is the build system's type, and Core carries a fact
-- a backend needs, not a manifest's vocabulary. The driver maps one to the
-- other.
module Core.Whole
  ( Program (..),
    Root (..),
    Mode (..),
    Runtime (..),
  )
where

import Core.Target qualified as Target
import Data.Name (Name)
import Gren.ModuleName qualified as ModuleName

-- | The roots are __in the order the build names them__, which is the order
-- 'Core.Program.link' walks and a backend emits in. Sorting them would reorder
-- the output of a build whose roots were given in another order.
data Program = Program
  { _programRoots :: ![Root],
    _programTarget :: !Target.Target,
    _programMode :: !Mode,
    _programRuntime :: !Runtime
  }
  deriving (Eq, Show)

-- | One root, written out rather than interned: a @Program@ has no string
-- table, and holds a handful of names each mentioned once.
data Root = Root
  { _rootHome :: !ModuleName.Canonical,
    _rootName :: !Name
  }
  deriving (Eq, Show)

-- | Whether the build is @--optimize@d. What that means is the backend's.
data Mode
  = Dev
  | Prod
  deriving (Eq, Show, Enum, Bounded)

-- | The runtime the application declares. A package declares @common@, and an
-- application that does not say otherwise is @node@.
data Runtime
  = Common
  | Browser
  | Node
  deriving (Eq, Show, Enum, Bounded)
