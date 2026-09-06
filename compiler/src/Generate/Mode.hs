-- | Dev or @--optimize@, and the field table the second one needs.
--
-- The table itself is built by `Generate.CoreJS.shortenFieldNames`, from the
-- linked program's field /set/. It was built here until the old pipeline was
-- retired, out of an @Opt.GlobalGraph@'s frequency /map/ — shortest names to
-- commonest fields. C6 wants a specified order and a set has one, so the
-- assignment is alphabetical instead, at a measured 0.34%
-- (@docs\/m1a-js-on-core.md@ §J15).
module Generate.Mode
  ( Mode (..),
    ShortFieldNames,
  )
where

import Data.Map qualified as Map
import Data.Name qualified as Name
import Generate.JavaScript.Name qualified as JsName

-- MODE

data Mode
  = Dev
  | Prod ShortFieldNames

-- SHORTEN FIELD NAMES

type ShortFieldNames =
  Map.Map Name.Name JsName.Name
