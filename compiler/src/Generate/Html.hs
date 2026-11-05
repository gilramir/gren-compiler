{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Generate.Html
  ( sandwich,
    leadingLines,
    script,
    scriptLeadingLines,
  )
where

import Data.ByteString.Builder qualified as B
import Data.Name qualified as Name
import Text.RawString.QQ (r)

leadingLines :: Int
leadingLines = 2

-- | A @browser@ program's page (D1072, geng-lang @browser.md@ §BR7): the
-- bundle, and a call that starts its @main@. A crash in the task's first
-- slice runs inside that call and is shown on the page as well as thrown; a
-- later one reaches the browser's console as any uncaught error does.
sandwich :: Name.Name -> B.Builder -> B.Builder
sandwich moduleName javascript =
  let name = Name.toBuilder moduleName
   in [r|<!DOCTYPE HTML>
<html>
<head>
  <meta charset="UTF-8">
  <title>|]
        <> name
        <> [r|</title>
</head>

<body>
<script>
try {
|]
        <> javascript
        <> [r|

  Gren.|]
        <> name
        <> [r|.init({});
}
catch (e)
{
  var pre = document.createElement("pre");
  pre.textContent = String(e);
  document.body.appendChild(pre);
  throw e;
}
</script>
</body>
</html>|]

scriptLeadingLines :: Int
scriptLeadingLines = 0

-- | A @browser@ program as a script for a page of its own (D1072): the bundle,
-- and a call that starts its @main@ when the script runs. It is a classic
-- script, since the bundle finds its global through @this@, which a module
-- does not have.
script :: Name.Name -> B.Builder -> B.Builder
script moduleName javascript =
  javascript
    <> [r|
this.Gren.|]
    <> Name.toBuilder moduleName
    <> [r|.init({});
|]
