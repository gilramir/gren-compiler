{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Reporting
  ( Style,
    silent,
    json,
    terminal,
    heldTerminal,
    releaseHeld,
    --
    attempt,
    attemptWithStyle,
    --
    Key,
    report,
    ignorer,
    ask,
    --
    BKey,
    BMsg (..),
    trackBuild,
    --
    reportGenerate,
    --
    putStrFlush,
  )
where

import Control.Concurrent
import Control.Exception (AsyncException (UserInterrupt), SomeException, catch, fromException, throw)
import Data.ByteString.Builder qualified as B
import Data.NonEmptyList qualified as NE
import Gren.ModuleName qualified as ModuleName
import Json.Encode qualified as Encode
import Reporting.Doc qualified as D
import Reporting.Exit qualified as Exit
import Reporting.Exit.Help qualified as Help
import System.Exit qualified as Exit
import System.IO (hFlush, hPutStr, hPutStrLn, stderr, stdout)
import System.Info qualified as Info

-- STYLE

-- | A 'Terminal' with a slot holds its build's "Success!" rather than
-- printing it: the run the refinement checker stops (geng-lang @m4-refine.md@
-- §RF26, D844) built a program it has not yet accepted, and its message is
-- printed by 'releaseHeld' only if the build goes on in that run.
data Style
  = Silent
  | Json
  | Terminal (MVar ()) (Maybe (MVar (Maybe String)))

silent :: Style
silent =
  Silent

json :: Style
json =
  Json

terminal :: IO Style
terminal =
  Terminal <$> newMVar () <*> pure Nothing

heldTerminal :: IO Style
heldTerminal =
  Terminal <$> newMVar () <*> (Just <$> newMVar Nothing)

-- | The message a held build kept, printed now.
releaseHeld :: Style -> IO ()
releaseHeld style =
  case style of
    Terminal mvar (Just held) ->
      do
        readMVar mvar
        message <- swapMVar held Nothing
        -- Flushed now: the build may yet fail in this run, a backend's
        -- refusal on stderr, and the line must not wait on the exit for it.
        mapM_ (\m -> putStrLn m >> hFlush stdout) message
    _ ->
      return ()

-- ATTEMPT

attempt :: (x -> Help.Report) -> IO (Either x a) -> IO a
attempt toReport work =
  do
    result <- work `catch` reportExceptionsNicely
    case result of
      Right a ->
        return a
      Left x ->
        do
          Exit.toStderr (toReport x)
          Exit.exitFailure

attemptWithStyle :: Style -> (x -> Help.Report) -> IO (Either x a) -> IO a
attemptWithStyle style toReport work =
  do
    result <- work `catch` reportExceptionsNicely
    case result of
      Right a ->
        case style of
          Silent ->
            return a
          Json ->
            return a
          Terminal mvar _ ->
            do
              readMVar mvar
              return a
      Left x ->
        case style of
          Silent ->
            do Exit.exitFailure
          Json ->
            do
              B.hPutBuilder stderr (Encode.encodeUgly (Exit.toJson (toReport x)))
              Exit.exitFailure
          Terminal mvar _ ->
            do
              readMVar mvar
              Exit.toStderr (toReport x)
              Exit.exitFailure

-- MARKS

isWindows :: Bool
isWindows =
  Info.os == "mingw32"

-- KEY

newtype Key msg = Key (msg -> IO ())

report :: Key msg -> msg -> IO ()
report (Key send) msg =
  send msg

ignorer :: Key msg
ignorer =
  Key (\_ -> return ())

-- ASK

ask :: Bool -> D.Doc -> IO Bool
ask skipPrompts doc =
  if skipPrompts
    then pure True
    else do
      Help.toStdout doc
      askHelp

askHelp :: IO Bool
askHelp =
  do
    hFlush stdout
    input <- getLine
    case input of
      "" -> return True
      "Y" -> return True
      "y" -> return True
      "n" -> return False
      _ ->
        do
          putStr "Must type 'y' for yes or 'n' for no: "
          askHelp

-- BUILD

type BKey = Key BMsg

type BResult a = Either Exit.BuildProblem a

trackBuild :: Style -> (BKey -> IO (BResult a)) -> IO (BResult a)
trackBuild style callback =
  case style of
    Silent ->
      callback (Key (\_ -> return ()))
    Json ->
      callback (Key (\_ -> return ()))
    Terminal mvar held ->
      do
        chan <- newChan

        _ <- forkIO $
          do
            takeMVar mvar
            putStrFlush "Compiling ..."
            buildLoop chan held 0
            putMVar mvar ()

        result <- callback (Key (writeChan chan . Left))
        writeChan chan (Right result)
        return result

data BMsg
  = BDone

buildLoop :: Chan (Either BMsg (BResult a)) -> Maybe (MVar (Maybe String)) -> Int -> IO ()
buildLoop chan held done =
  do
    msg <- readChan chan
    case msg of
      Left BDone ->
        do
          let !done1 = done + 1
          putStrFlush $ "\rCompiling (" ++ show done1 ++ ")"
          buildLoop chan held done1
      Right result ->
        let !message = toFinalMessage done result
            !width = 12 + length (show done)
         in case (held, result) of
              (Just slot, Right _) ->
                do
                  putStrFlush ('\r' : replicate width ' ' ++ "\r")
                  _ <- swapMVar slot (Just message)
                  return ()
              _ ->
                putStrLn $
                  if length message < width
                    then '\r' : replicate width ' ' ++ '\r' : message
                    else '\r' : message

toFinalMessage :: Int -> BResult a -> [Char]
toFinalMessage done result =
  case result of
    Right _ ->
      case done of
        0 -> "Success!"
        1 -> "Success! Compiled 1 module."
        n -> "Success! Compiled " ++ show n ++ " modules."
    Left problem ->
      case problem of
        Exit.BuildBadModules _ _ [] ->
          "Detected problems in 1 module."
        Exit.BuildBadModules _ _ (_ : ps) ->
          "Detected problems in " ++ show (2 + length ps) ++ " modules."
        Exit.BuildProjectProblem _ ->
          "Detected a problem."

-- GENERATE

reportGenerate :: Style -> NE.List ModuleName.Raw -> FilePath -> IO ()
reportGenerate style names output =
  case style of
    Silent ->
      return ()
    Json ->
      return ()
    Terminal mvar _ ->
      do
        readMVar mvar
        let cnames = fmap ModuleName.toChars names
        putStrLn ('\n' : toGenDiagram cnames output)

toGenDiagram :: NE.List [Char] -> FilePath -> [Char]
toGenDiagram (NE.List name names) output =
  let width = 3 + foldr (max . length) (length name) names
   in case names of
        [] ->
          toGenLine width name ('>' : ' ' : output ++ "\n")
        _ : _ ->
          unlines $
            toGenLine width name (vtop : hbar : hbar : '>' : ' ' : output)
              : reverse (zipWith (toGenLine width) (reverse names) ([vbottom] : repeat [vmiddle]))

toGenLine :: Int -> [Char] -> [Char] -> [Char]
toGenLine width name end =
  "    " ++ name ++ ' ' : replicate (width - length name) hbar ++ end

hbar :: Char
hbar = if isWindows then '-' else '─'

vtop :: Char
vtop = if isWindows then '+' else '┬'

vmiddle :: Char
vmiddle = if isWindows then '+' else '┤'

vbottom :: Char
vbottom = if isWindows then '+' else '┘'

--

putStrFlush :: String -> IO ()
putStrFlush str =
  hPutStr stdout str >> hFlush stdout

-- REPORT EXCEPTIONS NICELY

reportExceptionsNicely :: SomeException -> IO a
reportExceptionsNicely e =
  case fromException e of
    Just UserInterrupt -> throw e
    _ -> putException e >> throw e

putException :: SomeException -> IO ()
putException e = do
  hPutStrLn stderr ""
  Help.toStderr $
    D.stack $
      [ D.dullyellow "-- ERROR -----------------------------------------------------------------------",
        D.reflow $
          "I ran into something that bypassed the normal error reporting process!\
          \ I extracted whatever information I could from the internal error:",
        D.vcat $ map (\line -> D.red ">" <> "   " <> D.fromChars line) (lines (show e)),
        D.reflow $
          "These errors are usually pretty confusing, so start by asking around on one of\
          \ forums listed at https://gren-lang.org/community to see if anyone can get you\
          \ unstuck quickly.",
        D.dullyellow "-- REQUEST ---------------------------------------------------------------------",
        D.reflow $
          "If you are feeling up to it, please try to get your code down to the smallest\
          \ version that still triggers this message. Ideally in a single Main.geng and\
          \ geng.toml file.",
        D.reflow $
          "From there open a NEW issue at https://github.com/gren-lang/compiler/issues with\
          \ your reduced example pasted in directly. (Not a link to a repo or gist!) Do not\
          \ worry about if someone else saw something similar. More examples is better!",
        D.reflow $
          "This kind of error is usually tied up in larger architectural choices that are\
          \ hard to change, so even when we have a couple good examples, it can take some\
          \ time to resolve in a solid way."
      ]
