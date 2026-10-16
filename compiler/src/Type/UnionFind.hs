{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Type.UnionFind
  ( Point,
    fresh,
    union,
    equivalent,
    redundant,
    get,
    set,
    modify,
    pointId,
  )
where

{- This is based on the following implementations:

  - https://hackage.haskell.org/package/union-find-0.2/docs/src/Data-UnionFind-IO.html
  - http://yann.regis-gianas.org/public/mini/code_UnionFind.html

It seems like the OCaml one came first, but I am not sure.

Compared to the Haskell implementation, the major changes here include:

  1. No more reallocating PointInfo when changing the weight
  2. Using the strict modifyIORef

-}

import Control.Monad (when)
import Data.IORef (IORef, atomicModifyIORef', modifyIORef', newIORef, readIORef, writeIORef)
import Data.Word (Word32)
import System.IO.Unsafe (unsafePerformIO)

-- POINT

newtype Point a
  = Pt (IORef (PointInfo a))
  deriving (Eq)

data PointInfo a
  = Info {-# UNPACK #-} !(IORef Word32) {-# UNPACK #-} !(IORef a) {-# UNPACK #-} !Int
  | Link {-# UNPACK #-} !(Point a)

-- HELPERS

-- | Every point's number, for 'pointId'. Atomic, since modules are solved on
-- several threads; the numbers mean nothing from one run to the next.
counter :: IORef Int
counter = unsafePerformIO (newIORef 0)
{-# NOINLINE counter #-}

fresh :: a -> IO (Point a)
fresh value =
  do
    weight <- newIORef 1
    desc <- newIORef value
    i <- atomicModifyIORef' counter (\n -> (n + 1, n))
    link <- newIORef (Info weight desc i)
    return (Pt link)

repr :: Point a -> IO (Point a)
repr point@(Pt ref) =
  do
    pInfo <- readIORef ref
    case pInfo of
      Info _ _ _ ->
        return point
      Link point1@(Pt ref1) ->
        do
          point2 <- repr point1
          when (point2 /= point1) $
            do
              pInfo1 <- readIORef ref1
              writeIORef ref pInfo1
          return point2

-- | A number for the class a point is in, the same for every point in it until
-- the next 'union': its representative's. What a walk keyed on variables
-- memoizes by (geng-lang @m3-sweep.md@ §SW44). Not a 'StableName', which the
-- collector scans at every collection.
pointId :: Point a -> IO Int
pointId point =
  do
    Pt ref <- repr point
    pInfo <- readIORef ref
    case pInfo of
      Info _ _ i ->
        return i
      Link _ ->
        error "Type.UnionFind.pointId: a representative is never a link"

get :: Point a -> IO a
get point@(Pt ref) =
  do
    pInfo <- readIORef ref
    case pInfo of
      Info _ descRef _ ->
        readIORef descRef
      Link (Pt ref1) ->
        do
          link' <- readIORef ref1
          case link' of
            Info _ descRef _ ->
              readIORef descRef
            Link _ ->
              get =<< repr point

set :: Point a -> a -> IO ()
set point@(Pt ref) newDesc =
  do
    pInfo <- readIORef ref
    case pInfo of
      Info _ descRef _ ->
        writeIORef descRef newDesc
      Link (Pt ref1) ->
        do
          link' <- readIORef ref1
          case link' of
            Info _ descRef _ ->
              writeIORef descRef newDesc
            Link _ ->
              do
                newPoint <- repr point
                set newPoint newDesc

modify :: Point a -> (a -> a) -> IO ()
modify point@(Pt ref) func =
  do
    pInfo <- readIORef ref
    case pInfo of
      Info _ descRef _ ->
        modifyIORef' descRef func
      Link (Pt ref1) ->
        do
          link' <- readIORef ref1
          case link' of
            Info _ descRef _ ->
              modifyIORef' descRef func
            Link _ ->
              do
                newPoint <- repr point
                modify newPoint func

union :: Point a -> Point a -> a -> IO ()
union p1 p2 newDesc =
  do
    point1@(Pt ref1) <- repr p1
    point2@(Pt ref2) <- repr p2

    Info w1 d1 _ <- readIORef ref1
    Info w2 d2 _ <- readIORef ref2

    if point1 == point2
      then writeIORef d1 newDesc
      else do
        weight1 <- readIORef w1
        weight2 <- readIORef w2

        let !newWeight = weight1 + weight2

        if weight1 >= weight2
          then do
            writeIORef ref2 (Link point1)
            writeIORef w1 newWeight
            writeIORef d1 newDesc
          else do
            writeIORef ref1 (Link point2)
            writeIORef w2 newWeight
            writeIORef d2 newDesc

equivalent :: Point a -> Point a -> IO Bool
equivalent p1 p2 =
  do
    v1 <- repr p1
    v2 <- repr p2
    return (v1 == v2)

redundant :: Point a -> IO Bool
redundant (Pt ref) =
  do
    pInfo <- readIORef ref
    case pInfo of
      Info _ _ _ ->
        return False
      Link _ ->
        return True
