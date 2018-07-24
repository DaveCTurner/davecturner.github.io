{-# LANGUAGE TupleSections #-}

module Main where

import Graphics.Rendering.Cairo
import Control.Monad

data DotColour = Red | Blue

type Point = (Double, Double)

preservingContext :: Render a -> Render a
preservingContext go = do
  save
  result <- go
  restore
  return result

pixelsPerGridSquare :: Double
pixelsPerGridSquare = 20.0

coordsFromPoint :: Point -> (Double, Double)
coordsFromPoint (gridX, gridY) = (gridX * pixelsPerGridSquare, gridY * pixelsPerGridSquare)

moveToPoint :: Point -> Render ()
moveToPoint p = let (x,y) = coordsFromPoint p in moveTo x y

lineToPoint :: Point -> Render ()
lineToPoint p = let (x,y) = coordsFromPoint p in lineTo x y

translatePoint :: Double -> Double -> Point -> Point
translatePoint dx dy (x,y) = (x+dx,y+dy)

dot :: DotColour -> Point -> Render ()
dot col p = preservingContext $ do
  let (xc,yc) = coordsFromPoint p
  arc xc yc 10 0 (2*pi)
  case col of
    Red  -> setSourceRGB (182/255) (62/255) (69/255)
    Blue -> setSourceRGB (45/255) (112/255) (171/255)
  fillPreserve
  setSourceRGB 0.0 0.0 0.0
  stroke

dotPair :: Point -> Point -> Render ()
dotPair r b = preservingContext $ do
  moveToPoint r
  lineToPoint b
  stroke
  dot Red  r
  dot Blue b

drawPath :: [Point] -> Render ()
drawPath gridCoords = preservingContext $ do
  moveToPoint $ last gridCoords
  mapM_ lineToPoint gridCoords
  stroke

horizBrace :: Bool -> Double -> Double -> Double -> Render ()
horizBrace pointsDown yBase xLeft xRight = preservingContext $ do
  moveToPoint (xLeft,yStart)
  arcWith arcFn1 (xLeft + 0.5,  yStart) pi (3.0*pi/2.0)
  arcWith arcFn2 (xMid - 0.5,   yApex)  (pi/2.0) 0
  arcWith arcFn2 (xMid + 0.5,   yApex)  pi (pi/2.0)
  arcWith arcFn1 (xRight - 0.5, yStart) (3.0*pi/2.0) 0
  stroke

  where
    xMid  = (xLeft + xRight) * 0.5
    yStart = if pointsDown then yBase - 0.75 else yBase + 0.75
    yLine = if pointsDown then yStart - 0.5 else yStart + 0.5
    yApex = if pointsDown then yStart - 1.0 else yStart + 1.0

    arcWith arcFn centre angle0 angle1
      = let (xc,yc) = coordsFromPoint centre
            fixAngle = if pointsDown then id else negate
        in arcFn xc yc (pixelsPerGridSquare * 0.5)
              (fixAngle angle0) (fixAngle angle1)

    arcFn1 = if pointsDown then arc else arcNegative
    arcFn2 = if pointsDown then arcNegative else arc

main :: IO ()
main = do

  do
    let r1 = (8,2)
        r2 = (11,5)
        r3 = (5,7)
        r4 = (10,8)
        b1 = (15,2)
        b2 = (16,6)
        b3 = (12,11)
        b4 = (4,13)

    withImageSurface FormatARGB32 400 300 $ \surface -> do
      renderWith surface $ do
        dotPair r1 b1
        dotPair r2 b4
        dotPair r3 b3
        dotPair r4 b2
      surfaceWriteToPNG surface "01-example-layout-crossed.png"

    withImageSurface FormatARGB32 400 300 $ \surface -> do
      renderWith surface $ do
        dotPair r1 b1
        dotPair r2 b2
        dotPair r3 b4
        dotPair r4 b3
      surfaceWriteToPNG surface "02-example-layout-uncrossed.png"

  withImageSurface FormatARGB32 400 480 $ \surface -> do
    renderWith surface $ do
      let xs scaleFactor = map (\n -> (fromIntegral n - 2) * scaleFactor + 10) [0..4]
          rxs = xs 2.0
          bxs = xs 1.3
          renderUnchangedAt y = do
            zipWithM_ dotPair (map (,y) rxs) (map (,y+2) bxs)

      renderUnchangedAt 1
      renderUnchangedAt 14
      dotPair (4,2) (16,9)
      dotPair (4,9) (16,2)
      dotPair (4,15) (16,15)
      dotPair (4,22) (16,22)
      drawPath $ map (translatePoint 8 10)
            [(3,0),(3,1),(3.5,1),(2,2),(0.5,1),(1,1),(1,0),(2,0)]

    surfaceWriteToPNG surface "03-introducing-crossings.png"

  withImageSurface FormatARGB32 400 280 $ \surface -> do
    renderWith surface $ do
      forM_ [3,11] $ \y -> do
        preservingContext $ do
          moveToPoint (4,y)
          lineToPoint (16,y)
          stroke

        dot Red   (4,y)
        dot Red   (8,y)
        dot Blue (12,y)
        dot Blue (16,y)

      horizBrace True  3 4 12
      horizBrace False 3 8 16

      horizBrace True  11 4 16
      horizBrace False 11 8 12

      drawPath $ map (translatePoint 10 5.5)
        [(0,0),(1.5,1),(1,1),(1,2),(1.5,2),(0,3),(-1.5,2),(-1,2),(-1,1),(-1.5,1)]

    surfaceWriteToPNG surface "06-badly-collinear.png"

  withImageSurface FormatARGB32 400 240 $ \surface -> do
    renderWith surface $ do
      forM_ [3] $ \y -> do
        preservingContext $ do
          moveToPoint (4,y)
          lineToPoint (16,y)
          stroke

        dot Red   (4,y)
        dot Blue  (8,y)
        dot Blue (12,y)
        dot Red  (16,y)

      horizBrace True  3 4 12
      horizBrace False 3 8 16

      dotPair  (4,11)  (8,11)
      dotPair (16,11) (12,11)

      horizBrace True  11 4 8
      horizBrace True  11 12 16

      drawPath $ map (translatePoint 8 6)
            [(3,0),(3,1),(3.5,1),(2,2),(0.5,1),(1,1),(1,0),(2,0)]

    surfaceWriteToPNG surface "07-ok-collinear.png"

  withImageSurface FormatARGB32 400 340 $ \surface -> do
    renderWith surface $ do
      dotPair (4,2) (16,8)
      dotPair (15,4) (12,6)

      dotPair (4,10) (12,14)
      dotPair (15,12) (16,16)

      drawPath $ map (translatePoint 8 8)
            [(3,0),(3,1),(3.5,1),(2,2),(0.5,1),(1,1),(1,0),(2,0)]

    surfaceWriteToPNG surface "08-ok-collinear.png"

  withImageSurface FormatARGB32 400 410 $ \surface -> do
    renderWith surface $ do
      forM_ [2,6,10,14,18] $ \y -> do
        preservingContext $ do
          moveToPoint (4,y)
          lineToPoint (16,y)
          stroke

      let dots y cols = zipWithM_ go cols [4,8,12,16]
            where go col x = dot col (x,y)

      dots 2  [Blue,Red,Red,Blue]
      horizBrace True  2 4 12
      horizBrace False 2 8 16
      
      dots 6  [Red,Blue,Blue,Red]
      horizBrace True  6 4 12
      horizBrace False 6 8 16

      dots 10 [Red,Blue,Red,Blue]
      horizBrace True  10 4 16
      horizBrace False 10 8 12

      dots 14 [Red,Red,Blue,Blue]
      horizBrace True  14 4 12
      horizBrace False 14 8 16

      dots 18 [Red,Red,Blue,Blue]
      horizBrace True  18 4 16
      horizBrace False 18 8 12

    surfaceWriteToPNG surface "09-all-collinear-crossings.png"

  withImageSurface FormatARGB32 400 100 $ \surface -> do
    renderWith surface $
      forM_ (takeWhile (<= 16) $ iterate (+2) 4) $ \x -> do
        dot Red  (x,1)
        dot Blue (x,4)

    surfaceWriteToPNG surface "10-many-collinear-points.png"

  withImageSurface FormatARGB32 400 100 $ \surface -> do
    renderWith surface $
      forM_ (takeWhile (<= 16) $ iterate (+2) 4) $ \x -> do
        let isEndpoint = x==4 || x==16
        dot (if isEndpoint then Blue else Red) (x,1)
        dot (if isEndpoint then Red else Blue) (x,4)

    surfaceWriteToPNG surface "11-many-collinear-points.png"

