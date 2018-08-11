{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Control.Monad.Reader
import Graphics.Rendering.Cairo
import Graphics.Rendering.Cairo.Matrix (Matrix(..))
import Graphics.Rendering.Pango
import Control.Monad

axisOriginMargin :: Double
axisOriginMargin = 50

axisFreeEndMargin :: Double
axisFreeEndMargin = 11

transitionPointRadius :: Double
transitionPointRadius = 2.5

transitionHeight :: Double
transitionHeight = 100

axisLineWidth :: Double
axisLineWidth = 2.0

timeLineWidth :: Double
timeLineWidth = 1.0

arrowSize :: Double
arrowSize = 5.0

data TimeLineGraphConfig = TimeLineGraphConfig
  { _tlgcCentreOffset :: Double
  , _tlgcRenderSetup :: Render ()
  }

newtype TimeLineGraph a = TimeLineGraph { runTimeLineGraph :: ReaderT TimeLineGraphConfig Render a }
  deriving (Functor, Applicative, Monad, MonadReader TimeLineGraphConfig)

liftRender :: Render a -> TimeLineGraph a
liftRender r = do
  renderSetup <- asks _tlgcRenderSetup
  TimeLineGraph $ lift $ do
    save
    renderSetup
    result <- r
    restore
    return result

getTargetWidth :: TimeLineGraph Double
getTargetWidth = liftRender $ withTargetSurface $ \surface -> fromIntegral <$> imageSurfaceGetWidth surface

getTargetHeight :: TimeLineGraph Double
getTargetHeight = liftRender $ withTargetSurface $ \surface -> fromIntegral <$> imageSurfaceGetHeight surface

getCentreOffset :: TimeLineGraph Double
getCentreOffset = asks _tlgcCentreOffset

type Point = (Double, Double)

getBounds :: TimeLineGraph (Point, Point, Point)
getBounds = do
  centreOffset <- getCentreOffset
  w <- getTargetWidth
  h <- getTargetHeight

  let xMin = axisOriginMargin
      xMax = w - axisFreeEndMargin
      yMin = axisFreeEndMargin
      yMax = h - axisOriginMargin

  return ((xMin, yMin), ((xMin + xMax) / 2.0, (yMin + yMax) / 2.0), (xMax, yMax))

earliestCoordsFromOffset :: Double -> TimeLineGraph (Double, Double)
earliestCoordsFromOffset off = do
  centreOffset <- getCentreOffset
  ((xMin, _), (xc, yc), (_, yMax)) <- getBounds
  let ycOffset = yc - centreOffset + off
      lineLength = min (xc - xMin) (yMax - ycOffset)
  return (xc - lineLength, ycOffset + lineLength)

latestCoordsFromOffset :: Double -> TimeLineGraph (Double, Double)
latestCoordsFromOffset off = do
  centreOffset <- getCentreOffset
  ((_, yMin), (xc, yc), (xMax, _)) <- getBounds
  let ycOffset = yc - centreOffset + off
      lineLength = min (xMax - xc) (ycOffset - yMin)
  return (xc + lineLength, ycOffset - lineLength)

coordsFromOffset :: Double -> Double -> TimeLineGraph (Double, Double)
coordsFromOffset x off = do
  centreOffset <- getCentreOffset
  (_, (xc, yc), _) <- getBounds
  let ycOffset = yc - centreOffset + off
  return (xc + x, ycOffset - x)

drawBeforeTransition :: Double -> Double -> TimeLineGraph ()
drawBeforeTransition x off = do
  (x0, y0) <- earliestCoordsFromOffset off
  (x1, y1) <- coordsFromOffset x off
  liftRender $ do
    setLineCap LineCapSquare
    setLineWidth timeLineWidth
    moveTo x0 y0
    lineTo (x1 - transitionPointRadius + timeLineWidth) (y1 + transitionPointRadius - timeLineWidth)
    stroke
    arc x1 y1 transitionPointRadius 0 (2*pi)
    stroke

drawAfterTransition :: Double -> Double -> TimeLineGraph ()
drawAfterTransition t off = do
  (x0, y0) <- coordsFromOffset t off
  (x1, y1) <- latestCoordsFromOffset off
  liftRender $ do
    setLineCap LineCapSquare
    setLineWidth timeLineWidth
    arc x0 y0 transitionPointRadius 0 (2*pi)
    fillPreserve
    stroke
    moveTo (x0 + transitionPointRadius - timeLineWidth) (y0 - transitionPointRadius + timeLineWidth)
    lineTo x1 y1
    stroke

drawAxes :: TimeLineGraph ()
drawAxes = do
  ((xMin, yMin), _, (xMax, yMax)) <- getBounds
  liftRender $ do
    setLineWidth axisLineWidth
    moveTo xMin yMin
    lineTo xMin yMax
    lineTo xMax yMax
    stroke
    moveTo xMin (yMin - arrowSize)
    lineTo (xMin + arrowSize) (yMin +  arrowSize)
    lineTo (xMin - arrowSize) (yMin +  arrowSize)
    fill
    moveTo (xMax + arrowSize) yMax
    lineTo (xMax - arrowSize) (yMax - arrowSize)
    lineTo (xMax - arrowSize) (yMax + arrowSize)
    fill

    do
      pangoLayout <- createLayout "Universal time"
      liftIO $ do
        fontDescription <- fontDescriptionFromString "Sans 8"
        layoutSetFontDescription pangoLayout $ Just fontDescription
      PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
      moveTo (xMax - (x1 - x0)) (yMax + (y1 - y0))
      showLayout pangoLayout

    do
      pangoLayout <- createLayout "Local time"
      liftIO $ do
        fontDescription <- fontDescriptionFromString "Sans 8"
        layoutSetFontDescription pangoLayout $ Just fontDescription
      PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
      setMatrix (Matrix 0 (-1) 1 0 0 0)
      moveTo (x0 - x1 - (yMin + 2*arrowSize)) (xMin - y1 - 10)
      showLayout pangoLayout

drawConversion :: Double -> Double -> TimeLineGraph ()
drawConversion tUTC offset = do
  ((xMin, _), _, (_, yMax)) <- getBounds
  (x,y) <- coordsFromOffset tUTC offset
  liftRender $ do
    setLineCap LineCapSquare
    setLineWidth timeLineWidth
    setColourRed
    moveTo x    yMax
    lineTo x    y
    lineTo xMin y
    stroke

setColourBlue :: Render ()
setColourBlue = setSourceRGB (45/255) (112/255) (171/255)

setColourRed :: Render ()
setColourRed = setSourceRGB (182/255) (62/255) (69/255)

drawDiagram :: String -> Int -> Int -> Double -> TimeLineGraph a -> IO a
drawDiagram fileName width height centreOffset go =
  withImageSurface FormatARGB32 width height $ \surface -> do
    result <- renderWith surface $ flip runReaderT TimeLineGraphConfig
      { _tlgcCentreOffset = centreOffset
      , _tlgcRenderSetup  = return ()
      } $ runTimeLineGraph go

    surfaceWriteToPNG surface fileName
    return result

arrowFromUTC :: Double -> Double -> Double -> TimeLineGraph ()
arrowFromUTC t off d = do
  (x,y) <- coordsFromOffset t off
  liftRender $ do
    setColourRed
    moveTo x (y+d)
    lineTo (x+arrowSize) (y+d+arrowSize*2)
    lineTo (x-arrowSize) (y+d+arrowSize*2)
    fill

arrowToLocal :: Double -> Double -> Double -> TimeLineGraph ()
arrowToLocal t off d = do
  (x,y) <- coordsFromOffset t off
  liftRender $ do
    setColourRed
    moveTo (x-d-2*arrowSize) y
    lineTo (x-d) (y+arrowSize)
    lineTo (x-d) (y-arrowSize)
    fill

arrowToUTC :: Double -> Double -> Double -> TimeLineGraph ()
arrowToUTC t off d = do
  (x,y) <- coordsFromOffset t off
  liftRender $ do
    setColourRed
    moveTo x (y+d+arrowSize*2)
    lineTo (x+arrowSize) (y+d)
    lineTo (x-arrowSize) (y+d)
    fill

arrowFromLocal :: Double -> Double -> Double -> TimeLineGraph ()
arrowFromLocal t off d = do
  (x,y) <- coordsFromOffset t off
  liftRender $ do
    setColourRed
    moveTo (x-d) y
    lineTo (x-d-2*arrowSize) (y+arrowSize)
    lineTo (x-d-2*arrowSize) (y-arrowSize)
    fill

drawConstantOffset :: Double -> TimeLineGraph ()
drawConstantOffset off = drawConstantOffsetWithStyle off $ setLineWidth timeLineWidth

drawConstantOffsetWithStyle :: Double -> Render () -> TimeLineGraph ()
drawConstantOffsetWithStyle off applyStyle = do
  (x0, y0) <- earliestCoordsFromOffset off
  (x1, y1) <- latestCoordsFromOffset   off
  liftRender $ do
    applyStyle
    moveTo x0 y0
    lineTo x1 y1
    stroke

drawUTC :: TimeLineGraph ()
drawUTC = do
  drawConstantOffsetWithStyle 0 $ do
    setLineWidth timeLineWidth
    setSourceRGB 0.7 0.7 0.7
    setDash [5,5] 0
  (x,y) <- latestCoordsFromOffset 0
  liftRender $ do
    setSourceRGB 0.7 0.7 0.7
    pangoLayout <- createLayout "UTC"
    liftIO $ do
      fontDescription <- fontDescriptionFromString "Sans 8"
      layoutSetFontDescription pangoLayout $ Just fontDescription
    PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
    rotate (-pi/4)
    moveTo ((x-y) / sqrt 2 - (x1-x0)) ((x+y) / sqrt 2 + 2)
    showLayout pangoLayout

drawOffset :: Double -> Double -> Double -> TimeLineGraph ()
drawOffset t off0 off1 = do
  arrowFromUTC t off0 0
  arrowToUTC   t off1 ((-2) * arrowSize)
  (x0,y0) <- coordsFromOffset t off0
  (x1,y1) <- coordsFromOffset t off1
  liftRender $ do
    setLineWidth timeLineWidth
    setColourRed
    moveTo x0 y0
    lineTo x1 y1
    stroke

drawHorizOffset :: Double -> Double -> Double -> TimeLineGraph ()
drawHorizOffset t off0 off1 = do
  arrowToLocal   t off0 ((-2) * arrowSize)
  arrowFromLocal (t-off0) off1 0
  (x0,y0) <- coordsFromOffset t        off0
  (x1,y1) <- coordsFromOffset (t-off0) off1
  liftRender $ do
    setLineWidth timeLineWidth
    setColourRed
    moveTo x0 y0
    lineTo x1 y1
    stroke

drawGrid :: Double -> TimeLineGraph ()
drawGrid spacing = do
  (x0,y0) <- coordsFromOffset 0 0
  ((xMin, yMin), _, (xMax, yMax)) <- getBounds
  liftRender $ do
    setLineWidth 1
    setSourceRGB 0.9 0.9 0.9
    let vLine x = moveTo x yMin >> lineTo x yMax >> stroke
        hLine y = moveTo xMin y >> lineTo xMax y >> stroke
    mapM_ vLine $ takeWhile (<= xMax) $ map (\i -> x0 + i * spacing) [0..]
    mapM_ vLine $ takeWhile (>= xMin) $ map (\i -> x0 - i * spacing) [0..]
    mapM_ hLine $ takeWhile (<= yMax) $ map (\i -> y0 + i * spacing) [0..]
    mapM_ hLine $ takeWhile (>= yMin) $ map (\i -> y0 - i * spacing) [0..]

main :: IO ()
main = do

    drawDiagram "../../assets/2018-08-timezone-diagrams/01-utc.png" 400 400 0 $ do
      drawGrid 25
      drawConstantOffset 0
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/02-utc-4.png" 400 250 (-50) $ do
      drawGrid 25
      drawUTC
      drawConstantOffset (-100)
      drawOffset 0 (-100) 0
      (_, (xc,yc), _) <- getBounds
      liftRender $ do
        setColourRed
        pangoLayout <- createLayout "4h"
        liftIO $ do
          fontDescription <- fontDescriptionFromString "Sans 8"
          layoutSetFontDescription pangoLayout $ Just fontDescription
        PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
        moveTo (xc + 2) (yc - (y1-y0)/2.0 - 4)
        showLayout pangoLayout
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/03-clocks-go-forwards.png" 400 350 0 $ do
      drawGrid 25
      drawAxes
      drawBeforeTransition 0 50
      drawAfterTransition 0 (-50)

    drawDiagram "../../assets/2018-08-timezone-diagrams/04-clocks-go-backwards.png" 400 250 0 $ do
      drawGrid 25
      drawAxes
      drawBeforeTransition 0 (-50)
      drawAfterTransition 0 50

    drawDiagram "../../assets/2018-08-timezone-diagrams/05-utc-to-local-well-defined.png" 400 250 0 $ do
      drawGrid 25
      drawConversion 40 50
      arrowFromUTC 40 50 40
      arrowToLocal 40 50 40
      drawAxes
      drawBeforeTransition 0 (-50)
      drawAfterTransition 0 50

    drawDiagram "../../assets/2018-08-timezone-diagrams/06-local-to-utc-well-defined.png" 400 250 0 $ do
      drawGrid 25
      drawConversion 120 50
      arrowToUTC 120 50 40
      arrowFromLocal 120 50 40
      drawConversion (-105) (-50)
      arrowToUTC (-105) (-50) 20
      arrowFromLocal (-105) (-50) 40
      drawAxes
      drawBeforeTransition 0 (-50)
      drawAfterTransition 0 50

    drawDiagram "../../assets/2018-08-timezone-diagrams/07-local-to-utc-ambiguous.png" 400 250 0 $ do
      drawGrid 25
      drawConversion 60 50
      drawConversion (60-100) (-50)
      arrowToUTC 60 50 40
      arrowToUTC (60-100) (-50) 40
      arrowFromLocal (60-100) (-50) 40
      drawAxes
      drawBeforeTransition 0 (-50)
      drawAfterTransition 0 50

    drawDiagram "../../assets/2018-08-timezone-diagrams/08-local-to-utc-missing.png" 400 350 0 $ do
      drawGrid 25

      do  (x,y) <- coordsFromOffset 0 15
          ((xMin, _), _, (xMax, _)) <- getBounds
          liftRender $ do
            setLineCap LineCapSquare
            setLineWidth timeLineWidth
            setColourRed
            moveTo xMin y
            lineTo x y
            stroke
            moveTo x y
            lineTo xMax y
            setDash [5,5] 5
            stroke
          arrowFromLocal 0 15 40

      drawAxes
      drawBeforeTransition 0 50
      drawAfterTransition 0 (-50)

    drawDiagram "../../assets/2018-08-timezone-diagrams/09-lines-45-degrees.png" 400 250 0 $ do
      drawGrid 25
      let drawGradient t off = do
            (x,y) <- coordsFromOffset t off
            let x' = x-50
                y' = y+50
            liftRender $ do
              setLineWidth timeLineWidth
              setSourceRGB 0.7 0.7 0.7
              moveTo x y
              lineTo x y'
              lineTo x' y'
              stroke
              arc x' y' 20 (-pi/4) 0
              stroke

      drawGradient (-75) (-50)
      drawGradient 125 50
      drawAxes
      drawBeforeTransition 0 (-50)
      drawAfterTransition 0 50

    drawDiagram "../../assets/2018-08-timezone-diagrams/10-inclusive-exclusive.png" 400 250 0 $ do
      drawGrid 25
      drawConversion 0 50
      arrowFromUTC 0 50 20
      arrowToLocal 0 50 40
      drawConversion 100 50
      arrowFromLocal 100 50 140
      arrowToUTC 100 50 40

      drawBeforeTransition 0 (-50)
      drawAfterTransition 0 50
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/11-offset-is-vertical.png" 400 250 (-50) $ do
      drawGrid 25
      drawOffset 75 (-50) 0
      drawOffset (-25) (-100) 0

      drawBeforeTransition 0 (-100)
      drawAfterTransition 0 (-50)
      drawUTC
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/12-vertical-equals-horizontal-offset.png" 400 250 (-50) $ do
      drawGrid 25
      drawOffset (-25) (-100) 0
      drawHorizOffset (-125) (-100) 0

      drawBeforeTransition 0 (-100)
      drawAfterTransition 0 (-50)
      drawUTC
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/13-vertical-not-equals-horizontal-offset.png" 400 250 (-50) $ do
      drawGrid 25
      drawOffset 25 (-50) 0
      drawHorizOffset (-75) (-100) 0

      drawBeforeTransition 0 (-100)
      drawAfterTransition 0 (-50)
      drawUTC
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/14-interacting-transitions.png" 400 250 0 $ do
      drawGrid 25

      drawConversion (-75) (-75)
      drawConversion 0 0
      drawConversion 75 75
      arrowFromLocal (-75) (-75) 40
      arrowToUTC     (-75) (-75) 40
      arrowToUTC     0 0         40
      arrowToUTC     75 75       40

      drawBeforeTransition (-25) (-75)
      drawAfterTransition 25 75

      (x0, y0) <- coordsFromOffset (-25) 0
      (x1, y1) <- coordsFromOffset   25  0
      liftRender $ do
        setLineCap LineCapSquare
        setLineWidth timeLineWidth
        arc x0 y0 transitionPointRadius 0 (2*pi)
        fillPreserve
        stroke
        moveTo (x0 + transitionPointRadius - timeLineWidth) (y0 - transitionPointRadius + timeLineWidth)
        lineTo (x1 - transitionPointRadius + timeLineWidth) (y1 + transitionPointRadius - timeLineWidth)
        stroke
        arc x1 y1 transitionPointRadius 0 (2*pi)
        stroke

      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/15-eu-simultaneous-transitions.png" 400 250 0 $ do
      drawGrid 25

      ((_, yMin), _, (_, yMax)) <- getBounds
      (x, _) <- coordsFromOffset 0 0
      liftRender $ do
        setLineWidth timeLineWidth
        setSourceRGB 0.5 0.5 0.5
        setDash [5,5] 0
        moveTo x yMin
        lineTo x yMax
        stroke

      local (\c -> c { _tlgcRenderSetup = setColourRed }) $ do
        drawBeforeTransition 0 (-50)
        drawAfterTransition 0 0

      local (\c -> c { _tlgcRenderSetup = setColourBlue }) $ do
        drawBeforeTransition 0 0
        drawAfterTransition 0 50

      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/16-us-local-time-transitions.png" 400 250 0 $ do
      drawGrid 25

      ((xMin, _), _, (xMax, _)) <- getBounds
      (_, y) <- coordsFromOffset (-25) (-50)
      liftRender $ do
        setLineWidth timeLineWidth
        setSourceRGB 0.5 0.5 0.5
        setDash [5,5] 0
        moveTo xMin y
        lineTo xMax y
        stroke

      local (\c -> c { _tlgcRenderSetup = setColourRed }) $ do
        drawBeforeTransition (-25) (-50)
        drawAfterTransition (-25) 0

      local (\c -> c { _tlgcRenderSetup = setColourBlue }) $ do
        drawBeforeTransition 25 0
        drawAfterTransition 25 50

      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/17-offset-size.png" 400 250 (-50) $ do
      drawGrid 25
      drawUTC
      drawConstantOffset (-100)
      drawOffset 0 (-100) 0
      (_, (xc,yc), _) <- getBounds
      liftRender $ do
        setColourRed
        pangoLayout <- createLayout "?"
        liftIO $ do
          fontDescription <- fontDescriptionFromString "Sans 8"
          layoutSetFontDescription pangoLayout $ Just fontDescription
        PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
        moveTo (xc + 2) (yc - (y1-y0)/2.0 - 4)
        showLayout pangoLayout
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/17-offset-size.png" 400 250 (-50) $ do
      drawGrid 25
      drawUTC
      drawOffset 0 (-100) 0
      (_, (xc,yc), _) <- getBounds
      liftRender $ do
        setColourRed
        pangoLayout <- createLayout "?"
        liftIO $ do
          fontDescription <- fontDescriptionFromString "Sans 8"
          layoutSetFontDescription pangoLayout $ Just fontDescription
        PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
        moveTo (xc + 2) (yc - (y1-y0)/2.0 - 4)
        showLayout pangoLayout
      drawConstantOffset (-100)
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/18-transition-size.png" 400 250 (-50) $ do
      drawGrid 25
      drawOffset 0 (-100) 0
      (_, (xc,yc), _) <- getBounds
      liftRender $ do
        setColourRed
        pangoLayout <- createLayout "?"
        liftIO $ do
          fontDescription <- fontDescriptionFromString "Sans 8"
          layoutSetFontDescription pangoLayout $ Just fontDescription
        PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
        moveTo (xc + 2) (yc - (y1-y0)/2.0 - 4)
        showLayout pangoLayout
      drawBeforeTransition 0 (-100)
      drawAfterTransition  0 0
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/19-duplicated-midnight.png" 400 250 (-50) $ do
      drawGrid 25

      ((xMin, _), _, (xMax, _)) <- getBounds
      (_,y) <- coordsFromOffset 0 0
      liftRender $ do
        setLineWidth timeLineWidth
        setSourceRGB 0.7 0.7 0.7
        setDash [5,5] 0
        moveTo xMin y
        lineTo xMax y
        stroke

      liftRender $ do
        pangoLayout <- createLayout "00:00"
        liftIO $ do
          fontDescription <- fontDescriptionFromString "Sans 8"
          layoutSetFontDescription pangoLayout $ Just fontDescription
        PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
        moveTo (xMin + 2) (y - 6 - (y1 - y0))
        showLayout pangoLayout

      drawConversion 0 0
      drawConversion (-100) (-100)

      arrowFromLocal 0 0 40
      arrowToUTC     0 0 20
      arrowToUTC     (-100) (-100) 20

      drawBeforeTransition 0 (-100)
      drawAfterTransition  0 0
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/20-overlapping-days.png" 400 250 50 $ do
      drawGrid 25

      ((xMin, _), _, (xMax, _)) <- getBounds
      (_,y) <- coordsFromOffset 0 0
      liftRender $ do
        setLineWidth timeLineWidth
        setSourceRGB 0.7 0.7 0.7
        setDash [5,5] 0
        moveTo xMin y
        lineTo xMax y
        stroke

      liftRender $ do
        pangoLayout <- createLayout "00:00"
        liftIO $ do
          fontDescription <- fontDescriptionFromString "Sans 8"
          layoutSetFontDescription pangoLayout $ Just fontDescription
        PangoRectangle x0 y0 x1 y1 <- liftIO $ fst <$> layoutGetExtents pangoLayout
        moveTo (xMin + 2) (y - 6 - (y1 - y0))
        showLayout pangoLayout

      drawConversion 0 0
      drawConversion (-100) (-100)

      arrowFromLocal 0 0 40
      arrowToUTC     0 0 20
      arrowToUTC     (-100) (-100) 20

      drawBeforeTransition (-90) (-100)
      drawAfterTransition  (-90) 0
      drawAxes
