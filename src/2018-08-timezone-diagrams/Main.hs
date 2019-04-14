{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Data.Time.LocalTime.TimeZone.Diagram

import Control.Monad.Reader (local)
import Graphics.Rendering.Cairo
import Graphics.Rendering.Pango

main :: IO ()
main = do

    drawDiagram "../../assets/2018-08-timezone-diagrams/01-utc.png" 400 400 (Offset 0) $ do
      drawGrid 25
      drawConstantOffset utcOffset
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/02-utc-4.png" 400 250 (Offset (-50)) $ do
      drawGrid 25
      drawUTC
      let offset = Offset (-100)
      drawConstantOffset offset
      drawOffset (UTime 0) offset utcOffset
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

    drawDiagram "../../assets/2018-08-timezone-diagrams/03-clocks-go-forwards.png" 400 350 (Offset 0) $ do
      drawGrid 25
      drawAxes
      let transitionTime = UTime 0
          off0           = Offset 50
          off1           = Offset (-50)
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/04-clocks-go-backwards.png" 400 250 (Offset 0) $ do
      drawGrid 25
      drawAxes
      let transitionTime = UTime 0
          off0           = Offset (-50)
          off1           = Offset 50
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/05-utc-to-local-well-defined.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-50)
          off1           = Offset 50
          convertTime    = UTime 40

      drawConversion convertTime off1
      arrowFromUTC   convertTime off1 40
      arrowToLocal   convertTime off1 40

      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/06-local-to-utc-well-defined.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-50)
          off1           = Offset 50
          convertTime0   = UTime (-105)
          convertTime1   = UTime 120

      drawConversion convertTime1 off1
      arrowFromLocal convertTime1 off1 40
      arrowToUTC     convertTime1 off1 40

      drawConversion convertTime0 off0
      arrowFromLocal convertTime0 off0 40
      arrowToUTC     convertTime0 off0 20

      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/07-local-to-utc-ambiguous.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-50)
          off1           = Offset 50
          convertTime0   = UTime (60-100)
          convertTime1   = UTime 60

      drawConversion convertTime0 off0
      drawConversion convertTime1 off1
      arrowToUTC     convertTime0 off0 40
      arrowToUTC     convertTime1 off1 40
      arrowFromLocal convertTime0 off0 40

      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/08-local-to-utc-missing.png" 400 350 (Offset 0) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset 50
          off1           = Offset (-50)

      do  ((xMin, _), _, (xMax, _)) <- getBounds
          let conversionOffsetAtCentre = Offset 15
          (x,y) <- coordsFromOffset transitionTime conversionOffsetAtCentre
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
          arrowFromLocal transitionTime conversionOffsetAtCentre 40

      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/09-lines-45-degrees.png" 400 250 (Offset 0) $ do
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

      let transitionTime = UTime 0
          off0           = Offset (-50)
          off1           = Offset 50

      drawGradient (UTime (-75)) off0
      drawGradient (UTime 125)   off1

      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/10-inclusive-exclusive.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-50)
          off1           = Offset 50
          conversionTime = UTime 100

      drawConversion transitionTime off1
      arrowFromUTC   transitionTime off1 20
      arrowToLocal   transitionTime off1 40

      drawConversion conversionTime off1
      arrowFromLocal conversionTime off1 140
      arrowToUTC     conversionTime off1  40

      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/11-offset-is-vertical.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-100)
          off1           = Offset (-50)
          offTime0       = UTime (-25)
          offTime1       = UTime 75

      drawOffset offTime0 off0 utcOffset
      drawOffset offTime1 off1 utcOffset

      drawUTC
      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/12-vertical-equals-horizontal-offset.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-100)
          off1           = Offset (-50)
          offTime        = UTime (-25)
          horizOffTime   = UTime (-125)

      drawOffset      offTime      off0 utcOffset
      drawHorizOffset horizOffTime off0 utcOffset

      drawUTC
      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/13-vertical-not-equals-horizontal-offset.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-100)
          off1           = Offset (-50)
          offTime        = UTime (25)
          horizOffTime   = UTime (-75)

      drawOffset      offTime      off1 utcOffset
      drawHorizOffset horizOffTime off0 utcOffset

      drawUTC
      drawAxes
      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1

    drawDiagram "../../assets/2018-08-timezone-diagrams/14-interacting-transitions.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let off0             = Offset (-75)
          off1             = utcOffset
          off2             = Offset   75
          transitionTime01 = UTime  (-25)
          transitionTime12 = UTime    25
          conversionTime0  = UTime  (-75)
          conversionTime1  = UTime     0
          conversionTime2  = UTime    75

      drawConversion conversionTime0 off0
      drawConversion conversionTime1 off1
      drawConversion conversionTime2 off2

      arrowFromLocal conversionTime0 off0 40
      arrowToUTC     conversionTime0 off0 40
      arrowToUTC     conversionTime1 off1 40
      arrowToUTC     conversionTime2 off2 40

      drawBeforeTransition transitionTime01 off0
      drawAfterTransition  transitionTime12 off2

      (x0, y0) <- coordsFromOffset transitionTime01 off1
      (x1, y1) <- coordsFromOffset transitionTime12 off1
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

    drawDiagram "../../assets/2018-08-timezone-diagrams/15-eu-simultaneous-transitions.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime = UTime 0
          zone0Offset0   = Offset (-50)
          zone0Offset1   = Offset    0
          zone1Offset0   = Offset    0
          zone1Offset1   = Offset   50

      ((_, yMin), _, (_, yMax)) <- getBounds
      (x, _) <- coordsFromOffset transitionTime zone0Offset0
      liftRender $ do
        setLineWidth timeLineWidth
        setSourceRGB 0.5 0.5 0.5
        setDash [5,5] 0
        moveTo x yMin
        lineTo x yMax
        stroke

      local (\c -> c { _tlgcRenderSetup = setColourRed }) $ do
        drawBeforeTransition transitionTime zone0Offset0
        drawAfterTransition  transitionTime zone0Offset1

      local (\c -> c { _tlgcRenderSetup = setColourBlue }) $ do
        drawBeforeTransition transitionTime zone1Offset0
        drawAfterTransition  transitionTime zone1Offset1

      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/16-us-local-time-transitions.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime0 = UTime  (-25)
          transitionTime1 = UTime    25
          zone0Offset0    = Offset (-50)
          zone0Offset1    = Offset    0
          zone1Offset0    = Offset    0
          zone1Offset1    = Offset   50

      showLocalTime "02:00" transitionTime0 zone0Offset0

      local (\c -> c { _tlgcRenderSetup = setColourRed }) $ do
        drawBeforeTransition transitionTime0 zone0Offset0
        drawAfterTransition  transitionTime0 zone0Offset1

      local (\c -> c { _tlgcRenderSetup = setColourBlue }) $ do
        drawBeforeTransition transitionTime1 zone1Offset0
        drawAfterTransition  transitionTime1 zone1Offset1

      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/17-offset-size.png" 400 250 (Offset (-50)) $ do
      drawGrid 25
      drawUTC
      let offset = Offset (-100)
      drawOffset (UTime 0) offset utcOffset
      drawConstantOffset offset
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

    drawDiagram "../../assets/2018-08-timezone-diagrams/18-transition-size.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let transitionTime = UTime 0
          off0           = Offset (-100)
          off1           = Offset 0

      drawOffset transitionTime off0 off1

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

      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/19-duplicated-midnight.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let transitionTime    = UTime 0
          off0              = Offset (-100)
          off1              = Offset 0
          dupConversionTime = UTime (-100)

      showLocalTime "00:00" transitionTime off1

      drawConversion transitionTime    off1
      drawConversion dupConversionTime off0

      arrowFromLocal transitionTime    off1 40
      arrowToUTC     transitionTime    off1 20
      arrowToUTC     dupConversionTime off0 20

      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/20-overlapping-days.png" 400 250 (Offset 50) $ do
      drawGrid 25

      let transitionTime    = UTime (-90)
          off0              = Offset (-100)
          off1              = Offset 0
          conversionTime0   = UTime (-100)
          conversionTime1   = UTime 0

      showLocalTime "00:00" conversionTime0 off0

      drawConversion conversionTime1 off1
      drawConversion conversionTime0 off0

      arrowFromLocal conversionTime1 off1 40
      arrowToUTC     conversionTime1 off1 40
      arrowToUTC     conversionTime0 off0 40

      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1
      drawAxes

    drawDiagram "../../assets/2018-08-timezone-diagrams/21-no-midnight.png" 400 250 (Offset 0) $ do
      drawGrid 25

      let transitionTime    = UTime 0
          off0              = Offset 50
          off1              = Offset (-50)

      showLocalTime "00:00" transitionTime utcOffset

      drawBeforeTransition transitionTime off0
      drawAfterTransition  transitionTime off1
      drawAxes

