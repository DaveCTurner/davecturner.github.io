{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main (main) where

import Data.Time.LocalTime.TimeZone.Diagram

import Control.Monad.Reader
import Graphics.Rendering.Cairo
import Graphics.Rendering.Cairo.Matrix (Matrix(..))
import Graphics.Rendering.Pango

roundingArrow :: Offset -> UTime -> UTime -> TimeLineGraph ()
roundingArrow off t0 t1 = do
  (_, y0) <- coordsFromOffset t0 off
  (_, y1) <- coordsFromOffset t1 off
  let yMid = (y0 + y1) / 2.0
  ((x, _), _, _) <- getBounds
  let directedArrowSize = if y0 < y1 then arrowSize else negate arrowSize
  liftRender $ do
    setColourRed
    moveTo x y0
    lineTo x y1
    stroke
    moveTo x (yMid+directedArrowSize)
    lineTo (x+directedArrowSize) (yMid-directedArrowSize)
    lineTo (x-directedArrowSize) (yMid-directedArrowSize)
    fill

drawUTCCircle :: Render () -> UTime -> TimeLineGraph ()
drawUTCCircle setColour t = do
  (x, _) <- coordsFromOffset t utcOffset
  (_, _, (_, y)) <- getBounds
  liftRender $ do
    setColour
    moveTo x y
    arc x y transitionPointRadius 0 (2*pi)
    fillPreserve
    stroke

drawUTCStart :: UTime -> TimeLineGraph ()
drawUTCStart = drawUTCCircle setColourRed

drawUTCEnd :: UTime -> TimeLineGraph ()
drawUTCEnd = drawUTCCircle setColourBlue

drawRoundedLocals :: TimeLineGraph ()
drawRoundedLocals = do
  ((x, yMin), _, (_, yMax)) <- getBounds
  let getY t  = snd <$> coordsFromOffset (UTime t) utcOffset
      spacing = 75

      findStart t = do
        y <- getY t
        if y < yMax then findStart (t - spacing) else return t

      untilEnd t go = do
        y <- getY t
        if yMin + arrowSize < y then do
          when (y < yMax) (go y)
          untilEnd (t + spacing) go
          else return ()

  tStart <- findStart 0
  untilEnd tStart $ \y -> liftRender $ do
    setColourBlue
    moveTo x y
    arc x y transitionPointRadius 0 (2*pi)
    fillPreserve
    stroke

main :: IO ()
main = do

    drawDiagram "../../assets/2019-04-timezone-rounding/01-rounded-local-times.png" 400 250 (Offset (-75)) $ do
      drawGrid 25

      drawConstantOffset (Offset (-80))
      drawAxes
      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/02-rounded-local-times-conversions.png" 400 250 (Offset (-75)) $ do
      drawGrid 25

      let offset = Offset (-80)
          roundeds = [UTime (tLocal - 80) | tLocal <- [0, 75, 150]]

      forM_ roundeds $ \rounded -> do
        drawConversion rounded   offset
        arrowFromLocal rounded   offset 40

      forM_ (drop 1 roundeds) $ \rounded -> do
        arrowToUTC     rounded   offset 40

      drawConstantOffset offset
      drawAxes
      drawRoundedLocals

      mapM_ drawUTCEnd roundeds

    drawDiagram "../../assets/2019-04-timezone-rounding/03-fixed-offset.png" 400 250 (Offset (-75)) $ do
      drawGrid 25

      let offset    = Offset (-80)
          unrounded = UTime 37
          rounded   = UTime (-5)

      drawConversion unrounded   offset
      arrowFromUTC   unrounded   offset 40
      arrowToLocal   unrounded   offset 40

      drawConversion rounded offset
      arrowToUTC     rounded offset 40
      arrowFromLocal rounded offset 40

      drawConstantOffset offset
      drawAxes

      roundingArrow offset unrounded rounded
      drawUTCStart unrounded
      drawUTCEnd   rounded

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/04-clocks-go-back-ok-before-transition.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let offset0          = Offset (-120)
          offset1          = Offset (-18)
          transitionTime   = UTime 0
          unrounded        = UTime (-15)
          roundedInOffset0 = UTime (-45)

      drawConversion unrounded offset0
      arrowFromUTC   unrounded offset0 40
      arrowToLocal   unrounded offset0 40

      drawConversion roundedInOffset0 offset0
      arrowFromLocal roundedInOffset0 offset0 40
      arrowToUTC     roundedInOffset0 offset0 40

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      drawUTCStart unrounded
      drawUTCEnd   roundedInOffset0

      roundingArrow offset0 unrounded roundedInOffset0

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/05-clocks-go-back-ok-after-transition.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let offset0          = Offset (-120)
          offset1          = Offset (-18)
          transitionTime   = UTime 0
          unrounded        = UTime 92
          roundedInOffset1 = UTime 57

      drawConversion unrounded offset1
      arrowFromUTC   unrounded offset1 40
      arrowToLocal   unrounded offset1 40

      drawConversion roundedInOffset1 offset1
      arrowFromLocal roundedInOffset1 offset1 40
      arrowToUTC     roundedInOffset1 offset1 40

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      drawUTCStart unrounded
      drawUTCEnd   roundedInOffset1

      roundingArrow offset1 unrounded roundedInOffset1

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/06-clocks-go-back-needs-rounding-up.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let offset0          = Offset (-120)
          offset1          = Offset (-18)
          transitionTime   = UTime 0
          unrounded        = UTime 40
          roundedInOffset0 = UTime (-45)
          roundedInOffset1 = UTime 57

      drawConversion unrounded   offset1
      arrowFromUTC   unrounded   offset1 40
      arrowToLocal   unrounded   offset1 40

      drawConversion roundedInOffset0   offset0
      arrowFromLocal roundedInOffset0   offset0 40
      arrowToUTC     roundedInOffset0   offset0 40

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset1 unrounded roundedInOffset1
      drawUTCStart unrounded
      drawUTCEnd   roundedInOffset0

      drawRoundedLocals

    drawDiagram "../../assets/2019-04-timezone-rounding/07-clocks-go-back-needs-rounding-up-and-skip.png" 400 250 (Offset (-25)) $ do
      drawGrid 25

      let offset0          = Offset (-110)
          offset1          = Offset 40
          transitionTime   = UTime 0
          unrounded        = UTime 30
          roundedInOffset0 = UTime (-35)
          roundedInOffset1 = UTime 115

      drawConversion unrounded   offset1
      arrowFromUTC   unrounded   offset1 30
      arrowToLocal   unrounded   offset1 40

      drawConversion roundedInOffset0   offset0
      arrowFromLocal roundedInOffset0   offset0 40
      arrowToUTC     roundedInOffset0   offset0 40

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset1 unrounded roundedInOffset1
      drawUTCStart unrounded
      drawUTCEnd   roundedInOffset0

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/08-clocks-go-back-retry-at-transition.png" 400 250 (Offset (-25)) $ do
      drawGrid 25

      let offset0          = Offset (-110)
          offset1          = Offset 40
          transitionTime   = UTime 0
          unrounded        = UTime 30
          roundedInOffset0 = UTime (-35)
          roundedInOffset1 = UTime 115

      arrowFromUTC   unrounded   offset1 30
      arrowToLocal   unrounded   offset1 10

      arrowFromUTC   transitionTime   offset0 40
      arrowToLocal   transitionTime   offset0 40

      drawConversion roundedInOffset0   offset0
      arrowFromLocal roundedInOffset0   offset0 40
      arrowToUTC     roundedInOffset0   offset0 40

      (x0,y0) <- coordsFromOffset unrounded      offset1
      (x1,y1) <- coordsFromOffset transitionTime offset0
      ((xMin, _), _, (_, yMax)) <- getBounds
      liftRender $ do
        setLineCap LineCapSquare
        setLineWidth timeLineWidth
        setColourRed
        moveTo x0   yMax
        lineTo x0   y0
        lineTo x1   y0
        lineTo x1   y1
        lineTo xMin y1
        stroke
        setDash [5,5] 0
        setSourceRGB 0.7 0.7 0.7
        moveTo x1   yMax
        lineTo x1   y0
        lineTo xMin y0
        stroke

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset0 transitionTime roundedInOffset0
      drawUTCStart unrounded
      drawUTCEnd   roundedInOffset0

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/09-clocks-go-back-duplicated-midnight.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let transitionTime    = UTime (-25)
          offset0           = Offset (-135)
          offset1           = Offset (-30)
          conversionTime0   = UTime (-60)
          conversionTime1   = UTime 45
          unrounded         = UTime 65

      showLocalTime "00:00" conversionTime0 offset0

      ((xMin, _), _, (_, yMax)) <- getBounds

      do
        (x, y) <- coordsFromOffset conversionTime1 offset1
        liftRender $ do
          setLineCap LineCapSquare
          setLineWidth timeLineWidth
          setSourceRGB 0.7 0.7 0.7
          setDash [5,5] 0
          moveTo x   y
          lineTo x   yMax
          stroke

      do
        (x0, y0) <- coordsFromOffset unrounded      offset1
        (x1, y1) <- coordsFromOffset transitionTime offset0
        liftRender $ do
          setLineCap LineCapSquare
          setLineWidth timeLineWidth
          setColourRed
          moveTo x0 yMax
          lineTo x0 y0
          lineTo x1 y0
          lineTo x1 y1
          lineTo xMin y1
          stroke

      arrowFromUTC   unrounded       offset1 40
      arrowToLocal   unrounded       offset1 40
      arrowToLocal   transitionTime  offset0 40

      drawConversion conversionTime0 offset0
      arrowFromLocal conversionTime0 offset0 40
      arrowToUTC     conversionTime0 offset0 40

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset0 transitionTime conversionTime0
      drawUTCStart unrounded
      drawUTCEnd conversionTime0
      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/08-clocks-go-forward.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let offset0          = Offset (-23)
          offset1          = Offset (-80)
          unrounded        = UTime 37
          transitionTime   = UTime 15
          roundedInOffset1 = UTime (-5)

      drawConversion unrounded   offset1
      arrowFromUTC   unrounded   offset1 80
      arrowToLocal   unrounded   offset1 40

      do  (_,y) <- coordsFromOffset roundedInOffset1 offset1
          (x,_) <- coordsFromOffset transitionTime   offset1
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
          arrowFromLocal roundedInOffset1 offset1 40

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset1 unrounded roundedInOffset1
      drawUTCStart unrounded

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/09-clocks-go-forward-use-transition.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let offset0          = Offset (-23)
          offset1          = Offset (-80)
          unrounded        = UTime 37
          transitionTime   = UTime 15
          roundedInOffset1 = UTime (-5)
          roundedInOffset0 = UTime (-23)
          effectiveOffset  = Offset (-60)

      drawConversion unrounded   offset1
      arrowFromUTC   unrounded   offset1 40
      arrowToLocal   unrounded   offset1 40

      drawConversion transitionTime effectiveOffset
      arrowFromLocal transitionTime effectiveOffset 40
      arrowToUTC     transitionTime effectiveOffset 70

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset1 unrounded      roundedInOffset1
      drawUTCStart unrounded
      drawUTCEnd   transitionTime

      drawRoundedLocals


    drawDiagram "../../assets/2019-04-timezone-rounding/10-clocks-go-forward-retry-at-transition.png" 400 250 (Offset (-50)) $ do
      drawGrid 25

      let offset0          = Offset (-23)
          offset1          = Offset (-80)
          unrounded        = UTime 37
          transitionTime   = UTime 15
          roundedInOffset0 = UTime (-23)

      do  (x0,y0) <- coordsFromOffset unrounded        offset1
          (x1,y1) <- coordsFromOffset transitionTime   offset0
          ((xMin, _), _, (_, yMax)) <- getBounds
          liftRender $ do
            setLineCap LineCapSquare
            setLineWidth timeLineWidth
            setColourRed
            moveTo x0   yMax
            lineTo x0   y0
            lineTo x1   y0
            lineTo x1   y1
            lineTo xMin y1
            stroke

      drawConversion roundedInOffset0 offset0

      arrowFromUTC   unrounded        offset1 40
      arrowToUTC     transitionTime   offset1 20
      arrowToLocal   transitionTime   offset0 40
      arrowFromLocal roundedInOffset0 offset0 40
      arrowToUTC     roundedInOffset0 offset0 20

      drawBeforeTransition transitionTime offset0
      drawAfterTransition  transitionTime offset1
      drawAxes

      roundingArrow offset0 transitionTime roundedInOffset0
      drawUTCStart unrounded
      drawUTCEnd   roundedInOffset0

      drawRoundedLocals


