/- Historical scope: results after Hypatia and before the Principia.
Earlier classical results belong in ClassicsLib; results after the Principia
belong in ModernLib. Chronology concerns the mathematical result, not the
date of its Lean encoding. Newton's own results remain in their historical
witness files.
Arabic results belong here when their dates fit this window; pre-Principia
Chinese results belong in ClassicsLib under the user's explicit exception.
AI-derived results using only Barrow/Classics mathematics belong here.
Borrowed results must retain their exact original-language source passage;
formalization authorship does not establish discovery or historical dating.

Authorities and provenance: the name BarrowLib specifies the admitted
mathematical layer; it does not attribute all results to Isaac Barrow.
Polygon/SectorFan.lean quotes Euclid, Elements I.41 and the Common Notions
in Greek as background for triangle normalization and finite dissection.
Polygon/TriangleContent.lean states the precise supplied area convention.
These passages do not state the coordinate constructions proved here.
SectorFan, TriangleContent, FanDifference, BoxCoverArea and AreaDomain record
their own English statements and checked project derivations as provenance,
without external exact-result or priority claims. Exact original-language
attributions for other borrowed results remain to be verified individually;
successful compilation alone does not establish that source coverage. -/

import BarrowLib.Common.FiniteGrowth
import BarrowLib.Common.FiniteCrossing
import BarrowLib.Common.Exhaustion
import BarrowLib.Common.Quadratic
import BarrowLib.Common.RationalExhaustion
import BarrowLib.Common.RationalMagnitudes
import BarrowLib.Common.RationalTolerance
import BarrowLib.Common.SimplexExit
import BarrowLib.Common.UltimateScaling
import BarrowLib.Polygon.AccelerationEstimates
import BarrowLib.Polygon.BoundedIteration
import BarrowLib.Polygon.BoxCoverArea
import BarrowLib.Polygon.CalibratedGrowth
import BarrowLib.Polygon.CalibratedRefinement
import BarrowLib.Polygon.ConvexCover
import BarrowLib.Polygon.FilledStrips
import BarrowLib.Polygon.FanRadial
import BarrowLib.Polygon.FanCorridor
import BarrowLib.Polygon.FanDifference
import BarrowLib.Polygon.DyadicArithmetic
import BarrowLib.Polygon.EquivalentDuration
import BarrowLib.Polygon.FiniteAccumulation
import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Polygon.FiniteFactorProducts
import BarrowLib.Polygon.FinitePower
import BarrowLib.Polygon.FiniteRecurrence
import BarrowLib.Polygon.FiniteSequenceGap
import BarrowLib.Polygon.GeometricTail
import BarrowLib.Polygon.IntegerRefinement
import BarrowLib.Polygon.IntegerSchedule
import BarrowLib.Polygon.KinematicEstimates
import BarrowLib.Polygon.LatticeGeometry
import BarrowLib.Polygon.MonotoneRectangles
import BarrowLib.Polygon.MotionSampling
import BarrowLib.Polygon.MotionSectorCover
import BarrowLib.Polygon.MotionCurveCover
import BarrowLib.Polygon.RectangleContent
import BarrowLib.Polygon.SectorFan
import BarrowLib.Polygon.RadialSector
import BarrowLib.Polygon.RadialCollarCover
import BarrowLib.Polygon.RadialTriangleCover
import BarrowLib.Polygon.RationalBoundary
import BarrowLib.Polygon.Parallelogram
import BarrowLib.Polygon.PointAlgebra
import BarrowLib.Polygon.PointBounds
import BarrowLib.Polygon.PolygonFanArea
import BarrowLib.Polygon.QuadraticEstimates
import BarrowLib.Polygon.RationalIntervals
import BarrowLib.Polygon.StateDistance
import BarrowLib.Polygon.SupportingTangents
import BarrowLib.Polygon.TangentContact
import BarrowLib.Polygon.TangentBoundary
import BarrowLib.Polygon.TriangleContent
import BarrowLib.Polygon.AreaDomain
import BarrowLib.Polygon.TangentPolygonArea
import BarrowLib.Polygon.TimeCalibration
import BarrowLib.Polygon.TriangleBounds
import BarrowLib.Polygon.TriangleExchange
import BarrowLib.Polygon.TimeSubdivision
import BarrowLib.Polygon.CentralSchedule
import BarrowLib.Polygon.ZeroForce
import BarrowLib.Polygon.ImpulseComposition
import BarrowLib.Polygon.CommonMotion
