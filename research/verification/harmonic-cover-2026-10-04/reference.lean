import Std

/- Standalone common-denominator integer implementation only. All four state
   coordinates share a positive integer denominator. For duration p/q and
   field a(x)=-w*x, drift is followed by the impulse at the arrival point. -/
structure HState where
  den : Int
  x1 : Int
  x2 : Int
  v1 : Int
  v2 : Int
  deriving Repr

def absInt (z : Int) : Int := z.natAbs

def harmonicStep (p q wNum wDen : Int) (s : HState) : HState :=
  let X1 := q * s.x1 + p * s.v1
  let X2 := q * s.x2 + p * s.v2
  { den := s.den * q * q * wDen
    x1 := X1 * q * wDen
    x2 := X2 * q * wDen
    v1 := q * q * wDen * s.v1 - p * wNum * X1
    v2 := q * q * wDen * s.v2 - p * wNum * X2 }

def iterate (p q wNum wDen : Int) : Nat → HState → HState
  | 0, s => s
  | k + 1, s => iterate p q wNum wDen k (harmonicStep p q wNum wDen s)

def trace (p q wNum wDen : Int) : Nat → HState → List HState
  | 0, s => [s]
  | k + 1, s => s :: trace p q wNum wDen k (harmonicStep p q wNum wDen s)

-- New signed, nontrivial, multi-block input, selected before comparison.
-- w=-2/3, h=1/24, n=2; x=(-2/5,3/7), v=(4/9,-5/8).
-- The common initial denominator is 2520.
def initial : HState := ⟨2520, -1008, 1080, 1120, -1575⟩
def coarse2 : HState := iterate 1 12 (-2) 3 2 initial
def fine4 : HState := iterate 1 24 (-2) 3 4 initial

def stateErrorNumerator (c f : HState) : Int :=
  absInt (c.x1 * f.den - f.x1 * c.den) +
  absInt (c.x2 * f.den - f.x2 * c.den) +
  absInt (c.v1 * f.den - f.v1 * c.den) +
  absInt (c.v2 * f.den - f.v2 * c.den)
def stateErrorDenominator (c f : HState) : Int := c.den * f.den

def PairRat := Int × Int
def mulPair (a b : PairRat) : PairRat := (a.1 * b.1, a.2 * b.2)
def addPair (a b : PairRat) : PairRat := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)
def coverRadius : PairRat :=
  mulPair (mulPair (1, 24) (4783, 2520))
    (addPair (4, 1) (mulPair (3, 1) (mulPair (4, 24) (2, 3))))
def coverBudget : PairRat := mulPair (8, 1) (mulPair coverRadius coverRadius)

theorem small_time_sanity : (2 * (4 * 5) : Int) ≤ 24 * 3 := by decide
theorem radius_denominator_positive : coverRadius.2 > 0 := by decide
theorem budget_denominator_positive : coverBudget.2 > 0 := by decide

-- Each fineAt block is represented by two consecutive entries in this trace.
#eval trace 1 12 (-2) 3 2 initial
#eval trace 1 24 (-2) 3 4 initial
#eval (stateErrorNumerator coarse2 fine4, stateErrorDenominator coarse2 fine4)
#eval coverRadius
#eval coverBudget
#eval (2 * (4 * 5), 24 * 3)
