import BarrowLib.Polygon.FanValues
import BarrowLib.Polygon.DyadicNodes

/-! Area swept by a curve, defined intrinsically by triangle fans at its
actual dyadic time nodes. The curve argument is the explicitly given
trajectory: its existence is a premise, not an obligation of this area layer.
Unsigned fans count repeated coverage with
multiplicity; oriented fans keep the signed winding convention. Neither is
the unsigned union content between two paths. No area existence is assumed. -/

namespace NewtonLimitDynamics.Polygon.SweptArea
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeRealization BinaryTime
open CauchyValues PositionValues DyadicNodes SecantValues HarmonicTimeComparison PointBounds

/-- Absolute elapsed time is built from the two completed time names. -/
def intervalElapsedName (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) :
    EndpointCauchyName :=
  FanValues.absoluteName (secantName (Fraction.ofInt 1)
    (BinaryTime.timeName b T hT) (BinaryTime.timeName c T hT))

theorem interval_elapsed_approx (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) :
    stateEquiv ((intervalElapsedName b c T hT).approx m)
      (scalarState (countTime T m (intervalCount b c m))) := by
  have he := interval_count_time_gap T hT (ticks b m) (ticks c m) m
  constructor
  · constructor
    · change Fraction.equiv
        ((Fraction.mul (Fraction.ofInt 1)
          (HarmonicTimeComparison.durationDifference (timeApprox c T m) (timeApprox b T m))).abs)
        (countTime T m (intervalCount b c m))
      exact Fraction.equiv_trans (Fraction.abs_equiv (by
        simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
        ac_nf))
        (Fraction.equiv_trans (durationDifference_abs_symm _ _)
          (Fraction.equiv_symm he))
    · exact Fraction.equiv_refl _
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

def intervalElapsedValue (T : Fraction) (hT : 0 ≤ T.num)
    (t₀ t₁ : BinaryTime T hT) : Value :=
  FanValues.absoluteValue (secantValue (Fraction.ofInt 1)
    (timeCoordinate T hT t₀) (timeCoordinate T hT t₁))

def AreaAt (unsigned : Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue) (t : BinaryTime T hT) (area : Value) : Prop :=
  ∀ b : Nat → Bool, (Quotient.mk _ b : BinaryTime T hT)=t →
    ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N≤m →
      Within (FanValues.halfValue (FanValues.fanValue unsigned
        (fun k => (curve (nodeTime T hT m k)).val) (ticks b m))) area eps

/-- Intrinsic area over either ordering of two binary instants. At every
level the fan consists exactly of the curve-node cells between their ticks. -/
def AreaBetween (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue)
    (t₀ t₁ : BinaryTime T hT) (area : Value) : Prop :=
  ∀ b c : Nat → Bool, (Quotient.mk _ b : BinaryTime T hT)=t₀ →
    (Quotient.mk _ c : BinaryTime T hT)=t₁ →
    ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N≤m →
      Within (FanValues.halfValue (FanValues.intervalValue true
        (fun k => (curve (nodeTime T hT m k)).val)
        (min (ticks b m) (ticks c m))
        (max (ticks b m) (ticks c m)-min (ticks b m) (ticks c m)))) area eps

/-- Proposition I's swept-area target for an existing trajectory. The curve
is given; this proposition must be proved, never included in the trajectory
existence postulate. It asserts actual curve-node fan convergence on every
interval, with proportionality coefficient `abs(ell)/2`. The coefficient
must be identified from the mechanical data in a central-force proof.

This is obligation (A). It says nothing about the nonnegative region between
the curve and an impulse polygon, obligation (B), and does not identify
fan area counted with multiplicity with ordinary sector-union content. -/
def Proportional (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue) (ell : Fraction) : Prop :=
  ∀ t₀ t₁, AreaBetween T hT curve t₀ t₁
    (secantValue ell.abs.half (intervalElapsedValue T hT t₀ t₁)
      (embed FanValues.zeroState))

/-- Equal swept areas in equal times follow from the proportional-area
theorem. Existence of the common area is part of the conclusion, so this
cannot succeed vacuously when no fan limit exists. -/
theorem proportional_equal_times (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue) (ell : Fraction)
    (hlaw : Proportional T hT curve ell)
    (t₀ t₁ u₀ u₁ : BinaryTime T hT)
    (htime : intervalElapsedValue T hT t₀ t₁ = intervalElapsedValue T hT u₀ u₁) :
    ∃ area, AreaBetween T hT curve t₀ t₁ area ∧
      AreaBetween T hT curve u₀ u₁ area := by
  refine ⟨secantValue ell.abs.half (intervalElapsedValue T hT t₀ t₁)
    (embed FanValues.zeroState),hlaw t₀ t₁,?_⟩
  rw [htime]
  exact hlaw u₀ u₁

theorem areaBetween_reverse (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue)
    (t₀ t₁ : BinaryTime T hT) (area : Value)
    (h : AreaBetween T hT curve t₀ t₁ area) :
    AreaBetween T hT curve t₁ t₀ area := by
  intro c b hc hb eps heps
  simpa only [Nat.min_comm,Nat.max_comm] using h b c hb hc eps heps

theorem areaBetween_unique (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue)
    (t₀ t₁ : BinaryTime T hT) (a b : Value)
    (ha : AreaBetween T hT curve t₀ t₁ a)
    (hb : AreaBetween T hT curve t₀ t₁ b) : a=b := by
  have hsmall : ∀ eps : Fraction, 0 < eps.num → Within a b eps := by
    intro eps heps
    induction t₀ using Quotient.inductionOn with
    | _ x =>
      induction t₁ using Quotient.inductionOn with
      | _ y =>
        obtain ⟨N,hN⟩ := ha x y rfl rfl eps.half heps
        obtain ⟨M,hM⟩ := hb x y rfl rfl eps.half heps
        exact within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.half_add_self eps))
          (within_triangle _ _ _ _ _
            (within_symm _ _ _ (hN (max N M) (Nat.le_max_left _ _)))
            (hM (max N M) (Nat.le_max_right _ _)))
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro eps heps
      obtain ⟨N,hN⟩ := hsmall eps.half heps eps.half heps
      exact ⟨N,fun m hm => lt_equiv_right (hN m hm) (Fraction.half_add_self eps)⟩

/-- The actual curve-fan limit determines at most one swept area. Existence
is a separate construction, never a field of this definition. -/
theorem area_unique (unsigned : Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue) (t : BinaryTime T hT) (a b : Value)
    (ha : AreaAt unsigned T hT curve t a) (hb : AreaAt unsigned T hT curve t b) : a=b := by
  have hsmall : ∀ eps : Fraction, 0 < eps.num → Within a b eps := by
    intro eps heps
    induction t using Quotient.inductionOn with
    | _ c =>
      obtain ⟨N,hN⟩ := ha c rfl eps.half heps
      obtain ⟨M,hM⟩ := hb c rfl eps.half heps
      exact within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.half_add_self eps))
        (within_triangle _ _ _ _ _ (within_symm _ _ _ (hN (max N M) (Nat.le_max_left _ _)))
          (hM (max N M) (Nat.le_max_right _ _)))
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro eps heps
      obtain ⟨N,hN⟩ := hsmall eps.half heps eps.half heps
      exact ⟨N,fun m hm => lt_equiv_right (hN m hm) (Fraction.half_add_self eps)⟩

end NewtonLimitDynamics.Polygon.SweptArea
