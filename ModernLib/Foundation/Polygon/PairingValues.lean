import ModernLib.Foundation.Polygon.SecantValues
import ModernLib.Foundation.Polygon.BinaryTime
import BarrowLib.Polygon.TriangleBounds
import ModernLib.Foundation.Polygon.SampledValues

/-! Dot products and determinants of completed positions, with one shared
Cauchy and representative-independence proof. Finite bilinear differences
and magnitude bounds are the input; bounded Cauchy tails are derived.
SampledValues covers globally Lipschitz maps, whereas these pairings are
Lipschitz only on bounded sets. No integral or derivative is a primitive. -/

namespace NewtonLimitDynamics.Polygon.PairingValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates HarmonicTimeComparison HarmonicStability
open HarmonicComparison HarmonicAccumulation
open CauchyValues HarmonicDyadic BinaryTime SecantValues HarmonicTimeRealization

/-- The finite identities needed to complete a scalar pairing. -/
structure Form where
  apply : Point → Point → Fraction
  difference_identity : ∀ p q r s,
    Fraction.equiv (durationDifference (apply p q) (apply r s))
      (Fraction.add (apply (pointSub r p) q) (apply r (pointSub s q)))
  magnitude_bound : ∀ p q,
    Fraction.le (apply p q).abs (Fraction.mul (pointNorm p) (pointNorm q))

theorem dot_abs_le_product (p q : Point) :
    Fraction.le (dot p q).abs (Fraction.mul (pointNorm p) (pointNorm q)) := by
  let cross := Fraction.add (Fraction.mul p.1.abs q.2.abs) (Fraction.mul p.2.abs q.1.abs)
  have hb := Fraction.le_equiv_right (Fraction.abs_add_le (Fraction.mul p.1 q.1) (Fraction.mul p.2 q.2))
    (Fraction.add_equiv (Fraction.abs_mul _ _) (Fraction.abs_mul _ _))
  have hc : 0 ≤ cross.num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _))
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _))
  apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hb (Fraction.le_add_nonnegative _ cross hc))
  simp only [cross,pointNorm,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

theorem dot_congr {p p' q q' : Point} (hp : pointEquiv p p') (hq : pointEquiv q q') :
    Fraction.equiv (dot p q) (dot p' q') :=
  Fraction.add_equiv (Fraction.mul_equiv hp.1 hq.1) (Fraction.mul_equiv hp.2 hq.2)

def dotForm : Form where
  apply := dot
  difference_identity := by
    intro p q r s
    simp only [dot,durationDifference,HarmonicStability.negF,pointSub,pointNeg,pointAdd,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf <;> omega
  magnitude_bound := dot_abs_le_product

def detForm : Form where
  apply := det
  difference_identity := by
    intro p q r s
    simp only [det,durationDifference,HarmonicStability.negF,pointSub,pointNeg,pointAdd,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf <;> omega
  magnitude_bound := TriangleBounds.det_abs_le_product

theorem difference_bound (f : Form) (p q r s : Point) :
    Fraction.le (durationDifference (f.apply p q) (f.apply r s)).abs
      (Fraction.add (Fraction.mul (pointDistance p r) (pointNorm q))
        (Fraction.mul (pointNorm r) (pointDistance q s))) := by
  have hb := Fraction.magnitudes.le_trans (Fraction.abs_add_le _ _)
    (Fraction.add_le_add (f.magnitude_bound (pointSub r p) q)
      (f.magnitude_bound r (pointSub s q)))
  exact Fraction.le_equiv_right (Fraction.le_equiv_left (Fraction.abs_equiv (f.difference_identity p q r s)) hb)
    (Fraction.add_equiv
      (Fraction.mul_equiv (pointDistance_symm r p) (Fraction.equiv_refl _))
      (Fraction.mul_equiv (Fraction.equiv_refl _) (pointDistance_symm s q)))

def pairingState (f : Form) (s t : Point × Point) : Point × Point :=
  scalarState (f.apply s.1 t.1)

theorem pairing_state_bound (f : Form) (R : Fraction) (hR : 0 ≤ R.num)
    (s t u v : Point × Point)
    (hu : Fraction.le (pointNorm u.1) R) (ht : Fraction.le (pointNorm t.1) R) :
    Fraction.le (distance (pairingState f s t) (pairingState f u v))
      (Fraction.mul (Fraction.add (distance s u) (distance t v)) R) := by
  have h1 := Fraction.mul_le_mul_nonnegative_left ht (pointDistance s.1 u.1) (pointNorm_nonnegative _)
  have h2 := Fraction.mul_le_mul_nonnegative hu (pointDistance t.1 v.1) (pointNorm_nonnegative _)
  have h3 := Fraction.mul_le_mul_nonnegative (point_le_state (stateSub s u)) R hR
  have h4 := Fraction.mul_le_mul_nonnegative (point_le_state (stateSub t v)) R hR
  have hb := Fraction.magnitudes.le_trans (difference_bound f s.1 t.1 u.1 v.1)
    (Fraction.add_le_add h1 (Fraction.le_equiv_right h2 (Fraction.mul_comm _ _)))
  exact Fraction.le_equiv_left (Fraction.equiv_trans (stateSub_norm_symm _ _)
    (scalarState_distance _ _))
    (Fraction.le_equiv_right (Fraction.magnitudes.le_trans hb (Fraction.add_le_add h3 h4))
      (Fraction.equiv_symm (Fraction.add_mul _ _ _)))

def pairingOperation (f : Form) : BinaryLift.Operation where
  apply := pairingState f
  coefficient := id
  coefficient_nonnegative := fun _ hR => hR
  distance_bound := pairing_state_bound f

theorem fixed_left_bound (f : Form) (s t u : Point × Point) :
    Fraction.le (distance (pairingState f s t) (pairingState f s u))
      (Fraction.mul (distance t u) (pointNorm s.1)) := by
  have hb := difference_bound f s.1 t.1 s.1 u.1
  have hz : Fraction.equiv
      (Fraction.add (Fraction.mul (pointDistance s.1 s.1) (pointNorm t.1))
        (Fraction.mul (pointNorm s.1) (pointDistance t.1 u.1)))
      (Fraction.mul (pointDistance t.1 u.1) (pointNorm s.1)) := by
    apply Fraction.equiv_trans (Fraction.add_equiv
      (Fraction.mul_equiv (pointDistance_self_zero _) (Fraction.equiv_refl _)) (Fraction.equiv_refl _))
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,Int.one_mul,Int.mul_one]
    ac_nf
  exact Fraction.le_equiv_left (Fraction.equiv_trans (stateSub_norm_symm _ _) (scalarState_distance _ _))
    (Fraction.magnitudes.le_trans (Fraction.le_equiv_right hb hz)
      (Fraction.mul_le_mul_nonnegative (point_le_state (stateSub t u)) (pointNorm s.1)
        (pointNorm_nonnegative _)))

def pairingName (f : Form) (a b : EndpointCauchyName) : EndpointCauchyName :=
  BinaryLift.name (pairingOperation f) a b

theorem pairingName_equiv (f : Form) (a b a' b' : EndpointCauchyName)
    (ha : NameEquiv a a') (hb : NameEquiv b b') :
    NameEquiv (pairingName f a b) (pairingName f a' b') :=
  BinaryLift.name_equiv (pairingOperation f) a b a' b' ha hb

def pairingValue (f : Form) (x y : Value) : Value :=
  BinaryLift.value (pairingOperation f) x y

theorem pairingValue_embed (f : Form) (s t : Point × Point) :
    pairingValue f (embed s) (embed t) = embed (pairingState f s t) := rfl

theorem pairingValue_scalar (f : Form) (x y : Value) :
    PositionValues.firstValue (pairingValue f x y) = pairingValue f x y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => rfl

theorem scaled_pairing_approximant (f : Form) (c : Fraction) (a b : EndpointCauchyName) (j : Nat) :
    stateEquiv ((secantName c (pairingName f a b)
      (constantName (PositionValues.zeroPoint,PositionValues.zeroPoint))).approx j)
      (scalarState (Fraction.mul c (f.apply (a.approx j).1 (b.approx j).1))) := by
  have hzero : PositionValues.zeroPoint=(Fraction.ofInt 0,Fraction.ofInt 0) := rfl
  have hscalar : ∀ q, scalarState q=((q,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)) := fun _ => rfl
  constructor
  · constructor <;>
      simp only [secantName,pairingName,BinaryLift.name,secantOperation,pairingOperation,
        secantState,pointState,pairingState,constantName,
        hscalar,hzero,pointEquiv,pointSub,pointNeg,pointAdd,pointScale,Fraction.equiv,Fraction.add,
        Fraction.mul,Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.neg_zero,Int.add_zero,
        Int.zero_add,Int.mul_one,Int.one_mul]
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

/-- A proved bound on the fixed input tail transfers a completed bound in
the other input. The client supplies actual name estimates, not a bilinear
continuity premise on completed values. -/
theorem pairing_name_bound_right (f : Form) (a b c : EndpointCauchyName)
    (R S : Fraction) (hR : 0 ≤ R.num) (M : Nat)
    (ha : ∀ j, M≤j → Fraction.le (pointNorm (a.approx j).1) R)
    (hbc : NameBound b c S) :
    NameBound (pairingName f a b) (pairingName f a c) (Fraction.mul S R) := by
  have hb := SampledValues.nameBound_affine (pairingName f a b) (pairingName f a c)
    b c R S (Fraction.ofInt 0) hR M (fun j hj => by
      have hlevel := Fraction.magnitudes.le_trans (fixed_left_bound f _ _ _)
        (Fraction.mul_le_mul_nonnegative_left (ha j hj) (distance (b.approx j) (c.approx j))
          (stateNorm_nonnegative _))
      exact Fraction.le_equiv_right hlevel (Fraction.equiv_symm (Fraction.add_zero _))) hbc
  exact nameBound_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.add_zero _)) hb

end NewtonLimitDynamics.Polygon.PairingValues
