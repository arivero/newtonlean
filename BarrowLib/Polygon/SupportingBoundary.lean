import BarrowLib.Polygon.SupportingTangents
import BarrowLib.Polygon.CurveTrace

/-! Closed boundaries joined along the two supporting lines of each finite
monotone cell. Their enclosure is derived from the line data. Shrinking
maximum cell spans, a given curve's uniform modulus and uniform convergence
of the finite nodes then give a two-sided boundary limit. No tangent
existence, derivative identification, arclength or scalar area limit is a
consequence of this statement. -/

namespace NewtonLimitDynamics.Polygon.SupportingBoundary
open NewtonLimitDynamics TimeSubdivision PositionValues CauchyValues CompletionGeometry
open ConvexCover CurveTrace SupportingTangents FiniteEstimates PointBounds
open BinaryTime HarmonicTimeRealization HarmonicDyadic HarmonicBinaryPrefix DyadicNodes

/-- Use the joined finite segments. With coincident lines the possible finite
meetings give the same chord; an arbitrary point of the infinite common line
is not a polygon vertex. Both segments include all their completed points. -/
def cellTrace (p q : Point) (c : Cell p q) (x : PositionValue) : Prop :=
  ∃ r : Point, Meeting p q c r ∧
    (ClosedChord (embedPosition p) (embedPosition r) x ∨
      ClosedChord (embedPosition r) (embedPosition q) x)

def supportingTrace (points : Nat → Point) (cells : ∀ k, Cell (points k) (points (k+1)))
    (n : Nat) (x : PositionValue) : Prop :=
  ∃ k, k<n ∧ cellTrace (points k) (points (k+1)) (cells k) x

/-- The entire closed joined boundary inherits the endpoint rectangle's
distance bound; neither segment enclosure is a premise. -/
theorem cellTrace_bound (p q : Point) (c : Cell p q) (x : PositionValue)
    (hx : cellTrace p q c x) :
    Within x.val (embedPosition p).val (pointDistance q p) := by
  obtain ⟨r,hr,hx⟩ := hx
  have hb := rectangle_distance_bound p r q (meeting_rectangle p q c r hr)
  have hq : Within (embedPosition q).val (embedPosition p).val (pointDistance q p) :=
    (within_embedPosition_iff _ _ _).mpr (Fraction.magnitudes.le_refl _)
  have hR := pointNorm_nonnegative (pointSub q p)
  have hp : Within (embedPosition p).val (embedPosition p).val (pointDistance q p) :=
    within_mono _ _ _ _
      (by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hR)
      ((within_zero_iff _ _).mpr rfl)
  have hj := (within_embedPosition_iff r p _).mpr hb
  rcases hx with hx | hx
  · exact closedChord_ball _ _ x _ _ hp hj hx
  · exact closedChord_ball _ _ x _ _ hj hq hx

theorem supportingTrace_node (points : Nat → Point)
    (cells : ∀ k, Cell (points k) (points (k+1))) (n : Nat) (hn : 0<n)
    (k : Nat) (hk : k≤n) : supportingTrace points cells n (embedPosition (points k)) := by
  by_cases hkn : k<n
  · obtain ⟨r,hr⟩ := meeting_exists _ _ (cells k)
    refine ⟨k,hkn,r,hr,Or.inl (closure_contains _ _ ?_)⟩
    refine ⟨Fraction.ofInt 0,by constructor <;> decide,?_⟩
    exact (ConvexValues.convexPosition_zero (by constructor <;> decide) _ _).symm
  · have he : n-1+1=k := by omega
    obtain ⟨r,hr⟩ := meeting_exists _ _ (cells (n-1))
    refine ⟨n-1,by omega,r,hr,Or.inr (closure_contains _ _ ?_)⟩
    rw [he]
    refine ⟨Fraction.ofInt 1,by constructor <;> decide,?_⟩
    exact (ConvexValues.convexPosition_one (by constructor <;> decide) _ _).symm

/-- A given curve, finite supporting-line data, and shrinking time cells.
Node convergence is explicitly separate from line support; the desired
whole-boundary convergence is derived. Unequal cells and final nodes count. -/
theorem supportingTrace_limit (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (nodes : Nat → Nat → BinaryTime T hT) (count : Nat → Nat) (mesh : Nat → Fraction)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, Cell (points m k) (points m (k+1)))
    (hn : ∀ m, 0<count m)
    (hadj : ∀ m k, k<count m → TimeWithin T hT (nodes m k) (nodes m (k+1)) (mesh m))
    (hcover : ∀ m t, ∃ k, k≤count m ∧ TimeWithin T hT t (nodes m k) (mesh m))
    (hmesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m → Fraction.le (mesh m) delta)
    (hpoints : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ k, k≤count m → Within (embedPosition (points m k)).val (f (nodes m k)).val eps) :
    BoundaryLimit (fun m => supportingTrace (points m) (cells m) (count m)) (ImageTrace f) := by
  intro eps heps
  let e := eps.half.half
  have he : 0<e.num := heps
  obtain ⟨delta,hd,hc⟩ := hf e he
  obtain ⟨N,hN⟩ := hmesh delta hd
  obtain ⟨M,hM⟩ := hpoints e he
  refine ⟨max N M,?_⟩
  intro m hm
  have hmesh' := hN m (Nat.le_trans (Nat.le_max_left _ _) hm)
  have hp := hM m (Nat.le_trans (Nat.le_max_right _ _) hm)
  have hfour : Fraction.equiv (Fraction.add (Fraction.add (Fraction.add e e) e) e) eps :=
    Fraction.equiv_trans (Fraction.add_assoc (Fraction.add e e) e e)
      (Fraction.equiv_trans (Fraction.add_equiv (Fraction.half_add_self eps.half)
        (Fraction.half_add_self eps.half)) (Fraction.half_add_self eps))
  constructor
  · intro x hx
    obtain ⟨k,hk,hx⟩ := hx
    have hq : Within (embedPosition (points m (k+1))).val
        (embedPosition (points m k)).val (Fraction.add (Fraction.add e e) e) :=
      within_triangle _ _ _ _ _
        (within_triangle _ _ _ _ _ (hp (k+1) (by omega))
          (within_symm _ _ _ (hc _ _ (within_mono _ _ _ _ hmesh' (hadj m k hk)))))
        (within_symm _ _ _ (hp k (by omega)))
    have hb := (within_embedPosition_iff _ _ _).mp hq
    refine ⟨f (nodes m k),⟨nodes m k,rfl⟩,?_⟩
    exact within_mono _ _ _ _ (Fraction.le_of_equiv hfour)
      (within_triangle _ _ _ _ _ (within_mono _ _ _ _ hb
        (cellTrace_bound _ _ (cells m k) x hx)) (hp k (by omega)))
  · intro x hx
    obtain ⟨t,ht⟩ := hx
    obtain ⟨k,hk,hkt⟩ := hcover m t
    refine ⟨embedPosition (points m k),supportingTrace_node _ _ _ (hn m) k hk,?_⟩
    rw [←ht]
    have hsmall : Fraction.le (Fraction.add e e) eps :=
      Fraction.le_equiv_left (Fraction.half_add_self eps.half)
        (Fraction.magnitudes.lt_implies_le (Fraction.half_lt eps heps))
    exact within_mono _ _ _ _ hsmall
      (within_triangle _ _ _ _ _ (hc t (nodes m k) (within_mono _ _ _ _ hmesh' hkt))
        (within_symm _ _ _ (hp k hk)))

/-- Actual dyadic time cells supply their own spans and coverage. Only the
given geometric line data and convergence of their finite endpoint samples
remain premises. -/
theorem dyadic_supportingTrace_limit (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ k, k≤blocks m → Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => supportingTrace (points m) (cells m) (blocks m)) (ImageTrace f) := by
  apply supportingTrace_limit T hT f hf (nodeTime T hT) blocks (duration T) points cells
  · intro m; unfold blocks; exact Nat.pow_pos (by decide)
  · exact fun m k hk => adjacent_node_time_within T hT m k hk
  · intro m t
    induction t using Quotient.inductionOn with
    | _ b => exact ⟨ticks b m,ticks_le_blocks b m,
        within_symm _ _ _ (truncation_time_within b T hT m)⟩
  · intro delta hd
    obtain ⟨N,hN⟩ := duration_eventually_small T delta hT hd
    exact ⟨N,fun m hm => Fraction.magnitudes.lt_implies_le (hN m hm)⟩
  · exact hpoints

end NewtonLimitDynamics.Polygon.SupportingBoundary
