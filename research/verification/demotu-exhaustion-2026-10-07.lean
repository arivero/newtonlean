import NewtonLimitDynamics
import Lean

/-!
Target: reconstruct NATP00090 Theorem 1's unnumbered exhaustion passage
from its own law-driven finite triangle chain. For a given rational-time
state curve satisfying MotionSampling.Conditions and a positive monotone
RadialChart of its full image, prove any assigned swept-sector area equals
T * det(initial position, initial velocity) / 2. Prove the corresponding
comparison for two admissible windows sharing their initial state.

Source: NATP00090.par17, "Sunto jam hæc triangula numero infinita et
infinitè parva, sic, ut singulis temporis momentis singula respondeant
triangula, agente vi centripeta sine intermissione, et constabit propositio."
This conditional coordinate exhaustion is editorial reconstruction. The
source does not state our quadratic remainder, force comparison, finite
bounds, rational chart or partial geometric area convention.

May assume: those explicit mechanical/regularity and geometric premises,
centrality, and the assigned rational area of the actual swept sector.
Must not assume: area proportionality, polygon/sample agreement, shrinking
mesh, or any printed-edition theorem. NATP00089 remains separate. The curve
is given; no trajectory-existence construction is required. Whole-edge
mechanical polygon/curve agreement and its between-region B remain open.

Exact controls: inertial curve x(t)=(1,t), v(t)=(0,1), zero force and
T=1/4 have actual swept-sector area 1/8 under triangle normalization.
A second window T=1/8 has area 1/16. Positive durations and geometry must
be proved, not hidden in an assumed area law. Also test a constant radius
chart with a repeated node and a genuinely unequal-width partition in the
geometric exhaustion interface. Reject an incorrect assigned area using
the derived equality. These controls do not construct general area rules.
-/

/-! Adversarial exact controls for the NATP00090 conditional exhaustion.
The geometric partition includes a collapsed cell and unequal positive widths.
The inertial curve controls below use independently assigned triangle area. -/
namespace DeMotu1684.NATP00090.ExhaustionControls
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision MonotoneRectangles RadialSector HarmonicTimeComparison

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

private def z : Fraction := Fraction.ofInt 0
private def o : Fraction := Fraction.ofInt 1
private def eighth : Fraction := ⟨1, 8, by decide⟩
private def quarter : Fraction := ⟨1, 4, by decide⟩
private def sixteenth : Fraction := ⟨1, 16, by decide⟩
private def g : Fraction → Fraction := fun _ => o

private def uneven : Partition z quarter where
  count := 3
  positive_count := by decide
  nodes := fun n => if n = 0 then z else if n = 1 then z else if n = 2 then sixteenth else quarter
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with h | h | h <;> subst i <;> decide

example : Fraction.equiv (uneven.nodes 0) (uneven.nodes 1) := by decide
example : Fraction.equiv (width uneven 0) z := by decide
example : Fraction.equiv (width uneven 1) sixteenth := by decide
example : Fraction.equiv (width uneven 2) ⟨3, 16, by decide⟩ := by decide
example : ¬ Fraction.equiv (width uneven 1) (width uneven 2) := by decide
example : Fraction.equiv (gap (density g) uneven) z := by decide
example : Fraction.equiv (chordArea g uneven) eighth := by decide
example : Fraction.equiv (Fraction.mul eighth eighth)
    (Fraction.mul sixteenth quarter) := by decide

private def curve (t : Fraction) : Point × Point := ((o, t), (z, o))
private theorem curve_ray (t : Fraction) : pointEquiv (curve t).1 (ray (g t) t) := by
  constructor
  · exact Fraction.equiv_refl _
  · simp only [curve, ray, g, o, Fraction.equiv, Fraction.mul, Fraction.ofInt,
      Int.one_mul, Int.mul_one]
private theorem quarter_sector (x : Point) :
    MotionSampling.sweptSector curve quarter x ↔ sector g z quarter x := by
  constructor
  · rintro ⟨t, ht0, htT, w, hw, hx⟩
    exact ⟨t, ht0, htT, w, hw, pointEquiv_trans hx (pointScale_congr w (curve_ray t))⟩
  · rintro ⟨t, ht0, htT, w, hw, hx⟩
    exact ⟨t, ht0, htT, w, hw,
      pointEquiv_trans hx (pointEquiv_symm (pointScale_congr w (curve_ray t)))⟩
private theorem constant_monotone : MonotoneOn g z quarter :=
  fun _ _ _ _ _ => Fraction.magnitudes.le_refl _
private theorem quarter_area (area : SectorFan.AreaRules) :
    area.HasArea (MotionSampling.sweptSector curve quarter) eighth := by
  have hc := caps_enclosure g z quarter o o (by decide) constant_monotone (by decide)
    (by decide) (Fraction.magnitudes.le_refl _) (Fraction.magnitudes.le_refl _)
  have ht := area.triangle (ray o z) (ray o quarter)
    (ray_orientation _ _ _ _ (by decide) (by decide) (by decide))
  have hs : area.HasArea (sector g z quarter) eighth := area.congr_set _ _ _
    (fun x => ⟨hc.1 x, hc.2 x⟩) (area.congr_value _ _ _ (by decide) ht)
  exact area.congr_set _ _ _ (fun x => (quarter_sector x).symm) hs

example : 0 < quarter.num := by decide
example (area : SectorFan.AreaRules) :
    area.HasArea (MotionSampling.sweptSector curve quarter) eighth := quarter_area area

end DeMotu1684.NATP00090.ExhaustionControls

/-! A second positive-time inertial window has a full radial chart. Its area
exists under the explicit triangle convention; NATP00090's own exhaustion
identifies any assigned swept-sector area. -/
namespace NewtonLimitDynamics.Polygon.DeMotuMotionAreaControls
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates MotionSampling
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization MonotoneRectangles RadialSector

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def two := Fraction.ofInt 2
private def T : Fraction := ⟨1,8,by decide⟩
private def eighth : Fraction := ⟨1,8,by decide⟩
private def force : Point → Point := fun _ => (z,z)
private def curve (t : Fraction) : Point × Point := ((o,t),(z,o))
private def g : Fraction → Fraction := fun _ => o
private def timeAt (j k : Nat) : Fraction := if k=0 then z else countTime T j k
private theorem time_equiv (j k : Nat) : Fraction.equiv (timeAt j k) (countTime T j k) := by
  by_cases h : k=0
  · subst k
    simp only [timeAt,ite_eq_left,z,countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      Int.natCast_zero,Int.zero_mul,Int.mul_zero]
  · simp only [timeAt,ite_eq_right h]; exact Fraction.equiv_refl _
private theorem time_next (j k : Nat) :
    Fraction.equiv (timeAt j (k+1)) (Fraction.add (timeAt j k) (duration T j)) := by
  apply Fraction.equiv_trans (time_equiv j (k+1))
  apply Fraction.equiv_trans (b := Fraction.add (countTime T j k) (duration T j))
  · simp only [countTime,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  · exact Fraction.add_equiv_right _ (Fraction.equiv_symm (time_equiv j k))
private theorem curve_congr {s t : Fraction} (h : Fraction.equiv s t) : stateEquiv (curve s) (curve t) :=
  ⟨⟨Fraction.equiv_refl _,h⟩,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
private theorem curve_cell (t h : Fraction) :
    stateEquiv (curve (Fraction.add t h)) (cell force h (curve t)) := by
  constructor <;> constructor <;>
    simp only [curve,force,cell,pointAdd,pointScale,z,o,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.zero_add,Int.add_zero] <;> ac_nf
private theorem conditions : Conditions force z T z z two o curve := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,by decide,?_,?_,?_⟩
  · intro p r
    exact Fraction.le_of_equiv (Fraction.equiv_trans (pointDistance_self_zero (force p))
      (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.mul_zero _))))
  · intro j k _
    have he : stateEquiv (curve (timeAt j (k+1))) (cell force (duration T j) (curve (timeAt j k))) :=
      ⟨pointEquiv_trans (curve_congr (time_next j k)).1 (curve_cell _ _).1,
        pointEquiv_trans (curve_congr (time_next j k)).2 (curve_cell _ _).2⟩
    have hd : Fraction.equiv (stateDistance (curve (timeAt j (k+1)))
        (cell force (duration T j) (curve (timeAt j k)))) z :=
      Fraction.equiv_trans (Fraction.add_equiv
        (pointDistance_equiv he.1 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
        (pointDistance_equiv he.2 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)) (stateDistance_self_zero _)
    exact Fraction.le_of_equiv (Fraction.equiv_trans hd
      (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.mul_zero _))))
  · intro j k _
    change (0 : Int) ≤ 0
    decide
  · intro j k hk
    have ht : Fraction.le (timeAt j k) T := Fraction.le_equiv_left (time_equiv j k)
      (Fraction.le_equiv_right (BoundedIteration.time_monotone (duration T j) (by change (0 : Int) ≤ 1; decide)
        k (blocks j) (by omega)) (blocks_duration T j))
    have htn : 0 ≤ (timeAt j k).num := Fraction.nonnegative_equiv (time_equiv j k)
      (Fraction.nonnegative_mul _ _ (Int.natCast_nonneg _) (by change (0 : Int) ≤ 1; decide))
    have he : Fraction.equiv (pointNorm (curve (timeAt j k)).1) (Fraction.add o (timeAt j k)) :=
      Fraction.add_equiv (Fraction.abs_of_nonnegative _ (by change (0 : Int) ≤ 1; decide)) (Fraction.abs_of_nonnegative _ htn)
    exact Fraction.le_equiv_left he (Fraction.magnitudes.le_trans (Fraction.add_le_add_left ht o)
      (by change Fraction.le (Fraction.add o T) two; decide))
  · intro j k _
    change (1 : Int) ≤ 1
    decide
private def parts (j : Nat) : Partition z T where
  count := blocks j
  positive_count := by unfold blocks; exact Nat.pow_pos (by decide)
  nodes := countTime T j
  first := by simp only [countTime,z,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_zero,
    Int.zero_mul,Int.mul_zero]
  last := blocks_duration T j
  ordered := by
    intro i _
    simp only [Fraction.le,countTime,Fraction.mul,Fraction.ofInt,Int.natCast_add,Int.natCast_one,
      Int.mul_one,Int.one_mul,duration,T,Int.add_mul,Int.mul_add]
    have hp : 0 < (2 : Int)^j := Int.pow_pos (by decide)
    omega
private theorem curve_ray (t : Fraction) : pointEquiv (curve t).1 (ray (g t) t) := by
  constructor
  · exact Fraction.equiv_refl _
  · simp only [ray,curve,g,o,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
private theorem chart : RadialChart g z T T parts curve where
  monotone := fun _ _ _ _ _ => Fraction.magnitudes.le_refl _
  positive := by decide
  count := fun _ => rfl
  curve_points := fun t ht0 htT => ⟨t,ht0,htT,curve_ray t⟩
  graph_points := fun t ht0 htT => ⟨t,ht0,htT,curve_ray t⟩
  samples := by
    intro j k _
    exact pointEquiv_trans (curve_congr (time_equiv j k)).1 (curve_ray _)
private theorem central : CentralSchedule.central force := by
  intro p
  simp only [force,TimeSubdivision.det,z,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.zero_mul,Int.mul_zero,Int.neg_zero,Int.add_zero]
private theorem actual_area (area : SectorFan.AreaRules) : area.HasArea (sweptSector curve T) T.half := by
  have hc := caps_enclosure g z T o o (by decide) chart.monotone chart.positive
    (by decide) (Fraction.magnitudes.le_refl _) (Fraction.magnitudes.le_refl _)
  have ha := area.triangle (ray o z) (ray o T) (ray_orientation _ _ _ _ (by decide) (by decide) (by decide))
  have hr : area.HasArea (sector g z T) T.half := area.congr_set _ _ _
    (fun x => ⟨hc.1 x,hc.2 x⟩) (area.congr_value _ _ _ (by decide) ha)
  exact area.congr_set _ _ _ (fun x => (charted_sector g z T T parts curve chart x).symm) hr

example : 0 < T.num := by decide
example (area : SectorFan.AreaRules) : area.HasArea (sweptSector curve T) T.half := actual_area area
example (area : SectorFan.AreaRules) (A : Fraction) (hA : area.HasArea (sweptSector curve T) A) :
    Fraction.equiv A T.half :=
  Fraction.equiv_trans (DeMotu1684.NATP00090.AreaLaw.sampled_radial_sector_area area force central
    z T z z two o curve conditions g z T parts chart A hA) (by decide)

example (area : SectorFan.AreaRules) :
    ¬ area.HasArea (sweptSector curve T) eighth := by
  intro hwrong
  have he := DeMotu1684.NATP00090.AreaLaw.sampled_radial_sector_area area force central
    z T z z two o curve conditions g z T parts chart eighth hwrong
  have hn : ¬ Fraction.equiv eighth T.half := by decide
  exact hn (Fraction.equiv_trans he (by decide))

#print axioms DeMotu1684.NATP00090.AreaLaw.sampled_radial_sector_area

example : ∃ N, ∀ j, N ≤ j → ∀ k, k ≤ blocks j →
    0 < (BoundedIteration.run force (duration T j) (curve z) k).1.1.num :=
  polygon_eventually_positive force z T z z two o curve conditions g z T parts chart

example (area : SectorFan.AreaRules) :
    ∃ N, ∀ j, N ≤ j → area.HasArea (SectorFan.Region
      (DeMotu1684.NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd force (duration T j)
        (curve z)) (blocks j)) (Fraction.mul T (CentralSchedule.momentum (curve z))).half :=
  DeMotu1684.NATP00090.AreaLaw.eventual_mechanical_sector_area area force central
    z T z z two o curve conditions (by decide) g z T parts chart

end NewtonLimitDynamics.Polygon.DeMotuMotionAreaControls

/- The witness boundary is checked through compiled types, definitions and
private helpers, rather than inferred from imports or source names alone. -/
namespace DeMotu1684.NATP00090.ExhaustionDependencyControls
open Lean

private partial def reachesPrinted (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Bool :=
  match todo with
  | [] => false
  | name :: rest =>
    if seen.contains name then reachesPrinted env rest seen
    else
      let publicName := ((privateToUserName? name).getD name).toString
      if publicName.startsWith "Principia1687." || publicName.startsWith "Principia1713." then true
      else match env.find? name with
        | none => reachesPrinted env rest (seen.insert name)
        | some info =>
          let uses := info.type.getUsedConstants ++
            ((info.value? true).map Expr.getUsedConstants |>.getD #[])
          reachesPrinted env (uses.toList ++ rest) (seen.insert name)

run_elab do
  let env ← Lean.getEnv
  unless reachesPrinted env [`Principia1687.PropositionI.sampled_radial_sector_area] do
    throwError "printed-edition dependency control failed"
  for root in #[`DeMotu1684.NATP00090.AreaLaw.canonical_fan_law,
      `DeMotu1684.NATP00090.AreaLaw.radial_chord_errors_vanish,
      `DeMotu1684.NATP00090.AreaLaw.sampled_radial_sector_area,
      `DeMotu1684.NATP00090.AreaLaw.sampled_radial_sector_comparison] do
    if reachesPrinted env [root] then
      throwError "{root} reaches a printed-edition declaration"

end DeMotu1684.NATP00090.ExhaustionDependencyControls
