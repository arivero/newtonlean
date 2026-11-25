import BarrowLib.Polygon.UniformRadialSector

/-! An exact nonmonotone radial sector (newtonlean issue 3). The chart
`g(θ) = 1 + θ(1-θ)` on `[0,1]` rises from 1 to 5/4 and falls back to 1. For
the uniform `n`-cell partition the chord fan has the exact area
`41/60 - 1/(4n²) + 1/(15n⁴)`, proved from finite power sums with no
quadrature or integration theorem. The chords lie inside the sector, so any
assigned sector area equals 41/60, and the subtraction rule constructs the
area `1/(4n²) - 1/(15n⁴) > 0` of the actual curve/chord difference. The
existence of a sector area remains an explicit hypothesis.

Controls: a falling pair of endpoint scales and a repeated node are enclosed by
the caps, while the one-cell partition with ε = 1/10 fails because its upper
cap has scale 11/10 < 5/4 at θ = 1/2. The statements and proofs are project
derivations of elementary facts (power sums, chords of a concave chart); no
exact external theorem, historical priority or Newton quotation is claimed. -/

namespace NewtonLimitDynamics.Polygon.QuadraticSector
open NewtonLimitDynamics TimeSubdivision ConvexCover SupportingTangents
open MonotoneRectangles HarmonicTimeComparison PolygonFanArea
open RadialSector
open UniformRadialSector

/-! Controls. -/

/-- The quadratic chart `g(θ) = 1 + θ(1 - θ)`, not monotone on `[0,1]`. -/
def quadraticChart (t : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 1) (Fraction.mul t (durationDifference t (Fraction.ofInt 1)))

/-- The one-cell partition of `[0,1]`. -/
def oneCell : Partition (Fraction.ofInt 0) (Fraction.ofInt 1) where
  count := 1
  positive_count := by decide
  nodes := fun i => if i = 0 then Fraction.ofInt 0 else Fraction.ofInt 1
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have : i = 0 := by omega
    subst this
    show Fraction.le (Fraction.ofInt 0) (Fraction.ofInt 1)
    unfold Fraction.le
    decide

/-- Control: the chart rises and falls, `g(0) = g(1) = 1 < 5/4 = g(1/2)`. -/
theorem quadraticChart_values :
    Fraction.equiv (quadraticChart (Fraction.ofInt 0)) (Fraction.ofInt 1) ∧
    Fraction.equiv (quadraticChart (Fraction.ofInt 1)) (Fraction.ofInt 1) ∧
    Fraction.equiv (quadraticChart ⟨1,2,by decide⟩) ⟨5,4,by decide⟩ := by
  decide

/-- Control: the monotone API does not apply to the quadratic chart in either
direction, from the pairs `(1/2, 1)` and `(0, 1/2)`. -/
theorem quadraticChart_not_monotone :
    ¬ MonotoneOn quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1) ∧
    ¬ (∀ x y, Fraction.le (Fraction.ofInt 0) x → Fraction.le x y →
        Fraction.le y (Fraction.ofInt 1) → Fraction.le (quadraticChart y) (quadraticChart x)) := by
  constructor
  · intro h
    have := h ⟨1,2,by decide⟩ (Fraction.ofInt 1) (by unfold Fraction.le; decide)
      (by unfold Fraction.le; decide) (by unfold Fraction.le; decide)
    revert this
    unfold Fraction.le
    decide
  · intro h
    have := h (Fraction.ofInt 0) ⟨1,2,by decide⟩ (by unfold Fraction.le; decide)
      (by unfold Fraction.le; decide) (by unfold Fraction.le; decide)
    revert this
    unfold Fraction.le
    decide

/-- Control: a partition violating the mesh/modulus relation fails to enclose. With one cell
and `ε = 1/10` the upper cap has scale `11/10`, below `g(1/2) = 5/4`. -/
theorem coarse_partition_fails :
    ∃ x, sector quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1) x ∧
      ¬ upperCaps quadraticChart oneCell ⟨1,10,by decide⟩ x := by
  refine ⟨ray ⟨5,4,by decide⟩ ⟨1,2,by decide⟩,?_,?_⟩
  · refine ⟨⟨1,2,by decide⟩,by unfold Fraction.le; decide,by unfold Fraction.le; decide,
      Fraction.ofInt 1,⟨by decide,by decide⟩,?_⟩
    decide
  · rintro ⟨i,hi,u,v,hu,hv,huv,he⟩
    have hi0 : i = 0 := by
      have : i < 1 := hi
      omega
    subst hi0
    have h1 := (Fraction.equiv_iff_toRat _ _).mp he.1
    have huR := (Fraction.nonnegative_iff_toRat u).mp hu
    have hvR := (Fraction.nonnegative_iff_toRat v).mp hv
    have huvR := (Fraction.le_iff_toRat _ _).mp huv
    simp only [ray, pointAdd, pointScale, Fraction.toRat_add, Fraction.toRat_mul,
      Fraction.toRat_ofInt] at h1 huvR
    have hU : (upperScales quadraticChart oneCell ⟨1,10,by decide⟩ 0).toRat = 11/10 := by
      simp [upperScales, quadraticChart, oneCell, Fraction.toRat_add, Fraction.toRat_mul,
        Fraction.toRat_durationDifference, Fraction.toRat_ofInt]
      simp [Fraction.toRat]
      grind
    have h54 : (⟨5,4,by decide⟩ : Fraction).toRat = 5/4 := by simp [Fraction.toRat]
    rw [hU, h54] at h1
    grind

/-- Control: falling endpoint scales. The chord triangle with scales `2` at slope `0` and `1`
at slope `1` lies between the caps of scales `1` and `2`. -/
theorem falling_scales_enclosed :
    (∀ x, SectorFan.Triangle (ray (Fraction.ofInt 1) (Fraction.ofInt 0))
        (ray (Fraction.ofInt 1) (Fraction.ofInt 1)) x →
      SectorFan.Triangle (ray (Fraction.ofInt 2) (Fraction.ofInt 0))
        (ray (Fraction.ofInt 1) (Fraction.ofInt 1)) x) ∧
    (∀ x, SectorFan.Triangle (ray (Fraction.ofInt 2) (Fraction.ofInt 0))
        (ray (Fraction.ofInt 1) (Fraction.ofInt 1)) x →
      SectorFan.Triangle (ray (Fraction.ofInt 2) (Fraction.ofInt 0))
        (ray (Fraction.ofInt 2) (Fraction.ofInt 1)) x) :=
  cap_chord_enclosure_bounds (Fraction.ofInt 1) (Fraction.ofInt 2) (Fraction.ofInt 1)
    (Fraction.ofInt 2) (Fraction.ofInt 0) (Fraction.ofInt 1) (by decide) (by decide) (by decide)
    (by unfold Fraction.le; decide) (by unfold Fraction.le; decide)
    (by unfold Fraction.le; decide) (by unfold Fraction.le; decide)

/-- Control: a partition with a repeated node. The middle cell is degenerate and the finite
enclosure still holds for the constant chart with exact caps. -/
def repeatedNode : Partition (Fraction.ofInt 0) (Fraction.ofInt 1) where
  count := 3
  positive_count := by decide
  nodes := fun i => if i = 0 then Fraction.ofInt 0 else if i ≤ 2 then ⟨1,2,by decide⟩
    else Fraction.ofInt 1
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with h | h | h <;> subst h <;> (unfold Fraction.le; decide)

theorem repeated_node_enclosed :
    Fraction.equiv (width repeatedNode 1) (Fraction.ofInt 0) ∧
    (∀ x, strips repeatedNode (fun _ => Fraction.ofInt 1) repeatedNode.count x ↔
      sector (fun _ => Fraction.ofInt 1) (Fraction.ofInt 0) (Fraction.ofInt 1) x) := by
  refine ⟨by decide,fun x => ?_⟩
  have h := strips_enclosure (fun _ => Fraction.ofInt 1) repeatedNode
    (fun _ => Fraction.ofInt 1) (fun _ => Fraction.ofInt 1) (fun _ _ => by decide)
    (fun _ _ _ => by decide)
    (fun _ _ _ _ _ => ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩)
  exact ⟨h.1 x,h.2.1 x⟩

/-- The uniform partition of `[0,1]` into `n` cells. -/
def uniformPartition (n : Nat) (hn : 0 < n) : Partition (Fraction.ofInt 0) (Fraction.ofInt 1) where
  count := n
  positive_count := hn
  nodes := fun i => ⟨(i : Int), (n : Int), by omega⟩
  first := by simp [Fraction.equiv, Fraction.ofInt]
  last := by simp [Fraction.equiv, Fraction.ofInt]
  ordered := by
    intro i _
    simp only [Fraction.le]
    have h1 : (0 : Int) ≤ (n : Int) := by omega
    have h2 : (i : Int) ≤ ((i + 1 : Nat) : Int) := by omega
    exact Int.mul_le_mul_of_nonneg_right h2 h1

/-- closed form of the partial chord sums -/
def partialArea (k n : Rat) : Rat :=
  (k * (k - 1) * (2 * k - 1) * (3 * k * k - 3 * k - 1) / 30
    + (2 - 2 * n) * (k * k * (k - 1) * (k - 1) / 4)
    + (1 - 3 * n - n * n) * (k * (k - 1) * (2 * k - 1) / 6)
    + (2 * n * n * n - n * n - n) * (k * (k - 1) / 2)
    + (n * n * n * n + n * n * n - n * n) * k) / (2 * n * n * n * n * n)

theorem node_toRat (n : Nat) (hn : 0 < n) (i : Nat) :
    ((uniformPartition n hn).nodes i).toRat = (i : Rat) / (n : Rat) := by
  simp only [uniformPartition, Fraction.toRat]
  norm_cast

theorem chart_toRat (t : Fraction) :
    (quadraticChart t).toRat = 1 + t.toRat * (1 - t.toRat) := by
  simp [quadraticChart, Fraction.toRat_add, Fraction.toRat_mul, Fraction.toRat_durationDifference,
    Fraction.toRat_ofInt]

theorem partial_chord_sum (n : Nat) (hn : 0 < n) : ∀ k : Nat,
    (SectorFan.areaSum (fun i => ray (quadraticChart ((uniformPartition n hn).nodes i))
      ((uniformPartition n hn).nodes i)) k).toRat = partialArea k n
  | 0 => by
      simp only [SectorFan.areaSum, sum, Fraction.toRat_ofInt, partialArea]
      push_cast
      grind
  | k + 1 => by
      have ih := partial_chord_sum n hn k
      simp only [SectorFan.areaSum, sum, Fraction.toRat_add] at ih ⊢
      rw [ih, Fraction.toRat_half, (Fraction.equiv_iff_toRat _ _).mp (ray_det _ _ _ _)]
      simp only [Fraction.toRat_mul, Fraction.toRat_durationDifference, chart_toRat, node_toRat]
      have hnR : (n : Rat) ≠ 0 := by
        have : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
        grind
      simp only [partialArea]
      push_cast
      grind

/-- Exact chord-fan area of the quadratic chart on the uniform `n`-cell partition, cleared of
denominators: `60 n⁴ A_n = 41 n⁴ - 15 n² + 4`, that is `A_n = 41/60 - 1/(4n²) + 1/(15n⁴)`. -/
theorem quadratic_chord_area (n : Nat) (hn : 0 < n) :
    (chordArea quadraticChart (uniformPartition n hn)).toRat * (60 * ((n : Rat) * n * n * n))
      = 41 * ((n : Rat) * n * n * n) - 15 * ((n : Rat) * n) + 4 := by
  have h := partial_chord_sum n hn n
  have hnR : (n : Rat) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
    grind
  simp only [chordArea, uniformPartition] at h ⊢
  generalize (SectorFan.areaSum _ n).toRat = A at h ⊢
  have h2 : (n : Rat) * n ≠ 0 := by
    intro h0; rcases Rat.mul_eq_zero.mp h0 with h | h <;> exact hnR h
  have h4 : (n : Rat) * n * n * n ≠ 0 := by
    intro h0
    rcases Rat.mul_eq_zero.mp h0 with h | h
    · rcases Rat.mul_eq_zero.mp h with h | h
      · exact h2 h
      · exact hnR h
    · exact hnR h
  have h5 : 2 * (n : Rat) * n * n * n * n ≠ 0 := by
    intro h0
    rcases Rat.mul_eq_zero.mp h0 with h | h
    · exact h4 (by grind)
    · exact hnR h
  have hA : A * (2 * (n : Rat) * n * n * n * n) = (n : Rat) * (41 * ((n : Rat) * n * n * n)
      - 15 * ((n : Rat) * n) + 4) / 30 := by
    rw [h, partialArea, Rat.div_mul_cancel h5]
    grind
  have hz : (n : Rat) * (A * (60 * ((n : Rat) * n * n * n))
      - (41 * ((n : Rat) * n * n * n) - 15 * ((n : Rat) * n) + 4)) = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h | h
  · exact absurd h hnR
  · grind

/-- `A_1 = 1/2` and `A_2 = 5/8`. -/
theorem quadratic_chord_area_one_two :
    (chordArea quadraticChart (uniformPartition 1 (by decide))).toRat = 1 / 2 ∧
    (chordArea quadraticChart (uniformPartition 2 (by decide))).toRat = 5 / 8 := by
  have h1 := quadratic_chord_area 1 (by decide)
  have h2 := quadratic_chord_area 2 (by decide)
  constructor <;> grind

/-- A chord triangle of the quadratic chart lies in its sector cell: the chart is concave. -/
theorem quadratic_chord_inside (al be : Fraction)
    (h0 : Fraction.le (Fraction.ofInt 0) al) (hab : Fraction.le al be)
    (h1 : Fraction.le be (Fraction.ofInt 1)) :
    ∀ x, SectorFan.Triangle (ray (quadraticChart al) al) (ray (quadraticChart be) be) x →
      sector quadraticChart al be x := by
  rintro x ⟨u,v,hu,hv,huv,he⟩
  have h0R := (Fraction.le_iff_toRat _ _).mp h0
  have habR := (Fraction.le_iff_toRat _ _).mp hab
  have h1R := (Fraction.le_iff_toRat _ _).mp h1
  have huR := (Fraction.nonnegative_iff_toRat u).mp hu
  have hvR := (Fraction.nonnegative_iff_toRat v).mp hv
  have huvR := (Fraction.le_iff_toRat _ _).mp huv
  have hx1 := (Fraction.equiv_iff_toRat _ _).mp he.1
  have hx2 := (Fraction.equiv_iff_toRat _ _).mp he.2
  simp only [ray, pointAdd, pointScale, Fraction.toRat_add, Fraction.toRat_mul, chart_toRat,
    Fraction.toRat_ofInt] at h0R h1R huvR hx1 hx2
  generalize ha : al.toRat = a at *
  generalize hb : be.toRat = b at *
  generalize u.toRat = p at *
  generalize v.toRat = q at *
  -- scales r, s ≥ 1
  have hr : 1 ≤ 1 + a * (1 - a) := by
    have := Rat.mul_nonneg (show (0:Rat) ≤ a by grind) (show (0:Rat) ≤ 1 - a by grind)
    grind
  have hs : 1 ≤ 1 + b * (1 - b) := by
    have := Rat.mul_nonneg (show (0:Rat) ≤ b by grind) (show (0:Rat) ≤ 1 - b by grind)
    grind
  generalize hrdef : 1 + a * (1 - a) = r at *
  generalize hsdef : 1 + b * (1 - b) = s at *
  obtain ⟨X,hXdef⟩ : ∃ X : Rat, X = p * r + q * s := ⟨_,rfl⟩
  obtain ⟨Y,hYdef⟩ : ∃ Y : Rat, Y = p * (r * a) + q * (s * b) := ⟨_,rfl⟩
  have hpr : 0 ≤ p * r := Rat.mul_nonneg huR (by grind)
  have hqs : 0 ≤ q * s := Rat.mul_nonneg hvR (by grind)
  have hX0 : 0 ≤ X := by grind
  by_cases hXz : X = 0
  · -- the origin
    refine ⟨al,Fraction.magnitudes.le_refl _,hab,Fraction.ofInt 0,⟨by decide,by decide⟩,?_⟩
    have hpr0 : p * r = 0 := by grind
    have hqs0 : q * s = 0 := by grind
    have hp0 : p = 0 := by
      rcases Rat.mul_eq_zero.mp hpr0 with h | h
      · exact h
      · grind
    have hq0 : q = 0 := by
      rcases Rat.mul_eq_zero.mp hqs0 with h | h
      · exact h
      · grind
    constructor
    · apply (Fraction.equiv_iff_toRat _ _).mpr
      simp only [ray, pointScale, Fraction.toRat_mul, Fraction.toRat_ofInt]
      rw [hx1]; grind
    · apply (Fraction.equiv_iff_toRat _ _).mpr
      simp only [ray, pointScale, Fraction.toRat_mul, Fraction.toRat_ofInt]
      rw [hx2]; grind
  · have hXpos : 0 < X := by grind
    obtain ⟨th,hth⟩ : ∃ th : Rat, th * X = Y := ⟨Y / X,Rat.div_mul_cancel hXz⟩
    -- slope bounds
    have hlo : a ≤ th := by
      apply Rat.le_of_mul_le_mul_right (c := X) _ hXpos
      have hn := Rat.mul_nonneg hqs (show (0:Rat) ≤ b - a by grind)
      have hid : Y - a * X = q * s * (b - a) := by grind
      rw [hth]
      grind
    have hhi : th ≤ b := by
      apply Rat.le_of_mul_le_mul_right (c := X) _ hXpos
      have hn := Rat.mul_nonneg hpr (show (0:Rat) ≤ b - a by grind)
      have hid : b * X - Y = p * r * (b - a) := by grind
      rw [hth]
      grind
    -- concavity: X ≤ g(th)
    obtain ⟨G,hGdef⟩ : ∃ G : Rat, G = 1 + th * (1 - th) := ⟨_,rfl⟩
    have hkey : X * (X * X) ≤ G * (X * X) := by
      have hsq : 0 ≤ (r - s) * (r - s) := by
        rcases Rat.le_total (a := 0) (b := r - s) with h | h
        · exact Rat.mul_nonneg h h
        · have := Rat.mul_nonneg (show (0:Rat) ≤ -(r - s) by grind) (show (0:Rat) ≤ -(r - s) by grind)
          grind
      have hbb : 0 ≤ (b - a) * (b - a) := Rat.mul_nonneg (by grind) (by grind)
      have e1 := Rat.mul_nonneg (Rat.mul_nonneg hpr hqs) hbb
      have e2 := Rat.mul_nonneg (Rat.mul_nonneg huR hvR) hsq
      have hrr := Rat.mul_nonneg huR (Rat.mul_nonneg (show (0:Rat) ≤ r by grind) (show (0:Rat) ≤ r by grind))
      have hss := Rat.mul_nonneg hvR (Rat.mul_nonneg (show (0:Rat) ≤ s by grind) (show (0:Rat) ≤ s by grind))
      have e3 := Rat.mul_nonneg (show (0:Rat) ≤ 1 - (p + q) by grind)
        (show (0:Rat) ≤ p * (r * r) + q * (s * s) by grind)
      have e4 := Rat.mul_nonneg hX0 (show (0:Rat) ≤ (1 - (p + q)) * (p * (r * r) + q * (s * s))
          + p * q * ((r - s) * (r - s)) by grind)
      have hG2 : G * (X * X) = X * X + Y * X - Y * Y := by
        have : G * (X * X) = X * X + (th * X) * X - (th * X) * (th * X) := by rw [hGdef]; grind
        rw [this, hth]
      have hid : X * X + Y * X - Y * Y - X * (X * X)
          = X * ((1 - (p + q)) * (p * (r * r) + q * (s * s)) + p * q * ((r - s) * (r - s)))
            + p * r * (q * s) * ((b - a) * (b - a)) := by
        rw [hXdef, hYdef, ← hrdef, ← hsdef]
        grind
      rw [hG2]
      grind
    have hXG : X ≤ G := Rat.le_of_mul_le_mul_right hkey (Rat.mul_pos hXpos hXpos)
    have hGpos : 0 < G := by grind
    have hGz : G ≠ 0 := by grind
    obtain ⟨w,hwG⟩ : ∃ w : Rat, w * G = X := ⟨X / G,Rat.div_mul_cancel hGz⟩
    have hw0 : 0 ≤ w := by
      rcases Rat.le_total (a := 0) (b := w) with h | h
      · exact h
      · have := Rat.mul_le_mul_of_nonneg_right h (show (0:Rat) ≤ G by grind)
        grind
    have hw1 : w ≤ 1 := by
      apply Rat.le_of_mul_le_mul_right (c := G) _ hGpos
      grind
    refine ⟨Fraction.ofRat th,(Fraction.le_iff_toRat _ _).mpr (by rw [Fraction.toRat_ofRat, ha]; exact hlo),
      (Fraction.le_iff_toRat _ _).mpr (by rw [Fraction.toRat_ofRat, hb]; exact hhi),Fraction.ofRat w,
      ⟨(Fraction.nonnegative_iff_toRat _).mpr (by rw [Fraction.toRat_ofRat]; exact hw0),?_⟩,?_⟩
    · have hle : Fraction.le (Fraction.ofRat w) (Fraction.ofInt 1) :=
        (Fraction.le_iff_toRat _ _).mpr (by rw [Fraction.toRat_ofRat, Fraction.toRat_ofInt]; grind)
      simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hle
    · constructor
      · apply (Fraction.equiv_iff_toRat _ _).mpr
        simp only [ray, pointScale, Fraction.toRat_mul, chart_toRat, Fraction.toRat_ofRat]
        rw [hx1]; grind
      · apply (Fraction.equiv_iff_toRat _ _).mpr
        simp only [ray, pointScale, Fraction.toRat_mul, chart_toRat, Fraction.toRat_ofRat]
        rw [hx2]; grind

/-- The chord fan of the quadratic chart lies in its sector, for every partition of `[0,1]`. -/
theorem quadratic_chords_in_sector (p : Partition (Fraction.ofInt 0) (Fraction.ofInt 1)) :
    ∀ x, chordFigure quadraticChart p x →
      sector quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1) x := by
  rintro x ⟨i,hi,hx⟩
  obtain ⟨t,hat,htb,r,hr,he⟩ := quadratic_chord_inside (p.nodes i) (p.nodes (i+1))
    (node_bounds p i (by omega)).1 (p.ordered i hi) (node_bounds p (i+1) (by omega)).2 x hx
  exact ⟨t,Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hat,
    Fraction.magnitudes.le_trans htb (node_bounds p (i+1) (by omega)).2,r,hr,he⟩

/-- Bounds `1 ≤ g ≤ 5/4` on `[0,1]`. -/
theorem quadratic_bounds (t : Fraction) (h0 : Fraction.le (Fraction.ofInt 0) t)
    (h1 : Fraction.le t (Fraction.ofInt 1)) :
    Fraction.le (Fraction.ofInt 1) (quadraticChart t) ∧
    Fraction.le (quadraticChart t) ⟨5,4,by decide⟩ := by
  have h0R := (Fraction.le_iff_toRat _ _).mp h0
  have h1R := (Fraction.le_iff_toRat _ _).mp h1
  simp only [Fraction.toRat_ofInt] at h0R h1R
  have h54 : (⟨5,4,by decide⟩ : Fraction).toRat = 5/4 := by simp [Fraction.toRat]
  constructor
  · apply (Fraction.le_iff_toRat _ _).mpr
    rw [chart_toRat, Fraction.toRat_ofInt]
    have := Rat.mul_nonneg (show (0:Rat) ≤ t.toRat by grind) (show (0:Rat) ≤ 1 - t.toRat by grind)
    grind
  · apply (Fraction.le_iff_toRat _ _).mpr
    rw [chart_toRat, h54]
    have hsq : 0 ≤ (t.toRat - 1/2) * (t.toRat - 1/2) := by
      rcases Rat.le_total (a := 0) (b := t.toRat - 1/2) with h | h
      · exact Rat.mul_nonneg h h
      · have := Rat.mul_nonneg (show (0:Rat) ≤ -(t.toRat - 1/2) by grind)
          (show (0:Rat) ≤ -(t.toRat - 1/2) by grind)
        grind
    grind

/-- The graph of the quadratic chart is uniformly continuous on `[0,1]`, with `δ = ε/3`. -/
theorem quadratic_uniform :
    RationalBoundary.UniformOn (fun t => (t,quadraticChart t)) (Fraction.ofInt 0)
      (Fraction.ofInt 1) := by
  intro eps heps
  have hepsR := (Fraction.positive_iff_toRat eps).mp heps
  refine ⟨Fraction.ofRat (eps.toRat / 3),
    (Fraction.positive_iff_toRat _).mpr (by rw [Fraction.toRat_ofRat]; grind),?_⟩
  intro s t hs0 hs1 ht0 ht1 hd
  have hs0R := (Fraction.le_iff_toRat _ _).mp hs0
  have hs1R := (Fraction.le_iff_toRat _ _).mp hs1
  have ht0R := (Fraction.le_iff_toRat _ _).mp ht0
  have ht1R := (Fraction.le_iff_toRat _ _).mp ht1
  have hdR := (Fraction.le_iff_toRat _ _).mp hd
  simp only [Fraction.toRat_ofInt, Fraction.toRat_abs, Fraction.toRat_durationDifference,
    Fraction.toRat_ofRat] at hs0R hs1R ht0R ht1R hdR
  apply (Fraction.lt_iff_toRat _ _).mpr
  have hneg (x : Fraction) : (⟨-x.num, x.den, x.den_pos⟩ : Fraction).toRat = -x.toRat :=
    Fraction.toRat_negF x
  simp only [FiniteEstimates.pointDistance, PointBounds.pointNorm, pointSub, pointAdd, pointNeg,
    Fraction.toRat_add, Fraction.toRat_abs, hneg, chart_toRat]
  generalize s.toRat = a at *
  generalize t.toRat = b at *
  have hfac : (1 + a * (1 - a)) + -(1 + b * (1 - b)) = (a - b) * (1 - a - b) := by grind
  have hp1 := Rat.mul_nonneg (show (0:Rat) ≤ a by grind) (show (0:Rat) ≤ 1 - a by grind)
  rw [hfac]
  rcases Rat.le_total (a := 0) (b := a - b) with h | h
  · have u1 := Rat.mul_nonneg h (show (0:Rat) ≤ 1 - (1 - a - b) by grind)
    have u2 := Rat.mul_nonneg h (show (0:Rat) ≤ 1 + (1 - a - b) by grind)
    simp only [Rat.abs] at hdR ⊢
    split at hdR <;> split <;> split <;> grind
  · have u1 := Rat.mul_nonneg (show (0:Rat) ≤ -(a - b) by grind) (show (0:Rat) ≤ 1 - (1 - a - b) by grind)
    have u2 := Rat.mul_nonneg (show (0:Rat) ≤ -(a - b) by grind) (show (0:Rat) ≤ 1 + (1 - a - b) by grind)
    simp only [Rat.abs] at hdR ⊢
    split at hdR <;> split <;> split <;> grind

/-- Every cell of the uniform partition has width `1/n`. -/
theorem uniform_maxWidth (n : Nat) (hn : 0 < n) :
    Fraction.le (maxWidth (uniformPartition n hn)) ⟨1,(n : Int),by omega⟩ := by
  apply (maxWidth_bounds _).2
  intro i _
  apply (Fraction.le_iff_toRat _ _).mpr
  simp only [width, Fraction.toRat_durationDifference, node_toRat]
  have hnR : (n : Rat) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
    grind
  have h1 : (⟨1,(n : Int),by omega⟩ : Fraction).toRat = 1 / (n : Rat) := by
    simp only [Fraction.toRat]; norm_cast
  rw [h1]
  push_cast
  grind

/-- Two positive rational tolerances both exceed `1/n` for an explicit `n`. -/
theorem exists_fine (d e : Fraction) (hd : 0 < d.num) (he : 0 < e.num) :
    ∃ n : Nat, ∃ hn : 0 < n, Fraction.lt ⟨1,(n : Int),by omega⟩ d ∧
      Fraction.lt ⟨1,(n : Int),by omega⟩ e := by
  refine ⟨d.den.toNat + e.den.toNat + 1,Nat.succ_pos _,?_,?_⟩
  · have hdd := d.den_pos
    have hed := e.den_pos
    have hcast : ((d.den.toNat + e.den.toNat + 1 : Nat) : Int) = d.den + e.den + 1 := by omega
    show 1 * d.den < d.num * ((d.den.toNat + e.den.toNat + 1 : Nat) : Int)
    rw [hcast]
    have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ d.num by omega)
      (show (0 : Int) ≤ d.den + e.den + 1 by omega)
    omega
  · have hdd := d.den_pos
    have hed := e.den_pos
    have hcast : ((d.den.toNat + e.den.toNat + 1 : Nat) : Int) = d.den + e.den + 1 := by omega
    show 1 * e.den < e.num * ((d.den.toNat + e.den.toNat + 1 : Nat) : Int)
    rw [hcast]
    have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ e.num by omega)
      (show (0 : Int) ≤ d.den + e.den + 1 by omega)
    omega

/-- The chord-fan areas approach `41/60` from below: `41/60 - 1/n ≤ A_n < 41/60`. -/
theorem quadratic_chord_window (n : Nat) (hn : 0 < n) :
    41 / 60 - 1 / (n : Rat) ≤ (chordArea quadraticChart (uniformPartition n hn)).toRat ∧
    (chordArea quadraticChart (uniformPartition n hn)).toRat < 41 / 60 := by
  have h := quadratic_chord_area n hn
  generalize (chordArea quadraticChart (uniformPartition n hn)).toRat = A at h ⊢
  have hN1 : (1 : Rat) ≤ (n : Rat) := by exact_mod_cast hn
  generalize (n : Rat) = N at h hN1 ⊢
  have hNz : N ≠ 0 := by grind
  obtain ⟨u,hu⟩ : ∃ u : Rat, u * N = 1 := ⟨1 / N,Rat.div_mul_cancel hNz⟩
  have hu1 : 1 / N = u := by
    rw [Rat.div_def, Rat.one_mul]
    have := Rat.inv_mul_cancel N hNz
    have h3 : (u - N⁻¹) * N = 0 := by grind
    rcases Rat.mul_eq_zero.mp h3 with h | h
    · grind
    · exact absurd h hNz
  rw [hu1]
  have hN2 : (1 : Rat) ≤ N * N := by
    have := Rat.mul_nonneg (show (0:Rat) ≤ N - 1 by grind) (show (0:Rat) ≤ N + 1 by grind)
    grind
  have hN3 : N * N ≤ N * N * N := by
    have := Rat.mul_nonneg (show (0:Rat) ≤ N * N by grind) (show (0:Rat) ≤ N - 1 by grind)
    grind
  have hN4 : (0 : Rat) < N * N * N * N := Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by grind) (by grind)) (by grind)) (by grind)
  have hc : (0 : Rat) < 60 * (N * N * N * N) := by grind
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := 60 * (N * N * N * N)) _ hc
    have e : (41 / 60 - u) * (60 * (N * N * N * N)) = 41 * (N * N * N * N) - 60 * (N * N * N) * (u * N) := by
      grind
    rw [e, hu, h]
    grind
  · apply Rat.lt_of_mul_lt_mul_right (c := 60 * (N * N * N * N)) _ (Rat.le_of_lt hc)
    rw [h]
    grind

/-- Uniqueness: any assigned area of the quadratic sector is `41/60`. The area's existence
stays a hypothesis. -/
theorem quadratic_sector_area (area : SectorFan.AreaRules) (A : Fraction)
    (hA : area.HasArea (sector quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1)) A) :
    A.toRat = 41 / 60 := by
  have hpos (t : Fraction) (h0 : Fraction.le (Fraction.ofInt 0) t)
      (h1 : Fraction.le t (Fraction.ofInt 1)) : 0 < (quadraticChart t).num :=
    positive_of_le _ _ (by decide) (quadratic_bounds t h0 h1).1
  have hlow (n : Nat) (hn : 0 < n) :
      (chordArea quadraticChart (uniformPartition n hn)).toRat ≤ A.toRat :=
    (Fraction.le_iff_toRat _ _).mp (area.monotone _ _ _ _
      (quadratic_chords_in_sector (uniformPartition n hn))
      (chord_area_positive area quadraticChart (uniformPartition n hn) hpos) hA)
  by_cases heq : A.toRat = 41 / 60
  · exact heq
  exfalso
  rcases Rat.le_total (a := A.toRat) (b := 41 / 60) with hle | hge
  · -- A < 41/60 contradicts the lower approximations
    have hlt : A.toRat < 41 / 60 := by grind
    let g := Fraction.ofRat (41 / 60 - A.toRat)
    have hgR : g.toRat = 41 / 60 - A.toRat := Fraction.toRat_ofRat _
    have hg : 0 < g.num := (Fraction.positive_iff_toRat g).mpr (by rw [hgR]; grind)
    obtain ⟨n,hn,h1,_⟩ := exists_fine g g hg hg
    have h1R := (Fraction.lt_iff_toRat _ _).mp h1
    have hcast : (⟨1,(n : Int),by omega⟩ : Fraction).toRat = 1 / (n : Rat) := by
      simp only [Fraction.toRat]; norm_cast
    rw [hcast, hgR] at h1R
    have := (quadratic_chord_window n hn).1
    have := hlow n hn
    grind
  · -- A > 41/60 contradicts the cap gap
    have hgt : 41 / 60 < A.toRat := by grind
    let eta := Fraction.ofRat (A.toRat - 41 / 60)
    have hetaR : eta.toRat = A.toRat - 41 / 60 := Fraction.toRat_ofRat _
    have heta : 0 < eta.num := (Fraction.positive_iff_toRat eta).mpr (by rw [hetaR]; grind)
    obtain ⟨eps,delta,_,_,hdelta,hfine⟩ := caps_exhaust area quadraticChart (Fraction.ofInt 0)
      (Fraction.ofInt 1) (Fraction.ofInt 1) ⟨5,4,by decide⟩ (by unfold Fraction.le; decide)
      (by decide) quadratic_bounds quadratic_uniform eta heta
    obtain ⟨n,hn,h1,_⟩ := exists_fine delta delta hdelta hdelta
    have hp := hfine (uniformPartition n hn)
      (Fraction.magnitudes.lt_implies_le
        (Fraction.magnitudes.lt_of_le_lt (uniform_maxWidth n hn) h1))
    have herr := Fraction.magnitudes.lt_of_le_lt
      (chord_error_caps area quadraticChart (uniformPartition n hn) eps _ A hp.1 hA) hp.2
    have herrR := (Fraction.lt_iff_toRat _ _).mp herr
    rw [Fraction.toRat_abs, Fraction.toRat_durationDifference, hetaR] at herrR
    have hup := (quadratic_chord_window n hn).2
    simp only [Rat.abs] at herrR
    split at herrR <;> grind

/-- The exact between-area: with the subtraction rule and an assigned sector area, the actual
region between the quadratic sector and its `n`-cell chord fan has area `B_n` with
`60 n⁴ B_n = 15 n² - 4`, that is `B_n = 1/(4n²) - 1/(15n⁴) > 0`. -/
theorem quadratic_between_area (area : DifferenceAreaRules) (A : Fraction)
    (hA : area.HasArea (sector quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1)) A)
    (n : Nat) (hn : 0 < n) :
    ∃ B : Fraction, area.HasArea (between quadraticChart (uniformPartition n hn)) B ∧
      B.toRat * (60 * ((n : Rat) * n * n * n)) = 15 * ((n : Rat) * n) - 4 ∧ 0 < B.toRat := by
  have hpos (t : Fraction) (h0 : Fraction.le (Fraction.ofInt 0) t)
      (h1 : Fraction.le t (Fraction.ofInt 1)) : 0 < (quadraticChart t).num :=
    positive_of_le _ _ (by decide) (quadratic_bounds t h0 h1).1
  have hC := chord_area_positive area.toSectorAreaRules quadraticChart (uniformPartition n hn) hpos
  have hin := quadratic_chords_in_sector (uniformPartition n hn)
  have hsub := area.subtract _ _ _ _ hin hC hA
  refine ⟨_,area.congr_set _ _ _ (fun x => ?_) hsub,?_,?_⟩
  · constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨hc,hs⟩)
      · exact h
      · exact absurd (hin x hc) hs
  · rw [Fraction.toRat_durationDifference, quadratic_sector_area area.toSectorAreaRules A hA]
    have := quadratic_chord_area n hn
    grind
  · rw [Fraction.toRat_durationDifference, quadratic_sector_area area.toSectorAreaRules A hA]
    have := (quadratic_chord_window n hn).2
    grind

end NewtonLimitDynamics.Polygon.QuadraticSector
