import BarrowLib.Polygon.RectangleContent
import BarrowLib.Polygon.RationalIntervals

/-! Actual finite sector unions, distinguished from fans with multiplicity.
All vertices lie in the positive horizontal half-plane and consecutive
determinants are nonnegative. These local geometric conditions derive the
radial cuts separating successive triangles; separation is not a premise.
Area itself remains a supplied partial geometric relation, extended from the
rectangle convention by triangle areas and additivity across nonzero radial
lines. No curved sector or limiting area is postulated or constructed here.

Source of the coordinate definitions and derived lemmas below: the original
AI-assisted NewtonLean derivation in this file (English explanation and Lean
statements/proofs). No external exact-result source or priority is claimed.
The derivation uses BarrowLib only and is classified as Barrow support under
the user's dependency rule; recent authorship alone does not make it modern.

Classical background correspondence: Euclid, Elements I.41 (triangle area is half
the corresponding parallelogram) and Common Notions 2–5 (addition, subtraction,
coincidence and comparison of figures).
https://mathcs.clarku.edu/~djoyce/elements/bookI/propI41.html
https://mathcs.clarku.edu/~djoyce/elements/bookI/cn.html
Original Greek, I.41, Stamatis text as transcribed at:
https://physics.ntua.gr/mourmouras/euclid/book1/postulate41.html
Ἐὰν παραλληλόγραμμον τριγώνῳ βάσιν τε ἔχῃ τὴν αὐτὴν καὶ ἐν ταῖς
αὐταῖς παραλλήλοις ᾖ, διπλάσιόν ἐστι τὸ παραλληλόγραμμον τοῦ τριγώνου.

Original Greek Common Notions (same transcription, numbers 2, 3, 7, 8;
the latter two correspond to 4 and 5 in Joyce's five-notion presentation):
https://physics.ntua.gr/mourmouras/euclid/book1/elements1.html
Καὶ ἐὰν ἴσοις ἴσα προστεθῇ, τὰ ὅλα ἐστὶν ἴσα.
Καὶ ἐὰν ἀπὸ ἴσων ἴσα ἀφαιρεθῇ, τὰ καταλειπόμενά ἐστιν ἴσα.
Καὶ τὰ ἐφαρμόζοντα ἐπ᾿ ἄλληλα ἴσα ἀλλήλοις ἐστίν.
Καὶ τὸ ὅλον τοῦ μέρους μεῖζον [ἐστιν].

These are source-identified geometric premises, not a claim that Euclid
states the coordinate predicates below. The radial ordering proof is our
finite coordinate reconstruction of the dissection. Triangle normalization
and radial-cut additivity remain supplied; a full synthetic proof of the
area convention is not claimed. -/
namespace NewtonLimitDynamics.Polygon.SectorFan
open NewtonLimitDynamics TimeSubdivision PolygonFanArea

/-- The filled triangle with vertices the fixed origin, `p` and `q`. -/
def Triangle (p q x : Point) : Prop :=
  ∃ u v : Fraction, 0 ≤ u.num ∧ 0 ≤ v.num ∧
    Fraction.le (Fraction.add u v) (Fraction.ofInt 1) ∧
    pointEquiv x (pointAdd (pointScale u p) (pointScale v q))

def Region (p : Nat → Point) (n : Nat) (x : Point) : Prop :=
  ∃ i, i < n ∧ Triangle (p i) (p (i+1)) x

def areaSum (p : Nat → Point) (n : Nat) : Fraction :=
  sum (fun i => (det (p i) (p (i+1))).half) n

/-- Additional elementary geometric area rules. The triangle normalization
and radial additivity are explicit premises, not consequences of the existing
rectangle-only convention. The nonzero cut is essential: the zero vector
would place every set on both sides and make additivity inconsistent. -/
structure AreaRules extends RectangleContent.AreaRules where
  triangle : ∀ p q, 0 ≤ (det p q).num → HasArea (Triangle p q) (det p q).half
  radial_union : ∀ U V A B r, (r.1.num ≠ 0 ∨ r.2.num ≠ 0) →
    (∀ x, U x → 0 ≤ (det x r).num) →
    (∀ x, V x → 0 ≤ (det r x).num) →
    HasArea U A → HasArea V B → HasArea (fun x => U x ∨ V x) (Fraction.add A B)

/-- Reordering the two nonorigin vertices preserves the filled triangle.
Source: the original English statement and barycentric proof here. -/
theorem triangle_swap (p q x : Point) : Triangle p q x ↔ Triangle q p x := by
  constructor <;> rintro ⟨u,v,hu,hv,hs,hx⟩
  · exact ⟨v,u,hv,hu,Fraction.le_equiv_left (Fraction.add_comm _ _) hs,
      pointEquiv_trans hx (pointAdd_comm _ _)⟩
  · exact ⟨v,u,hv,hu,Fraction.le_equiv_left (Fraction.add_comm _ _) hs,
      pointEquiv_trans hx (pointAdd_comm _ _)⟩

/-- The supplied oriented normalization also assigns an unsigned area to
every radial connector, including reversed and collapsed triangles. Source:
this original finite derivation; no further area convention is added. -/
theorem unsigned_triangle_area (area : AreaRules) (p q : Point) :
    area.HasArea (Triangle p q) (det p q).abs.half := by
  by_cases h : 0 ≤ (det p q).num
  · exact area.congr_value _ _ _
      (RationalIntervals.half_equiv (Fraction.equiv_symm (Fraction.abs_of_nonnegative _ h)))
      (area.triangle p q h)
  · let neg : Fraction := ⟨-(det p q).num,(det p q).den,(det p q).den_pos⟩
    have hn : 0 ≤ neg.num := by dsimp [neg]; omega
    have he : Fraction.equiv (det q p) neg := by
      simp only [neg,det,Fraction.equiv,Fraction.add,Fraction.mul,Int.neg_mul,Int.mul_neg,
        Int.neg_add,Int.add_mul,Int.mul_add,Int.neg_neg]
      ac_nf
    have habs : Fraction.equiv neg (det p q).abs :=
      Fraction.equiv_trans (Fraction.equiv_symm (Fraction.abs_of_nonnegative neg hn))
        (Fraction.abs_neg (det p q))
    have hqa := area.triangle q p (Fraction.nonnegative_equiv he hn)
    exact area.congr_set _ _ _ (fun x => (triangle_swap q p x))
      (area.congr_value _ _ _ (RationalIntervals.half_equiv (Fraction.equiv_trans he habs)) hqa)

def slope (p : Point) (hp : 0 < p.1.num) : Fraction :=
  ⟨p.2.num * p.1.den, p.2.den * p.1.num, Int.mul_pos p.2.den_pos hp⟩

theorem slope_order (p q : Point) (hp : 0 < p.1.num) (hq : 0 < q.1.num) :
    Fraction.le (slope p hp) (slope q hq) ↔ 0 ≤ (det p q).num := by
  simp only [slope, Fraction.le, det, Fraction.add, Fraction.mul,
    Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Local orientation propagates through every pair of rays in a common
positive half-plane. A polygon winding around the origin need not satisfy
this half-plane premise. -/
theorem pairwise_orientation (p : Nat → Point) (n : Nat)
    (hp : ∀ i, i ≤ n → 0 < (p i).1.num)
    (hc : ∀ i, i < n → 0 ≤ (det (p i) (p (i+1))).num) :
    ∀ i j, i ≤ j → j ≤ n → 0 ≤ (det (p i) (p j)).num := by
  intro i j
  induction j generalizing i with
  | zero =>
    intro hij _
    have hi : i = 0 := by omega
    subst i
    exact Fraction.nonnegative_equiv (det_self _) (by decide)
  | succ j ih =>
    intro hij hj
    by_cases he : i = j+1
    · subst i
      exact Fraction.nonnegative_equiv (det_self _) (by decide)
    · have hi : i ≤ j := by omega
      have hleft := (slope_order (p i) (p j) (hp i (by omega)) (hp j (by omega))).mpr
        (ih i hi (by omega))
      have hright := (slope_order (p j) (p (j+1)) (hp j (by omega)) (hp (j+1) hj)).mpr
        (hc j (by omega))
      exact (slope_order (p i) (p (j+1)) (hp i (by omega)) (hp (j+1) hj)).mp
        (Fraction.magnitudes.le_trans hleft hright)

theorem triangle_left (p q r x : Point) (hx : Triangle p q x)
    (hp : 0 ≤ (det p r).num) (hq : 0 ≤ (det q r).num) :
    0 ≤ (det x r).num := by
  obtain ⟨u,v,hu,hv,_,he⟩ := hx
  have hd := Fraction.equiv_trans
    (TimeSubdivision.det_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    (Fraction.equiv_trans (det_add_left r _ _)
      (Fraction.add_equiv (det_scale_left u r p) (det_scale_left v r q)))
  exact Fraction.nonnegative_equiv hd
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hu hp)
      (Fraction.nonnegative_mul _ _ hv hq))

theorem triangle_right (p q r x : Point) (hx : Triangle p q x)
    (hp : 0 ≤ (det r p).num) (hq : 0 ≤ (det r q).num) :
    0 ≤ (det r x).num := by
  obtain ⟨u,v,hu,hv,_,he⟩ := hx
  have hd := Fraction.equiv_trans
    (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ he)
    (Fraction.equiv_trans (det_add_right r _ _)
      (Fraction.add_equiv (det_scale_right u r p) (det_scale_right v r q)))
  exact Fraction.nonnegative_equiv hd
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hu hp)
      (Fraction.nonnegative_mul _ _ hv hq))

theorem region_succ (p : Nat → Point) (n : Nat) (x : Point) :
    Region p (n+1) x ↔ Region p n x ∨ Triangle (p n) (p (n+1)) x := by
  constructor
  · rintro ⟨i,hi,hx⟩
    by_cases h : i < n
    · exact Or.inl ⟨i,h,hx⟩
    · have he : i = n := by omega
      subst i
      exact Or.inr hx
  · rintro (⟨i,hi,hx⟩ | hx)
    · exact ⟨i,by omega,hx⟩
    · exact ⟨n,by omega,hx⟩

/-- The represented triangle union has the sum of its triangle areas.
Radial separation follows from the local half-plane and orientation data.
No multiplicity or nonoverlap assertion is assumed in the theorem. -/
theorem region_area (area : AreaRules) (p : Nat → Point) (n : Nat)
    (hp : ∀ i, i ≤ n → 0 < (p i).1.num)
    (hc : ∀ i, i < n → 0 ≤ (det (p i) (p (i+1))).num) :
    area.HasArea (Region p n) (areaSum p n) := by
  induction n with
  | zero =>
    apply area.congr_set (fun _ => False) _ _ _ area.empty
    intro x
    simp only [Region, Nat.not_lt_zero, false_and, exists_false]
  | succ n ih =>
    have hprev := ih (fun i hi => hp i (by omega)) (fun i hi => hc i (by omega))
    have hlast := area.triangle (p n) (p (n+1)) (hc n (by omega))
    have hordered := pairwise_orientation p (n+1) hp hc
    have hu := area.radial_union _ _ _ _ (p n) (Or.inl (Int.ne_of_gt (hp n (by omega))))
      ?_ ?_ hprev hlast
    · exact area.congr_set _ _ _ (fun x => (region_succ p n x).symm) hu
    · intro x hx
      obtain ⟨i,hi,hx⟩ := hx
      exact triangle_left _ _ _ x hx
        (hordered i n (by omega) (by omega)) (hordered (i+1) n (by omega) (by omega))
    · intro x hx
      exact triangle_right _ _ _ x hx
        (Fraction.nonnegative_equiv (det_self _) (by decide)) (hc n (by omega))

end NewtonLimitDynamics.Polygon.SectorFan
