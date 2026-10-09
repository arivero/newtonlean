import BarrowLib.Polygon.RectangleContent
import BarrowLib.Polygon.GeometricTail

/-! Rectangle approximation with an assigned area magnitude which need not
be a rational number. Coordinates and finite side-product sums remain rational.
The partial geometric area convention and the abstract magnitude domain are
supplied; neither arbitrary area existence nor a completion is constructed.

Classical exhaustion premise: Euclid, Elements X.1, including its final
sentence permitting subtraction of exact halves. Original Greek, Stamatis
transcription, retrieved 9 October 2026:
https://physics.ntua.gr/mourmouras/euclid_desktop/book10/postulate1.html
Archived original: docs/classics/euclid-X1.html.
Δύο μεγεθῶν ἀνίσων ἐκκειμένων, ἐὰν ἀπὸ τοῦ μείζονος ἀφαιρεθῇ
μεῖζον ἢ τὸ ἥμισυ καὶ τοῦ καταλειπομένου μεῖζον ἢ τὸ ἥμισυ, καὶ
τοῦτο ἀεὶ γίγνηται, λειφθήσεταί τι μέγεθος, ὃ ἔσται ἔλασσον τοῦ
ἐκκειμένου ἐλάσσονος μεγέθους.
ὁμοίως δὲ δειχθήσεται, κἂν ἡμίση ᾖ τὰ ἀφαιρούμενα.

`unit_halves_exhaust` is the explicit supplied application to comparable area
magnitudes and the halves of one positive area unit. It is not proved here
for an arbitrary `Q`, and is not a postulate that curves have rational areas.
Source-support correspondence: X.1 → unit_halves_exhaust; witness Stamatis
transcription, final sentence at the URL above; status editorial_interpretation;
confidence high for this unit-halving specialization. No Newton citation of
X.1 is asserted. Book V definitions 4–5, archived in docs/classics/euclid-V.html,
concern comparable magnitudes and equimultiple ratio comparisons; they do not
assert arbitrary curved-area existence. The order/addition/embed operations
below are explicit editorial modeling data, not quoted Euclid definitions.

Provenance of the pullback and approximation results: their original English
statements and checked project derivations below. Known exhaustion mathematics
remains attributed to Euclid; no originality or historical priority is claimed.
Barrow classification follows the rational arithmetic dependencies. -/

namespace NewtonLimitDynamics.Polygon.MagnitudeContent
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison MonotoneRectangles

structure Rules (Q : Type) where
  order : Magnitudes Q
  add : Q → Q → Q
  embed : Fraction → Q
  embed_le : ∀ a b, order.le (embed a) (embed b) ↔ Fraction.le a b
  embed_add : ∀ a b,
    order.le (embed (Fraction.add a b)) (add (embed a) (embed b)) ∧
    order.le (add (embed a) (embed b)) (embed (Fraction.add a b))
  unit_positive : order.positive (embed (Fraction.ofInt 1))
  add_le_add_right : ∀ a b, order.le a b → ∀ c, order.le (add a c) (add b c)
  add_lt_add_left : ∀ a b, order.lt a b → ∀ c, order.lt (add c a) (add c b)
  /-- Supplied classical X.1 halving premise, for this area-magnitude domain. -/
  unit_halves_exhaust : ∀ d, order.positive d → ∃ n,
    order.lt (embed (HarmonicDyadic.duration (Fraction.ofInt 1) n)) d

/-- The domain assumptions are realized by the already proved rational model.
This witnesses consistency of this interface, not a construction of all
incommensurable geometric magnitudes or of their area assignments. -/
def rational : Rules Fraction where
  order := Fraction.magnitudes
  add := Fraction.add
  embed := id
  embed_le := fun _ _ => Iff.rfl
  embed_add := fun _ _ => ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩
  unit_positive := by change (0 : Int)<1; decide
  add_le_add_right := fun _ _ h c => Fraction.add_le_add_right h c
  add_lt_add_left := fun _ _ h c => Fraction.add_lt_add_left h c
  unit_halves_exhaust := by
    intro d hd
    obtain ⟨N,hN⟩ := HarmonicTimeRealization.duration_eventually_small
      (Fraction.ofInt 1) d (by decide) hd
    exact ⟨N,hN N (Nat.le_refl _)⟩

structure AreaRules (Q : Type) where
  magnitudes : Rules Q
  HasArea : (Point → Prop) → Q → Prop
  empty : HasArea (fun _ => False) (magnitudes.embed (Fraction.ofInt 0))
  congr_set : ∀ U V A, (∀ x, U x ↔ V x) → HasArea U A → HasArea V A
  congr_value : ∀ U A B, magnitudes.order.le A B → magnitudes.order.le B A →
    HasArea U A → HasArea U B
  rectangle : ∀ l r H, Fraction.le l r → 0≤H.num →
    HasArea (MonotoneRectangles.rectangle l r H)
      (magnitudes.embed (Fraction.mul (durationDifference l r) H))
  separated_union : ∀ U V A B c,
    (∀ x, U x → Fraction.le x.1 c) → (∀ x, V x → Fraction.le c x.1) →
    HasArea U A → HasArea V B → HasArea (fun x => U x ∨ V x) (magnitudes.add A B)
  monotone : ∀ U V A B, (∀ x, U x → V x) → HasArea U A → HasArea V B →
    magnitudes.order.le A B

/-- The old partial area convention realizes the rational specialization.
Its geometric existence is still supplied, exactly as in the old interface. -/
def ofRationalAreas (area : RectangleContent.AreaRules) : AreaRules Fraction where
  magnitudes := rational
  HasArea := area.HasArea
  empty := area.empty
  congr_set := area.congr_set
  congr_value := fun U A B hab hba hA => area.congr_value U A B
    ((Fraction.equiv_iff_mutual_le A B).mpr ⟨hab,hba⟩) hA
  rectangle := area.rectangle
  separated_union := area.separated_union
  monotone := area.monotone

/-- Pull back only rational-valued assignments. All existing finite rectangle
proofs then apply unchanged, without requiring the curved area to be in the
image of the rational embedding. No geometric assignment is invented. -/
def rationalAreas {Q : Type} (area : AreaRules Q) : RectangleContent.AreaRules where
  HasArea := fun U A => area.HasArea U (area.magnitudes.embed A)
  empty := area.empty
  congr_set := fun U V A h hA => area.congr_set U V _ h hA
  congr_value := by
    intro U A B h hA
    exact area.congr_value U _ _
      ((area.magnitudes.embed_le A B).mpr (Fraction.le_of_equiv h))
      ((area.magnitudes.embed_le B A).mpr (Fraction.le_of_equiv (Fraction.equiv_symm h))) hA
  rectangle := area.rectangle
  separated_union := by
    intro U V A B c hU hV hA hB
    exact area.congr_value _ _ _ (area.magnitudes.embed_add A B).2
      (area.magnitudes.embed_add A B).1 (area.separated_union U V _ _ c hU hV hA hB)
  monotone := fun U V A B h hA hB =>
    (area.magnitudes.embed_le A B).mp (area.monotone U V _ _ h hA hB)

/-- Actual rectangle unions enclose any assigned area magnitude of the figure.
The area magnitude is an arbitrary `Q`, not a supplied rational number. -/
theorem curved_area_enclosure {Q : Type} (area : AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hA : area.HasArea (figure g a b) A) :
    area.magnitudes.order.le (area.magnitudes.embed (lowerSum g p)) A ∧
      area.magnitudes.order.le A (area.magnitudes.embed (upperSum g p)) := by
  have hfinite := RectangleContent.lower_upper_areas (rationalAreas area) g a b p hg hbase
  have hsets := figure_enclosure g p hg
  exact ⟨area.monotone _ _ _ _ hsets.1 hfinite.1 hA,
    area.monotone _ _ _ _ hsets.2 hA hfinite.2⟩

/-- X.1 supplies a rational unit subdivision below each positive magnitude
tolerance, so rational gap exhaustion transfers to the supplied domain. -/
theorem rational_exhaustion {Q : Type} (M : Rules Q) (gap : Nat → Fraction)
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes gap) :
    Exhaustion.VanishingDifference M.order (fun m => M.embed (gap m)) := by
  intro d hd
  obtain ⟨n,hn⟩ := M.unit_halves_exhaust d hd
  obtain ⟨N,hN⟩ := hgap (HarmonicDyadic.duration (Fraction.ofInt 1) n)
    (by change (0 : Int)<1; decide)
  exact ⟨N,fun m hm => M.order.lt_of_le_lt
    ((M.embed_le _ _).mpr (Fraction.magnitudes.lt_implies_le (hN m hm))) hn⟩

/-- Division-free absolute approximation: both errors are smaller than each
positive magnitude tolerance, expressed by addition and strict comparison. -/
def ErrorsVanish {Q : Type} (M : Rules Q) (L U : Nat → Fraction) (A : Q) : Prop :=
  ∀ d, M.order.positive d → Exhaustion.Eventually (fun m =>
    M.order.lt A (M.add (M.embed (L m)) d) ∧
      M.order.lt (M.embed (U m)) (M.add A d))

/-- Finite geometric assignments plus approximation to the supplied curved
area magnitude. The desired error estimate is a conclusion, not a field of
the area rules. -/
def Approximates {Q : Type} (area : AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (parts : Nat → Partition a b) : Prop :=
  (∀ m, area.HasArea (lowerFigure g (parts m)) (area.magnitudes.embed (lowerSum g (parts m))) ∧
    area.HasArea (upperFigure g (parts m)) (area.magnitudes.embed (upperSum g (parts m)))) ∧
  ErrorsVanish area.magnitudes (fun m => lowerSum g (parts m)) (fun m => upperSum g (parts m)) A

/-- A single finite enclosing gap controls both errors against any assigned
area magnitude. This extracts the comparison step shared by exhaustion
arguments; no geometric assignment or limiting conclusion is assumed. -/
theorem enclosure_errors_lt {Q : Type} (M : Rules Q) (L U : Fraction) (A d : Q)
    (henclose : M.order.le (M.embed L) A ∧ M.order.le A (M.embed U))
    (hgap : M.order.lt (M.embed (durationDifference L U)) d) :
    M.order.lt A (M.add (M.embed L) d) ∧ M.order.lt (M.embed U) (M.add A d) := by
  have hsum : M.order.le (M.embed U)
      (M.add (M.embed L) (M.embed (durationDifference L U))) :=
    M.order.le_trans ((M.embed_le _ _).mpr (Fraction.le_of_equiv
      (Fraction.equiv_symm (add_difference_cancel L U)))) (M.embed_add _ _).1
  have hbound := M.order.lt_of_le_lt hsum
    (M.add_lt_add_left _ _ hgap (M.embed L))
  exact ⟨M.order.lt_of_le_lt henclose.2 hbound,
    M.order.lt_of_lt_le hbound (M.add_le_add_right _ _ henclose.1 d)⟩

theorem errors_vanish {Q : Type} (M : Rules Q) (L U : Nat → Fraction) (A : Q)
    (henclose : ∀ m, M.order.le (M.embed (L m)) A ∧ M.order.le A (M.embed (U m)))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => durationDifference (L m) (U m))) : ErrorsVanish M L U A := by
  intro d hd
  obtain ⟨N,hN⟩ := rational_exhaustion M _ hgap d hd
  exact ⟨N,fun m hm => enclosure_errors_lt M _ _ A d (henclose m) (hN m hm)⟩

/-! Integer-multiple comparisons for ultimate equality of assigned magnitudes.
Source language: Euclid, Elements V, definitions 2 and 5, same Greek witness
as docs/classics/euclid-V.html, paragraphs β΄ [2] and ε΄ [5]:
Πολλαπλάσιον δὲ τὸ μεῖζον τοῦ ἐλάττονος, ὅταν καταμετρῆται ὑπὸ τοῦ ἐλάττονος.
Ἐν τῷ αὐτῷ λόγῳ μεγέθη λέγεται εἶναι πρῶτον πρὸς δεύτερον καὶ
τρίτον πρὸς τέταρτον, ὅταν τὰ τοῦ πρώτου καὶ τρίτου ἰσάκις
πολλαπλάσια τῶν τοῦ δευτέρου καὶ τετάρτου ἰσάκις πολλαπλασίων
καθ᾿ ὁποιονοῦν πολλαπλασιασμὸν ἑκάτερον ἑκατέρου ἢ ἅμα
ὑπερέχῃ ἢ ἅμα ἴσα ᾖ ἢ ἅμα ἐλλείπῃ ληφθέντα κατάλληλα.
URL: https://physics.ntua.gr/mourmouras/euclid/book5/elements5.html
Status editorial_interpretation; confidence high for comparison of multiples,
not an attribution of the following sequence-limit definition to Euclid.
`RatiosOne` eventually gives the comparisons against each unequal positive
integer pair that equality of ratios to 1 would give. It does not assert exact
finite equality of ratios or require a quotient of general magnitudes.
The extra compatibility laws are supplied order/addition modeling data, not
a convergence premise. Their rational realization and all exact statements
and derivations below are project provenance, without priority claims. -/

structure MultipleRules {Q : Type} (M : Rules Q) where
  add_le_add_left : ∀ a b, M.order.le a b → ∀ c,
    M.order.le (M.add c a) (M.add c b)
  embed_lt : ∀ a b, Fraction.lt a b → M.order.lt (M.embed a) (M.embed b)

def rationalMultiples : MultipleRules rational where
  add_le_add_left := fun _ _ h c => Fraction.add_le_add_left h c
  embed_lt := fun _ _ h => h

/-- Actual repeated addition, including a zero starting value. -/
def multiple {Q : Type} (M : Rules Q) : Nat → Q → Q
  | 0, _ => M.embed (Fraction.ofInt 0)
  | n+1, A => M.add (multiple M n A) A

private def scale (n : Nat) (a : Fraction) : Fraction :=
  Fraction.mul (Fraction.ofInt (n : Int)) a

private theorem scale_succ (n : Nat) (a : Fraction) :
    Fraction.equiv (scale (n+1) a) (Fraction.add (scale n a) a) := by
  simp only [scale, Fraction.equiv, Fraction.mul, Fraction.ofInt, Fraction.add,
    Int.natCast_add, Int.natCast_one, Int.one_mul, Int.mul_one, Int.add_mul, Int.mul_add]
  ac_nf

theorem multiple_monotone {Q : Type} (M : Rules Q) (R : MultipleRules M)
    (n : Nat) {A B : Q} (h : M.order.le A B) :
    M.order.le (multiple M n A) (multiple M n B) := by
  induction n with
  | zero => exact M.order.le_refl _
  | succ n ih =>
    exact M.order.le_trans (M.add_le_add_right _ _ ih A)
      (R.add_le_add_left _ _ h (multiple M n B))

theorem multiple_embed {Q : Type} (M : Rules Q) (n : Nat) (a : Fraction) :
    M.order.le (multiple M n (M.embed a)) (M.embed (scale n a)) ∧
      M.order.le (M.embed (scale n a)) (multiple M n (M.embed a)) := by
  induction n with
  | zero =>
    constructor <;> apply (M.embed_le _ _).mpr <;>
      simp [multiple, scale, Fraction.le, Fraction.mul, Fraction.ofInt]
  | succ n ih =>
    have hs := (Fraction.equiv_iff_mutual_le _ _).mp (scale_succ n a)
    exact ⟨M.order.le_trans (M.add_le_add_right _ _ ih.1 (M.embed a))
        (M.order.le_trans (M.embed_add _ _).2 ((M.embed_le _ _).mpr hs.2)),
      M.order.le_trans ((M.embed_le _ _).mpr hs.1)
        (M.order.le_trans (M.embed_add _ _).1 (M.add_le_add_right _ _ ih.2 (M.embed a)))⟩

/-- Each positive rational comparison with unity holds on a returned tail,
in both directions. This is a limit of comparisons, not exact finite equality.
Zero figures require separate treatment and do not satisfy this predicate. -/
def RatiosOne {Q : Type} (M : Rules Q) (X Y : Nat → Q) : Prop :=
  ∀ n m : Nat, 0<n → n<m → Exhaustion.Eventually (fun k =>
    M.order.lt (multiple M n (X k)) (multiple M m (Y k)) ∧
      M.order.lt (multiple M n (Y k)) (multiple M m (X k)))

private theorem scale_gap_compare (n m : Nat) (hnm : n<m) (B L U : Fraction)
    (hB : 0<B.num) (hBL : Fraction.le B L)
    (hsmall : Fraction.lt (scale n (durationDifference L U)) B) :
    Fraction.lt (scale n U) (scale m L) := by
  have hL : 0<L.num := (Fraction.positive_iff_zero_lt L).mpr
    (Fraction.magnitudes.lt_of_lt_le ((Fraction.positive_iff_zero_lt B).mp hB) hBL)
  have he := Fraction.equiv_trans
    (Fraction.mul_equiv_left (Fraction.ofInt (n : Int))
      (Fraction.equiv_symm (add_difference_cancel L U)))
    (Fraction.mul_add (Fraction.ofInt (n : Int)) L (durationDifference L U))
  have hnext : Fraction.lt (scale n U) (scale (n+1) L) :=
    Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv he)
      (Fraction.magnitudes.lt_of_lt_le (Fraction.add_lt_add_left hsmall (scale n L))
        (Fraction.le_equiv_right (Fraction.add_le_add_left hBL _)
          (Fraction.equiv_symm (scale_succ n L))))
  have hnm' : Fraction.le (Fraction.ofInt ((n+1 : Nat) : Int))
      (Fraction.ofInt (m : Int)) := by
    simp only [Fraction.le, Fraction.ofInt, Int.mul_one]
    omega
  exact Fraction.magnitudes.lt_of_lt_le hnext
    (Fraction.mul_le_mul_nonnegative hnm' L (Int.le_of_lt hL))

/-- A positive eventual lower bracket and shrinking rational bracket gap
force mutual unit-ratio comparisons for any two supplied magnitudes between
the brackets. No quotient, rational-image assumption or limit is supplied. -/
theorem ratios_one_of_enclosure {Q : Type} (M : Rules Q) (R : MultipleRules M)
    (L U : Nat → Fraction) (X Y : Nat → Q)
    (hX : ∀ k, M.order.le (M.embed (L k)) (X k) ∧
      M.order.le (X k) (M.embed (U k)))
    (hY : ∀ k, M.order.le (M.embed (L k)) (Y k) ∧
      M.order.le (Y k) (M.embed (U k)))
    (B : Fraction) (hB : 0<B.num) (N : Nat)
    (hBL : ∀ k, N≤k → Fraction.le B (L k))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun k => durationDifference (L k) (U k))) : RatiosOne M X Y := by
  intro n m _ hnm
  let C := Fraction.ofInt (n : Int)
  have hC : 0≤C.num := by change 0≤(n : Int); omega
  obtain ⟨K,hK⟩ := hgap (HarmonicTimeRealization.factorDelta C B hC)
    (HarmonicTimeRealization.factorDelta_positive C B hC hB)
  refine ⟨N+K,fun k hk => ?_⟩
  have hLU : Fraction.le (L k) (U k) :=
    (M.embed_le _ _).mp (M.order.le_trans (hX k).1 (hX k).2)
  have hnon := (difference_nonnegative_iff _ _).mpr hLU
  have hsmall := HarmonicTimeRealization.factor_control C B
    (durationDifference (L k) (U k)) hC hnon (hK k (by omega))
  have hscaled : Fraction.lt (scale n (U k)) (scale m (L k)) :=
    scale_gap_compare n m hnm B _ _ hB (hBL k (by omega))
      (Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_of_equiv (Fraction.mul_comm C _)) hsmall)
  have hcross : M.order.lt (multiple M n (M.embed (U k)))
      (multiple M m (M.embed (L k))) :=
    M.order.lt_of_le_lt (multiple_embed M n _).1
      (M.order.lt_of_lt_le (R.embed_lt _ _ hscaled) (multiple_embed M m _).2)
  exact ⟨M.order.lt_of_le_lt (multiple_monotone M R n (hX k).2)
      (M.order.lt_of_lt_le hcross (multiple_monotone M R m (hY k).1)),
    M.order.lt_of_le_lt (multiple_monotone M R n (hY k).2)
      (M.order.lt_of_lt_le hcross (multiple_monotone M R m (hX k).1))⟩

/-- All three mutual comparisons in Lemmas II–III, without dividing general
magnitudes. The fixed rectangle used for positivity may start inside the
patch, so initial lower sums may vanish. -/
def AreaRatiosOne {Q : Type} (M : Rules Q) (L U : Nat → Fraction) (A : Q) : Prop :=
  RatiosOne M (fun k => M.embed (L k)) (fun k => M.embed (U k)) ∧
    RatiosOne M (fun k => M.embed (L k)) (fun _ => A) ∧
    RatiosOne M (fun k => M.embed (U k)) (fun _ => A)

/-- The actual interior rectangle derives the eventual positive bracket.
Its finite gap exhaustion then gives all three unit-ratio comparisons for
an arbitrary assigned curved-area magnitude. General area existence and
nonrational coordinates are not asserted. Provenance: this exact project
statement and derivation, using the source-qualified comparison language. -/
theorem rectangle_magnitude_ratios {Q : Type} (area : AreaRules Q)
    (R : MultipleRules area.magnitudes) (g : Fraction → Fraction)
    (a b c : Fraction) (A : Q) (parts : Nat → Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (henclose : ∀ k, area.magnitudes.order.le
      (area.magnitudes.embed (lowerSum g (parts k))) A ∧
      area.magnitudes.order.le A (area.magnitudes.embed (upperSum g (parts k))))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun k => gap g (parts k))) :
    AreaRatiosOne area.magnitudes (fun k => lowerSum g (parts k))
      (fun k => upperSum g (parts k)) A := by
  obtain ⟨B,hB,N,hBN⟩ := RectangleContent.rectangle_interior_denominator_bound
    (rationalAreas area) g a b c parts hg hbase hac hcb hgc hgap
  have hLU (k : Nat) := area.magnitudes.order.le_trans (henclose k).1 (henclose k).2
  have hL (k : Nat) : area.magnitudes.order.le
      (area.magnitudes.embed (lowerSum g (parts k)))
      (area.magnitudes.embed (lowerSum g (parts k))) ∧
      area.magnitudes.order.le (area.magnitudes.embed (lowerSum g (parts k)))
        (area.magnitudes.embed (upperSum g (parts k))) :=
    ⟨area.magnitudes.order.le_refl _,hLU k⟩
  have hU (k : Nat) : area.magnitudes.order.le
      (area.magnitudes.embed (lowerSum g (parts k)))
      (area.magnitudes.embed (upperSum g (parts k))) ∧
      area.magnitudes.order.le (area.magnitudes.embed (upperSum g (parts k)))
        (area.magnitudes.embed (upperSum g (parts k))) :=
    ⟨hLU k,area.magnitudes.order.le_refl _⟩
  exact ⟨ratios_one_of_enclosure area.magnitudes R _ _ _ _ hL hU B hB N
      (fun k hk => (hBN k hk).1) hgap,
    ratios_one_of_enclosure area.magnitudes R _ _ _ _ hL henclose B hB N
      (fun k hk => (hBN k hk).1) hgap,
    ratios_one_of_enclosure area.magnitudes R _ _ _ _ hU henclose B hB N
      (fun k hk => (hBN k hk).1) hgap⟩

end NewtonLimitDynamics.Polygon.MagnitudeContent
