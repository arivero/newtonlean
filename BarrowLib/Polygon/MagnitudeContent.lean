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

theorem errors_vanish {Q : Type} (M : Rules Q) (L U : Nat → Fraction) (A : Q)
    (henclose : ∀ m, M.order.le (M.embed (L m)) A ∧ M.order.le A (M.embed (U m)))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => durationDifference (L m) (U m))) : ErrorsVanish M L U A := by
  intro d hd
  obtain ⟨N,hN⟩ := rational_exhaustion M _ hgap d hd
  refine ⟨N,fun m hm => ?_⟩
  have hsum : M.order.le (M.embed (U m))
      (M.add (M.embed (L m)) (M.embed (durationDifference (L m) (U m)))) :=
    M.order.le_trans ((M.embed_le _ _).mpr (Fraction.le_of_equiv
      (Fraction.equiv_symm (add_difference_cancel (L m) (U m))))) (M.embed_add _ _).1
  have hbound := M.order.lt_of_le_lt hsum
    (M.add_lt_add_left _ _ (hN m hm) (M.embed (L m)))
  exact ⟨M.order.lt_of_le_lt (henclose m).2 hbound,
    M.order.lt_of_lt_le hbound (M.add_le_add_right _ _ (henclose m).1 d)⟩

end NewtonLimitDynamics.Polygon.MagnitudeContent
