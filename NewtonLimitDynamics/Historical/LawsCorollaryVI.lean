import BarrowLib.Polygon.CommonMotion
import NewtonLimitDynamics.Historical.LawI
import NewtonLimitDynamics.Historical.LawII

/-! Historical result: laws_corollary_vi.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
Each edition retains its exact source statement and proof.
-/

/-! 1687 witness.
Source: docs/m1/NATP00076.xml
SHA-256: fc2984820b61f64fdbf5efe1142ea8cf5458b75dd54fc6525f73ee705a8a9b1c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par22
Anchor URLs: NATP00076.par22 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par22; NATP00076.par23 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par23
Proof-step correspondence: "Quomodocunque inter se" is read as an arbitrary impulse rule, including prescribed impulse histories; that the rule sees only the table of relative positions and velocities (`RelativeKick`) is an editorial premise carried over from Corollary V, which this corollary's text leaves implicit. Equal accelerative forces along parallel lines act "pro quantitatibus movendorum corporum"; they are represented by one calibrated velocity change per cell, the same for every body, which the edition's Law II predicate adds to each body's own impulse. Supplied Law I inertia carries each body between impulses; no law is cited for that step. At every cell boundary each body's state is then its unforced state plus the one common motion that the added changes generate from rest ("æqualiter (quoad velocitatem) movebunt"), so all mutual positions and motions are unchanged. Both runs share one time. Forces depending on absolute position or velocity lie outside the impulse rule and are not covered.
-/
/- LATIN BEGIN NATP00076.par22
Si corpora moveantur quomodocunq; inter se & a viribus acceleratricibus æqualibus secundum lineas parallelas urgeantur; pergent omnia eodem modo moveri inter se ac si viribus illis non essent incitata.
LATIN END NATP00076.par22 -/
/- LATIN BEGIN NATP00076.par23
Nam vires illæ æqualiter (pro quantitatibus movendorum corporum) & secundum lineas parallelas agendo, corpora omnia æqualiter (quoad velocitatem) movebunt per Legem 2.) adeoq; nunquam mutabunt positiones & motus eorum inter se.
LATIN END NATP00076.par23 -/
/-! Historical dependency ledger for this exact witness:
- P1687.Law2 → P1687.LawCor6; passage NATP00076.par23; witness Axiomata Sive Leges Motus (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par23; status explicit_dependency; confidence high.
- P1687.Law1 → P1687.LawCor6; passage NATP00076.par23 (motion between impulses, for which no law is cited); witness Axiomata Sive Leges Motus (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par23; status editorial_interpretation; confidence medium.
-/

namespace Principia1687.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision CommonMotion

/-- "Corpora omnia æqualiter (quoad velocitatem) movebunt": with the common
velocity changes `h` added to arbitrary mutual impulses, each body's state at
every cell boundary is its unforced state plus the common motion that `h`
alone generates from rest at the origin. -/
theorem corollary6_equal_motion {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 : ι → State) (h : Nat → Point) (n : Nat) (i : ι) :
    stateEquiv (run motion dt (fun k D j v => update (update v (kick k D j)) (h k)) S0 n i)
      (stateAdd (run motion dt (fun k D j v => update v (kick k D j)) S0 n i)
        (commonRun (ZeroForce.zeroPoint, ZeroForce.zeroPoint) dt h n)) :=
  common_superposition motion dt kick _ _ h (ZeroForce.zeroPoint, ZeroForce.zeroPoint) S0 S0
    hI hK (fun _ _ _ v => hII v _)
    (fun _ _ _ v => pointEquiv_trans (hII _ _) (pointAdd_congr (hII v _) (pointEquiv_refl _)))
    (fun _ => stateEquiv_symm ⟨pointAdd_zero _, pointAdd_zero _⟩) n i

/-- Laws Corollary VI: the bodies' mutual positions and motions with the
common forces equal those without them at every cell boundary. -/
theorem corollary6_motions_inter_se {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 : ι → State) (h : Nat → Point) (n : Nat) (i j : ι) :
    stateEquiv
      (relative (run motion dt (fun k D l v => update (update v (kick k D l)) (h k)) S0 n) i j)
      (relative (run motion dt (fun k D l v => update v (kick k D l)) S0 n) i j) :=
  relative_unchanged motion dt kick _ _ h (ZeroForce.zeroPoint, ZeroForce.zeroPoint) S0 S0
    hI hK (fun _ _ _ v => hII v _)
    (fun _ _ _ v => pointEquiv_trans (hII _ _) (pointAdd_congr (hII v _) (pointEquiv_refl _)))
    (fun _ => stateEquiv_symm ⟨pointAdd_zero _, pointAdd_zero _⟩) n i j

end Principia1687.Laws

/-! 1713 witness.
Source: docs/m1/NATP00081.xml
SHA-256: 5c72c73d9f396d3b34475543fa7cd158ab29006fb43fa35bc63df9b7e4be6bfe
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par22
Anchor URLs: NATP00081.par22 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par22; NATP00081.par23 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par23
Proof-step correspondence: "Quomodocunque inter se" is read as an arbitrary impulse rule, including prescribed impulse histories; that the rule sees only the table of relative positions and velocities (`RelativeKick`) is an editorial premise carried over from Corollary V, which this corollary's text leaves implicit. Equal accelerative forces along parallel lines act "pro quantitatibus movendorum corporum"; they are represented by one calibrated velocity change per cell, the same for every body, which the edition's Law II predicate adds to each body's own impulse. Supplied Law I inertia carries each body between impulses; no law is cited for that step. At every cell boundary each body's state is then its unforced state plus the one common motion that the added changes generate from rest ("æqualiter (quoad velocitatem) movebunt"), so all mutual positions and motions are unchanged. Both runs share one time. Forces depending on absolute position or velocity lie outside the impulse rule and are not covered.
-/
/- LATIN BEGIN NATP00081.par22
Si corpora moveatur quomodocunq; inter se, & a viribus acceleratricibus æqualibus secundum lineas parallelas urgeantur; pergent omnia eodem modo moveri inter se, ac si viribus illis non essent incitata.
LATIN END NATP00081.par22 -/
/- LATIN BEGIN NATP00081.par23
Nam vires illæ æqualiter (pro quantitatibus movendorum corporum) & secundum lineas parallelas agendo, corpora omnia æqualiter (quoad velocitatem) movebunt per Legem II.) adeoque nunquam mutabunt positiones & motus eorum inter se.
LATIN END NATP00081.par23 -/
/-! Historical dependency ledger for this exact witness:
- P1713.Law2 → P1713.LawCor6; passage NATP00081.par23; witness Axiomata Sive Leges Motus (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par23; status explicit_dependency; confidence high.
- P1713.Law1 → P1713.LawCor6; passage NATP00081.par23 (motion between impulses, for which no law is cited); witness Axiomata Sive Leges Motus (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par23; status editorial_interpretation; confidence medium.
-/

namespace Principia1713.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision CommonMotion

/-- "Corpora omnia æqualiter (quoad velocitatem) movebunt": with the common
velocity changes `h` added to arbitrary mutual impulses, each body's state at
every cell boundary is its unforced state plus the common motion that `h`
alone generates from rest at the origin. -/
theorem corollary6_equal_motion {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 : ι → State) (h : Nat → Point) (n : Nat) (i : ι) :
    stateEquiv (run motion dt (fun k D j v => update (update v (kick k D j)) (h k)) S0 n i)
      (stateAdd (run motion dt (fun k D j v => update v (kick k D j)) S0 n i)
        (commonRun (ZeroForce.zeroPoint, ZeroForce.zeroPoint) dt h n)) :=
  common_superposition motion dt kick _ _ h (ZeroForce.zeroPoint, ZeroForce.zeroPoint) S0 S0
    hI hK (fun _ _ _ v => hII v _)
    (fun _ _ _ v => pointEquiv_trans (hII _ _) (pointAdd_congr (hII v _) (pointEquiv_refl _)))
    (fun _ => stateEquiv_symm ⟨pointAdd_zero _, pointAdd_zero _⟩) n i

/-- Laws Corollary VI: the bodies' mutual positions and motions with the
common forces equal those without them at every cell boundary. -/
theorem corollary6_motions_inter_se {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 : ι → State) (h : Nat → Point) (n : Nat) (i j : ι) :
    stateEquiv
      (relative (run motion dt (fun k D l v => update (update v (kick k D l)) (h k)) S0 n) i j)
      (relative (run motion dt (fun k D l v => update v (kick k D l)) S0 n) i j) :=
  relative_unchanged motion dt kick _ _ h (ZeroForce.zeroPoint, ZeroForce.zeroPoint) S0 S0
    hI hK (fun _ _ _ v => hII v _)
    (fun _ _ _ v => pointEquiv_trans (hII _ _) (pointAdd_congr (hII v _) (pointEquiv_refl _)))
    (fun _ => stateEquiv_symm ⟨pointAdd_zero _, pointAdd_zero _⟩) n i j

end Principia1713.Laws
