import BarrowLib.Polygon.CommonMotion
import NewtonLimitDynamics.Historical.LawI
import NewtonLimitDynamics.Historical.LawII

/-! Historical result: laws_corollary_v.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
Each edition retains its exact source statement and proof.
-/

/-! NATP00090. Lex 3: the same statement as a law, without proof. -/
/-! Witness: NATP00090.
Source: docs/m1/NATP00090.xml
SHA-256: 790b468987fd8c7716d9d43197ec3a724f7f581ec8b6ed3998edc191b951f998
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par7
Anchor URLs: NATP00090.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par7
Proof-step correspondence: In this witness the statement is Lex 3, a law given without proof; the deleted "Hypoth" before the supralinear "Lex" records an earlier label as a hypothesis. It is a premise of this witness, so there is no proof to formalize. No Lean theorem is attached to this witness; the 1687 and 1713 sections prove the printed corollary from each edition's printed Laws.
-/
/- LATIN BEGIN NATP00090.par7
[del: Hypoth] [add: Lex] 3. Corporum dato spatio inclusorum eosdem esse motus inter se sive spatium illud quiescat sive moveat id perpetuò et uniformiter in directum abs motu circulari.
LATIN END NATP00090.par7 -/

/-! 1687 witness.
Source: docs/m1/NATP00076.xml
SHA-256: fc2984820b61f64fdbf5efe1142ea8cf5458b75dd54fc6525f73ee705a8a9b1c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par20
Anchor URLs: NATP00076.par20 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par20; NATP00076.par21 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par21
Proof-step correspondence: The resting and moving cases share one cell schedule and one impulse rule. Impulses arise from the table of relative positions and velocities ("ex his summis vel differentiis oriuntur congressus"); vector differences represent both the differences of like-directed motions and the sums of opposed ones. Equal relative tables give equal calibrated impulses, and the edition's Law II predicate adds each impulse to the body's velocity in both cases ("æquales erunt congressuum effectus"). Supplied Law I inertia carries each body between impulses. "Ex hypothesi" supplies equal initial relative tables in the two cases, the premise of `corollary5_motions_inter_se`; the mutual relative states then agree at every cell boundary. Reading the moving space as every resting state plus the space's displacement and velocity satisfies that premise, and `corollary5_relative_to_space` then also compares each body with the uniformly moving space itself. A translated space has no circular motion. Two Galilean premises stay explicit: velocities compose by vector addition and both cases share one time. Impulses at cell boundaries stand for the collisions; contact geometry and continuous trajectories are not derived.
Historical dependency ledger for this exact witness:
- P1687.Law2 → P1687.LawCor5; passage NATP00076.par21 ("per Legem 2"); witness Axiomata Sive Leges Motus (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par21; status explicit_dependency; confidence high.
- P1687.Law1 → P1687.LawCor5; passage NATP00076.par21 (motion between collisions, for which no law is cited); witness Axiomata Sive Leges Motus (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par21; status editorial_interpretation; confidence medium.
-/
/- LATIN BEGIN NATP00076.par20
Corporum dato spatio inclusorum ijdem sunt motus inter se, sive spatium illud quiescat, sive moveatur idem uniformiter in directum absq; motu circulari.
LATIN END NATP00076.par20 -/
/- LATIN BEGIN NATP00076.par21
Nam differentiæ motuum tendentium ad eandem partem, & summæ tendentium ad contrarias, ea dem sunt sub initio in utroq; casu (ex hypothesi) & ex his summis vel differentiis oriuntur congressus & impetus quibus corpora se mutuo feriunt. Ergo per Legem 2 æquales erunt congressuum effectus in utroq; casu, & propterea manebunt motus inter se in uno casu æquales motibus inter se in altero. Idem comprobatur experimento luculento. Motus omnes eodem modo se habent in Navi, sive ea quiescat, sive moveatur uniformiter in directum.
LATIN END NATP00076.par21 -/

namespace Principia1687.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision CommonMotion

/-- Laws Corollary V at every cell boundary. Each body in a space displaced by
`c` and moving uniformly in a straight line with velocity `w` has, relative to
that space, the state it has in the resting space. Impulses depend only on
the bodies' relative states; inertia and calibrated additive change are this
edition's explicit premises. -/
theorem corollary5_relative_to_space {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 : ι → State) (c w : Point) (n : Nat) (i : ι) :
    stateEquiv
      (stateSub (run motion dt (fun k D j v => update v (kick k D j)) (boost S0 c w) n i)
        (ZeroForce.inertialAt c w (elapsedTime dt n), w))
      (run motion dt (fun k D j v => update v (kick k D j)) S0 n i) :=
  stateEquiv_trans
    (stateSub_congr (stateEquiv_refl _) (stateEquiv_symm (commonRun_uniform c w dt n)))
    (relative_to_common motion dt kick _ _ (fun _ => ZeroForce.zeroPoint) (c, w) S0
      (boost S0 c w) hI hK (fun _ _ _ v => hII v _)
      (fun _ _ _ v => pointEquiv_trans (hII v _) (pointEquiv_symm (pointAdd_zero _)))
      (fun _ => stateEquiv_refl _) n i)

/-- "ijdem sunt motus inter se": when the initial relative tables agree, as
Newton's "ex hypothesi" asserts for the resting and moving cases, the bodies'
mutual relative positions and velocities agree at every cell boundary. -/
theorem corollary5_motions_inter_se {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 T0 : ι → State)
    (h0 : ∀ i j, stateEquiv (relative T0 i j) (relative S0 i j)) (n : Nat) (i j : ι) :
    stateEquiv
      (relative (run motion dt (fun k D l v => update v (kick k D l)) T0 n) i j)
      (relative (run motion dt (fun k D l v => update v (kick k D l)) S0 n) i j) :=
  relative_autonomous motion dt kick _ _ (fun _ => ZeroForce.zeroPoint)
    (fun _ => ZeroForce.zeroPoint) T0 S0 hI hK
    (fun _ _ _ v => pointEquiv_trans (hII v _) (pointEquiv_symm (pointAdd_zero _)))
    (fun _ _ _ v => pointEquiv_trans (hII v _) (pointEquiv_symm (pointAdd_zero _)))
    h0 n i j

end Principia1687.Laws

/-! 1713 witness.
Source: docs/m1/NATP00081.xml
SHA-256: 5c72c73d9f396d3b34475543fa7cd158ab29006fb43fa35bc63df9b7e4be6bfe
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par20
Anchor URLs: NATP00081.par20 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par20; NATP00081.par21 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par21
Proof-step correspondence: The resting and moving cases share one cell schedule and one impulse rule. Impulses arise from the table of relative positions and velocities ("ex his summis vel differentiis oriuntur congressus"); vector differences represent both the differences of like-directed motions and the sums of opposed ones. Equal relative tables give equal calibrated impulses, and the edition's Law II predicate adds each impulse to the body's velocity in both cases ("æquales erunt congressuum effectus"). Supplied Law I inertia carries each body between impulses. "Ex hypothesi" supplies equal initial relative tables in the two cases, the premise of `corollary5_motions_inter_se`; the mutual relative states then agree at every cell boundary. Reading the moving space as every resting state plus the space's displacement and velocity satisfies that premise, and `corollary5_relative_to_space` then also compares each body with the uniformly moving space itself. A translated space has no circular motion. Two Galilean premises stay explicit: velocities compose by vector addition and both cases share one time. Impulses at cell boundaries stand for the collisions; contact geometry and continuous trajectories are not derived.
Historical dependency ledger for this exact witness:
- P1713.Law2 → P1713.LawCor5; passage NATP00081.par21 ("per Legem II"); witness Axiomata Sive Leges Motus (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par21; status explicit_dependency; confidence high.
- P1713.Law1 → P1713.LawCor5; passage NATP00081.par21 (motion between collisions, for which no law is cited); witness Axiomata Sive Leges Motus (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par21; status editorial_interpretation; confidence medium.
-/
/- LATIN BEGIN NATP00081.par20
Corporum dato spatio inclusorum iidem sunt motus inter se, sive spatium illud quiescat, sive moveatur idem uniformiter in directum absque motu circulari.
LATIN END NATP00081.par20 -/
/- LATIN BEGIN NATP00081.par21
Nam differentiæ motuum tendentium ad eandem partem, & summæ tendentium ad contrarias, ea dem sunt sub initio in utroq; casu (ex hypothesi) & ex his summis vel differentiis oriuntur congressus & impetus quibus corpora se mutuo feriunt. Ergo per Legem II æquales erunt congressuum effectus in utroq; casu; & propterea manebunt motus inter se in uno casu æquales motibus inter se in altero. Idem comprobatur experimento luculento. Motus omnes eodem modo se habent in Navi, sive ea quiescat, sive moveatur uniformiter in directum.
LATIN END NATP00081.par21 -/

namespace Principia1713.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision CommonMotion

/-- Laws Corollary V at every cell boundary. Each body in a space displaced by
`c` and moving uniformly in a straight line with velocity `w` has, relative to
that space, the state it has in the resting space. Impulses depend only on
the bodies' relative states; inertia and calibrated additive change are this
edition's explicit premises. -/
theorem corollary5_relative_to_space {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 : ι → State) (c w : Point) (n : Nat) (i : ι) :
    stateEquiv
      (stateSub (run motion dt (fun k D j v => update v (kick k D j)) (boost S0 c w) n i)
        (ZeroForce.inertialAt c w (elapsedTime dt n), w))
      (run motion dt (fun k D j v => update v (kick k D j)) S0 n i) :=
  stateEquiv_trans
    (stateSub_congr (stateEquiv_refl _) (stateEquiv_symm (commonRun_uniform c w dt n)))
    (relative_to_common motion dt kick _ _ (fun _ => ZeroForce.zeroPoint) (c, w) S0
      (boost S0 c w) hI hK (fun _ _ _ v => hII v _)
      (fun _ _ _ v => pointEquiv_trans (hII v _) (pointEquiv_symm (pointAdd_zero _)))
      (fun _ => stateEquiv_refl _) n i)

/-- "iidem sunt motus inter se": when the initial relative tables agree, as
Newton's "ex hypothesi" asserts for the resting and moving cases, the bodies'
mutual relative positions and velocities agree at every cell boundary. -/
theorem corollary5_motions_inter_se {ι : Type}
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (dt : Nat → Fraction) (kick : Nat → (ι → ι → State) → ι → Point)
    (hK : RelativeKick kick) (S0 T0 : ι → State)
    (h0 : ∀ i j, stateEquiv (relative T0 i j) (relative S0 i j)) (n : Nat) (i j : ι) :
    stateEquiv
      (relative (run motion dt (fun k D l v => update v (kick k D l)) T0 n) i j)
      (relative (run motion dt (fun k D l v => update v (kick k D l)) S0 n) i j) :=
  relative_autonomous motion dt kick _ _ (fun _ => ZeroForce.zeroPoint)
    (fun _ => ZeroForce.zeroPoint) T0 S0 hI hK
    (fun _ _ _ v => pointEquiv_trans (hII v _) (pointEquiv_symm (pointAdd_zero _)))
    (fun _ _ _ v => pointEquiv_trans (hII v _) (pointEquiv_symm (pointAdd_zero _)))
    h0 n i j

end Principia1713.Laws
