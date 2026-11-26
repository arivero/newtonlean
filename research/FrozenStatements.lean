import NewtonLimitDynamics
import research.RationalTimeSlope

/-!
Frozen statements (newtonlean issue 6). Verification layer only: this module
proves nothing new, earns no completion credit and is imported by no library.
`lake build` compiles it as part of the default `Verification` target.

Each `example` writes out the complete type of a named theorem as it stood at
`623afe6` (the issue 3 uniform and Lipschitz additions: as added) and closes
it with `@` and the fully qualified name, so a later change of statement,
hypothesis or binder type fails this build. The types were printed from the
compiled environment with fully qualified names and explicit numeral types,
then compiled back; two statements whose printed form loses a
structure type are written by hand and marked. The definitional checks at the
end fix the reviewed definitions by `rfl` or `Iff.rfl`.

Coverage:
* Proposition I: `sampled_radial_sector_area` and
  `mechanical_between_area_approximation` for NATP00090 (manuscript
  `SectorFan.AreaRules`), 1687 and 1713 (printed
  `RadialSector.DifferenceAreaRules`), each with its separate between-area
  hypothesis; NATP00089's finite equal-area and block statements under their
  own names.
* Lemmas I–III: every public theorem of the 1687 and 1713 sections, including
  `given_time_exhaustion` (1687), `finite_time_before_end_exhaustion` (1713)
  and each edition's equal-width (II) and unequal-width (III) gap and
  area-ratio statements.
* Issue 2–5 diagnostics: every public theorem of `CoupledPolygons`,
  `UniformRadialSector`, `QuadraticSector`, `ReciprocalPhase` and
  `ArealBounds`, the two lower-bound mesh lemmas of `MotionSampling`, and
  `RationalTimeSlope.common_seven`.
-/

/-! BarrowLib.Polygon.MotionSampling -/
example :
    ∀ (a : NewtonLimitDynamics.Polygon.TimeSubdivision.Point → NewtonLimitDynamics.Polygon.TimeSubdivision.Point)
      (C T P V : NewtonLimitDynamics.Fraction) (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      {l r : NewtonLimitDynamics.Fraction} (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r)
      (q : Nat → NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point)
      (j k : Nat),
      k < p.count →
        ∀ (m : NewtonLimitDynamics.Fraction) (hm : (0 : Int) < m.num),
          (∀ (i : Nat), i ≤ p.count → m.le (g (p.nodes i))) →
            (0 : Int) ≤ C.num →
              (0 : Int) ≤ T.num →
                (0 : Int) ≤ P.num →
                  (NewtonLimitDynamics.Polygon.PointBounds.pointNorm (q k).fst).le P →
                    (NewtonLimitDynamics.Polygon.PointBounds.pointNorm (q k).snd).le V →
                      (∀ (i : Nat),
                          i ≤ p.count →
                            NewtonLimitDynamics.Polygon.TimeSubdivision.pointEquiv (q i).fst
                              (NewtonLimitDynamics.Polygon.RadialSector.ray (g (p.nodes i)) (p.nodes i))) →
                        (NewtonLimitDynamics.Polygon.FiniteEstimates.stateDistance (q (k + (1 : Nat)))
                                (NewtonLimitDynamics.Polygon.FiniteEstimates.cell a
                                  (NewtonLimitDynamics.Polygon.HarmonicDyadic.duration T j) (q k))).le
                            (NewtonLimitDynamics.Polygon.MotionSampling.remainder C T j) →
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.width p k).le
                            ((NewtonLimitDynamics.Polygon.MotionSampling.slopeCoefficient m P V C T hm).mul
                              (NewtonLimitDynamics.Polygon.HarmonicDyadic.duration T j)) :=
  @NewtonLimitDynamics.Polygon.MotionSampling.radial_width_bound_lower

example :
    ∀ (a : NewtonLimitDynamics.Polygon.TimeSubdivision.Point → NewtonLimitDynamics.Polygon.TimeSubdivision.Point)
      (C T P V : NewtonLimitDynamics.Fraction) (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (l r : NewtonLimitDynamics.Fraction) (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r)
      (q :
        Nat → Nat → NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point)
      (m : NewtonLimitDynamics.Fraction),
      (0 : Int) < m.num →
        (∀ (j i : Nat), i ≤ (parts j).count → m.le (g ((parts j).nodes i))) →
          (0 : Int) ≤ C.num →
            (0 : Int) ≤ T.num →
              (0 : Int) ≤ P.num →
                (0 : Int) ≤ V.num →
                  (∀ (j : Nat), (parts j).count = NewtonLimitDynamics.Polygon.HarmonicDyadic.blocks j) →
                    (∀ (j k : Nat),
                        k < NewtonLimitDynamics.Polygon.HarmonicDyadic.blocks j →
                          (NewtonLimitDynamics.Polygon.PointBounds.pointNorm (q j k).fst).le P) →
                      (∀ (j k : Nat),
                          k < NewtonLimitDynamics.Polygon.HarmonicDyadic.blocks j →
                            (NewtonLimitDynamics.Polygon.PointBounds.pointNorm (q j k).snd).le V) →
                        (∀ (j k : Nat),
                            k ≤ (parts j).count →
                              NewtonLimitDynamics.Polygon.TimeSubdivision.pointEquiv (q j k).fst
                                (NewtonLimitDynamics.Polygon.RadialSector.ray (g ((parts j).nodes k))
                                  ((parts j).nodes k))) →
                          (∀ (j k : Nat),
                              k < NewtonLimitDynamics.Polygon.HarmonicDyadic.blocks j →
                                (NewtonLimitDynamics.Polygon.FiniteEstimates.stateDistance (q j (k + (1 : Nat)))
                                      (NewtonLimitDynamics.Polygon.FiniteEstimates.cell a
                                        (NewtonLimitDynamics.Polygon.HarmonicDyadic.duration T j) (q j k))).le
                                  (NewtonLimitDynamics.Polygon.MotionSampling.remainder C T j)) →
                            NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                              fun (j : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts j) :=
  @NewtonLimitDynamics.Polygon.MotionSampling.radial_mesh_vanishes_lower


/-! BarrowLib.Polygon.QuadraticSector -/
example :
    (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart (NewtonLimitDynamics.Fraction.ofInt (0 : Int))).equiv
        (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) ∧
      (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).equiv
          (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) ∧
        (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
              { num := (1 : Int), den := (2 : Int), den_pos := of_decide_eq_true (id (Eq.refl Bool.true)) }).equiv
          { num := (5 : Int), den := (4 : Int), den_pos := of_decide_eq_true (id (Eq.refl Bool.true)) } :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart_values

example :
    ¬NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
          (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) ∧
      ¬∀ (x y : NewtonLimitDynamics.Fraction),
          (NewtonLimitDynamics.Fraction.ofInt (0 : Int)).le x →
            x.le y →
              y.le (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) →
                (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart y).le
                  (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart x) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart_not_monotone

example :
    ∃ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
      NewtonLimitDynamics.Polygon.RadialSector.sector NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
          (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) x ∧
        ¬NewtonLimitDynamics.Polygon.UniformRadialSector.upperCaps
            NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart NewtonLimitDynamics.Polygon.QuadraticSector.oneCell
            { num := (1 : Int), den := (10 : Int), den_pos := of_decide_eq_true (id (Eq.refl Bool.true)) } x :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.coarse_partition_fails

example :
    (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
        NewtonLimitDynamics.Polygon.SectorFan.Triangle
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (1 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (1 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
            x →
          NewtonLimitDynamics.Polygon.SectorFan.Triangle
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (2 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (1 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
            x) ∧
      ∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
        NewtonLimitDynamics.Polygon.SectorFan.Triangle
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (2 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (1 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
            x →
          NewtonLimitDynamics.Polygon.SectorFan.Triangle
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (2 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))
            (NewtonLimitDynamics.Polygon.RadialSector.ray (NewtonLimitDynamics.Fraction.ofInt (2 : Int))
              (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
            x :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.falling_scales_enclosed

example :
    (NewtonLimitDynamics.Polygon.MonotoneRectangles.width NewtonLimitDynamics.Polygon.QuadraticSector.repeatedNode
            (1 : Nat)).equiv
        (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) ∧
      ∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
        NewtonLimitDynamics.Polygon.RadialSector.strips NewtonLimitDynamics.Polygon.QuadraticSector.repeatedNode
            (fun (_ : Nat) => NewtonLimitDynamics.Fraction.ofInt (1 : Int))
            NewtonLimitDynamics.Polygon.QuadraticSector.repeatedNode.count x ↔
          NewtonLimitDynamics.Polygon.RadialSector.sector
            (fun (_ : NewtonLimitDynamics.Fraction) => NewtonLimitDynamics.Fraction.ofInt (1 : Int))
            (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) x :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.repeated_node_enclosed

example :
    ∀ (n : Nat) (hn : (0 : Nat) < n) (i : Nat),
      ((NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn).nodes i).toRat = ↑i / ↑n :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.node_toRat

example :
    ∀ (t : NewtonLimitDynamics.Fraction),
      (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart t).toRat = (1 : Rat) + t.toRat * ((1 : Rat) - t.toRat) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.chart_toRat

example :
    ∀ (n : Nat) (hn : (0 : Nat) < n) (k : Nat),
      (NewtonLimitDynamics.Polygon.SectorFan.areaSum
            (fun (i : Nat) =>
              NewtonLimitDynamics.Polygon.RadialSector.ray
                (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
                  ((NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn).nodes i))
                ((NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn).nodes i))
            k).toRat =
        NewtonLimitDynamics.Polygon.QuadraticSector.partialArea ↑k ↑n :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.partial_chord_sum

example :
    ∀ (n : Nat) (hn : (0 : Nat) < n),
      (NewtonLimitDynamics.Polygon.RadialSector.chordArea NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
              (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn)).toRat *
          ((60 : Rat) * (↑n * ↑n * ↑n * ↑n)) =
        (41 : Rat) * (↑n * ↑n * ↑n * ↑n) - (15 : Rat) * (↑n * ↑n) + (4 : Rat) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_chord_area

example :
    (NewtonLimitDynamics.Polygon.RadialSector.chordArea NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
            (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition (1 : Nat)
              (of_decide_eq_true (id (Eq.refl Bool.true))))).toRat =
        (1 / 2 : Rat) ∧
      (NewtonLimitDynamics.Polygon.RadialSector.chordArea NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
            (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition (2 : Nat)
              (of_decide_eq_true (id (Eq.refl Bool.true))))).toRat =
        (5 / 8 : Rat) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_chord_area_one_two

example :
    ∀ (al be : NewtonLimitDynamics.Fraction),
      (NewtonLimitDynamics.Fraction.ofInt (0 : Int)).le al →
        al.le be →
          be.le (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) →
            ∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
              NewtonLimitDynamics.Polygon.SectorFan.Triangle
                  (NewtonLimitDynamics.Polygon.RadialSector.ray
                    (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart al) al)
                  (NewtonLimitDynamics.Polygon.RadialSector.ray
                    (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart be) be)
                  x →
                NewtonLimitDynamics.Polygon.RadialSector.sector NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
                  al be x :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_chord_inside

example :
    ∀
      (p :
        NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition (NewtonLimitDynamics.Fraction.ofInt (0 : Int))
          (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
      (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
      NewtonLimitDynamics.Polygon.RadialSector.chordFigure NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart p x →
        NewtonLimitDynamics.Polygon.RadialSector.sector NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
          (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) x :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_chords_in_sector

example :
    ∀ (t : NewtonLimitDynamics.Fraction),
      (NewtonLimitDynamics.Fraction.ofInt (0 : Int)).le t →
        t.le (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) →
          (NewtonLimitDynamics.Fraction.ofInt (1 : Int)).le (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart t) ∧
            (NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart t).le
              { num := (5 : Int), den := (4 : Int), den_pos := of_decide_eq_true (id (Eq.refl Bool.true)) } :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_bounds

example :
    NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn
      (fun (t : NewtonLimitDynamics.Fraction) => (t, NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart t))
      (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_uniform

example :
    ∀ (n : Nat) (hn : (0 : Nat) < n),
      (NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth
            (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn)).le
        { num := (1 : Int), den := ↑n,
          den_pos :=
            Decidable.byContradiction fun (a : ¬(0 : Int) < ↑n) =>
              NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition._proof_1 n hn a } :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.uniform_maxWidth

-- Written by hand: the printed structure literal omits its type and its
-- automatically generated positivity proof.
example :
    ∀ (d e : NewtonLimitDynamics.Fraction), (0 : Int) < d.num → (0 : Int) < e.num →
      ∃ (n : Nat), ∃ (hn : (0 : Nat) < n),
        NewtonLimitDynamics.Fraction.lt ⟨(1 : Int), (n : Int), by omega⟩ d ∧
          NewtonLimitDynamics.Fraction.lt ⟨(1 : Int), (n : Int), by omega⟩ e :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.exists_fine

example :
    ∀ (n : Nat) (hn : (0 : Nat) < n),
      (41 / 60 : Rat) - (1 : Rat) / ↑n ≤
          (NewtonLimitDynamics.Polygon.RadialSector.chordArea NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
              (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn)).toRat ∧
        (NewtonLimitDynamics.Polygon.RadialSector.chordArea NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
              (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn)).toRat <
          (41 / 60 : Rat) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_chord_window

example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules) (A : NewtonLimitDynamics.Fraction),
      area.HasArea
          (NewtonLimitDynamics.Polygon.RadialSector.sector NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
            (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
          A →
        A.toRat = (41 / 60 : Rat) :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_sector_area

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RadialSector.DifferenceAreaRules) (A : NewtonLimitDynamics.Fraction),
      area.HasArea
          (NewtonLimitDynamics.Polygon.RadialSector.sector NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
            (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int)))
          A →
        ∀ (n : Nat) (hn : (0 : Nat) < n),
          ∃ (B : NewtonLimitDynamics.Fraction),
            area.HasArea
                (NewtonLimitDynamics.Polygon.RadialSector.between NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
                  (NewtonLimitDynamics.Polygon.QuadraticSector.uniformPartition n hn))
                B ∧
              B.toRat * ((60 : Rat) * (↑n * ↑n * ↑n * ↑n)) = (15 : Rat) * (↑n * ↑n) - (4 : Rat) ∧ (0 : Rat) < B.toRat :=
  @NewtonLimitDynamics.Polygon.QuadraticSector.quadratic_between_area


/-! BarrowLib.Polygon.UniformRadialSector -/
example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b R S : NewtonLimitDynamics.Fraction),
      a.le b →
        (0 : Int) ≤ R.num →
          (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) < (g t).num) →
            (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → R.le (g t)) →
              (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (g t).le S) →
                (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                    NewtonLimitDynamics.Polygon.SectorFan.Triangle (NewtonLimitDynamics.Polygon.RadialSector.ray R a)
                        (NewtonLimitDynamics.Polygon.RadialSector.ray R b) x →
                      NewtonLimitDynamics.Polygon.RadialSector.sector g a b x) ∧
                  ∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                    NewtonLimitDynamics.Polygon.RadialSector.sector g a b x →
                      NewtonLimitDynamics.Polygon.SectorFan.Triangle (NewtonLimitDynamics.Polygon.RadialSector.ray S a)
                        (NewtonLimitDynamics.Polygon.RadialSector.ray S b) x :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.caps_enclosure_bounds

example :
    ∀ (R P Q S a b : NewtonLimitDynamics.Fraction),
      (0 : Int) ≤ R.num →
        (0 : Int) < P.num →
          (0 : Int) < Q.num →
            R.le P →
              R.le Q →
                P.le S →
                  Q.le S →
                    (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                        NewtonLimitDynamics.Polygon.SectorFan.Triangle (NewtonLimitDynamics.Polygon.RadialSector.ray R a)
                            (NewtonLimitDynamics.Polygon.RadialSector.ray R b) x →
                          NewtonLimitDynamics.Polygon.SectorFan.Triangle (NewtonLimitDynamics.Polygon.RadialSector.ray P a)
                            (NewtonLimitDynamics.Polygon.RadialSector.ray Q b) x) ∧
                      ∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                        NewtonLimitDynamics.Polygon.SectorFan.Triangle (NewtonLimitDynamics.Polygon.RadialSector.ray P a)
                            (NewtonLimitDynamics.Polygon.RadialSector.ray Q b) x →
                          NewtonLimitDynamics.Polygon.SectorFan.Triangle (NewtonLimitDynamics.Polygon.RadialSector.ray S a)
                            (NewtonLimitDynamics.Polygon.RadialSector.ray S b) x :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.cap_chord_enclosure_bounds

example :
    ∀ {a b : NewtonLimitDynamics.Fraction} (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b) (lo hi : Nat → NewtonLimitDynamics.Fraction),
      (∀ (i : Nat), i < p.count → (0 : Int) ≤ (lo i).num) →
        (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) < (g t).num) →
          (∀ (i : Nat),
              i < p.count →
                ∀ (t : NewtonLimitDynamics.Fraction),
                  (p.nodes i).le t → t.le (p.nodes (i + (1 : Nat))) → (lo i).le (g t) ∧ (g t).le (hi i)) →
            (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                NewtonLimitDynamics.Polygon.RadialSector.strips p lo p.count x →
                  NewtonLimitDynamics.Polygon.RadialSector.sector g a b x) ∧
              (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                  NewtonLimitDynamics.Polygon.RadialSector.sector g a b x →
                    NewtonLimitDynamics.Polygon.RadialSector.strips p hi p.count x) ∧
                (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                    NewtonLimitDynamics.Polygon.RadialSector.strips p lo p.count x →
                      NewtonLimitDynamics.Polygon.RadialSector.chordFigure g p x) ∧
                  ∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
                    NewtonLimitDynamics.Polygon.RadialSector.chordFigure g p x →
                      NewtonLimitDynamics.Polygon.RadialSector.strips p hi p.count x :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.strips_enclosure

example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules) {a b : NewtonLimitDynamics.Fraction}
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) < (g t).num) →
        area.HasArea (NewtonLimitDynamics.Polygon.RadialSector.chordFigure g p)
          (NewtonLimitDynamics.Polygon.RadialSector.chordArea g p) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.chord_area_positive

example :
    ∀ {a b : NewtonLimitDynamics.Fraction} (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b)
      (lo hi : Nat → NewtonLimitDynamics.Fraction) (E : NewtonLimitDynamics.Fraction),
      (∀ (i : Nat),
          i < p.count →
            (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference ((lo i).mul (lo i)).half
                  ((hi i).mul (hi i)).half).le
              E) →
        (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
              (NewtonLimitDynamics.Polygon.RadialSector.stripSum p lo p.count)
              (NewtonLimitDynamics.Polygon.RadialSector.stripSum p hi p.count)).le
          (E.mul (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference a b)) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.strip_gap_bound

example :
    ∀ (G eps : NewtonLimitDynamics.Fraction),
      (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
            ((NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference eps G).mul
                (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference eps G)).half
            ((G.add eps).mul (G.add eps)).half).equiv
        ((eps.add eps).mul G) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.scale_gap

example :
    ∀ {a b : NewtonLimitDynamics.Fraction} (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b) (eps : NewtonLimitDynamics.Fraction),
      (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
            (NewtonLimitDynamics.Polygon.RadialSector.stripSum p
              (NewtonLimitDynamics.Polygon.UniformRadialSector.lowerScales g p eps) p.count)
            (NewtonLimitDynamics.Polygon.RadialSector.stripSum p
              (NewtonLimitDynamics.Polygon.UniformRadialSector.upperScales g p eps) p.count)).equiv
        (NewtonLimitDynamics.Polygon.PolygonFanArea.sum
          (fun (i : Nat) =>
            (NewtonLimitDynamics.Polygon.MonotoneRectangles.width p i).mul ((eps.add eps).mul (g (p.nodes i))))
          p.count) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.caps_gap_identity

example :
    ∀ {a b : NewtonLimitDynamics.Fraction} (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b) (eps M : NewtonLimitDynamics.Fraction),
      (0 : Int) ≤ eps.num →
        (∀ (i : Nat), i < p.count → (g (p.nodes i)).le M) →
          (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                (NewtonLimitDynamics.Polygon.RadialSector.stripSum p
                  (NewtonLimitDynamics.Polygon.UniformRadialSector.lowerScales g p eps) p.count)
                (NewtonLimitDynamics.Polygon.RadialSector.stripSum p
                  (NewtonLimitDynamics.Polygon.UniformRadialSector.upperScales g p eps) p.count)).le
            (((eps.add eps).mul M).mul (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference a b)) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.caps_gap_bound

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction),
      NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
        ∀ (eps : NewtonLimitDynamics.Fraction),
          (0 : Int) < eps.num →
            ∃ (delta : NewtonLimitDynamics.Fraction),
              (0 : Int) < delta.num ∧
                ∀ (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
                  (NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth p).le delta →
                    ∀ (i : Nat),
                      i < p.count →
                        ∀ (t : NewtonLimitDynamics.Fraction),
                          (p.nodes i).le t →
                            t.le (p.nodes (i + (1 : Nat))) →
                              (NewtonLimitDynamics.Polygon.UniformRadialSector.lowerScales g p eps i).le (g t) ∧
                                (g t).le (NewtonLimitDynamics.Polygon.UniformRadialSector.upperScales g p eps i) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.fine_cell_bounds

example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b m M : NewtonLimitDynamics.Fraction),
      (0 : Int) < m.num →
        (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → m.le (g t) ∧ (g t).le M) →
          NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
            ∀ (eps : NewtonLimitDynamics.Fraction),
              (0 : Int) < eps.num →
                eps.le m →
                  ∃ (delta : NewtonLimitDynamics.Fraction),
                    (0 : Int) < delta.num ∧
                      ∀ (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth p).le delta →
                          NewtonLimitDynamics.Polygon.UniformRadialSector.CapsEnclose area g a b p eps M :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.fine_caps

example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules) {a b : NewtonLimitDynamics.Fraction}
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b) (eps M A : NewtonLimitDynamics.Fraction),
      NewtonLimitDynamics.Polygon.UniformRadialSector.CapsEnclose area g a b p eps M →
        area.HasArea (NewtonLimitDynamics.Polygon.RadialSector.sector g a b) A →
          (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference A
                  (NewtonLimitDynamics.Polygon.RadialSector.chordArea g p)).abs.le
            (NewtonLimitDynamics.Polygon.UniformRadialSector.capsGap g p eps) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.chord_error_caps

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RadialSector.DifferenceAreaRules) {a b : NewtonLimitDynamics.Fraction}
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b) (eps M : NewtonLimitDynamics.Fraction),
      NewtonLimitDynamics.Polygon.UniformRadialSector.CapsEnclose area.toSectorAreaRules g a b p eps M →
        (∀ (x : NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
            NewtonLimitDynamics.Polygon.RadialSector.between g p x →
              NewtonLimitDynamics.Polygon.UniformRadialSector.capsCollar g p eps x) ∧
          area.HasArea (NewtonLimitDynamics.Polygon.UniformRadialSector.capsCollar g p eps)
              (NewtonLimitDynamics.Polygon.UniformRadialSector.capsGap g p eps) ∧
            ∀ (B : NewtonLimitDynamics.Fraction),
              area.HasArea (NewtonLimitDynamics.Polygon.RadialSector.between g p) B →
                (0 : Int) ≤ B.num ∧ B.le (NewtonLimitDynamics.Polygon.UniformRadialSector.capsGap g p eps) :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.between_caps

example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b m M : NewtonLimitDynamics.Fraction),
      a.le b →
        (0 : Int) < m.num →
          (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → m.le (g t) ∧ (g t).le M) →
            NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a
                b →
              ∀ (eta : NewtonLimitDynamics.Fraction),
                (0 : Int) < eta.num →
                  ∃ (eps : NewtonLimitDynamics.Fraction),
                    ∃ (delta : NewtonLimitDynamics.Fraction),
                      (0 : Int) < eps.num ∧
                        eps.le m ∧
                          (0 : Int) < delta.num ∧
                            ∀ (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth p).le delta →
                                NewtonLimitDynamics.Polygon.UniformRadialSector.CapsEnclose area g a b p eps M ∧
                                  (NewtonLimitDynamics.Polygon.UniformRadialSector.capsGap g p eps).lt eta :=
  @NewtonLimitDynamics.Polygon.UniformRadialSector.caps_exhaust


/-! ModernLib.Diagnostic.ArealBounds -/
example :
    NewtonLimitDynamics.Polygon.CentralSchedule.central NewtonLimitDynamics.Diagnostic.ArealBounds.freeField :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.freeField_central

example :
    NewtonLimitDynamics.Polygon.CentralSchedule.central NewtonLimitDynamics.Diagnostic.ArealBounds.hookeField :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.hookeField_central

example :
    ∀ (ds : List NewtonLimitDynamics.Fraction)
      (s : NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
      (NewtonLimitDynamics.Polygon.CentralSchedule.swept NewtonLimitDynamics.Diagnostic.ArealBounds.freeField ds s).equiv
        (NewtonLimitDynamics.Polygon.CentralSchedule.swept NewtonLimitDynamics.Diagnostic.ArealBounds.hookeField ds s) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.equal_swept_areas

example :
    ¬NewtonLimitDynamics.Polygon.TimeSubdivision.pointEquiv
        (NewtonLimitDynamics.Polygon.CentralSchedule.schedule NewtonLimitDynamics.Diagnostic.ArealBounds.freeField
            [NewtonLimitDynamics.Fraction.ofInt (1 : Int), NewtonLimitDynamics.Fraction.ofInt (1 : Int)]
            NewtonLimitDynamics.Diagnostic.ArealBounds.start).fst
        (NewtonLimitDynamics.Polygon.CentralSchedule.schedule NewtonLimitDynamics.Diagnostic.ArealBounds.hookeField
            [NewtonLimitDynamics.Fraction.ofInt (1 : Int), NewtonLimitDynamics.Fraction.ofInt (1 : Int)]
            NewtonLimitDynamics.Diagnostic.ArealBounds.start).fst :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.different_polygons

example :
    ∀ (m k r v : Rat), r ≠ (0 : Rat) → m * (v * v) / r = k / (r * r * r) → m * r * v * (m * r * v) = m * k :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.circular_action

example :
    ∀ (m k L E r rdot : Rat),
      (0 : Rat) < m →
        r ≠ (0 : Rat) →
          m * k < L * L →
            NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m k L E r rdot →
              (0 : Rat) < E ∧ L * L - m * k ≤ (2 : Rat) * m * (r * r) * E :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.supercritical_bound

example :
    ∀ (m k L E r rdot : Rat),
      (0 : Rat) < m →
        r ≠ (0 : Rat) →
          L * L < m * k →
            (0 : Rat) ≤ E → NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m k L E r rdot → rdot ≠ (0 : Rat) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.subcritical_no_apsis

example :
    ∀ (m k L E r rdot : Rat),
      NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m k L E r rdot →
        (2 : Rat) * m * (r * r) * -E ≤ m * k - L * L :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.subcritical_bounded

example :
    ∀ (m k L E r rdot : Rat),
      (0 : Rat) < m →
        r ≠ (0 : Rat) →
          L * L = m * k →
            NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m k L E r rdot → (rdot = (0 : Rat) ↔ E = (0 : Rat)) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.critical_radial

example :
    ∀ (m k L r rdot : Rat), NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m k L (0 : Rat) r rdot → L * L ≤ m * k :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.zero_energy_upper

example :
    ∀ (m k L E r : Rat),
      (0 : Rat) < m →
        r ≠ (0 : Rat) →
          NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m k L E r (0 : Rat) →
            (E < (0 : Rat) ↔ L * L < m * k) ∧ ((0 : Rat) < E ↔ m * k < L * L) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.apsis_energy_sign

example :
    ∀ (m c eps : Rat),
      (0 : Rat) < m →
        (0 : Rat) < c →
          (0 : Rat) < eps →
            ∃ (L : Rat),
              ∃ (rdot : Rat),
                (0 : Rat) < L ∧
                  L < eps ∧
                    rdot < (0 : Rat) ∧
                      L * L < c * c ∧
                        NewtonLimitDynamics.Diagnostic.ArealBounds.EnergyRelation m (c * c / m) L (0 : Rat) (1 : Rat) rdot :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.small_action_infall

example :
    ∀ (G M r hbar c lam twoA : Rat),
      G ≠ (0 : Rat) →
        c ≠ (0 : Rat) → twoA * twoA = G * M * r → twoA * twoA = lam * lam * (hbar * G / c) → M * c * r = lam * lam * hbar :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.planck_areal_radius

example :
    ∀ (m hbar G c lam twoA : Rat),
      c ≠ (0 : Rat) → twoA * twoA = lam * lam * (hbar * G / c) → m * twoA * (m * twoA) * c = lam * lam * (m * m * hbar * G) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.test_body_action

example :
    ∀ (m hbar G c twoA : Rat),
      c ≠ (0 : Rat) →
        hbar ≠ (0 : Rat) → twoA * twoA = hbar * G / c → (m * twoA * (m * twoA) = hbar * hbar ↔ m * m * G = hbar * c) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.action_is_hbar_iff

example :
    ∀ (m kappa r v : Rat), r ≠ (0 : Rat) → m * (v * v) / r = kappa / (r * r * r) → m * (r * v * (r * v)) = kappa :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.gauss_five

example :
    ∀ (m kappa r v : Rat), r ≠ (0 : Rat) → m * (v * v) / r = kappa / (r * r) → m * (r * v * (r * v)) = kappa * r :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.gauss_four

example :
    ∀ (n m M G hbar c r : Rat),
      (0 : Rat) < hbar →
        (0 : Rat) < G →
          (0 : Rat) < m → n * hbar * (n * hbar) = m * m * G * M * r → (hbar ≤ M * c * r ↔ G * (m * m) ≤ n * n * hbar * c) :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.bohr_bound_iff

example :
    ∀ (G M r v hbar c : Rat), v * v * r = G * M → M * c * r = hbar → v * v * hbar = G * M * M * c :=
  @NewtonLimitDynamics.Diagnostic.ArealBounds.matched_speed


/-! ModernLib.Diagnostic.CoupledPolygons -/
example :
    ∀ (a : NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.pairTerm a a = NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.zero :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.pairTerm_self

example :
    ∀ (κ : Rat) (xs : List NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.vsum
          (List.map
            (fun (xi : NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3) =>
              xi.cross (NewtonLimitDynamics.Diagnostic.CoupledPolygons.force κ xs xi))
            xs) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.zero :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.torque_zero

example :
    ∀ (m h : Rat)
      (s : NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3 × NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3),
      (NewtonLimitDynamics.Diagnostic.CoupledPolygons.driftPos m h s).cross s.snd = s.fst.cross s.snd :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.drift_cross

example :
    ∀ (κ m h : Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss (NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell κ m h st) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss st :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell_gauss

example :
    ∀ (κ m : Rat) (hs : List Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.schedule κ m hs st) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss st :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.schedule_gauss

example :
    ∀ (m h : Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.vsum
          (List.map (NewtonLimitDynamics.Diagnostic.CoupledPolygons.triangle m h) st) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.smul (h / ((2 : Rat) * m))
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss st) :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.triangle_sum

example :
    ∀ (κ m : Rat) (hs : List Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.swept κ m hs st =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.smul
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.elapsed hs / ((2 : Rat) * m))
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss st) :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.swept_eq

example :
    ∀ (κ m h : Rat),
      List.map (NewtonLimitDynamics.Diagnostic.CoupledPolygons.triangle m h)
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell κ m h
            NewtonLimitDynamics.Diagnostic.CoupledPolygons.exampleStart) =
        [{ x := (0 : Rat), y := (0 : Rat), z := κ * h * h / ((2 : Rat) * m) },
          { x := (0 : Rat), y := (0 : Rat), z := -(κ * h * h / ((2 : Rat) * m)) }] :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.example_areas

example :
    List.map (NewtonLimitDynamics.Diagnostic.CoupledPolygons.triangle (3 / 2 : Rat) (1 / 5 : Rat))
        (NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell (9 / 4 : Rat) (3 / 2 : Rat) (1 / 5 : Rat)
          NewtonLimitDynamics.Diagnostic.CoupledPolygons.exampleStart) =
      [{ x := (0 : Rat), y := (0 : Rat), z := (3 / 100 : Rat) }, { x := (0 : Rat), y := (0 : Rat), z := (-3 / 100 : Rat) }] :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.example_areas_numeric

-- Written by hand: the printed anonymous constructors omit their type.
example :
    (⟨(0 : Rat), (0 : Rat), (3 / 100 : Rat)⟩ : NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3) ≠
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.zero ∧
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.add ⟨(0 : Rat), (0 : Rat), (3 / 100 : Rat)⟩
          ⟨(0 : Rat), (0 : Rat), (-3 / 100 : Rat)⟩ =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.zero :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.example_nonzero_cancel

example :
    ∀ (κ m h s : Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell κ m h
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.dilate s st) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.dilate s
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell κ m (s * h) st) :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.cell_dilate

example :
    ∀ (κ m s : Rat) (hs : List Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.schedule κ m hs
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.dilate s st) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.dilate s
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.schedule κ m (List.map (fun (x : Rat) => s * x) hs) st) :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.schedule_dilate

example :
    ∀ (s : Rat) (st : NewtonLimitDynamics.Diagnostic.CoupledPolygons.State),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss (NewtonLimitDynamics.Diagnostic.CoupledPolygons.dilate s st) =
        NewtonLimitDynamics.Diagnostic.CoupledPolygons.Vec3.smul (s * s * s)
          (NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss st) :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.gauss_dilate

example :
    ∀ (s : Rat) (hs : List Rat),
      NewtonLimitDynamics.Diagnostic.CoupledPolygons.elapsed (List.map (fun (x : Rat) => s * x) hs) =
        s * NewtonLimitDynamics.Diagnostic.CoupledPolygons.elapsed hs :=
  @NewtonLimitDynamics.Diagnostic.CoupledPolygons.elapsed_scale


/-! ModernLib.Diagnostic.ReciprocalPhase -/
example :
    ∀ (mA mB F k h : Rat),
      mA ≠ (0 : Rat) →
        mB ≠ (0 : Rat) →
          ∀ (z : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.State),
            mA * (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell mA mB F k h z).vA +
                mB * (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell mA mB F k h z).vB =
              mA * z.vA + mB * z.vB :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell_momentum

example :
    ∀ (mA mB F k h : Rat) (z : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.State),
      mA * (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell mA mB F k h z).qA +
          mB * (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell mA mB F k h z).qB =
        mA * z.qA + mB * z.qB + h * (mA * z.vA + mB * z.vB) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell_centre

example :
    ∀ (mA mB nA nB dA dB : Rat),
      dA ≠ (0 : Rat) → mA * dA + mB * dB = (0 : Rat) → nA * dA + nB * dB = (0 : Rat) → mA * nB = nA * mB :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.inertia_ratio

example :
    ∀ (mA mB F k h c : Rat),
      c ≠ (0 : Rat) →
        ∀ (z : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.State),
          NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell (c * mA) (c * mB) (c * F) (c * k) h z =
            NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell mA mB F k h z :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.cell_rescale

example :
    ∀ (mA mB F k c : Rat),
      c ≠ (0 : Rat) →
        ∀ (hs : List Rat) (z : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.State),
          NewtonLimitDynamics.Diagnostic.ReciprocalPhase.schedule (c * mA) (c * mB) (c * F) (c * k) hs z =
            NewtonLimitDynamics.Diagnostic.ReciprocalPhase.schedule mA mB F k hs z :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.schedule_rescale

example :
    ∀ (sA sB : Rat) (W : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Phase) (F k : Rat),
      k ≠ (0 : Rat) → NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces sA sB W F k → sA = sB :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.hooke_equates

example :
    ∀ (s F k : Rat),
      s ≠ (0 : Rat) →
        NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces s s
          (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.springPhase s F k) F k :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.common_value_free

example :
    ∀ (sA sB F : Rat),
      sA ≠ (0 : Rat) →
        sB ≠ (0 : Rat) →
          NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces sA sB
            (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linearPhase sA sB F) F (0 : Rat) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.constant_force_free

example :
    NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces (1 : Rat) (2 : Rat)
        (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linearPhase (1 : Rat) (2 : Rat) (1 : Rat)) (1 : Rat) (0 : Rat) ∧
      (1 : Rat) ≠ (2 : Rat) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.constant_force_unequal_example

example :
    ∀ (W : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Phase),
      NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Relative W ↔
        ∀ (qA qB t : Rat), W.value (qA + t) (qB + t) = W.value qA qB :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.relative_iff_translation_invariant

example :
    ∀ (sA sB : Rat) (W : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Phase) (F k x : Rat),
      NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Relative W →
        NewtonLimitDynamics.Diagnostic.ReciprocalPhase.slope F k x ≠ (0 : Rat) →
          NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces sA sB W F k → sA = sB :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.relative_phase_equates

example :
    ∀ (sA sB F qA qB t : Rat),
      sA ≠ (0 : Rat) →
        sB ≠ (0 : Rat) →
          sA * sB *
              ((NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linearPhase sA sB F).value (qA + t) (qB + t) -
                (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linearPhase sA sB F).value qA qB) =
            F * t * (sB - sA) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linear_phase_translation

example :
    ∀ (sA sB mA mB : Rat) (W : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Phase) (F k h qA qB : Rat),
      mA ≠ (0 : Rat) →
        mB ≠ (0 : Rat) →
          NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces sA sB W F k →
            mA * -(h * (sA * W.dA qA qB) / mA) = -(h * NewtonLimitDynamics.Diagnostic.ReciprocalPhase.slope F k (qA - qB)) ∧
              mB * -(h * (sB * W.dB qA qB) / mB) = h * NewtonLimitDynamics.Diagnostic.ReciprocalPhase.slope F k (qA - qB) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.phase_impulses

example :
    ∀ (sA sB : Rat),
      NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces sA sB
        { b := (0 : Rat), c := (0 : Rat), d := (0 : Rat), e := (0 : Rat), f := (0 : Rat) } (0 : Rat) (0 : Rat) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.free_bodies_unrelated

example :
    ∀ (sA sB F k : Rat),
      sA ≠ (0 : Rat) →
        sB ≠ (0 : Rat) →
          (∀ (qA qB : Rat),
              sA * (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.hookeCovectors sA sB F k).gA qA qB =
                  NewtonLimitDynamics.Diagnostic.ReciprocalPhase.slope F k (qA - qB) ∧
                sB * (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.hookeCovectors sA sB F k).gB qA qB =
                  -NewtonLimitDynamics.Diagnostic.ReciprocalPhase.slope F k (qA - qB)) ∧
            ((NewtonLimitDynamics.Diagnostic.ReciprocalPhase.hookeCovectors sA sB F k).Closed ↔ k * (sA - sB) = (0 : Rat)) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.separate_covectors

example :
    ∀ (sA sB F : Rat),
      sA ≠ (0 : Rat) →
        sB ≠ (0 : Rat) →
          (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Relative
              (NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linearPhase sA sB F) ↔
            F * (sA - sB) = (0 : Rat)) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.linear_phase_relative_iff

example :
    ∀ (sB : Rat) (W : NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Phase) (F k : Rat),
      NewtonLimitDynamics.Diagnostic.ReciprocalPhase.Reproduces (0 : Rat) sB W F k → F = (0 : Rat) ∧ k = (0 : Rat) :=
  @NewtonLimitDynamics.Diagnostic.ReciprocalPhase.zero_excluded


/-! NewtonLimitDynamics.Historical.AreaLaw -/
example :
    ∀ {Point Impulse : Type} (g : NewtonLimitDynamics.Polygon.EuclideanConstruction Point Impulse) (p q : Point)
      (impulse : Nat → Impulse) (n : Nat),
      NewtonLimitDynamics.Polygon.unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  @DeMotu1684.AreaLaw.natp00089_finite_equal_areas

example :
    ∀ {Point Impulse : Type} (g : NewtonLimitDynamics.Polygon.EuclideanConstruction Point Impulse) (p q : Point)
      (impulse : Nat → Impulse) (dt : Nat),
      (0 : Nat) < dt →
        ∀ (start₁ start₂ m n : Nat),
          (0 : Nat) < m →
            (0 : Nat) < n →
              (0 : Nat) < m * dt ∧
                (0 : Nat) < n * dt ∧
                  NewtonLimitDynamics.Polygon.unsignedBlock g p q impulse start₁ m * (n * dt) =
                    NewtonLimitDynamics.Polygon.unsignedBlock g p q impulse start₂ n * (m * dt) :=
  @DeMotu1684.AreaLaw.natp00089_finite_block_comparison

example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules) (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
              (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
              NewtonLimitDynamics.Polygon.MotionSampling.RadialChart g l r T parts u →
                ∀ (A : NewtonLimitDynamics.Fraction),
                  area.HasArea (NewtonLimitDynamics.Polygon.MotionSampling.sweptSector u T) A →
                    A.equiv
                      (T.mul
                          (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                            (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))))).half :=
  @DeMotu1684.NATP00090.AreaLaw.sampled_radial_sector_area

example :
    ∀ (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            (0 : Int) ≤
                (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                    (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))).num →
              ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
                (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
                NewtonLimitDynamics.Polygon.MotionSampling.RadialChart g l r T parts u →
                  ∀ (D : Nat → NewtonLimitDynamics.Fraction),
                    (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                      (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @DeMotu1684.NATP00090.AreaLaw.mechanical_between_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RadialSector.DifferenceAreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
              (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
              NewtonLimitDynamics.Polygon.MotionSampling.RadialChart g l r T parts u →
                ∀ (A : NewtonLimitDynamics.Fraction),
                  area.HasArea (NewtonLimitDynamics.Polygon.MotionSampling.sweptSector u T) A →
                    A.equiv
                      (T.mul
                          (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                            (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))))).half :=
  @Principia1687.PropositionI.sampled_radial_sector_area

example :
    ∀ (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            (0 : Int) ≤
                (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                    (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))).num →
              ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
                (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
                NewtonLimitDynamics.Polygon.MotionSampling.RadialChart g l r T parts u →
                  ∀ (D : Nat → NewtonLimitDynamics.Fraction),
                    (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                      (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @Principia1687.PropositionI.mechanical_between_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RadialSector.DifferenceAreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
              (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
              NewtonLimitDynamics.Polygon.MotionSampling.RadialChart g l r T parts u →
                ∀ (A : NewtonLimitDynamics.Fraction),
                  area.HasArea (NewtonLimitDynamics.Polygon.MotionSampling.sweptSector u T) A →
                    A.equiv
                      (T.mul
                          (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                            (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))))).half :=
  @Principia1713.PropositionI.sampled_radial_sector_area

example :
    ∀ (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            (0 : Int) ≤
                (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                    (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))).num →
              ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
                (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
                NewtonLimitDynamics.Polygon.MotionSampling.RadialChart g l r T parts u →
                  ∀ (D : Nat → NewtonLimitDynamics.Fraction),
                    (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                      (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @Principia1713.PropositionI.mechanical_between_area_approximation


/-! NewtonLimitDynamics.Historical.LemmaI -/
example :
    ∀ {Q : Type} (g : NewtonLimitDynamics.Magnitudes Q) (gap : Nat → Q) (D : Q),
      NewtonLimitDynamics.Exhaustion.VanishingDifference g gap →
        NewtonLimitDynamics.Exhaustion.TerminalLower g gap D → ¬g.positive D :=
  @Principia1687.LemmaI.no_positive_ultimate_difference

example :
    ∀ {Q : Type} (g : NewtonLimitDynamics.Magnitudes Q) (T : Q),
      g.positive T →
        ∀ (gap : Q → Q) (D : Q),
          (∀ (d : Q), g.positive d → NewtonLimitDynamics.Exhaustion.BeforeEnd g T fun (h : Q) => g.lt (gap h) d) →
            (∀ (d : Q),
                g.positive d → g.lt d D → NewtonLimitDynamics.Exhaustion.BeforeEnd g T fun (h : Q) => g.lt d (gap h)) →
              ¬g.positive D :=
  @Principia1687.LemmaI.given_time_exhaustion

example :
    ∀ (gap : Nat → NewtonLimitDynamics.Fraction) (D : NewtonLimitDynamics.Fraction),
      (0 : Int) ≤ D.num →
        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes gap →
          NewtonLimitDynamics.Exhaustion.TerminalLower NewtonLimitDynamics.Fraction.magnitudes gap D →
            D.equiv (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) :=
  @Principia1687.LemmaI.ultimate_difference_zero

example :
    ∀ {Q : Type} (g : NewtonLimitDynamics.Magnitudes Q) (gap : Nat → Q) (D : Q),
      NewtonLimitDynamics.Exhaustion.VanishingDifference g gap →
        NewtonLimitDynamics.Exhaustion.TerminalLower g gap D → ¬g.positive D :=
  @Principia1713.LemmaI.no_positive_ultimate_difference

example :
    ∀ {Q : Type} (g : NewtonLimitDynamics.Magnitudes Q) (T : Q),
      g.positive T →
        ∀ (gap : Q → Q) (D : Q),
          (∀ (d : Q), g.positive d → NewtonLimitDynamics.Exhaustion.BeforeEnd g T fun (h : Q) => g.lt (gap h) d) →
            (∀ (d : Q),
                g.positive d → g.lt d D → NewtonLimitDynamics.Exhaustion.BeforeEnd g T fun (h : Q) => g.lt d (gap h)) →
              ¬g.positive D :=
  @Principia1713.LemmaI.finite_time_before_end_exhaustion

example :
    ∀ (gap : Nat → NewtonLimitDynamics.Fraction) (D : NewtonLimitDynamics.Fraction),
      (0 : Int) ≤ D.num →
        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes gap →
          NewtonLimitDynamics.Exhaustion.TerminalLower NewtonLimitDynamics.Fraction.magnitudes gap D →
            D.equiv (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) :=
  @Principia1713.LemmaI.ultimate_difference_zero

example :
    ∀ {Q : Type} (g : NewtonLimitDynamics.Magnitudes Q) (ratio lower upper : Q → Q) (c : Q),
      NewtonLimitDynamics.Ultimate g lower c →
        NewtonLimitDynamics.Ultimate g upper c →
          (NewtonLimitDynamics.Near g fun (h : Q) => g.le (lower h) (ratio h) ∧ g.le (ratio h) (upper h)) →
            NewtonLimitDynamics.Ultimate g ratio c :=
  @DeMotu1684.Exhaustion.natp00090_enclosing_ratio_reconstruction


/-! NewtonLimitDynamics.Historical.LemmaII -/
example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b M : NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (∀ (i : Nat), i < p.count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width p i).equiv M) →
          (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g p).equiv
            (M.mul (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  @Principia1687.LemmaII.lemma2_equal_width_gap

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g p).le A ∧
              A.le (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g p) :=
  @Principia1687.LemmaII.rectangle_area_enclosure

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
          (∀ (m i : Nat),
              i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
            NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
              NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m) :=
  @Principia1687.LemmaII.equal_width_gap_vanishes

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
          (∀ (m i : Nat),
              i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
            NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
              ∀ (D : NewtonLimitDynamics.Fraction),
                (0 : Int) ≤ D.num →
                  NewtonLimitDynamics.Exhaustion.TerminalLower NewtonLimitDynamics.Fraction.magnitudes
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) D →
                    D.equiv (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) :=
  @Principia1687.LemmaII.equal_width_ultimate_gap_zero

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                        fun (m : Nat) =>
                        (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
                      NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                        fun (m : Nat) =>
                        (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference A
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))).abs :=
  @Principia1687.LemmaII.equal_width_curved_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (hpositive : (0 : Int) < A.num) (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                      fun (m : Nat) =>
                      (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                          (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)))
                          (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs) ∧
                    NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                      fun (m : Nat) =>
                      (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                          (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m)))
                          (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs :=
  @Principia1687.LemmaII.equal_width_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        a.lt b →
          (0 : Int) < (g a).num →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) →
              (∀ (m : Nat),
                  area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                NewtonLimitDynamics.Polygon.RectangleContent.MutualRatiosOne
                  (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) fun (m : Nat) =>
                  NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1687.LemmaII.rectangle_mutual_ratios_from_gap

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        a.lt b →
          (0 : Int) < (g a).num →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    NewtonLimitDynamics.Polygon.RectangleContent.MutualRatiosOne
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                      fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1687.LemmaII.equal_width_mutual_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    NewtonLimitDynamics.Polygon.RectangleContent.EventuallyMutualRatiosOne
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                      fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1687.LemmaII.rectangle_mutual_ratios_from_gap_interior

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
                  (∀ (m i : Nat),
                      i < (parts m).count →
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                    NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                      (∀ (m : Nat),
                          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                            area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                        NewtonLimitDynamics.Polygon.RectangleContent.EventuallyMutualRatiosOne
                          (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                          fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1687.LemmaII.equal_width_mutual_area_ratios_interior

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            area.magnitudes.order.le (area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g p))
                A ∧
              area.magnitudes.order.le A
                (area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g p)) :=
  @Principia1687.LemmaII.rectangle_magnitude_enclosure

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  NewtonLimitDynamics.Polygon.MagnitudeContent.Approximates area g a b A parts ∧
                    ∀ (D : Q),
                      NewtonLimitDynamics.Exhaustion.TerminalLower area.magnitudes.order
                          (fun (m : Nat) =>
                            area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)))
                          D →
                        ¬area.magnitudes.order.positive D :=
  @Principia1687.LemmaII.equal_width_magnitude_approximation

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
          NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
            (0 : Int) ≤ (g a).num →
              a.le c →
                c.lt b →
                  (0 : Int) < (g c).num →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
                        (∀ (k i : Nat),
                            i < (parts k).count →
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts k) i).equiv (mesh k)) →
                          NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                            NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                              (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts k))
                              (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts k)) A :=
  @Principia1687.LemmaII.equal_width_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q),
      a.le b →
        (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
          NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
            area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
              NewtonLimitDynamics.Polygon.UniformRectangles.Exhausts area g a b A :=
  @Principia1687.LemmaII.uniform_graph_rectangle_exhaustion

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
                  NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn
                      (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      NewtonLimitDynamics.Polygon.UniformRectangles.RatiosExhaust area g a b A :=
  @Principia1687.LemmaII.uniform_graph_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b)
          (eps : Nat → NewtonLimitDynamics.Fraction) (indices : Nat → Nat),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t))
                    a b →
                  NewtonLimitDynamics.Polygon.UniformRectangles.MatchedApproximation area g a b A parts eps indices →
                    have selected := fun (k : Nat) => parts (indices k);
                    NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.lowerHeights g (selected k) (eps k)))
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.upperHeights g (selected k) (eps k)))
                      A :=
  @Principia1687.LemmaII.uniform_graph_matched_area_ratios

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b M : NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (∀ (i : Nat), i < p.count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width p i).equiv M) →
          (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g p).equiv
            (M.mul (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  @Principia1713.LemmaII.lemma2_equal_width_gap

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g p).le A ∧
              A.le (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g p) :=
  @Principia1713.LemmaII.rectangle_area_enclosure

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
          (∀ (m i : Nat),
              i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
            NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
              NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m) :=
  @Principia1713.LemmaII.equal_width_gap_vanishes

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
          (∀ (m i : Nat),
              i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
            NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
              ∀ (D : NewtonLimitDynamics.Fraction),
                (0 : Int) ≤ D.num →
                  NewtonLimitDynamics.Exhaustion.TerminalLower NewtonLimitDynamics.Fraction.magnitudes
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) D →
                    D.equiv (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) :=
  @Principia1713.LemmaII.equal_width_ultimate_gap_zero

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                        fun (m : Nat) =>
                        (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
                      NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                        fun (m : Nat) =>
                        (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference A
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))).abs :=
  @Principia1713.LemmaII.equal_width_curved_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (hpositive : (0 : Int) < A.num) (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                      fun (m : Nat) =>
                      (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                          (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)))
                          (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs) ∧
                    NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                      fun (m : Nat) =>
                      (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                          (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                            (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m)))
                          (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs :=
  @Principia1713.LemmaII.equal_width_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        a.lt b →
          (0 : Int) < (g a).num →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) →
              (∀ (m : Nat),
                  area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                NewtonLimitDynamics.Polygon.RectangleContent.MutualRatiosOne
                  (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) fun (m : Nat) =>
                  NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1713.LemmaII.rectangle_mutual_ratios_from_gap

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        a.lt b →
          (0 : Int) < (g a).num →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    NewtonLimitDynamics.Polygon.RectangleContent.MutualRatiosOne
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                      fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1713.LemmaII.equal_width_mutual_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    NewtonLimitDynamics.Polygon.RectangleContent.EventuallyMutualRatiosOne
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                      fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1713.LemmaII.rectangle_mutual_ratios_from_gap_interior

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
                  (∀ (m i : Nat),
                      i < (parts m).count →
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                    NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                      (∀ (m : Nat),
                          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                            area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                        NewtonLimitDynamics.Polygon.RectangleContent.EventuallyMutualRatiosOne
                          (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                          fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1713.LemmaII.equal_width_mutual_area_ratios_interior

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q)
      (p : NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            area.magnitudes.order.le (area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g p))
                A ∧
              area.magnitudes.order.le A
                (area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g p)) :=
  @Principia1713.LemmaII.rectangle_magnitude_enclosure

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
              (∀ (m i : Nat),
                  i < (parts m).count → (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts m) i).equiv (mesh m)) →
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                  NewtonLimitDynamics.Polygon.MagnitudeContent.Approximates area g a b A parts ∧
                    ∀ (D : Q),
                      NewtonLimitDynamics.Exhaustion.TerminalLower area.magnitudes.order
                          (fun (m : Nat) =>
                            area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)))
                          D →
                        ¬area.magnitudes.order.positive D :=
  @Principia1713.LemmaII.equal_width_magnitude_approximation

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
          NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
            (0 : Int) ≤ (g a).num →
              a.le c →
                c.lt b →
                  (0 : Int) < (g c).num →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      ∀ (mesh : Nat → NewtonLimitDynamics.Fraction),
                        (∀ (k i : Nat),
                            i < (parts k).count →
                              (NewtonLimitDynamics.Polygon.MonotoneRectangles.width (parts k) i).equiv (mesh k)) →
                          NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes mesh →
                            NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                              (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts k))
                              (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts k)) A :=
  @Principia1713.LemmaII.equal_width_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q),
      a.le b →
        (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
          NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
            area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
              NewtonLimitDynamics.Polygon.UniformRectangles.Exhausts area g a b A :=
  @Principia1713.LemmaII.uniform_graph_rectangle_exhaustion

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
                  NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn
                      (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      NewtonLimitDynamics.Polygon.UniformRectangles.RatiosExhaust area g a b A :=
  @Principia1713.LemmaII.uniform_graph_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b)
          (eps : Nat → NewtonLimitDynamics.Fraction) (indices : Nat → Nat),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t))
                    a b →
                  NewtonLimitDynamics.Polygon.UniformRectangles.MatchedApproximation area g a b A parts eps indices →
                    have selected := fun (k : Nat) => parts (indices k);
                    NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.lowerHeights g (selected k) (eps k)))
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.upperHeights g (selected k) (eps k)))
                      A :=
  @Principia1713.LemmaII.uniform_graph_matched_area_ratios


/-! NewtonLimitDynamics.Historical.LemmaIII -/
example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
            NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
          NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
            NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m) :=
  @Principia1687.LemmaIII.unequal_width_gap_vanishes

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
            NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
          ∀ (D : NewtonLimitDynamics.Fraction),
            (0 : Int) ≤ D.num →
              NewtonLimitDynamics.Exhaustion.TerminalLower NewtonLimitDynamics.Fraction.magnitudes
                  (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) D →
                D.equiv (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) :=
  @Principia1687.LemmaIII.unequal_width_ultimate_gap_zero

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              (∀ (m : Nat),
                  area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                    (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
                  NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                    fun (m : Nat) =>
                    (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference A
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))).abs :=
  @Principia1687.LemmaIII.unequal_width_curved_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (hpositive : (0 : Int) < A.num) (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                  (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                      (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)))
                      (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs) ∧
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                  (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                      (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m)))
                      (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs :=
  @Principia1687.LemmaIII.unequal_width_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        a.lt b →
          (0 : Int) < (g a).num →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              (∀ (m : Nat),
                  area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                NewtonLimitDynamics.Polygon.RectangleContent.MutualRatiosOne
                  (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) fun (m : Nat) =>
                  NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1687.LemmaIII.unequal_width_mutual_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    NewtonLimitDynamics.Polygon.RectangleContent.EventuallyMutualRatiosOne
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                      fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1687.LemmaIII.unequal_width_mutual_area_ratios_interior

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              NewtonLimitDynamics.Polygon.MagnitudeContent.Approximates area g a b A parts ∧
                ∀ (D : Q),
                  NewtonLimitDynamics.Exhaustion.TerminalLower area.magnitudes.order
                      (fun (m : Nat) =>
                        area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)))
                      D →
                    ¬area.magnitudes.order.positive D :=
  @Principia1687.LemmaIII.unequal_width_magnitude_approximation

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
          NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
            (0 : Int) ≤ (g a).num →
              a.le c →
                c.lt b →
                  (0 : Int) < (g c).num →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                          fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts k)) →
                        NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                          (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts k))
                          (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts k)) A :=
  @Principia1687.LemmaIII.unequal_width_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q),
      a.le b →
        (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
          NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
            area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
              NewtonLimitDynamics.Polygon.UniformRectangles.Exhausts area g a b A :=
  @Principia1687.LemmaIII.uniform_graph_rectangle_exhaustion

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
                  NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn
                      (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      NewtonLimitDynamics.Polygon.UniformRectangles.RatiosExhaust area g a b A :=
  @Principia1687.LemmaIII.uniform_graph_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b)
          (eps : Nat → NewtonLimitDynamics.Fraction) (indices : Nat → Nat),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t))
                    a b →
                  NewtonLimitDynamics.Polygon.UniformRectangles.MatchedApproximation area g a b A parts eps indices →
                    have selected := fun (k : Nat) => parts (indices k);
                    NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.lowerHeights g (selected k) (eps k)))
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.upperHeights g (selected k) (eps k)))
                      A :=
  @Principia1687.LemmaIII.uniform_graph_matched_area_ratios

example :
    ∀ {K : Type} [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
      [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] (g : K → K) (a b : K)
      (parts : Nat → NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Partition a b) (heights : Nat → Nat → K)
      (mesh : Nat → K),
      NewtonLimitDynamics.Polygon.CurvilinearCoincidence.UniformOn g a b →
        NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Shrinks mesh →
          (∀ (k i : Nat), i < (parts k).count → (parts k).nodes (i + (1 : Nat)) - (parts k).nodes i ≤ mesh k) →
            (∀ (k i : Nat),
                i < (parts k).count →
                  NewtonLimitDynamics.Polygon.CurvilinearCoincidence.CellHeight g (parts k) i (heights k i)) →
              ∀ (eps : K),
                (0 : K) < eps →
                  ∃ (N : Nat),
                    ∀ (k : Nat),
                      N ≤ k →
                        ∀ (i : Nat),
                          i < (parts k).count →
                            ∀ (t : K),
                              (parts k).nodes i ≤ t →
                                t ≤ (parts k).nodes (i + (1 : Nat)) → -eps < heights k i - g t ∧ heights k i - g t < eps :=
  @Principia1687.LemmaIII.unequal_width_ordinate_control

example :
    ∀ {K : Type} [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
      [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] (inner outer : Nat → K × K → Prop) (mesh : Nat → K) (height : K),
      (0 : K) ≤ height →
        ∀
          (d :
            (k : Nat) →
              NewtonLimitDynamics.Polygon.SolidFigureExhaustion.GapDissection (inner k) (outer k) (mesh k) height),
          NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Shrinks mesh →
            NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Shrinks fun (k : Nat) =>
              (List.map NewtonLimitDynamics.Polygon.SolidFigureExhaustion.Box.value (d k).boxes).sum :=
  @Principia1687.LemmaIII.unequal_width_dissection_gap

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
            NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
          NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
            NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m) :=
  @Principia1713.LemmaIII.unequal_width_gap_vanishes

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
            NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
          ∀ (D : NewtonLimitDynamics.Fraction),
            (0 : Int) ≤ D.num →
              NewtonLimitDynamics.Exhaustion.TerminalLower NewtonLimitDynamics.Fraction.magnitudes
                  (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)) D →
                D.equiv (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) :=
  @Principia1713.LemmaIII.unequal_width_ultimate_gap_zero

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              (∀ (m : Nat),
                  area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                    (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
                  NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                    fun (m : Nat) =>
                    (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference A
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))).abs :=
  @Principia1713.LemmaIII.unequal_width_curved_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b A : NewtonLimitDynamics.Fraction)
      (hpositive : (0 : Int) < A.num) (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                  (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                      (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)))
                      (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs) ∧
                NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                  (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference
                      (NewtonLimitDynamics.Polygon.RectangleContent.ratioTo A hpositive
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m)))
                      (NewtonLimitDynamics.Fraction.ofInt (1 : Int))).abs :=
  @Principia1713.LemmaIII.unequal_width_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        a.lt b →
          (0 : Int) < (g a).num →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              (∀ (m : Nat),
                  area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                NewtonLimitDynamics.Polygon.RectangleContent.MutualRatiosOne
                  (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) fun (m : Nat) =>
                  NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1713.LemmaIII.unequal_width_mutual_area_ratios

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RectangleContent.AreaRules)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
                  (∀ (m : Nat),
                      area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)) ∧
                        area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m))
                          (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m))) ∧
                    NewtonLimitDynamics.Polygon.RectangleContent.EventuallyMutualRatiosOne
                      (fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m))
                      fun (m : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m) :=
  @Principia1713.LemmaIII.unequal_width_mutual_area_ratios_interior

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
            (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes fun (m : Nat) =>
                NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)) →
              NewtonLimitDynamics.Polygon.MagnitudeContent.Approximates area g a b A parts ∧
                ∀ (D : Q),
                  NewtonLimitDynamics.Exhaustion.TerminalLower area.magnitudes.order
                      (fun (m : Nat) =>
                        area.magnitudes.embed (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)))
                      D →
                    ¬area.magnitudes.order.positive D :=
  @Principia1713.LemmaIII.unequal_width_magnitude_approximation

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
          NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
            (0 : Int) ≤ (g a).num →
              a.le c →
                c.lt b →
                  (0 : Int) < (g c).num →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      (NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes
                          fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts k)) →
                        NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                          (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts k))
                          (fun (k : Nat) => NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts k)) A :=
  @Principia1713.LemmaIII.unequal_width_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q)
      (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction) (A : Q),
      a.le b →
        (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
          NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
            area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
              NewtonLimitDynamics.Polygon.UniformRectangles.Exhausts area g a b A :=
  @Principia1713.LemmaIII.uniform_graph_rectangle_exhaustion

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                (∀ (t : NewtonLimitDynamics.Fraction), a.le t → t.le b → (0 : Int) ≤ (g t).num) →
                  NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn
                      (fun (t : NewtonLimitDynamics.Fraction) => (t, g t)) a b →
                    area.HasArea (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) A →
                      NewtonLimitDynamics.Polygon.UniformRectangles.RatiosExhaust area g a b A :=
  @Principia1713.LemmaIII.uniform_graph_assigned_magnitude_ratios

example :
    ∀ {Q : Type} (area : NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules Q),
      NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules area.magnitudes →
        ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b c : NewtonLimitDynamics.Fraction) (A : Q)
          (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b)
          (eps : Nat → NewtonLimitDynamics.Fraction) (indices : Nat → Nat),
          a.le c →
            c.lt b →
              (0 : Int) < (g c).num →
                NewtonLimitDynamics.Polygon.RationalBoundary.UniformOn (fun (t : NewtonLimitDynamics.Fraction) => (t, g t))
                    a b →
                  NewtonLimitDynamics.Polygon.UniformRectangles.MatchedApproximation area g a b A parts eps indices →
                    have selected := fun (k : Nat) => parts (indices k);
                    NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRatiosOne area.magnitudes
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.lowerHeights g (selected k) (eps k)))
                      (fun (k : Nat) =>
                        NewtonLimitDynamics.Polygon.UniformRectangles.value (selected k)
                          (NewtonLimitDynamics.Polygon.UniformRectangles.upperHeights g (selected k) (eps k)))
                      A :=
  @Principia1713.LemmaIII.uniform_graph_matched_area_ratios

example :
    ∀ {K : Type} [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
      [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] (g : K → K) (a b : K)
      (parts : Nat → NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Partition a b) (heights : Nat → Nat → K)
      (mesh : Nat → K),
      NewtonLimitDynamics.Polygon.CurvilinearCoincidence.UniformOn g a b →
        NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Shrinks mesh →
          (∀ (k i : Nat), i < (parts k).count → (parts k).nodes (i + (1 : Nat)) - (parts k).nodes i ≤ mesh k) →
            (∀ (k i : Nat),
                i < (parts k).count →
                  NewtonLimitDynamics.Polygon.CurvilinearCoincidence.CellHeight g (parts k) i (heights k i)) →
              ∀ (eps : K),
                (0 : K) < eps →
                  ∃ (N : Nat),
                    ∀ (k : Nat),
                      N ≤ k →
                        ∀ (i : Nat),
                          i < (parts k).count →
                            ∀ (t : K),
                              (parts k).nodes i ≤ t →
                                t ≤ (parts k).nodes (i + (1 : Nat)) → -eps < heights k i - g t ∧ heights k i - g t < eps :=
  @Principia1713.LemmaIII.unequal_width_ordinate_control

example :
    ∀ {K : Type} [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
      [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] (inner outer : Nat → K × K → Prop) (mesh : Nat → K) (height : K),
      (0 : K) ≤ height →
        ∀
          (d :
            (k : Nat) →
              NewtonLimitDynamics.Polygon.SolidFigureExhaustion.GapDissection (inner k) (outer k) (mesh k) height),
          NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Shrinks mesh →
            NewtonLimitDynamics.Polygon.CurvilinearCoincidence.Shrinks fun (k : Nat) =>
              (List.map NewtonLimitDynamics.Polygon.SolidFigureExhaustion.Box.value (d k).boxes).sum :=
  @Principia1713.LemmaIII.unequal_width_dissection_gap

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          (∀ (delta : NewtonLimitDynamics.Fraction),
              (0 : Int) < delta.num →
                ∃ (N : Nat),
                  ∀ (m : Nat), N ≤ m → (NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)).lt delta) →
            (∀ (m : Nat),
                (∀ (x : NewtonLimitDynamics.Polygon.PositionValues.PositionValue),
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m)) x →
                      NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) x) ∧
                  ∀ (x : NewtonLimitDynamics.Polygon.PositionValues.PositionValue),
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) x →
                      NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m)) x) ∧
              (∀ (m : Nat),
                  ((0 : Int) ≤ (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)).num ∧
                      (0 : Int) ≤ (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m)).num) ∧
                    (0 : Int) ≤ (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)).num ∧
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)).le
                        ((NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)).mul
                          (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference (g a) (g b)))) ∧
                ∀ (eps : NewtonLimitDynamics.Fraction),
                  (0 : Int) < eps.num →
                    ∃ (N : Nat),
                      ∀ (m : Nat), N ≤ m → (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)).lt eps :=
  @Principia1687.LemmaIII.unequal_width_completed_enclosure_and_gap

example :
    ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (a b : NewtonLimitDynamics.Fraction)
      (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition a b),
      NewtonLimitDynamics.Polygon.MonotoneRectangles.MonotoneOn g a b →
        (0 : Int) ≤ (g a).num →
          (∀ (delta : NewtonLimitDynamics.Fraction),
              (0 : Int) < delta.num →
                ∃ (N : Nat),
                  ∀ (m : Nat), N ≤ m → (NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)).lt delta) →
            (∀ (m : Nat),
                (∀ (x : NewtonLimitDynamics.Polygon.PositionValues.PositionValue),
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerFigure g (parts m)) x →
                      NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) x) ∧
                  ∀ (x : NewtonLimitDynamics.Polygon.PositionValues.PositionValue),
                    NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.figure g a b) x →
                      NewtonLimitDynamics.Polygon.MonotoneRectangles.completed
                        (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperFigure g (parts m)) x) ∧
              (∀ (m : Nat),
                  ((0 : Int) ≤ (NewtonLimitDynamics.Polygon.MonotoneRectangles.lowerSum g (parts m)).num ∧
                      (0 : Int) ≤ (NewtonLimitDynamics.Polygon.MonotoneRectangles.upperSum g (parts m)).num) ∧
                    (0 : Int) ≤ (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)).num ∧
                      (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)).le
                        ((NewtonLimitDynamics.Polygon.MonotoneRectangles.maxWidth (parts m)).mul
                          (NewtonLimitDynamics.Polygon.HarmonicTimeComparison.durationDifference (g a) (g b)))) ∧
                ∀ (eps : NewtonLimitDynamics.Fraction),
                  (0 : Int) < eps.num →
                    ∃ (N : Nat),
                      ∀ (m : Nat), N ≤ m → (NewtonLimitDynamics.Polygon.MonotoneRectangles.gap g (parts m)).lt eps :=
  @Principia1713.LemmaIII.unequal_width_completed_enclosure_and_gap

/-! Uniform-chart Proposition I clients, added 26 November 2026 (issue 3) -/
example :
    ∀ (area : NewtonLimitDynamics.Polygon.SectorFan.AreaRules) (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
              (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r)
              (m M : NewtonLimitDynamics.Fraction),
              NewtonLimitDynamics.Polygon.UniformMotionChart.UniformRadialChart g l r T parts u m M →
                ∀ (A : NewtonLimitDynamics.Fraction),
                  area.HasArea (NewtonLimitDynamics.Polygon.MotionSampling.sweptSector u T) A →
                    A.equiv
                      (T.mul
                          (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                            (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))))).half :=
  @DeMotu1684.NATP00090.AreaLaw.sampled_uniform_sector_area

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RadialSector.DifferenceAreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
              (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r)
              (m M : NewtonLimitDynamics.Fraction),
              NewtonLimitDynamics.Polygon.UniformMotionChart.UniformRadialChart g l r T parts u m M →
                ∀ (A : NewtonLimitDynamics.Fraction),
                  area.HasArea (NewtonLimitDynamics.Polygon.MotionSampling.sweptSector u T) A →
                    A.equiv
                      (T.mul
                          (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                            (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))))).half :=
  @Principia1687.PropositionI.sampled_uniform_sector_area

example :
    ∀ (area : NewtonLimitDynamics.Polygon.RadialSector.DifferenceAreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r : NewtonLimitDynamics.Fraction)
              (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r)
              (m M : NewtonLimitDynamics.Fraction),
              NewtonLimitDynamics.Polygon.UniformMotionChart.UniformRadialChart g l r T parts u m M →
                ∀ (A : NewtonLimitDynamics.Fraction),
                  area.HasArea (NewtonLimitDynamics.Polygon.MotionSampling.sweptSector u T) A →
                    A.equiv
                      (T.mul
                          (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                            (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))))).half :=
  @Principia1713.PropositionI.sampled_uniform_sector_area

/-! Lipschitz-chart between-area clients and support, added 26 November 2026 (issue 3) -/
example :
    ∀ (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            (0 : Int) ≤
                (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                    (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))).num →
              ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r m M K : NewtonLimitDynamics.Fraction)
                (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
                NewtonLimitDynamics.Polygon.LipschitzCurveCover.LipschitzRadialChart g l r T parts u m M K →
                  ∀ (D : Nat → NewtonLimitDynamics.Fraction),
                    (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                      (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @DeMotu1684.NATP00090.AreaLaw.lipschitz_between_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            (0 : Int) ≤
                (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                    (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))).num →
              ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r m M K : NewtonLimitDynamics.Fraction)
                (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
                NewtonLimitDynamics.Polygon.LipschitzCurveCover.LipschitzRadialChart g l r T parts u m M K →
                  ∀ (D : Nat → NewtonLimitDynamics.Fraction),
                    (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                      (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @Principia1687.PropositionI.lipschitz_between_area_approximation

example :
    ∀ (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.CentralSchedule.Field),
      NewtonLimitDynamics.Polygon.CentralSchedule.central a →
        ∀ (C T L B P V : NewtonLimitDynamics.Fraction)
          (u :
            NewtonLimitDynamics.Fraction →
              NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point),
          NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
            (0 : Int) ≤
                (NewtonLimitDynamics.Polygon.CentralSchedule.momentum
                    (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int)))).num →
              ∀ (g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction) (l r m M K : NewtonLimitDynamics.Fraction)
                (parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r),
                NewtonLimitDynamics.Polygon.LipschitzCurveCover.LipschitzRadialChart g l r T parts u m M K →
                  ∀ (D : Nat → NewtonLimitDynamics.Fraction),
                    (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                      (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                        NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @Principia1713.PropositionI.lipschitz_between_area_approximation

example :
    ∀ {g : NewtonLimitDynamics.Fraction → NewtonLimitDynamics.Fraction} {l r T m M K : NewtonLimitDynamics.Fraction}
      {parts : Nat → NewtonLimitDynamics.Polygon.MonotoneRectangles.Partition l r}
      {u :
        NewtonLimitDynamics.Fraction →
          NewtonLimitDynamics.Polygon.TimeSubdivision.Point × NewtonLimitDynamics.Polygon.TimeSubdivision.Point}
      (area : NewtonLimitDynamics.Polygon.TriangleContent.AreaRules)
      (a : NewtonLimitDynamics.Polygon.TimeSubdivision.Point → NewtonLimitDynamics.Polygon.TimeSubdivision.Point)
      (C L B P V : NewtonLimitDynamics.Fraction),
      NewtonLimitDynamics.Polygon.MotionSampling.Conditions a C T L B P V u →
        NewtonLimitDynamics.Polygon.LipschitzCurveCover.LipschitzRadialChart g l r T parts u m M K →
          (∀ (j k : Nat),
              k < NewtonLimitDynamics.Polygon.HarmonicDyadic.blocks j →
                (0 : Int) ≤
                  (NewtonLimitDynamics.Polygon.TimeSubdivision.det
                      (NewtonLimitDynamics.Polygon.BoundedIteration.run a
                          (NewtonLimitDynamics.Polygon.HarmonicDyadic.duration T j)
                          (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))) k).fst
                      (NewtonLimitDynamics.Polygon.BoundedIteration.run a
                          (NewtonLimitDynamics.Polygon.HarmonicDyadic.duration T j)
                          (u (NewtonLimitDynamics.Fraction.ofInt (0 : Int))) (k + (1 : Nat))).fst).num) →
            ∀ (D : Nat → NewtonLimitDynamics.Fraction),
              (∀ (j : Nat), area.HasArea (NewtonLimitDynamics.Polygon.MotionCurveCover.between a T u j) (D j)) →
                (∀ (j : Nat), (0 : Int) ≤ (D j).num) ∧
                  NewtonLimitDynamics.Exhaustion.VanishingDifference NewtonLimitDynamics.Fraction.magnitudes D :=
  @NewtonLimitDynamics.Polygon.LipschitzCurveCover.assigned_between_areas_vanish

example :
    NewtonLimitDynamics.Polygon.LipschitzCurveCover.LipschitzOn NewtonLimitDynamics.Polygon.QuadraticSector.quadraticChart
      (NewtonLimitDynamics.Fraction.ofInt (0 : Int)) (NewtonLimitDynamics.Fraction.ofInt (1 : Int))
      (NewtonLimitDynamics.Fraction.ofInt (1 : Int)) :=
  @NewtonLimitDynamics.Polygon.LipschitzCurveCover.quadratic_lipschitz

/-! research.RationalTimeSlope -/
example :
    ∀ (a b : Nat), 21 * a ^ 5 + 70 * a ^ 3 * b ^ 2 + 105 * a * b ^ 4 = 15 * b ^ 5 →
      a % 7 = 0 ∧ b % 7 = 0 :=
  @RationalTimeSlope.common_seven

/-! Definitional checks for the reviewed definitions. -/
section Definitions
open NewtonLimitDynamics.Diagnostic.CoupledPolygons Vec3 in
example (a b : Vec3) :
    cross a b = ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩ := rfl

open NewtonLimitDynamics.Diagnostic.CoupledPolygons Vec3 in
example (xi xj : Vec3) :
    pairTerm xi xj = add (smul (dot xj xj) xi) (smul (-(dot xi xj)) xj) := rfl

open NewtonLimitDynamics.Diagnostic.CoupledPolygons Vec3 in
example (st : State) : gauss st = vsum (st.map fun s => cross s.1 s.2) := rfl

open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.TimeSubdivision
  ConvexCover SupportingTangents MonotoneRectangles HarmonicTimeComparison PolygonFanArea
  RadialSector UniformRadialSector in
example (area : SectorFan.AreaRules) (g : Fraction → Fraction) (a b : Fraction)
    (p : Partition a b) (eps M : Fraction) :
    CapsEnclose area g a b p eps M ↔
      ((∀ x, lowerCaps g p eps x → sector g a b x) ∧
      (∀ x, sector g a b x → upperCaps g p eps x) ∧
      (∀ x, lowerCaps g p eps x → chordFigure g p x) ∧
      (∀ x, chordFigure g p x → upperCaps g p eps x) ∧
      area.HasArea (lowerCaps g p eps) (stripSum p (lowerScales g p eps) p.count) ∧
      area.HasArea (upperCaps g p eps) (stripSum p (upperScales g p eps) p.count) ∧
      area.HasArea (chordFigure g p) (chordArea g p) ∧
      Fraction.le (capsGap g p eps)
        (Fraction.mul (Fraction.mul (Fraction.add eps eps) M) (durationDifference a b))) :=
  Iff.rfl

open NewtonLimitDynamics.Diagnostic.ReciprocalPhase in
example (sA sB : Rat) (W : Phase) (F k : Rat) :
    Reproduces sA sB W F k ↔
      ∀ qA qB, sA * W.dA qA qB = slope F k (qA - qB) ∧ sB * W.dB qA qB = -slope F k (qA - qB) :=
  Iff.rfl

open NewtonLimitDynamics.Diagnostic.ArealBounds in
example (m k L E r rdot : Rat) :
    EnergyRelation m k L E r rdot ↔
      2 * m * (r * r) * E = (m * r * rdot) * (m * r * rdot) + (L * L - m * k) :=
  Iff.rfl

-- The initial state of the issue 5 polygons, x = (1, 0) and p = (0, 1).
open NewtonLimitDynamics NewtonLimitDynamics.Diagnostic.ArealBounds in
example :
    start = ((Fraction.ofInt 1, Fraction.ofInt 0), (Fraction.ofInt 0, Fraction.ofInt 1)) :=
  rfl
end Definitions
