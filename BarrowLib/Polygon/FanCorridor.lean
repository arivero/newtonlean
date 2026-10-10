import BarrowLib.Polygon.FilledStrips
import BarrowLib.Polygon.FanRadial
import BarrowLib.Common.FiniteCrossing

/-! Adjacent filled cells cover a complete interval of a fixed rational ray.
Source: the original English statements and finite checked proofs below.
This is project proof provenance, without external historical textual
attribution or a claim of discovery or priority. The internal connector
points join neighboring cells; no internal origin triangle is added to
the cover. No monotonicity of the intermediate radial positions is needed.
-/

namespace NewtonLimitDynamics.Polygon.FanCorridor
open NewtonLimitDynamics TimeSubdivision ConvexCover FilledStrips FanRadial
open NewtonLimitDynamics.FanIntervalChain

private def zero : Fraction := Fraction.ofInt 0

private theorem segment_in_cell (p0 p1 q0 q1 a b x : Point) (s : Fraction)
    (ha : Fraction.equiv (height s a) zero)
    (hb : Fraction.equiv (height s b) zero)
    (hx : Fraction.equiv (height s x) zero)
    (hbetween : Between a.1.toRat x.1.toRat b.1.toRat)
    (hca : FilledCell p0 p1 q0 q1 a)
    (hcb : FilledCell p0 p1 q0 q1 b) :
    FilledCell p0 p1 q0 q1 x := by
  obtain ⟨u,hu,he⟩ := ray_between s a x b ha hx hb hbetween
  exact filledCell_congr p0 p1 q0 q1 x (lerp u a b) he
    (filledCell_convex p0 p1 q0 q1 a b u hu hca hcb)

/-- A corridor of m+1 filled cells covers every rational point on the ray
between its two on-ray endpoints. Every internal connector is supplied only
as an on-ray segment point; its whole origin triangle is never budgeted. -/
theorem corridor_offset (p q : Nat → Point) (n a : Nat) (s : Fraction)
    (c0 : Point) (hc0 : FilledCell (p a) (p (a+1)) (q a) (q (a+1)) c0)
    (hr0 : Fraction.equiv (height s c0) zero) :
    ∀ m : Nat, ∀ c1 : Point,
      a+m < n →
      FilledCell (p (a+m)) (p (a+m+1)) (q (a+m)) (q (a+m+1)) c1 →
      Fraction.equiv (height s c1) zero →
      (∀ j, 0 < j → j ≤ m → ∃ ell : Fraction, UnitInterval ell ∧
        Fraction.equiv (height s (lerp ell (p (a+j)) (q (a+j)))) zero) →
      ∀ x : Point, Fraction.equiv (height s x) zero →
        Between c0.1.toRat x.1.toRat c1.1.toRat → FilledRegion p q n x := by
  intro m
  induction m with
  | zero =>
      intro c1 hbound hc1 hr1 hconn x hrx hbetween
      have hc : FilledCell (p a) (p (a+1)) (q a) (q (a+1)) x :=
        segment_in_cell _ _ _ _ c0 c1 x s hr0 hr1 hrx hbetween hc0 (by simpa using hc1)
      obtain ⟨theta,mu,lambda,ht,hm,hl,he⟩ := hc
      exact ⟨a,by simpa using hbound,theta,mu,lambda,ht,hm,hl,he⟩
  | succ m ih =>
      intro c1 hbound hc1 hr1 hconn x hrx hbetween
      let k := a + (m+1)
      obtain ⟨ell,hell,hrz⟩ := hconn (m+1) (by omega) (by omega)
      let z := lerp ell (p k) (q k)
      have hk : k < n := by dsimp [k]; omega
      have hprev : a+m < n := by omega
      have hzprev : FilledCell (p (a+m)) (p (a+m+1))
          (q (a+m)) (q (a+m+1)) z := by
        simpa only [z,k,Nat.add_succ] using
          (end_connector (p (a+m)) (p (a+m+1)) (q (a+m)) (q (a+m+1)) ell hell)
      have hznext : FilledCell (p k) (p (k+1)) (q k) (q (k+1)) z :=
        start_connector (p k) (p (k+1)) (q k) (q (k+1)) ell hell
      have hc1' : FilledCell (p k) (p (k+1)) (q k) (q (k+1)) c1 := by
        simpa only [k,Nat.add_succ] using hc1
      rcases (show Between c0.1.toRat x.1.toRat z.1.toRat ∨
          Between z.1.toRat x.1.toRat c1.1.toRat from by grind [Between]) with hleft | hright
      · apply ih z hprev hzprev hrz
          (fun j hj hjm => hconn j hj (by omega)) x hrx hleft
      · have hc : FilledCell (p k) (p (k+1)) (q k) (q (k+1)) x :=
          segment_in_cell _ _ _ _ z c1 x s hrz hr1 hrx hright hznext hc1'
        exact ⟨k,hk,hc⟩

/-- Public indexed form of the finite ray corridor. -/
theorem corridor (p q : Nat → Point) (n a b : Nat) (hab : a ≤ b) (hbn : b < n)
    (s : Fraction) (c0 c1 x : Point)
    (hc0 : FilledCell (p a) (p (a+1)) (q a) (q (a+1)) c0)
    (hc1 : FilledCell (p b) (p (b+1)) (q b) (q (b+1)) c1)
    (hr0 : Fraction.equiv (height s c0) zero)
    (hr1 : Fraction.equiv (height s c1) zero)
    (hrx : Fraction.equiv (height s x) zero)
    (hbetween : Between c0.1.toRat x.1.toRat c1.1.toRat)
    (hconn : ∀ k, a < k → k ≤ b → ∃ ell : Fraction, UnitInterval ell ∧
      Fraction.equiv (height s (lerp ell (p k) (q k))) zero) :
    FilledRegion p q n x := by
  have hsum : a + (b-a) = b := by omega
  have h := corridor_offset p q n a s c0 hc0 hr0 (b-a) c1
    (by simpa only [hsum] using hbn)
    (by simpa only [hsum] using hc1) hr1
    (fun j hj hjm => hconn (a+j) (by omega) (by omega))
    x hrx hbetween
  exact h

end NewtonLimitDynamics.Polygon.FanCorridor
