import BarrowLib.Common.RationalMagnitudes

/-! Finite rational interval chains.
Source: the original English statements and checked finite proofs below.
This records project derivation, without external historical textual support
or a claim of discovery or priority. No completeness or intermediate-value
theorem is used: the crossings are between finitely many rational entries.
-/

namespace NewtonLimitDynamics.FanIntervalChain
open NewtonLimitDynamics Fraction

/-- A finite rational sequence with endpoints on opposite sides of a level
has a forward crossing edge. The intermediate entries need not be monotone. -/
theorem rising_crossing (r : Nat → Fraction) (x : Fraction) :
    ∀ n : Nat, 0 < n → Fraction.le (r 0) x → Fraction.le x (r n) →
      ∃ k : Nat, k < n ∧ Fraction.le (r k) x ∧ Fraction.le x (r (k+1)) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn h0 hlast
      by_cases hmid : Fraction.le x (r n)
      · by_cases hz : n=0
        · subst n
          exact ⟨0,by omega,h0,hlast⟩
        · obtain ⟨k,hk,ha,hb⟩ := ih (by omega) h0 hmid
          exact ⟨k,by omega,ha,hb⟩
      · have hreverse : Fraction.le (r n) x := by
          unfold Fraction.le at *
          omega
        exact ⟨n,by omega,hreverse,hlast⟩

/-- The reversed endpoint order also supplies a crossing edge. -/
theorem falling_crossing (r : Nat → Fraction) (x : Fraction) :
    ∀ n : Nat, 0 < n → Fraction.le x (r 0) → Fraction.le (r n) x →
      ∃ k : Nat, k < n ∧ Fraction.le x (r k) ∧ Fraction.le (r (k+1)) x := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn h0 hlast
      by_cases hmid : Fraction.le (r n) x
      · by_cases hz : n=0
        · subst n
          exact ⟨0,by omega,h0,hlast⟩
        · obtain ⟨k,hk,ha,hb⟩ := ih (by omega) h0 hmid
          exact ⟨k,by omega,ha,hb⟩
      · have hreverse : Fraction.le x (r n) := by
          unfold Fraction.le at *
          omega
        exact ⟨n,by omega,hreverse,hlast⟩

/-- Closed ray intervals, including a vertex exactly at the level. -/
def Between (a x b : Fraction) : Prop :=
  (Fraction.le a x ∧ Fraction.le x b) ∨
  (Fraction.le b x ∧ Fraction.le x a)

theorem finite_crossing (r : Nat → Fraction) (x : Fraction) (n : Nat)
    (hn : 0 < n) (h : Between (r 0) x (r n)) :
    ∃ k : Nat, k < n ∧ Between (r k) x (r (k+1)) := by
  rcases h with ⟨h0,hnx⟩ | ⟨hnx,h0⟩
  · obtain ⟨k,hk,ha,hb⟩ := rising_crossing r x n hn h0 hnx
    exact ⟨k,hk,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨k,hk,ha,hb⟩ := falling_crossing r x n hn h0 hnx
    exact ⟨k,hk,Or.inr ⟨hb,ha⟩⟩

/-- A family of closed interval covers therefore covers every level between
the chain endpoints; no order of the intermediate radii is assumed. -/
theorem chain_cover (r : Nat → Fraction) (C : Nat → Fraction → Prop)
    (n : Nat) (hn : 0 < n)
    (hcell : ∀ k, k < n → ∀ x, Between (r k) x (r (k+1)) → C k x)
    (x : Fraction) (hx : Between (r 0) x (r n)) :
    ∃ k, k < n ∧ C k x := by
  obtain ⟨k,hk,hbetween⟩ := finite_crossing r x n hn hx
  exact ⟨k,hk,hcell k hk x hbetween⟩

/-- Once two monotone vertex sequences cross the same level in ordered cells,
every intervening paired connector straddles that level. -/
theorem ordered_connector_bracket (p q : Nat → Fraction) (level : Fraction)
    (ip iq k : Nat)
    (hpmono : ∀ i j, i ≤ j → Fraction.le (p i) (p j))
    (hqmono : ∀ i j, i ≤ j → Fraction.le (q i) (q j))
    (hleft : ip + 1 ≤ k) (hright : k ≤ iq)
    (hp : Fraction.le level (p (ip+1)))
    (hq : Fraction.le (q iq) level) :
    Fraction.le level (p k) ∧ Fraction.le (q k) level := by
  constructor
  · exact Fraction.magnitudes.le_trans hp (hpmono (ip+1) k hleft)
  · exact Fraction.magnitudes.le_trans (hqmono k iq hright) hq

end NewtonLimitDynamics.FanIntervalChain
