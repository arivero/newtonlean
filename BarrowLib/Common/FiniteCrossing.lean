/-! Finite rational interval chains.
Source: the original English statements and checked finite proofs below.
This records project derivation, without external historical textual support
or a claim of discovery or priority. No completeness or intermediate-value
theorem is used: the crossings are between finitely many rational entries.
-/

namespace NewtonLimitDynamics.FanIntervalChain

/-- A finite rational sequence with endpoints on opposite sides of a level
has a forward crossing edge. The intermediate entries need not be monotone. -/
theorem rising_crossing (r : Nat → Rat) (x : Rat) :
    ∀ n : Nat, 0 < n → r 0 ≤ x → x ≤ r n →
      ∃ k : Nat, k < n ∧ r k ≤ x ∧ x ≤ r (k+1) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn h0 hlast
      by_cases hmid : x ≤ r n
      · by_cases hz : n=0
        · subst n
          exact ⟨0,by omega,h0,hlast⟩
        · obtain ⟨k,hk,ha,hb⟩ := ih (by omega) h0 hmid
          exact ⟨k,by omega,ha,hb⟩
      · have hreverse : r n ≤ x := by grind
        exact ⟨n,by omega,hreverse,hlast⟩

/-- The reversed endpoint order also supplies a crossing edge. -/
theorem falling_crossing (r : Nat → Rat) (x : Rat) :
    ∀ n : Nat, 0 < n → x ≤ r 0 → r n ≤ x →
      ∃ k : Nat, k < n ∧ x ≤ r k ∧ r (k+1) ≤ x := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn h0 hlast
      by_cases hmid : r n ≤ x
      · by_cases hz : n=0
        · subst n
          exact ⟨0,by omega,h0,hlast⟩
        · obtain ⟨k,hk,ha,hb⟩ := ih (by omega) h0 hmid
          exact ⟨k,by omega,ha,hb⟩
      · have hreverse : x ≤ r n := by grind
        exact ⟨n,by omega,hreverse,hlast⟩

/-- Closed ray intervals, including a vertex exactly at the level. -/
def Between (a x b : Rat) : Prop := (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)

theorem finite_crossing (r : Nat → Rat) (x : Rat) (n : Nat)
    (hn : 0 < n) (h : Between (r 0) x (r n)) :
    ∃ k : Nat, k < n ∧ Between (r k) x (r (k+1)) := by
  rcases h with ⟨h0,hnx⟩ | ⟨hnx,h0⟩
  · obtain ⟨k,hk,ha,hb⟩ := rising_crossing r x n hn h0 hnx
    exact ⟨k,hk,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨k,hk,ha,hb⟩ := falling_crossing r x n hn h0 hnx
    exact ⟨k,hk,Or.inr ⟨hb,ha⟩⟩

end NewtonLimitDynamics.FanIntervalChain
