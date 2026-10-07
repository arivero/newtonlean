import ModernLib.Foundation.Polygon.IntegerTime

/-! Explicit terminating binary addresses for every integer numerator below
2^m. This is finite arithmetic, with no external real interval assumed. -/

namespace NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix
open HarmonicDyadic

def finiteAddress : Nat → Nat → Nat → Bool
  | 0,_,_ => false
  | m+1,k,j => if j=m then decide (k%2=1) else finiteAddress m (k/2) j

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem finiteAddress_tail : (m k j : Nat) → m ≤ j → finiteAddress m k j = false
  | 0,_,_,_ => rfl
  | m+1,k,j,hj => by
      have hn : j ≠ m := by omega
      simp only [finiteAddress,hn,if_false]
      exact finiteAddress_tail m (k/2) j (by omega)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem ticks_congr_before (b c : Nat → Bool) : (m : Nat) →
    (∀ i, i<m → b i=c i) → ticks b m=ticks c m
  | 0,_ => rfl
  | m+1,h => by
      have hp := ticks_congr_before b c m (fun i hi => h i (by omega))
      have hb := h m (by omega)
      simp only [ticks,hp,bit,hb]

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem finiteAddress_ticks : (m k : Nat) → k<blocks m → ticks (finiteAddress m k) m=k
  | 0,k,hk => by
      have hb : blocks 0=1 := rfl
      have hz : k=0 := by rw [hb] at hk; omega
      subst k
      rfl
  | m+1,k,hk => by
      have hk' : k<blocks m*2 := by simpa only [blocks,Nat.pow_succ] using hk
      have hd : k/2<blocks m := (Nat.div_lt_iff_lt_mul (by decide)).mpr hk'
      have hp := ticks_congr_before (finiteAddress (m+1) k) (finiteAddress m (k/2)) m
        (fun i hi => by
          have hn : i ≠ m := by omega
          simp only [finiteAddress,hn,if_false])
      have hbit : bit (finiteAddress (m+1) k) m=k%2 := by
        have hmod := Nat.mod_lt k (by decide : 0<2)
        by_cases hm : k%2=1
        · simp only [bit,finiteAddress,if_pos rfl,hm,decide_true,if_true]
        · have hz : k%2=0 := by omega
          simp [bit,finiteAddress,hz]
      change 2*ticks (finiteAddress (m+1) k) m+bit (finiteAddress (m+1) k) m=k
      rw [hp,finiteAddress_ticks m (k/2) hd,hbit]
      exact Nat.div_add_mod k 2

end NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix
