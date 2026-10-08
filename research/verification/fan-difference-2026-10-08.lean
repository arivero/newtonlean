import BarrowLib.Polygon.FanDifference

/-! Target pin: positive first coordinates, nonnegative consecutive
determinants and a common initial vertex suffice for the actual finite
sector-union symmetric difference to lie in independent-parameter filled
edge strips plus the terminal radial connector. No area, desired inclusion,
curve agreement, modern topology or completion may be assumed.

Exact controls force both strict orders of boundary-crossing cell indices,
with the terminal connector excluded, then a collapsed cell and a terminal-
only point outside every filled cell. Separate scalar and convexity controls
include nonmonotone intermediate radii and zero group weights. These are
shared-kernel checks using the same rational definitions as the general
proof; they do not independently certify the kernel or assign union areas.
The full-turn multiplicity falsifier remains in sector-unions.
-/

namespace NewtonLimitDynamics.Polygon.FanDifferenceReview
open NewtonLimitDynamics TimeSubdivision SectorFan ConvexCover FanDifference
local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
private def pt (a b : Int) : Point := (Fraction.ofInt a,Fraction.ofInt b)
private def half : Fraction := ⟨1,2,by decide⟩
private def third : Fraction := ⟨1,3,by decide⟩
private def quarter : Fraction := ⟨1,4,by decide⟩
private def fiveFourth : Fraction := ⟨5,4,by decide⟩
private def fiveTwelfth : Fraction := ⟨5,12,by decide⟩
private def ninth : Fraction := ⟨1,9,by decide⟩
private def twoThirds : Fraction := ⟨2,3,by decide⟩
private def zero : Fraction := Fraction.ofInt 0

-- p crosses the y=0 ray in cell 0; q crosses it in cell 1.
private def pf (k : Nat) : Point :=
  if k=0 then pt 1 (-1) else if k=1 then (Fraction.ofInt 1,half) else pt 1 1
private def qf (k : Nat) : Point :=
  if k=0 then pt 1 (-1) else if k=1 then pt 2 (-1) else pt 4 1
private def xf : Point := pt 2 0
private theorem pfpos : ∀ k, k≤2 → 0 < (pf k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
private theorem qfpos : ∀ k, k≤2 → 0 < (qf k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
private theorem pforient : ∀ k, k<2 → 0 ≤ (det (pf k) (pf (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qforient : ∀ k, k<2 → 0 ≤ (det (qf k) (qf (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qfhit : Region qf 2 xf := by
  exact ⟨1,by decide,third,third,by decide,by decide,by decide,
    by constructor <;> decide⟩
private theorem pf_first (k : Nat) : (pf k).1 = Fraction.ofInt 1 := by
  by_cases h0 : k=0
  · simp [pf,h0,pt]
  · by_cases h1 : k=1
    · simp [pf,h0,h1,pt]
    · simp [pf,h0,h1,pt]
private theorem pfmiss : ¬ Region pf 2 xf := by
  rintro ⟨k,_,u,v,_,_,hs,hx⟩
  have he : Fraction.equiv xf.1 (Fraction.add u v) := Fraction.equiv_trans hx.1 (by
    simp only [pointAdd,pointScale,pf_first,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one])
  have hb := Fraction.le_equiv_left he hs
  have hn : ¬ Fraction.le xf.1 (Fraction.ofInt 1) := by decide
  exact hn hb
private theorem pf_terminal_miss : ¬ Triangle (pf 2) (qf 2) xf := by
  intro hx
  have hb := triangle_right _ _ (qf 2) _ hx (by decide) (by decide)
  have hn : ¬ 0 ≤ (det (qf 2) xf).num := by decide
  exact hn hb
example : FilledRegion pf qf 2 xf := by
  rcases difference_cover pf qf 2 pfpos qfpos pforient qforient
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    xf qfhit pfmiss with h | h
  · exact h
  · exact False.elim (pf_terminal_miss h)

-- q crosses the same ray in cell 0; p crosses it in cell 1.
private def pr (k : Nat) : Point :=
  if k=0 then pt 1 (-1) else if k=1 then (Fraction.ofInt 1,⟨-1,2,by decide⟩) else pt 1 1
private def qr (k : Nat) : Point :=
  if k=0 then pt 1 (-1) else if k=1 then pt 2 1 else pt 3 2
private def xr : Point := (fiveFourth,zero)
private theorem prpos : ∀ k, k≤2 → 0 < (pr k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
private theorem qrpos : ∀ k, k≤2 → 0 < (qr k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
private theorem prorient : ∀ k, k<2 → 0 ≤ (det (pr k) (pr (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qrorient : ∀ k, k<2 → 0 ≤ (det (qr k) (qr (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qrhit : Region qr 2 xr := by
  exact ⟨0,by decide,fiveTwelfth,fiveTwelfth,by decide,by decide,by decide,
    by constructor <;> decide⟩
private theorem pr_first (k : Nat) : (pr k).1 = Fraction.ofInt 1 := by
  by_cases h0 : k=0
  · simp [pr,h0,pt]
  · by_cases h1 : k=1
    · simp [pr,h0,h1,pt]
    · simp [pr,h0,h1,pt]
private theorem prmiss : ¬ Region pr 2 xr := by
  rintro ⟨k,_,u,v,_,_,hs,hx⟩
  have he : Fraction.equiv xr.1 (Fraction.add u v) := Fraction.equiv_trans hx.1 (by
    simp only [pointAdd,pointScale,pr_first,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one])
  have hb := Fraction.le_equiv_left he hs
  have hn : ¬ Fraction.le xr.1 (Fraction.ofInt 1) := by decide
  exact hn hb
private theorem pr_terminal_miss : ¬ Triangle (pr 2) (qr 2) xr := by
  intro hx
  have hb := triangle_right _ _ (qr 2) _ hx (by decide) (by decide)
  have hn : ¬ 0 ≤ (det (qr 2) xr).num := by decide
  exact hn hb
example : FilledRegion pr qr 2 xr := by
  rcases difference_cover pr qr 2 prpos qrpos prorient qrorient
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    xr qrhit prmiss with h | h
  · exact h
  · exact False.elim (pr_terminal_miss h)

-- The first p cell is collapsed: determinant zero and identical endpoints.
private def pc (k : Nat) : Point :=
  if k=0 ∨ k=1 then pt 1 (-1) else pt 1 1
private def qc (k : Nat) : Point :=
  if k=0 then pt 1 (-1) else if k=1 then pt 2 0 else pt 3 2
private def xc : Point := pt 2 1
private theorem pcpos : ∀ k, k≤2 → 0 < (pc k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
private theorem qcpos : ∀ k, k≤2 → 0 < (qc k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
private theorem pcorient : ∀ k, k<2 → 0 ≤ (det (pc k) (pc (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qcorient : ∀ k, k<2 → 0 ≤ (det (qc k) (qc (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qchit : Region qc 2 xc := by
  exact ⟨1,by decide,quarter,half,by decide,by decide,by decide,
    by constructor <;> decide⟩
private theorem pc_first (k : Nat) : (pc k).1 = Fraction.ofInt 1 := by
  by_cases h : k=0 ∨ k=1
  · simp [pc,h,pt]
  · simp [pc,h,pt]
private theorem pcmiss : ¬ Region pc 2 xc := by
  rintro ⟨k,_,u,v,_,_,hs,hx⟩
  have he : Fraction.equiv xc.1 (Fraction.add u v) := Fraction.equiv_trans hx.1 (by
    simp only [pointAdd,pointScale,pc_first,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one])
  have hb := Fraction.le_equiv_left he hs
  have hn : ¬ Fraction.le xc.1 (Fraction.ofInt 1) := by decide
  exact hn hb
private theorem pc_terminal_miss : ¬ Triangle (pc 2) (qc 2) xc := by
  intro hx
  have hb := triangle_right _ _ (qc 2) _ hx (by decide) (by decide)
  have hn : ¬ 0 ≤ (det (qc 2) xc).num := by decide
  exact hn hb
example : FilledRegion pc qc 2 xc := by
  rcases difference_cover pc qc 2 pcpos qcpos pcorient qcorient
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    xc qchit pcmiss with h | h
  · exact h
  · exact False.elim (pc_terminal_miss h)

-- A terminal-only point has radius below the endpoint connector while every
-- point in the sole filled edge cell has horizontal coordinate 1.
private def ptm (k : Nat) : Point := if k=0 then pt 1 (-1) else pt 1 0
private def qtm (k : Nat) : Point := if k=0 then pt 1 (-1) else pt 1 1
private def xtm : Point := (half,⟨3,8,by decide⟩)
private theorem ptmp : ∀ k, k≤1 → 0 < (ptm k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem qtmp : ∀ k, k≤1 → 0 < (qtm k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
private theorem ptmo : ∀ k, k<1 → 0 ≤ (det (ptm k) (ptm (k+1))).num := by
  intro k hk
  have he : k=0 := by omega
  subst k
  decide
private theorem qtmo : ∀ k, k<1 → 0 ≤ (det (qtm k) (qtm (k+1))).num := by
  intro k hk
  have he : k=0 := by omega
  subst k
  decide
private theorem qtmhit : Region qtm 1 xtm := by
  exact ⟨0,by decide,⟨1,16,by decide⟩,⟨7,16,by decide⟩,
    by decide,by decide,by decide,by constructor <;> decide⟩
private theorem ptmmiss : ¬ Region ptm 1 xtm := by
  rintro ⟨k,hk,htri⟩
  have h0 : k=0 := by omega
  subst k
  have hb := triangle_left _ _ (ptm 1) _ htri (by decide) (by decide)
  have hn : ¬ 0 ≤ (det xtm (ptm 1)).num := by decide
  exact hn hb
private theorem xtm_terminal : Triangle (ptm 1) (qtm 1) xtm := by
  exact ⟨⟨1,8,by decide⟩,⟨3,8,by decide⟩,by decide,by decide,by decide,
    by constructor <;> decide⟩
private theorem xtm_not_filled : ¬ FilledRegion ptm qtm 1 xtm := by
  rintro ⟨k,hk,theta,mu,lambda,_,_,_,he⟩
  have h0 : k=0 := by omega
  subst k
  have hf : Fraction.equiv (filledPatch theta mu lambda (ptm 0) (ptm 1) (qtm 0) (qtm 1)).1
      (Fraction.ofInt 1) := by
    change Fraction.equiv
      (filledPatch theta mu lambda (pt 1 (-1)) (pt 1 0) (pt 1 (-1)) (pt 1 1)).1
      (Fraction.ofInt 1)
    simp only [filledPatch,lerp,complement,pt,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub,
      Int.one_mul,Int.mul_one] <;>
      ac_nf <;> omega
  have hn : ¬ Fraction.equiv xtm.1 (Fraction.ofInt 1) := by decide
  exact hn (Fraction.equiv_trans he.1 hf)
example : Triangle (ptm 1) (qtm 1) xtm := by
  rcases difference_cover ptm qtm 1 ptmp qtmp ptmo qtmo
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ xtm qtmhit ptmmiss with h | h
  · exact False.elim (xtm_not_filled h)
  · exact h

-- The symmetric form also covers the reversed direction, with one common
-- terminal triangle orientation, rather than two different connector sets.
example : FilledRegion qf pf 2 xf := by
  rcases symmetric_difference_cover qf pf 2 qfpos pfpos qforient pforient
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ xf (Or.inl ⟨qfhit,pfmiss⟩) with h | h
  · exact h
  · exact False.elim (pf_terminal_miss ((triangle_swap _ _ _).mp h))

-- Intermediate radii may reverse their direction. Finite crossings need
-- no monotonicity premise for those radii.
private def radii (k : Nat) : Fraction :=
  Fraction.ofInt (if k=0 then 1 else if k=1 then 4 else if k=2 then 2 else 5)
example : ¬ Fraction.le (radii 1) (radii 2) := by decide
example : ∃ k, k<3 ∧ FanIntervalChain.Between (radii k) (Fraction.ofInt 3) (radii (k+1)) :=
  FanIntervalChain.finite_crossing radii (Fraction.ofInt 3) 3 (by decide)
    (Or.inl ⟨by decide,by decide⟩)

-- Interpolating at either endpoint makes one entire group weight zero.
-- Repeated vertices are allowed by the same convexity proof.
example (a b c d : Point) :
    FilledStrips.FilledCell a b c d (lerp zero (lerp half a b) (lerp third c d)) :=
  FilledStrips.filledCell_convex a b c d _ _ zero ⟨by decide,by decide⟩
    (FilledStrips.p_edge a b c d half ⟨by decide,by decide⟩)
    (FilledStrips.q_edge a b c d third ⟨by decide,by decide⟩)
example (a b : Point) :
    FilledStrips.FilledCell a a b b (lerp (Fraction.ofInt 1) (lerp half a a) (lerp third b b)) :=
  FilledStrips.filledCell_convex a a b b _ _ (Fraction.ofInt 1) ⟨by decide,by decide⟩
    (FilledStrips.p_edge a a b b half ⟨by decide,by decide⟩)
    (FilledStrips.q_edge a a b b third ⟨by decide,by decide⟩)

#print axioms symmetric_difference_cover
end NewtonLimitDynamics.Polygon.FanDifferenceReview
