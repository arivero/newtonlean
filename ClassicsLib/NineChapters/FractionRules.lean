/-!
Classical attestation of fraction operations, not an arithmetic dependency.
Core Rat remains encoding infrastructure. No existing proof is routed through
this file. Chinese results before the Principia belong in ClassicsLib by the
user's explicit chronology exception.

Witness: 九章算術 (四部叢刊本), 景上海涵芬樓藏微波榭刊本,
魏劉徽注 / 唐李淳風等奉敕注釋. Chinese Wikisource transcriptions:
I: https://zh.wikisource.org/w/index.php?oldid=2658134 (scan pages 13–25)
VIII: https://zh.wikisource.org/w/index.php?oldid=2658141 (scan pages 9–11)
Archived HTML, exact rule/commentary separation and SHA-256:
docs/classics/nine-chapters-I.md and nine-chapters-VIII.md.
Line wraps are joined; quoted characters and word order are retained.
S/R classifications are in THEOREM_CASCADE.md. Core proofs verify the stated
identities; they do not assert ancient use of Lean's algorithms or structures.
Chapter I uses positive parts and denominators. Chapter VIII below uses signed
positive integer quantities, embedded in Rat, without extending the source to
all signed rational arithmetic. No signed multiplication or signed order is
attributed here. The text's 無入 cases are encoded by an absent entry (0),
not offered as an attestation of a general theory of zero.
-/

namespace ClassicsLib.NineChapters

/-- The subtraction branch of 更相減損. The zero guards make the encoding
    total; the sourced theorem only asserts its positive-input case. The
    optional preliminary halving is accounted for in `yuefen_value`. -/
def commonMeasure (a b : Nat) : Nat :=
  if a = 0 then b else if b = 0 then a else if a = b then a
  else if b < a then commonMeasure (a-b) b else commonMeasure a (b-a)
termination_by a+b

/- 約分術, 卷一 方田. Exact rule text, separate from the small-type annotation:
術曰可半者半之不可半者副置分母子之數以少減多更相減損求其等也以等數約之

Proof correspondence (R): stop when the positive entries are equal; subtract
smaller from larger otherwise. Each subtraction preserves the common measure,
and the sum decreases. Identifying the resulting 等數 with the core name gcd
is a qualified algorithm reconstruction. Euclid VII.2 has a parallel common-
measure procedure; its Greek witness is independent and is not merged here. -/
theorem commonMeasure_eq_gcd (a b : Nat) (ha : 0<a) (hb : 0<b) :
    commonMeasure a b = Nat.gcd a b := by
  induction n : a+b using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    rw [commonMeasure]
    simp only [Nat.ne_of_gt ha, Nat.ne_of_gt hb, ↓reduceIte]
    by_cases he : a=b
    · subst b; simp
    · rw [ite_eq_right he]
      split
      · rename_i hlt
        rw [ih ((a-b)+b) (by omega) (a-b) b (by omega) hb rfl]
        exact Nat.gcd_sub_self_left (by omega)
      · rename_i hlt
        rw [ih (a+(b-a)) (by omega) a (b-a) ha (by omega) rfl]
        exact Nat.gcd_sub_self_right (by omega)

/- 約分術, same rule:
術曰可半者半之不可半者副置分母子之數以少減多更相減損求其等也以等數約之

Proof correspondence (S): dividing both positive entries by their common
measure preserves the value. The second clause separately verifies the
optional 可半者半之 step when both entries are divisible by two. Factor both
entries by the divisor and cancel it; no signed-input extension is claimed. -/
theorem yuefen_value (a b : Nat) (ha : 0<a) (hb : 0<b) :
    let g := commonMeasure a b
    (((a/g : Nat) : Rat) / ((b/g : Nat) : Rat) = (a : Rat)/b) ∧
      (2∣a → 2∣b → ((a/2 : Nat) : Rat) / ((b/2 : Nat) : Rat) = (a : Rat)/b) := by
  have cancel (k : Nat) (hk : 0<k) (hka : k∣a) (hkb : k∣b) :
      ((a/k : Nat) : Rat) / ((b/k : Nat) : Rat) = (a : Rat)/b := by
    have hx := congrArg (fun n : Nat => (n : Rat)) (Nat.div_mul_cancel hka)
    have hy := congrArg (fun n : Nat => (n : Rat)) (Nat.div_mul_cancel hkb)
    simp only [Rat.natCast_mul] at hx hy
    have hk' : (k : Rat) ≠ 0 := by simp [Nat.ne_of_gt hk]
    have hb' : (b : Rat) ≠ 0 := by simp [Nat.ne_of_gt hb]
    grind
  dsimp
  rw [commonMeasure_eq_gcd a b ha hb]
  exact ⟨cancel _ (Nat.gcd_pos_of_pos_left b ha)
    (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b),
    fun h2a h2b => cancel 2 (by decide) h2a h2b⟩

/- 合分術, 卷一 方田. Rule excerpt (not Liu Hui's explanation of 齊/同):
術曰母互乘子并以爲實母相乘爲法
實如法而一不滿法者以法命之

Proof correspondence (S): cross-multiply the numerators, add them, multiply
the denominators, then divide 實 by 法. Two positive fractions are the stated
case; returning the rational value abstracts the mixed-number output. -/
theorem hefen (a b c d : Nat) (_ha : 0<a) (hb : 0<b) (_hc : 0<c) (hd : 0<d) :
    (a : Rat)/b+(c : Rat)/d = ((a : Rat)*d+c*b)/(b*d) := by
  have hb' : (b : Rat) ≠ 0 := by simp [Nat.ne_of_gt hb]
  have hd' : (d : Rat) ≠ 0 := by simp [Nat.ne_of_gt hd]
  grind

/- 減分術, 卷一 方田:
術曰母互乘子以少減多餘爲實母相乘爲法實如法而一

Proof correspondence (S): cross-multiply, subtract smaller from larger, then
divide by the product denominator. The strict hypothesis enforces 以少減多;
this is not an attestation of negative fractions or zero-result subtraction. -/
theorem jianfen (a b c d : Nat) (_ha : 0<a) (hb : 0<b) (_hc : 0<c) (hd : 0<d)
    (_hsmall : c*b<a*d) :
    (a : Rat)/b-(c : Rat)/d = ((a : Rat)*d-c*b)/(b*d) := by
  have hb' : (b : Rat) ≠ 0 := by simp [Nat.ne_of_gt hb]
  have hd' : (d : Rat) ≠ 0 := by simp [Nat.ne_of_gt hd]
  grind

/- 課分術, 卷一 方田 (乗 is retained from this witness):
術曰母互乘子以少減多餘爲實母相乗爲法實如法而一卽相多也

Proof correspondence (R): the text computes which fraction exceeds the other
and by how much. The comparison criterion below isolates that first step;
it does not claim that the text states this modern iff formulation. Positive
denominators preserve comparison when each is cleared. -/
theorem kefen (a b c d : Nat) (_ha : 0<a) (hb : 0<b) (_hc : 0<c) (hd : 0<d) :
    (a : Rat)/b < (c : Rat)/d ↔ a*d<c*b := by
  have hb' : 0 < (b : Rat) := Rat.natCast_pos.mpr hb
  have hd' : 0 < (d : Rat) := Rat.natCast_pos.mpr hd
  rw [Rat.div_lt_iff hb']
  have he : (c : Rat)/d*b = (c*b)/d := by grind
  rw [he, Rat.lt_div_iff hd']
  simp only [← Rat.natCast_mul, Rat.natCast_lt_natCast]

/- 平分術, 卷一 方田 (all small-type commentary is excluded):
術曰母互乘子副并爲平實母相乘爲法以列數乘未并者各自爲列實亦以列數乘法
以平實減列實餘約之爲所減并所減以益於少以法命平實各得其平

Proof correspondence (R): a nonempty list encodes the positive parts; its
length is 列數. Their common value is the sum divided by the number of parts.
The first clause conserves the total. The other clauses remove an excess or
add a deficit to reach that value. This is the averaging/redistribution
identity, not an execution model of the text's common-denominator work array. -/
theorem pingfen (parts : List Rat) (hne : parts ≠ []) (_hp : ∀ q ∈ parts, 0<q) :
    let m := parts.sum/(parts.length : Rat)
    m*(parts.length : Rat) = parts.sum ∧
      ∀ q ∈ parts, (m<q → q-(q-m)=m) ∧ (q<m → q+(m-q)=m) := by
  have hn : (parts.length : Rat) ≠ 0 := by simp [List.length_eq_zero_iff, hne]
  dsimp
  constructor
  · exact Rat.div_mul_cancel hn
  · intro q hq
    constructor <;> intro h <;> grind

/- 乘分術, 卷一 方田:
術曰母相乘爲法子相乘爲實實如法而一

Proof correspondence (S): multiply positive numerators and denominators, then
divide the resulting 實 by 法. Signed multiplication is outside this statement. -/
theorem chengfen (a b c d : Nat) (_ha : 0<a) (_hb : 0<b) (_hc : 0<c) (_hd : 0<d) :
    ((a : Rat)/b)*((c : Rat)/d) = ((a : Rat)*c)/(b*d) := by
  grind

/- 經分術, 卷一 方田:
術曰以人數爲法錢數爲實實如法而一有分者通之重有分者同而通之

Proof correspondence (S): money is divided by the number of people, each
possibly fractional. 通之 clears the parts on both sides; the dividend a/b
and divisor c/d give the positive share ad/(bc). Their roles are not swapped. -/
theorem jingfen (a b c d : Nat) (_ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    ((a : Rat)/b)/((c : Rat)/d) = ((a : Rat)*d)/(b*c) := by
  have hb' : (b : Rat) ≠ 0 := by simp [Nat.ne_of_gt hb]
  have hc' : (c : Rat) ≠ 0 := by simp [Nat.ne_of_gt hc]
  have hd' : (d : Rat) ≠ 0 := by simp [Nat.ne_of_gt hd]
  grind

/- Commentary witness, NOT 術: Liu Hui's commentary, dated 263 CE, transmitted
with later Li Chunfeng annotations in this edition. Exact opening annotation:
今兩算得失相反要令正負以名之正算赤負算黑否則以邪正爲異

It names opposite gains/losses 正/負 and distinguishes rods by colour or
orientation. This is separate evidence from the two procedural clauses below;
it does not date this surviving printed/transcribed witness to 263. See the
companion for the chronology reference and the limits of textual collation. -/

/- 正負術, 卷八 方程, subtraction clause (not the preceding annotation):
正負術曰同名相除異名相益正無入負之負無入正之

Proof correspondence (R): same-named quantities subtract their magnitudes;
opposite names add magnitudes. Nat differences and a case distinction encode
which named quantity remains. 無入 is an absent opposing entry, represented
by 0 only in these explicit cases. Positive whole magnitudes are embedded in
Rat; no theorem about general signed rationals or numerical order is sourced. -/
theorem zhengfu_sub (a b : Nat) (_ha : 0<a) (_hb : 0<b) :
    ((a : Rat)-(b : Rat) = if b≤a then ((a-b : Nat) : Rat) else -((b-a : Nat) : Rat)) ∧
    (-(a : Rat)-(-(b : Rat)) = if b≤a then -((a-b : Nat) : Rat) else ((b-a : Nat) : Rat)) ∧
    ((a : Rat)-(-(b : Rat)) = ((a+b : Nat) : Rat)) ∧
    (-(a : Rat)-(b : Rat) = -((a+b : Nat) : Rat)) ∧
    (0-(a : Rat) = -(a : Rat)) ∧ (0-(-(a : Rat)) = (a : Rat)) := by
  by_cases h : b≤a
  · have hd := congrArg (fun n : Nat => (n : Rat)) (Nat.sub_add_cancel h)
    simp only [Rat.natCast_add] at hd
    simp only [h, ↓reduceIte, Rat.natCast_add]
    grind
  · have hd := congrArg (fun n : Nat => (n : Rat)) (Nat.sub_add_cancel (show a≤b by omega))
    simp only [Rat.natCast_add] at hd
    simp only [h, ↓reduceIte, Rat.natCast_add]
    grind

/- 正負術, 卷八 方程, addition clause:
其異名相除同名相益正無入正之負無入負之

Proof correspondence (R): opposite names subtract magnitudes; same names add
them. Case distinctions retain the surviving name, with the text's explicit
absent-entry cases. As above, Rat only encodes signed positive whole quantities. -/
theorem zhengfu_add (a b : Nat) (_ha : 0<a) (_hb : 0<b) :
    ((a : Rat)+(b : Rat) = ((a+b : Nat) : Rat)) ∧
    (-(a : Rat)+(-(b : Rat)) = -((a+b : Nat) : Rat)) ∧
    ((a : Rat)+(-(b : Rat)) = if b≤a then ((a-b : Nat) : Rat) else -((b-a : Nat) : Rat)) ∧
    (-(a : Rat)+(b : Rat) = if b≤a then -((a-b : Nat) : Rat) else ((b-a : Nat) : Rat)) ∧
    (0+(a : Rat) = (a : Rat)) ∧ (0+(-(a : Rat)) = -(a : Rat)) := by
  by_cases h : b≤a
  · have hd := congrArg (fun n : Nat => (n : Rat)) (Nat.sub_add_cancel h)
    simp only [Rat.natCast_add] at hd
    simp only [h, ↓reduceIte, Rat.natCast_add]
    grind
  · have hd := congrArg (fun n : Nat => (n : Rat)) (Nat.sub_add_cancel (show a≤b by omega))
    simp only [Rat.natCast_add] at hd
    simp only [h, ↓reduceIte, Rat.natCast_add]
    grind

end ClassicsLib.NineChapters
