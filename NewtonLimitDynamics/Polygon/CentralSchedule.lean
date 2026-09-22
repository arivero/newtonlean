import NewtonLimitDynamics.Polygon.TimeSubdivision

/-!
Finite impulse polygons for an arbitrary position-dependent central force,
with arbitrary (possibly unequal) rational time cells.  Modern rational
coordinate reconstruction motivated by the finite part of Proposition I
(1687 NATP00077 par45, 1713 NATP00082 par51), which divides time into
*equal* parts and applies each impulse at the vertex reached by inertial
motion.  The centre S is the origin.  No curve, limit or force regularity is
assumed; the field is an arbitrary function on represented points.
-/

namespace NewtonLimitDynamics.Polygon.CentralSchedule

open NewtonLimitDynamics
open TimeSubdivision

/-- An accelerative force field on represented points. -/
abbrev Field := Point → Point

/-- Central about S: the force at each point is parallel to the radius. -/
def central (a : Field) : Prop :=
  ∀ p, Fraction.equiv (det p (a p)) (Fraction.ofInt 0)

/-- One cell: inertial drift for duration `d` with the incoming velocity, then
    the impulse of the field at the arrival vertex. -/
def cell (a : Field) (d : Fraction) (s : Point × Point) : Point × Point :=
  (pointAdd s.1 (pointScale d s.2),
    pointAdd s.2 (pointScale d (a (pointAdd s.1 (pointScale d s.2)))))

/-- Doubled areal velocity `det(position, velocity)` about S. -/
def momentum (s : Point × Point) : Fraction := det s.1 s.2

/-- The constructed polygon for a finite list of rational cell durations. -/
def schedule (a : Field) : List Fraction → Point × Point → Point × Point
  | [], s => s
  | d :: ds, s => schedule a ds (cell a d s)

/-- Sum of doubled triangle areas `S x_i x_(i+1)` over the schedule. -/
def swept (a : Field) : List Fraction → Point × Point → Fraction
  | [], _ => Fraction.ofInt 0
  | d :: ds, s => Fraction.add (det s.1 (cell a d s).1) (swept a ds (cell a d s))

/-- Total elapsed time of the schedule. -/
def elapsed : List Fraction → Fraction
  | [] => Fraction.ofInt 0
  | d :: ds => Fraction.add d (elapsed ds)

theorem det_drift (x v : Point) (d : Fraction) :
    Fraction.equiv (det (pointAdd x (pointScale d v)) v) (det x v) := by
  unfold Fraction.equiv det pointAdd pointScale Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem det_kick_split (x v w : Point) (d : Fraction) :
    Fraction.equiv (det x (pointAdd v (pointScale d w)))
      (Fraction.add (det x v) (Fraction.mul d (det x w))) := by
  unfold Fraction.equiv det pointAdd pointScale Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- The doubled triangle swept in one drift is duration times areal velocity. -/
theorem det_cell_area (x v : Point) (d : Fraction) :
    Fraction.equiv (det x (pointAdd x (pointScale d v))) (Fraction.mul d (det x v)) := by
  unfold Fraction.equiv det pointAdd pointScale Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

private theorem add_equiv_left (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.add c a) (Fraction.add c b) :=
  Fraction.equiv_trans (Fraction.add_comm c a)
    (Fraction.equiv_trans (Fraction.add_equiv_right c h) (Fraction.add_comm b c))

private theorem mul_equiv_right (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.mul a c) (Fraction.mul b c) :=
  Fraction.equiv_trans (Fraction.mul_comm a c)
    (Fraction.equiv_trans (Fraction.mul_equiv_left c h) (Fraction.mul_comm c b))

private theorem mul_zero (d : Fraction) :
    Fraction.equiv (Fraction.mul d (Fraction.ofInt 0)) (Fraction.ofInt 0) := by
  unfold Fraction.equiv Fraction.mul Fraction.ofInt
  simp

private theorem add_zero (c : Fraction) :
    Fraction.equiv (Fraction.add c (Fraction.ofInt 0)) c := by
  unfold Fraction.equiv Fraction.add Fraction.ofInt
  simp only [Int.mul_one, Int.zero_mul, Int.add_zero]
  try ac_rfl

private theorem add_mul (a b c : Fraction) :
    Fraction.equiv (Fraction.mul (Fraction.add a b) c)
      (Fraction.add (Fraction.mul a c) (Fraction.mul b c)) := by
  unfold Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add]
  try ac_nf

/-- A central impulse at `x` leaves `det(x, ·)` unchanged. -/
theorem central_kick (a : Field) (hc : central a) (x v : Point) (d : Fraction) :
    Fraction.equiv (det x (pointAdd v (pointScale d (a x)))) (det x v) :=
  Fraction.equiv_trans (det_kick_split x v (a x) d)
    (Fraction.equiv_trans
      (add_equiv_left (det x v)
        (Fraction.equiv_trans (Fraction.mul_equiv_left d (hc x)) (mul_zero d)))
      (add_zero (det x v)))

/-- Each cell (drift, then central impulse at the arrival vertex) preserves the
    areal velocity exactly, for any cell duration. -/
theorem cell_momentum (a : Field) (hc : central a) (d : Fraction) (s : Point × Point) :
    Fraction.equiv (momentum (cell a d s)) (momentum s) :=
  Fraction.equiv_trans (central_kick a hc _ s.2 d) (det_drift s.1 s.2 d)

theorem schedule_momentum (a : Field) (hc : central a) :
    (ds : List Fraction) → (s : Point × Point) →
    Fraction.equiv (momentum (schedule a ds s)) (momentum s)
  | [], _ => Fraction.equiv_refl _
  | d :: ds, s =>
      Fraction.equiv_trans (schedule_momentum a hc ds (cell a d s)) (cell_momentum a hc d s)

/-- Areas proportional to times, for arbitrary unequal rational cells and any
    central field: the swept doubled area equals elapsed time times the initial
    doubled areal velocity. -/
theorem swept_eq (a : Field) (hc : central a) :
    (ds : List Fraction) → (s : Point × Point) →
    Fraction.equiv (swept a ds s) (Fraction.mul (elapsed ds) (momentum s))
  | [], _ => by
      unfold swept elapsed Fraction.equiv Fraction.mul Fraction.ofInt
      simp
  | d :: ds, s => by
      have hcell : Fraction.equiv (det s.1 (cell a d s).1) (Fraction.mul d (momentum s)) :=
        det_cell_area s.1 s.2 d
      have hrest : Fraction.equiv (swept a ds (cell a d s))
          (Fraction.mul (elapsed ds) (momentum s)) :=
        Fraction.equiv_trans (swept_eq a hc ds (cell a d s))
          (Fraction.mul_equiv_left (elapsed ds) (cell_momentum a hc d s))
      exact Fraction.equiv_trans
        (Fraction.equiv_trans (Fraction.add_equiv_right _ hcell) (add_equiv_left _ hrest))
        (Fraction.equiv_symm (add_mul d (elapsed ds) (momentum s)))

/-- Refinement of one cell `h+k` into `h` then `k`, for an arbitrary field:
    the fine endpoint exceeds the coarse one by exactly `h*k` times the force at
    the intermediate vertex.  No regularity of the field is used. -/
theorem refine_position (a : Field) (h k : Fraction) (s : Point × Point) :
    pointEquiv (cell a k (cell a h s)).1
      (pointAdd (cell a (Fraction.add h k) s).1
        (pointScale (Fraction.mul h k) (a (cell a h s).1))) := by
  constructor <;>
  · unfold cell pointAdd pointScale Fraction.equiv Fraction.add Fraction.mul
    dsimp
    simp only [Int.add_mul, Int.mul_add]
    ac_nf

private def fsub (p q : Fraction) : Fraction := Fraction.add p ⟨-q.num, q.den, q.den_pos⟩

private theorem velocity_scalar (v ay az aX h k : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add v (Fraction.mul h ay)) (Fraction.mul k az))
      (Fraction.add (Fraction.add v (Fraction.mul (Fraction.add h k) aX))
        (Fraction.add (Fraction.mul h (fsub ay aX)) (Fraction.mul k (fsub az aX)))) := by
  unfold fsub Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Velocity mismatch of the same refinement, exactly: the fine velocity equals
    the coarse one plus `h*(a y - a X) + k*(a z - a X)`, where `y`, `z` are the
    fine vertices and `X` the coarse vertex.  It vanishes for a constant field;
    otherwise its control is a premise about the field, not a consequence of
    the construction. -/
theorem refine_velocity (a : Field) (h k : Fraction) (s : Point × Point) :
    pointEquiv (cell a k (cell a h s)).2
      (pointAdd (cell a (Fraction.add h k) s).2
        (pointAdd
          (pointScale h (pointSub (a (cell a h s).1) (a (cell a (Fraction.add h k) s).1)))
          (pointScale k (pointSub (a (cell a k (cell a h s)).1) (a (cell a (Fraction.add h k) s).1))))) :=
  ⟨velocity_scalar _ _ _ _ _ _, velocity_scalar _ _ _ _ _ _⟩

theorem det_add_right (x v w : Point) :
    Fraction.equiv (det x (pointAdd v w)) (Fraction.add (det x v) (det x w)) := by
  unfold Fraction.equiv det pointAdd Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

private theorem add_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) : Fraction.equiv (Fraction.add a c) (Fraction.add b d) :=
  Fraction.equiv_trans (Fraction.add_equiv_right c h) (add_equiv_left b k)

private theorem expand_left (d d' L K : Fraction) :
    Fraction.equiv (Fraction.mul d (Fraction.mul d' (Fraction.add L K)))
      (Fraction.add (Fraction.mul (Fraction.mul d d') L) (Fraction.mul (Fraction.mul d d') K)) := by
  unfold Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

private theorem expand_right (d d' L : Fraction) :
    Fraction.equiv (Fraction.mul d' (Fraction.mul d L)) (Fraction.mul (Fraction.mul d d') L) := by
  unfold Fraction.equiv Fraction.mul
  dsimp
  ac_nf

private theorem add_cancel_num {P Q : Fraction} (h : Fraction.equiv (Fraction.add P Q) P) :
    Q.num = 0 := by
  unfold Fraction.equiv Fraction.add at h
  dsimp at h
  have hpd := P.den_pos
  have e1 : P.num * Q.den * P.den = P.num * (P.den * Q.den) := by ac_rfl
  have hz : Q.num * P.den * P.den = 0 := by
    rw [Int.add_mul] at h
    omega
  rcases Int.mul_eq_zero.mp hz with h1 | h1
  · rcases Int.mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · omega
  · omega

/-- Converse for **unequal** cells (motivated by Proposition II, whose statement
    speaks of areas proportional to times): drift `d` from `x` with velocity
    `v`, an arbitrary impulse `J` at the arrival vertex `x'`, then drift `d'`.
    If the two doubled areas are proportional to the nonzero durations, the
    impulse is parallel to the radius `Sx'`. -/
theorem unequal_cells_converse (x v J : Point) (d d' : Fraction)
    (hd : d.num ≠ 0) (hd' : d'.num ≠ 0)
    (h : Fraction.equiv
      (Fraction.mul d (det (pointAdd x (pointScale d v))
        (pointAdd (pointAdd x (pointScale d v)) (pointScale d' (pointAdd v J)))))
      (Fraction.mul d' (det x (pointAdd x (pointScale d v))))) :
    Fraction.equiv (det (pointAdd x (pointScale d v)) J) (Fraction.ofInt 0) := by
  -- second triangle: d' * (L + K), with L = det x v and K = det x' J
  have hA : Fraction.equiv
      (det (pointAdd x (pointScale d v))
        (pointAdd (pointAdd x (pointScale d v)) (pointScale d' (pointAdd v J))))
      (Fraction.mul d' (Fraction.add (det x v) (det (pointAdd x (pointScale d v)) J))) :=
    Fraction.equiv_trans (det_cell_area _ _ d')
      (Fraction.mul_equiv_left d'
        (Fraction.equiv_trans (det_add_right _ v J)
          (Fraction.add_equiv_right _ (det_drift x v d))))
  have hB := det_cell_area x v d
  have h1 := Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_equiv_left d hA))
    (Fraction.equiv_trans h (Fraction.mul_equiv_left d' hB))
  have h2 := Fraction.equiv_trans (Fraction.equiv_symm (expand_left d d' _ _))
    (Fraction.equiv_trans h1 (expand_right d d' _))
  have hq := add_cancel_num h2
  have hq' : d.num * d'.num * (det (pointAdd x (pointScale d v)) J).num = 0 := hq
  have hK : (det (pointAdd x (pointScale d v)) J).num = 0 := by
    rcases Int.mul_eq_zero.mp hq' with h3 | h3
    · rcases Int.mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hd
      · exact absurd h4 hd'
    · exact h3
  unfold Fraction.equiv Fraction.ofInt
  dsimp
  rw [hK]
  simp

/-- A varying central field: force proportional to distance, toward S. -/
def harmonic : Field := fun p => pointNeg p

theorem harmonic_central : central harmonic := by
  intro p
  unfold harmonic pointNeg det Fraction.equiv Fraction.add Fraction.mul Fraction.ofInt
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.zero_mul]
  ac_nf
  omega

def exampleState : Point × Point := ((one, zero), (zero, one))

/-- In the harmonic example, refining a unit cell into two half cells changes the
    terminal velocity as well as the endpoint: a varying force breaks the
    exact velocity agreement that holds for constant force. -/
theorem harmonic_refinement_changes_velocity :
    ¬ pointEquiv (cell harmonic half (cell harmonic half exampleState)).2
        (cell harmonic (Fraction.add half half) exampleState).2 ∧
    ¬ pointEquiv (cell harmonic half (cell harmonic half exampleState)).1
        (cell harmonic (Fraction.add half half) exampleState).1 := by
  decide

/-- Both schedules nevertheless sweep the same doubled area, as `swept_eq`
    requires: elapsed time times the initial areal velocity. -/
theorem harmonic_equal_swept :
    Fraction.equiv (swept harmonic [half, half] exampleState)
      (swept harmonic [Fraction.add half half] exampleState) := by
  decide

end NewtonLimitDynamics.Polygon.CentralSchedule
