import BarrowLib.Polygon.PointAlgebra

namespace NewtonLimitDynamics.Polygon.TimeSubdivision

open NewtonLimitDynamics

def positiveDuration (d : Fraction) : Prop := Fraction.positive d

/-- One finite end-kick cell: drift using the incoming velocity, then change
    velocity by the constant accelerative force times the cell duration. -/
def endKick (d : Fraction) (state : Point × Point) (a : Point) : Point × Point :=
  (pointAdd state.1 (pointScale d state.2), pointAdd state.2 (pointScale d a))

def coarse (h k : Fraction) (p v a : Point) : Point × Point :=
  endKick (Fraction.add h k) (p, v) a

def fine (h k : Fraction) (p v a : Point) : Point × Point :=
  endKick k (endKick h (p, v) a) a

def totalDuration (h k : Fraction) : Fraction := Fraction.add h k

theorem totalDuration_positive (h k : Fraction)
    (hh : positiveDuration h) (hk : positiveDuration k) :
    positiveDuration (totalDuration h k) := by
  unfold positiveDuration totalDuration Fraction.positive Fraction.add
  dsimp
  exact Int.add_pos (Int.mul_pos hh k.den_pos) (Int.mul_pos hk h.den_pos)

private theorem fine_position_scalar (h k p v a : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add p (Fraction.mul h v))
        (Fraction.mul k (Fraction.add v (Fraction.mul h a))))
      (Fraction.add (Fraction.add p (Fraction.mul (Fraction.add h k) v))
        (Fraction.mul (Fraction.mul h k) a)) := by
  have hdist : Fraction.equiv (Fraction.mul k (Fraction.add v (Fraction.mul h a)))
      (Fraction.add (Fraction.mul k v) (Fraction.mul k (Fraction.mul h a))) :=
    Fraction.mul_add k v (Fraction.mul h a)
  have hkv : Fraction.equiv (Fraction.add (Fraction.mul h v) (Fraction.mul k v))
      (Fraction.mul (Fraction.add h k) v) := by
    exact Fraction.equiv_trans (Fraction.add_equiv (Fraction.mul_comm h v) (Fraction.mul_comm k v))
      (Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_add v h k))
        (Fraction.equiv_symm (Fraction.mul_comm (Fraction.add h k) v)))
  have hka : Fraction.equiv (Fraction.mul k (Fraction.mul h a))
      (Fraction.mul (Fraction.mul h k) a) := by
    exact Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_assoc k h a))
      (Fraction.mul_equiv_right a (Fraction.mul_comm k h))
  exact Fraction.equiv_trans
    (Fraction.equiv_trans (Fraction.add_assoc p (Fraction.mul h v)
      (Fraction.mul k (Fraction.add v (Fraction.mul h a))))
      (Fraction.add_equiv_left p (Fraction.add_equiv (Fraction.equiv_refl (Fraction.mul h v)) hdist)))
    (Fraction.equiv_trans
      (Fraction.add_equiv_left p (Fraction.equiv_symm (Fraction.add_assoc (Fraction.mul h v)
        (Fraction.mul k v) (Fraction.mul k (Fraction.mul h a)))))
      (Fraction.equiv_trans (Fraction.add_equiv_left p (Fraction.add_equiv hkv hka))
        (Fraction.equiv_symm (Fraction.add_assoc p (Fraction.mul (Fraction.add h k) v)
          (Fraction.mul (Fraction.mul h k) a)))))

/-- For the stated end-kick scheduling convention, time subdivision changes
    the final position by `h*k*a`.  This is finite Fraction arithmetic, not a
    trajectory-existence theorem or a Newton central-force theorem. -/
theorem fine_position_eq_coarse_plus (h k : Fraction) (p v a : Point) :
    pointEquiv (fine h k p v a).1
      (pointAdd (coarse h k p v a).1 (pointScale (Fraction.mul h k) a)) := by
  constructor <;> apply fine_position_scalar

private theorem fine_velocity_scalar (h k v a : Fraction) :
    Fraction.equiv (Fraction.add (Fraction.add v (Fraction.mul h a)) (Fraction.mul k a))
      (Fraction.add v (Fraction.mul (Fraction.add h k) a)) := by
  exact Fraction.equiv_trans (Fraction.add_assoc v (Fraction.mul h a) (Fraction.mul k a))
    (Fraction.equiv_trans
      (Fraction.add_equiv_left v (Fraction.add_equiv (Fraction.mul_comm h a) (Fraction.mul_comm k a)))
      (Fraction.equiv_trans
        (Fraction.add_equiv_left v (Fraction.equiv_symm (Fraction.mul_add a h k)))
        (Fraction.add_equiv_left v (Fraction.equiv_symm (Fraction.mul_comm (Fraction.add h k) a)))))

theorem fine_velocity_eq_coarse (h k : Fraction) (p v a : Point) :
    pointEquiv (fine h k p v a).2 (coarse h k p v a).2 := by
  constructor <;>
    dsimp [fine, coarse, endKick, pointAdd, pointScale] <;>
    apply fine_velocity_scalar

def half : Fraction := ⟨1, 2, by decide⟩
def zero : Fraction := Fraction.ofInt 0
def one : Fraction := Fraction.ofInt 1
def quarter : Fraction := ⟨1, 4, by decide⟩
def negQuarter : Fraction := ⟨-1, 4, by decide⟩

def exampleP : Point := (zero, zero)
def exampleV : Point := (one, zero)
def exampleA : Point := (zero, one)
def exampleB : Point := (half, zero)
def exampleC : Point := (one, zero)
def exampleD : Point := (one, quarter)

theorem example_half_positive : positiveDuration half := by
  unfold positiveDuration Fraction.positive half
  decide

theorem example_total_positive : positiveDuration (totalDuration half half) :=
  totalDuration_positive half half example_half_positive example_half_positive

theorem example_coarse_position : pointEquiv (coarse half half exampleP exampleV exampleA).1 exampleC := by
  decide

theorem example_fine_middle : pointEquiv (endKick half (exampleP, exampleV) exampleA).1 exampleB := by
  decide

theorem example_fine_position : pointEquiv (fine half half exampleP exampleV exampleA).1 exampleD := by
  decide

theorem example_endpoints_differ : ¬ pointEquiv exampleD exampleC := by
  intro h
  have := h.2
  change (1 : Int) * 1 = 0 * 4 at this
  omega

theorem example_fine_coarse_endpoints_differ :
    ¬ pointEquiv (fine half half exampleP exampleV exampleA).1
      (coarse half half exampleP exampleV exampleA).1 := by
  intro h
  exact example_endpoints_differ
    ⟨Fraction.equiv_trans (Fraction.equiv_symm example_fine_position.1)
        (Fraction.equiv_trans h.1 example_coarse_position.1),
      Fraction.equiv_trans (Fraction.equiv_symm example_fine_position.2)
        (Fraction.equiv_trans h.2 example_coarse_position.2)⟩

/-- The explicitly directed closing connector from the fine endpoint D to the
    coarse endpoint C.  It is bookkeeping for a closed finite boundary. -/
def directedConnector (d c : Point) : Point := pointSub c d

theorem example_connector : pointEquiv (directedConnector exampleD exampleC) (zero, negQuarter) := by
  decide


theorem example_closedBoundaryTwice :
    Fraction.equiv (closedBoundaryTwice exampleP exampleB exampleD exampleC) (⟨-1, 8, by decide⟩) := by
  decide

end NewtonLimitDynamics.Polygon.TimeSubdivision
