import BarrowLib.Polygon.MonotoneRectangles
import ModernLib.Foundation.Polygon.CompletionGeometry

namespace NewtonLimitDynamics.Polygon.MonotoneRectangles
open NewtonLimitDynamics TimeSubdivision PositionValues CompletionGeometry

def completed (A : Point → Prop) (x : PositionValue) : Prop :=
  Closure (fun z => ∃ y : Point, A y ∧ z=embedPosition y) x

/-- Metric closure transfers the proved point-set enclosure to all completed
points, rather than retaining only rational samples of the figure. -/
theorem completed_enclosure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) :
    (∀ x, completed (lowerFigure g p) x → completed (figure g a b) x) ∧
      (∀ x, completed (figure g a b) x → completed (upperFigure g p) x) := by
  have hs := figure_enclosure g p hg
  constructor
  · intro x hx
    exact closure_mono _ _ (fun z hz => by
      obtain ⟨y,hy,he⟩ := hz; exact ⟨y,hs.1 y hy,he⟩) x hx
  · intro x hx
    exact closure_mono _ _ (fun z hz => by
      obtain ⟨y,hy,he⟩ := hz; exact ⟨y,hs.2 y hy,he⟩) x hx


end NewtonLimitDynamics.Polygon.MonotoneRectangles
