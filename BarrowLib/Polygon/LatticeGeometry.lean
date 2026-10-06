import Std

namespace NewtonLimitDynamics.Polygon

/-- A concrete consistency model in integer coordinates. The synthetic result
    above is conditional on the named Euclidean identities, not on coordinates. -/
abbrev LatticePoint := Int × Int

def det (p q : LatticePoint) : Int := p.1 * q.2 - p.2 * q.1

def extend (p q : LatticePoint) : LatticePoint := (2*q.1-p.1, 2*q.2-p.2)
def kick (q x : LatticePoint) (j : Int) : LatticePoint := (x.1+j*q.1, x.2+j*q.2)


end NewtonLimitDynamics.Polygon
