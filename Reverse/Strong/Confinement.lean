import Reverse.KK.WeakSector

/-!
PHYSICAL STAGE:
  Colour sector: dimensional transmutation, mass gap, confinement and the
  low-energy hadron sector. The intended chain is
    SU(3)_colour → transmutation → Λ_colour → gap / confinement → singlets,
  so the colour coupling is never set to zero here.
MATHEMATICAL CONTENT:
  Three logically distinct hypotheses on a gauge sector, kept as separate
  structures, and the hadron carrier that only exists given confinement.
INPUT PARAMETERS:
  Colour coupling g₃ (nonzero), colour spectrum.
OUTPUT PARAMETERS:
  Λ_colour, the gap, hadron states; hadronic masses are to be referred to
  Λ_colour in a later pass.
PROVED HERE:
  Formal consequences of the hypotheses: hadron states are singlets, hadron
  masses sit above the gap.
ASSUMED HERE:
  Existence of a positive colour scale; a positive mass gap; confinement;
  stable proton- and neutron-like singlet states.
OPEN PROBLEMS USED:
  3+1-dimensional Yang–Mills mass gap; rigorous QCD confinement.
NEXT REDUCTION:
  `Reverse/Matter/NeutralMatter.lean`: nuclei and neutral composite matter.

STATUS: open problems (gap, confinement) and physical hypotheses (scale,
nucleons), with their formal consequences as theorems.
-/

namespace Reverse.Strong
open Reverse.Parent Reverse.KK NewtonLimitDynamics

/-- Dimensional transmutation: the sector owns a positive scale Λ. The
running that trades the coupling for Λ is physics outside this interface. -/
structure HasColourScale (C : GaugeSector) where
  scale : Scalar
  scale_positive : Fraction.positive scale

/-- Mass gap: the vacuum is massless and every other physical state has mass
at least `gap > 0`. OPEN PROBLEM in 3+1 dimensions; stated, never proved,
here. -/
structure HasMassGap (C : GaugeSector) where
  gap : Scalar
  gap_positive : Fraction.positive gap
  vacuum_massless : (C.mass C.vacuum).num = 0
  above_gap : ∀ s : C.Spectrum, s ≠ C.vacuum → Fraction.le gap (C.mass s)

/-- Confinement: every physical state is gauge invariant (a colour singlet).
Logically distinct from the mass gap and from the existence of nucleons. -/
structure HasConfinement (C : GaugeSector) where
  physical_states_invariant : ∀ s : C.Spectrum, C.invariant s

/-- Low-energy hadron sector read inside the physical spectrum, excluding the
vacuum. Its type depends on confinement and on the colour scale so that any
use of hadrons carries both hypotheses visibly. -/
structure HadronSector (C : GaugeSector) (_hConf : HasConfinement C)
    (_hΛ : HasColourScale C) where
  Hadron : Type
  state : Hadron → C.Spectrum
  nonvacuum : ∀ h, state h ≠ C.vacuum

/-- Hadron states are colour singlets: a formal consequence of confinement. -/
theorem HadronSector.singlet {C : GaugeSector} {hConf : HasConfinement C}
    {hΛ : HasColourScale C} (H : HadronSector C hConf hΛ) (h : H.Hadron) :
    C.invariant (H.state h) :=
  hConf.physical_states_invariant (H.state h)

/-- Hadron masses lie above the gap: a formal consequence of the gap for
non-vacuum states. -/
theorem HadronSector.mass_above_gap {C : GaugeSector} {hConf : HasConfinement C}
    {hΛ : HasColourScale C} (H : HadronSector C hConf hΛ) (hGap : HasMassGap C)
    (h : H.Hadron) : Fraction.le hGap.gap (C.mass (H.state h)) :=
  hGap.above_gap (H.state h) (H.nonvacuum h)

/-- Stable proton- and neutron-like states. Their existence is a hypothesis
separate from gap and confinement. Neutron stability presupposes the weak
decoupling recorded upstream; that link is physical interpretation. -/
structure HasStableNucleons {C : GaugeSector} {hConf : HasConfinement C}
    {hΛ : HasColourScale C} (H : HadronSector C hConf hΛ) where
  proton : H.Hadron
  neutron : H.Hadron
  distinct : proton ≠ neutron
  proton_mass_positive : Fraction.positive (C.mass (H.state proton))
  neutron_mass_positive : Fraction.positive (C.mass (H.state neutron))

end Reverse.Strong
