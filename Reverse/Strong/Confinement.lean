import Reverse.KK.WeakSector

/-!
PHYSICAL STAGE:
  Colour sector: dimensional transmutation, mass gap, confinement and the
  low-energy hadron sector. The intended chain is
    SU(3)_colour → transmutation → Λ_colour → gap / confinement → singlets,
  so the colour coupling is never set to zero here.
MATHEMATICAL CONTENT:
  Separate hypotheses on a gauge sector, kept as distinct structures: colour
  scale, mass gap, Gauss-law gauge invariance, colour-singlet asymptotic
  spectrum, confinement (placeholder carrying the previous property), stable
  nucleons; and the hadron carrier inside the asymptotic spectrum.
INPUT PARAMETERS:
  Colour coupling g₃ (nonzero), colour spectrum.
OUTPUT PARAMETERS:
  Λ_colour, the gap, hadron states; hadronic masses are to be referred to
  Λ_colour in a later pass.
PROVED HERE:
  Formal consequences of the hypotheses: hadron states are singlets, hadron
  masses sit above the gap.
ASSUMED HERE:
  Existence of a positive colour scale; a positive mass gap above a massless
  vacuum; a colour-singlet asymptotic spectrum, as the consequence of
  confinement; stable proton- and neutron-like states.
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

/-- Gauss-law gauge invariance of the physical states: a kinematic property
of the physical state space of any gauge theory, confining or not. It says
nothing about confinement, because a gauge-invariant state can still carry
global colour charge. Recorded to keep the notions apart; nothing
downstream consumes it. -/
structure HasGaugeInvariantPhysicalStates (C : GaugeSector) where
  gauss : ∀ s : C.Spectrum, C.gaugeInvariant s

/-- The asymptotic particle spectrum consists of colour singlets: no
observable asymptotic coloured particle. This is the property the matter
sector consumes. -/
structure HasColourSingletAsymptoticSpectrum (C : GaugeSector) where
  singlet_of_asymptotic : ∀ s : C.Spectrum, C.asymptotic s → C.singlet s

/-- Confinement proper. PLACEHOLDER: the dynamical criterion (area law and
string tension, or the superselection structure of the charged sectors) is
not encoded. At this milestone the structure carries only the consequence
used downstream, so that a later pass can strengthen it without touching
its consumers. OPEN PROBLEM: rigorous QCD confinement. -/
structure HasConfinement (C : GaugeSector) where
  singlet_asymptotics : HasColourSingletAsymptoticSpectrum C

/-- Low-energy hadron sector read inside the physical spectrum, excluding the
vacuum. Its type depends on confinement and on the colour scale so that any
use of hadrons carries both hypotheses visibly. -/
structure HadronSector (C : GaugeSector) (_hConf : HasConfinement C)
    (_hΛ : HasColourScale C) where
  Hadron : Type
  state : Hadron → C.Spectrum
  asymptotic : ∀ h, C.asymptotic (state h)
  nonvacuum : ∀ h, state h ≠ C.vacuum

/-- Hadron states are colour singlets: a formal consequence of the singlet
asymptotic spectrum carried by confinement. -/
theorem HadronSector.singlet {C : GaugeSector} {hConf : HasConfinement C}
    {hΛ : HasColourScale C} (H : HadronSector C hConf hΛ) (h : H.Hadron) :
    C.singlet (H.state h) :=
  hConf.singlet_asymptotics.singlet_of_asymptotic (H.state h) (H.asymptotic h)

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
