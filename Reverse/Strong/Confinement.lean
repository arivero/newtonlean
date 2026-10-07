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
  nucleons. The hadron spectrum is defined as the asymptotic non-vacuum part
  of the physical spectrum, so hadron properties are theorems about the
  hypotheses rather than fields of an assumed carrier.
INPUT PARAMETERS:
  Colour coupling g₃ (nonzero), colour spectrum.
OUTPUT PARAMETERS:
  Λ_colour, the gap, nucleon states with masses written as ratio · Λ_colour
  and with electromagnetic charges.
PROVED HERE:
  Formal consequences of the hypotheses: hadrons are singlets given
  confinement, hadron masses lie above the gap and are positive given the
  gap; the same for the nucleons.
ASSUMED HERE:
  Existence of a positive colour scale; a positive mass gap above a massless
  vacuum; a colour-singlet asymptotic spectrum, as the consequence of
  confinement; stable proton- and neutron-like states with their mass
  ratios and charges.
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

/-- The hadron spectrum: asymptotic, non-vacuum states of the colour sector.
A definition rather than an assumed carrier. -/
def hadronSpectrum (C : GaugeSector) : Type :=
  { s : C.Spectrum // C.asymptotic s ∧ s ≠ C.vacuum }

/-- Hadrons are colour singlets: a formal consequence of the singlet
asymptotic spectrum carried by confinement. -/
theorem hadron_singlet {C : GaugeSector} (hConf : HasConfinement C)
    (h : hadronSpectrum C) : C.singlet h.val :=
  hConf.singlet_asymptotics.singlet_of_asymptotic h.val h.property.1

/-- Hadron masses lie above the gap. -/
theorem hadron_mass_above_gap {C : GaugeSector} (hGap : HasMassGap C)
    (h : hadronSpectrum C) : Fraction.le hGap.gap (C.mass h.val) :=
  hGap.above_gap h.val h.property.2

/-- Hadron masses are positive, since the gap is. -/
theorem hadron_mass_positive {C : GaugeSector} (hGap : HasMassGap C)
    (h : hadronSpectrum C) : Fraction.positive (C.mass h.val) :=
  (Fraction.positive_iff_zero_lt _).mpr
    (Fraction.magnitudes.lt_of_lt_le
      ((Fraction.positive_iff_zero_lt _).mp hGap.gap_positive)
      (hadron_mass_above_gap hGap h))

/-- Stable proton- and neutron-like hadrons, with masses referred to the
colour scale and with electromagnetic charges. The mass ratios are the
dimensionless effective constants the Newtonian sector inherits; writing
m = ratio · Λ is bookkeeping of dimensional transmutation, never a
derivation of the ratios. The proton charge is positive and the neutron
charge zero by convention. Neutron stability presupposes the weak
decoupling upstream; that link is physical interpretation. -/
structure HasStableNucleons (C : GaugeSector) (hΛ : HasColourScale C) where
  proton : hadronSpectrum C
  neutron : hadronSpectrum C
  distinct : proton ≠ neutron
  protonMassRatio : Scalar
  neutronMassRatio : Scalar
  proton_mass : Fraction.equiv (C.mass proton.val) (Fraction.mul protonMassRatio hΛ.scale)
  neutron_mass : Fraction.equiv (C.mass neutron.val) (Fraction.mul neutronMassRatio hΛ.scale)
  protonCharge : Scalar
  neutronCharge : Scalar
  protonCharge_positive : Fraction.positive protonCharge
  neutronCharge_zero : neutronCharge.num = 0

/-- Nucleons are colour singlets, given confinement. -/
theorem HasStableNucleons.singlet {C : GaugeSector} {hΛ : HasColourScale C}
    (hConf : HasConfinement C) (N : HasStableNucleons C hΛ) :
    C.singlet N.proton.val ∧ C.singlet N.neutron.val :=
  ⟨hadron_singlet hConf N.proton, hadron_singlet hConf N.neutron⟩

/-- Nucleon masses are positive, given the gap. -/
theorem HasStableNucleons.masses_positive {C : GaugeSector} {hΛ : HasColourScale C}
    (hGap : HasMassGap C) (N : HasStableNucleons C hΛ) :
    Fraction.positive (C.mass N.proton.val) ∧ Fraction.positive (C.mass N.neutron.val) :=
  ⟨hadron_mass_positive hGap N.proton, hadron_mass_positive hGap N.neutron⟩

end Reverse.Strong
