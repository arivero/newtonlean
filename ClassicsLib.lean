/- Historical scope: classical results through Hypatia.
Results after Hypatia and before the Principia belong in BarrowLib; results
after the Principia belong in ModernLib. Chronology concerns the mathematical
result, not the date of its Lean encoding.
Chinese results before the Principia also belong here, by the user's explicit
exception. Arabic results after Hypatia and before the Principia go to BarrowLib.
AI-derived results using only Classics mathematics belong here.
Borrowed results must retain their exact original-language source passage;
formalization authorship does not establish discovery or historical dating.

Authorities: Euclid, Elements I.37 (equal triangles on the same base between
the same parallels) and I.38 (equal bases between the same parallels).
Their original Greek statements and exact source URLs are in
ClassicsLib/Euclid/PropositionI37.lean and PropositionI38.lean. The checked
results are integer-coordinate determinant special cases; FiniteLattice.lean
assembles their finite model. VII.31 and IX.20 supply prime divisors and primes
outside any finite collection. Aristotle, Prior Analytics I.23, 41a26-27,
attests the diagonal's parity contradiction; Aristotle/SquareRootTwo.lean
states the limits of that source and proves the integer-ratio impossibility.
The new arithmetic files use only Lean core and classical arithmetic; their
comments compare the inspected mathlib routes without importing them.
These are not full synthetic Elements or diagonal constructions.
The entry-point name does not certify the source or dependency class of every
helper; unresolved exact-result attributions remain unverified. -/

import ClassicsLib.Euclid.PropositionI37
import ClassicsLib.Euclid.PropositionI38
import ClassicsLib.Euclid.FiniteLattice
import ClassicsLib.Euclid.PropositionVII31
import ClassicsLib.Euclid.PropositionIX20
import ClassicsLib.Aristotle.SquareRootTwo
