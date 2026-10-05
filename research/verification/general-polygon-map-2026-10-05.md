# Shared polygon geometry and general whole-edge map, 5 October 2026

Root Sol 6.1 implementation following the user-requested theorem-growth study
and its one sequential Astra architectural review. This increment is a
source-free modern reconstruction; De Motu, 1687 and 1713 remain separate.

PolygonValues constructs a polygon on the existing binary-time quotient from
actual vertices and a proved position join. Same-cell aliases, adjacent-cell
aliases, zero time, affine vertex control and the initial endpoint are proved
once, independently of the law producing those vertices. Six retained harmonic
proofs now use this shared core, with every old statement unchanged.

GeneralForcePolygonCurve instantiates the core with the actual sampled runs.
The velocity bound V=|v0|+T*B follows from the actual sample bounds; A is the
existing derived prefix-to-curve coefficient. Every time, including cell
boundaries and the final endpoint, satisfies

    Within(polygonMap_m(t), gammaPosition(t), (T*V+A)/2^m).

Rational exhaustion gives uniform convergence. The initial endpoints agree.
HarmonicGeneralPolygon proves exact equality with the retained harmonic
polygon, without a small-window or supplied-curve premise for that finite
identity. All alias proofs precede quotient lifting.

The global comparison region, calibrated short window and actual/coarse/shadow
force bounds remain explicit conditions for the curve comparison. This unit
does not construct the general matched region/content, establish annular
confinement or gluing, or prove motion precision/partition independence,
unrestricted differentiation, external real-time identification, potential
asymptotics or a historical limiting theorem. No derivative, integral, ODE,
mathlib or additional axiom is imported.

The next bounded unit shares matched-region enclosure geometry while preserving
cell closures, simultaneous connectors, overlaps counted once, and the final
connector. Completion scores remain unchanged: about 38% overall (35–46%),
Proposition I 60%. Helper or compatibility counts receive no separate credit.

Targeted Lean 4.19 core compilation and all 16 sequential checklist commands
pass. All 1,741 prior public names/signatures at a83f44d remain unchanged, with
23 new names. The catalogue contains 1,386 distinct rows and 1,246 references;
live heuristic counts are 1,010 substantive, 195 plumbing, 155 sample and 26
duplicate. All 15 new rows and all 572 Barrow rows are source-free. The axiom
union is propext, Classical.choice and Quot.sound, with no sorryAx, project axiom
or external package. The graph stays 77/68/249. Logs:
/tmp/newton-sol61-general-polygon-final-01.log through -16.log. Root Sol 6.1
commits the verified increment; unrelated archives remain untouched.
