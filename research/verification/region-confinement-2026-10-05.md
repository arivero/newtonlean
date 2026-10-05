# Finite regional confinement, 5 October 2026

Root Sol 6.1, first finite A.6 increment after a688803. A sequential gpt-6-sol
read-only review identified the partial-time invariant and both shadow samples;
it made no edits and did not independently verify the proofs. All new rows are
source-free modern reconstructions. De Motu, 1687 and 1713 remain separate.

RegionConfinement.Frame contains geometric/time data, not a confinement trace.
For fixed local acceleration budget B, set V=|v0|_1+T*B and choose an outer
radius R>=|x0|_1+T*V. At elapsed time t<=T, the shared invariant proves

    |v_t|_1<=|v0|_1+t*B,
    |x_t|_1<=|x0|_1+t*V,
    det(x_t,v_t)=ell.

Before the next force evaluation, y=x_t+h*v_t has the outer bound and
|ell|=|det(y,v_t)|<=|y|_1*V. The condition r0*V<=|ell| and positive V give the
inner radius. For r0=0, the proof instead uses nonnegativity and includes
zero velocity/time and zero areal product. Only after y is in the band is
its regional acceleration bound used. The next kick advances the velocity
budget to |v0|_1+(t+h)*B and conserves ell. There is no circular assumption of
BoundedSamples or membership of the resulting run.

The bound is needed only on the certified band inside the oracle region.
This preserves the harmonic region=True, since that unbounded force has a
finite bound on every ball. Local Lipschitz comparison is not used by this
finite result. Both actual and coarse runs instantiate the same step theorem.
Both coarse-field shadow arrivals are also covered: append two half cells to
the coarse prefix, with elapsed 2*(k+1)*h<=T. The first shadow kick is included
before certifying the second arrival. Keeping only a uniform speed bound would
lose this partial-time accounting.

TriangleBounds.radius_lower_of_areal_bound and one shared positive-factor
cancellation are generic foundation arithmetic. The force invariant and its
actual-run/shadow clients remain Newton-side. The Lean control instantiates
an annular harmonic sample with initial ((1/2,0),(0,1)), T=1/8, B=2 and
band [1/4,2], uniformly in the mesh; it supplies only the force bound on that
band. A zero-time/zero-speed ball works. A zero-speed countermodel refutes
cancelling V when asserting a positive inner radius. These controls are not
an independent numerical orbit or a Kepler implementation.

A.6 remains incomplete: existing Conditions and the completed-force operation
still require whole-plane comparison. Pointwise comparison certificates,
local construction migration, completed curve confinement and an actual
Euclidean Kepler 1/r^2 oracle are next within A.6. L1 band radii must not be
identified with Euclidean radii; rational squared-radius bridges are needed.
Task E and new completed quantities have not started. Scores stay 38.59%
overall (35.16-46.30%) and Prop I 61.25%.

Targeted Lean 4.19 core compilation and the scope/control file pass. All 16 sequential checklist commands pass, including the default and both
explicit library builds, catalogue/reference and standard-axiom inspection,
source/graph, rendering, hashes and whitespace. There are 1,358 emitted
reference checks; the graph has 77 nodes, 68 edges and 253 passages. The
axiom union is propext, Classical.choice and Quot.sound, with no sorryAx,
project axiom, external package or Newton/Mathlib foundation import. PDF
dates were restored only after proving all other bytes unchanged. Logs:
/tmp/newton-sol61-region-finite-final-01.log through -16.log. The live catalogue has 1,502 rows and 627
Barrow rows; heuristic counts are 1,114 substantive, 199 plumbing, 163 sample
and 26 duplicate. All 1,915 prior public names/signatures at a688803 remain,
with 15 new names and 11 source-free theorem rows. Source inventories are not
kernel verification. API audit: /tmp/newton-sol61-region-finite-api.json.
Unrelated conversation archives remain excluded from staging.
