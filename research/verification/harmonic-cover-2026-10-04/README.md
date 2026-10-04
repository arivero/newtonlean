# Exact arithmetic holdout for the finite harmonic cover

These are unchanged copies of the third sequential holdout against frozen
commit `15d50adda7b8dfeec809559bef785f173d11e017`. The original `/tmp` paths,
birth/contact times and SHA-256 values are retained in [provenance](provenance.md).
The first two harness attempts are marked burned in their separate records;
they are excluded from the passing claim. No project code was repaired.

The Std-only [reference](reference.lean) advances integer common-denominator
states. The [comparator](comparator.lean) checks project coordinates, final
L1 error, radius and cover budget by exact cross multiplication. The
[corrupted comparator](corrupted-comparator.lean) changes the radius numerator
by 1; its recorded failure is a false equality, not an import or timeout error.
The files are a fixed verification artifact, not a new general-purpose tool.

From the repository root with Lean 4.19.0, replay in this order:

```sh
lake build NewtonLimitDynamics
lake env lean research/verification/harmonic-cover-2026-10-04/reference.lean
lake env lean research/verification/harmonic-cover-2026-10-04/comparator.lean
lake env lean research/verification/harmonic-cover-2026-10-04/corrupted-comparator.lean
```

The reference and comparator must exit 0. The final command must exit nonzero
and report that `decide` proved the altered radius equality false. Logs are
included. This is an arithmetic check of one fresh case; it does not certify
the general enclosure proof, planar union content, trajectory existence or a
historical claim. The chosen update model, integer arithmetic and Lean kernel
are shared with the production route; state representation and implementation
are distinct. The radius/budget checks use the proposed formula, so they check
its project implementation rather than independently deriving its geometry.
