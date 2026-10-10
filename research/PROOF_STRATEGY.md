# Proof strategy

Use this guide to choose and design a proof increment.
[VERIFICATION.md](VERIFICATION.md) gives the acceptance checks;
[STATE.md](STATE.md) holds the current obligations. This file introduces no
second task list, proof ledger or dependency catalog.
The earlier [theorem-growth analysis](THEOREM_PROLIFERATION.md) records the
representation and duplication issues behind this guidance.

## What the classical examples teach us

The prime and square-root examples are much smaller than the Newton
development, even after exposing their elementary helper proofs. Their exact
file and dependency measurements are in the [README](../README.md#measured-work).
That difference deserves attention, but it has several causes.

Both examples use Lean's existing natural/integer arithmetic. Our counts omit
Lean/Std theorems, so that foundation is not charged to their proof trees.
Newton's coordinate development instead includes our unnormalized fractions,
equivalence of representatives, finite geometry, geometric area rules and
approximation estimates. Those project theorems are counted. This is a real
implementation burden, with an asymmetry in the reported library boundary.

Historical ownership and representation cost require separate decisions.
The [boundary note](BARROWLIB_BOUNDARY.md) now links the independent Nine
Chapters source-attestation file, with positive-input and signed-whole domains.
No existing proof is routed through it. Euclid VII.19 and additional signed
operations still need exact source review. An unchanged move leaves the total
theorem count unchanged, even though library ownership changes. Cross-product
equivalence alone does not source all signed arithmetic.

On 10 October the user selected Lean 4.34.1 and its core `Rat`, after a
scratch check of order, arithmetic, absolute value and `grind`. The approved
migration uses reduced rationals and equality, with a temporary conversion
bridge; a quotient over unreduced Fraction would retain the ordered-field
proof burden. Migrate clients in import order, deleting core duplicates and
redundant representative transport. Compare compiled cascades against the
scratch baseline. Moving arithmetic into core reduces the counted project
boundary, not the total supporting mathematics or the remaining geometry.
Core availability also does not establish historical availability: retain
source attestations, their original languages and their stated domains.

The classical statements also have narrow conclusions: a new prime outside
a finite list, and exclusion of an integer square equation. The second does
not construct a real square root or a geometric diagonal. Newton's target
connects a given motion, mechanical laws, polygons, actual regions and an area
law. The historical files additionally preserve separate textual witnesses;
their aggregate counts can include several results and modern sections.
Comparing that aggregate with a one-line mathlib theorem application cannot
measure the cost of the mathematical argument alone. The authors of
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html)
also explain that their displayed examples suppress imports of supporting
theory and automation.

These explanations do not justify every abstraction in our development.
More conditional interfaces can leave the same geometric premise open.
Separate edition wrappers preserve source correspondence, but repeating a
wrapper is not another mathematical advance. The area-domain countermodel
already shows why a shrinking cover cannot by itself supply an area
assignment for every difference. Review the missing argument before adding
another layer of estimates around it.

## Design from the target, prove the necessary parts

1. Read the witness's statement and proof. State the intended Lean conclusion
   and its allowed premises before selecting helper lemmas. Keep given curve,
   mechanical assumptions and the desired area conclusion distinct.
2. Write the short mathematical argument first, including the step that
   removes the current open obligation. Search existing ClassicsLib, BarrowLib
   and Lean core/Std for its parts with `rg` and `#check`. Use mathlib source
   only for comparison; a replacement needs its own permitted dependencies.
3. Reuse the smallest sufficient statement. Keep a one-use calculation local;
   extract a lemma when it removes unnecessary hypotheses, has mathematical
   meaning of its own, or supports an actual second use. Add an interface only
   when the target needs its operations. Avoid a general framework whose
   intended application still requires the missing theorem as a premise.
4. Share elementary mathematics across editions, keeping exact Latin,
   interpretive premises and historical clients separate. Each client must
   use its own witness's required results; shared code cannot invent a textual
   dependency or merge the De Motu witnesses.
5. Inspect Lean's actual goal after a failed step. Use focused `have`, `calc`,
   `rw`, `simp` or core arithmetic automation to prove that goal. Compile the
   affected module and its client while developing; run the full acceptance
   checklist once the increment is ready. Do not repeatedly rerun the full
   suite when no relevant change or failure calls for it.
6. Stop when the selected obligation and its client compile, or when a
   precise missing premise or counterexample determines the next decision.
   Report which conclusion, premise or domain changed. Structural cleanup
   has value, but does not increase mathematical completion by itself.

These choices preserve the core-only and no-sorry policy. Design sketches
belong in prose or disposable scratch work; no unfinished declaration enters
the maintained proof library. A shorter proof must retain its statement,
premises, source scope and dependency classification.

## Public Lean guidance and agent skills

Source review, 8 October 2026; no package was installed or executed. The two
public agent skills below offer useful proof engineering guidance. Their
availability does not establish compatibility with our Lean 4.34.1 core-only environment.

| Source | Useful guidance here | Adaptation required |
| --- | --- | --- |
| [Trail of Bits: writing-lean-proofs](https://github.com/trailofbits/skills/blob/main/plugins/writing-lean-proofs/skills/writing-lean-proofs/SKILL.md) | Design statements first; focus one goal; inspect compiler-reported goals; extract helpers when they remove hypotheses or clarify mathematics; audit actual axioms. | Its worked procedure uses sorry skeletons and mathlib/Batteries linters. Use prose sketches and our existing core-only checker instead. Its advice explicitly defers to a project's own conventions. |
| [Cameron Freer: lean4-skills](https://github.com/cameronfreer/lean4-skills/blob/main/plugins/lean4/skills/lean4/SKILL.md) | Search before proving, compile incrementally, preserve existing theorem contracts, distinguish strategy changes from tactic shortening. | Much of the package assumes mathlib search, host commands, extra tools and optional agent delegation. Its [refactor command](https://github.com/cameronfreer/lean4-skills/blob/main/plugins/lean4/commands/refactor.md) also has per-batch approval behavior. Select compatible techniques; do not adopt its execution rules or dependency expansion automatically. |

For core proof techniques, consult
[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/),
especially tactics, induction, structures and axioms. Its current web edition
can change over time, so check examples against our pinned compiler.
Use [Mathlib's style guide](https://leanprover-community.github.io/contribute/style.html)
as a readability reference without importing its mathematical library or
treating its repository rules as ours. No new agent skill is required to
apply the local strategy above.
