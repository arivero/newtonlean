# Theorem cascade and provenance

This note records the detailed meaning of the theorem counts in the README.
The counts are produced from the compiled Lean environment by
`research/CheckReferences.lean`; they are not a count of historical
propositions and they are not additive across rows.

There are three different quantities:

- **Own theorems** are named theorem declarations in the file or library,
  including private helpers. Definitions, examples and compiler-generated
  equation lemmas are excluded.
- **Proof tree** is the distinct set of project theorems reached by traversing
  the types, definitions, proof bodies and private helpers of every declaration
  in the file. A shared theorem is counted once.
- **Import tree** is the distinct set of project theorems available in the
  file's compiled transitive imports. It includes theorems that the file does
  not use. This is the total cascade requested for each historical file,
  including the library theorems below it.

The current compiled cascade is:

| Entry | Own | Proof tree | Import tree |
| --- | ---: | ---: | ---: |
| `LemmaII.lean` | 16 | 95 | 295 |
| `LemmaIII.lean` | 12 | 140 | 417 |
| `LemmaIII/CorollaryI.lean` | 4 | 80 | 455 |
| `LemmaIII/CorollaryII.lean` | 2 | 70 | 457 |
| `LemmaIII/CorollaryIII.lean` | 10 | 208 | 591 |
| `LemmaIII/CorollaryIV.lean` | 12 | 469 | 1336 |
| `ClassicsLib` | 16 | 16 | 26 |
| `BarrowLib` | 973 | 973 | 973 |
| `ModernLib` | 1157 | 1496 | 1688 |

The complete per-file table, including the other historical witnesses and
classical files, remains in the README. Reproduce and check it with:

```sh
NEWTON_PRINT_THEOREM_COUNTS=1 lake env lean research/CheckReferences.lean
NEWTON_CHECK_README_COUNTS=1 lake env lean research/CheckReferences.lean
```

## Source versus project authorship

Every Lean declaration is authored in this repository. “Sourced” below means
that the owning file contains an exact historical-language witness and a
passage URL for the mathematical result or proof step. “Project-authored”
means that the declaration is a formal reconstruction or supporting result
whose exact result is not claimed by that passage. A source witness can
therefore contain several project-authored Lean declarations; the two counts
must not be conflated.

| Cascade component | Exact source witnesses | Project-authored declarations |
| --- | ---: | ---: |
| `LemmaII.lean` | 2 edition witness sections (1687, 1713) | 16 Lean theorems |
| `LemmaIII.lean` | 2 edition witness sections (1687, 1713) | 12 Lean theorems |
| `ClassicsLib` | 5 source-linked result files; `FiniteLattice` is support | 16 Lean theorems |
| Existing `BarrowLib` support | Euclid I.41 is background for supplied area rules | 968 prior project theorems |
| Current zero-base increment | 0 exact external result claims | 5 new project theorems, 1 public and 4 private |
| `ModernLib` | No exact original-language result is claimed by the aggregate row | 1157 Lean theorems |

The two Lemma II and two Lemma III witness sections preserve their separate
Latin passages and edition-local proof interfaces. Their theorem declarations
are formalizations written here; the source passage does not certify every
supporting coordinate lemma. The current `BarrowLib` increment proves
`lower_sum_eventually_positive` from finite ordered-partition arithmetic, a
midpoint interval split and the supplied shrinking maximum-width premise. It
has no Newton quotation or external priority claim, so its five declarations
are project-authored. The harness example is anonymous and is not included in
the theorem count.

The import-tree number is the safe answer when asking “how many theorems are
needed or available for this file?” The proof-tree number is the narrower
answer for what the compiled declarations actually traverse. Source status is
an independent provenance property and cannot be inferred from either number.

No new classical or Barrow-era axiom was introduced for this increment. If a
future reduction in theorem proliferation uses an axiom, it must be declared
explicitly, placed in the correct historical library, and accompanied by an
original-language passage stating that exact premise. It must also remain
visible in the compiled dependency and provenance checks; an unattributed
convenience axiom would not count as historical progress.
