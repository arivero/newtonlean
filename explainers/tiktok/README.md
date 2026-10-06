# TikTok explainers: plan

Short vertical videos built from the research conversation of 6 October
2026. Seven scripts are drafted; each turns one verified finding into a
75–90 second story. A later model is expected to produce the video ("the
cinema") from these files, so every script carries its narration, a scene
table and a sources-and-status block.

## Scripts

| File | Working title | Core hook |
| --- | --- | --- |
| [01-the-withheld-proof.md](01-the-withheld-proof.md) | Newton's orbit waited 150 years for a proof | Cauchy's existence proof was printed and then kept from the public |
| [02-two-orbits-cannot-touch.md](02-two-orbits-cannot-touch.md) | The line Newton never proved | Newton's 1713 and 1726 uniqueness clause, Peano's counterexample, Norton's dome |
| [03-atoms-of-time.md](03-atoms-of-time.md) | Young Newton believed in atoms of time | The student notebook's least time and "stops & stays" |
| [04-derivative-as-renormalization.md](04-derivative-as-renormalization.md) | Every derivative subtracts an infinity | Berkeley's ghosts, Feynman's "dippy process", Newton's force as a finite part |
| [05-cauchys-flat-function.md](05-cauchys-flat-function.md) | The function that sank Lagrange runs quantum physics | e^(−1/x²) and the tunnelling weight e^(−A/ħ) |
| [06-limits-that-bite.md](06-limits-that-bite.md) | Old physics is a limit with teeth | Berry's singular limits and Newton refining at ħ = 0 |
| [07-half-a-stick-each-day.md](07-half-a-stick-each-day.md) | 一尺之捶，日取其半，萬世不竭 | The *Zhuangzi*'s halved stick, Zeno's dichotomy, and the Bactria question |

## Status rules

Each claim in a script's source block carries one tag.

- **VERIFIED**: checked in this session against a primary source, with the
  anchor or page given. Narration may state it as fact.
- **SECONDARY**: taken from a published secondary account and not checked
  against the original. Narration may use it with attribution.
- **INTERPRETATION**: our reading. Narration must mark it as a reading
  ("one way to see it", "read that way").
- **MEMORY**: recalled by the model and not yet checked. It must be verified
  or cut before production.

The research notes behind the scripts are
[EXISTENCE_OF_THE_CURVE](../../research/EXISTENCE_OF_THE_CURVE.md),
[TIME_SUBDIVISION](../../research/TIME_SUBDIVISION.md#newtons-time-parts-and-boundaries)
and the [Berry background](../../research/action-arguments/background-berry-singular-limits.md).

## House style

- Lead each line with the direct statement. Avoid hooks of the form "X is
  not Y, it's Z"; one load-bearing contrast per script at most.
- Quote short phrases in the original language on screen, with the English
  in the narration.
- Keep dates and names exact. Prefer "around 1664" to a false precision.
- Every script ends on a verified fact or a clearly marked reading, never on
  a cliffhanger that overclaims.

## Production notes for the video model

- **Format:** 9:16, 1080×1920, 75–90 seconds, burned-in captions, one
  narrator. Scene tables give approximate timings for roughly 150 spoken
  words per minute.
- **Visual vocabulary:** animated geometry for polygons, orbits and graphs;
  handwritten-style equations; page close-ups only where the licence allows.
- **Licences, to check before use:**
  - Newton Project transcriptions are CC BY-NC-ND 3.0. Showing transcribed
    text may count as reproduction, and the NonCommercial term matters on a
    monetized account.
  - Manuscript images from Cambridge University Library carry their own
    licence terms.
  - The Moigno (1844) and Peano (1890) scans on the Internet Archive are
    public domain by age; confirm the scan's own terms.
  - Berry's papers and Feynman's *QED* are in copyright: short spoken quotes
    only, no page images.
- **Animations requested across scripts:** a polygon refining into an
  ellipse (01, 06), a curve leaving a rest point at different times (02),
  a dotted "staircase" of least steps with pauses (03), a fraction splitting
  into two growing terms (04), the flat graph of e^(−1/x²) (05).

## Backlog, not yet scripted

- **Cayley's trees** (1857) behind Butcher's Runge–Kutta theory and the
  Connes–Kreimer algebra of renormalization (MEMORY throughout).
- **Why the constant is called Lipschitz**: Cauchy's derivative bound enters
  only as a difference ratio; Lipschitz assumed the ratio itself (Peano 1890,
  pp. 207–208, VERIFIED).
- **Kaluza's cylinder condition** as an axiom whose removal gives Klein's
  radius (MEMORY).
- **The forced Navier–Stokes blow-up of September 2026**: on hold. The
  attribution dispute is ongoing, an Anthropic employee is a party to it,
  and these scripts are drafted by an Anthropic model. Revisit only with
  settled, independent sources.
