# Background: Berry on singular limits between theories

- Written: 6 October 2026 by Claude Opus 5.5 (Claude Code), from a discussion
  with the user.
- Layer: background for the action diagnostic. It supplies no premise to a
  historical proof and gives no verdict on an action constant.
- Sources, both retrieved on 6 October 2026. They remain under copyright, so
  only the links and short quotations are kept here.
  - M. V. Berry, "Asymptotics, singularities and the reduction of theories",
    in *Logic, Methodology and Philosophy of Science IX*, eds. D. Prawitz,
    B. Skyrms and D. Westerståhl (Elsevier, 1994), pp. 597–607. Berry's
    publication 260:
    <https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry260.pdf>.
    The PDF is a scan without a text layer; the quotations below were
    transcribed from its page images.
  - M. V. Berry, "Singular limits", *Physics Today* 55(5), 10–11 (May 2002),
    Berry's publication 341:
    <https://aip.brightspotcdn.com/PTO.v55.i5.10_1.online.pdf>.

## What Berry claims

1. **Reduction is a limit in a dimensionless parameter.** "The less general
   theory must appear as a particular case of the encompassing one, as some
   dimensionless parameter - call it δ - takes a particular limiting value."
   His scheme is "encompassing theory → less general theory as δ → 0", and
   "The crucial question will be: what is the nature of the limit δ → 0?"
   (1994, p. 598).

2. **Six examples** (1994, p. 599), with S "typical classical action":

   | Encompassing → less general | δ |
   | --- | --- |
   | special relativity → Newtonian mechanics | v/c |
   | general relativity → special relativity | Gm/c²a |
   | statistical mechanics → thermodynamics | 1/N |
   | viscous (Navier–Stokes) → inviscid (Euler) flow | 1/Re = η/ρav |
   | wave optics → ray optics | λ/a |
   | quantum mechanics → classical mechanics | ħ/S |

3. **The regular case is the exception.** Special relativity "is analytic in
   δ at δ = 0, so that the limit is unproblematic". Then: "My main point will
   be that this simple state of affairs is an exceptional situation. Usually,
   limits of physical theories are not analytic: they are singular, and the
   emergent phenomena associated with reduction are contained in the
   singularity." (1994, p. 599). In 2002 he lists the classical, ray-optics,
   thermodynamic and inviscid limits and says they "are all singular—they
   must be, because the theories they connect involve concepts that are
   qualitatively very different."

4. **Recovering the older theory needs an added ingredient.** In the ray
   limit the wave oscillates without bound, and "Only if we consider the wave
   intensity … and average over a small interval corresponding to the finite
   resolution of a detector, do we get the finite and smooth result";
   interference "requires an extra average" (1994, p. 601). In 2002: "Young's
   “demonstrable” invisibility requires an additional concept", and
   "Nowadays this application of the idea that the average of a cosine is
   zero, elaborated and reincarnated, is called decoherence."

5. **Limits that do not commute.** "the ħ → 0 limit is enriched by another
   limit, which is fundamental, namely the long-time limit t → ∞", and "the
   two limits do not commute: taking the classical limit first, and the
   long-time limit second, leads to a different result from taking the
   limits in the reverse order." He calls the point ħ = 1/t = 0 "truly a
   'dragon's lair'" (1994, p. 603).

6. **The older theory is never reached.** "for any finite ħ, however small,
   the spectrum is always discrete: the classical continuum is never reached,
   and so cannot be said to be logically contained in the semiclassical
   limit." (1994, p. 604).

7. **Berkeley.** Berry sets aside "one aspect of the study of limits in
   physics which has attracted the attention of philosophers, beginning with
   Berkeley": "the limit δ = 0 is always an idealization; in any actual
   situation, δ is always finite." (1994, p. 598).

8. **Singular perturbation.** "in all nontrivial reductions the encompassing
   theory is a singular perturbation of the less general one." (1994,
   p. 605).

## Bearing on this project

Each item below is our reading of Berry, with its status.

a. **The textbook slogan.** The user observed on 6 October that physics
   teaches an older theory as a newer one with a constant sent to zero, as if
   the older theory carried an unneeded axiom. Berry's scheme fits that
   slogan exactly in his analytic case, special relativity to Newton in v/c,
   which he calls exceptional. In the singular cases the older theory is the
   limit together with an added concept, averaging over the fast phase, and
   Berry declines to call it logically contained.
   *Status:* `editorial_interpretation`, confidence medium.

b. **The relevant small quantity is a ratio of actions.** Berry's δ for the
   classical limit is ħ/S. The Principia's Section I scholium treats
   quantities taken singly, each divisible without limit, and the student
   notebook's least distance and least time fix a speed
   ([TIME_SUBDIVISION](../TIME_SUBDIVISION.md#newtons-time-parts-and-boundaries)).
   Neither text addresses a least action, the quantity Berry's δ compares.
   *Status:* `editorial_interpretation`.

c. **Newton's refinement and the classical limit pull apart.** For one Newton
   cell of duration h at force F and mass m, the action of the deflection is
   of order F²h³/m ([Arg008](261005opus5.5v1Arg008.md)). Taking S at that cell
   scale gives δ = mħ/(F²h³) = (t_*/h)³, with t_* = (mħ/F²)^{1/3} the time of
   [Arg005](260922opus5.5v1Arg005.md) and Arg008. Newton's limit h → 0 at
   fixed ħ drives this δ upward, out of the classical regime, while the
   classical limit drives it to zero. The two limits ħ → 0 and h → 0 therefore
   fail to commute, with the same structure as Berry's ħ → 0 and t → ∞ at the
   opposite end of the time axis. Newton's construction sets ħ = 0 before it
   refines.
   *Status:* `modern_reconstruction`. Berry does not consider this cell scale.

d. **Berkeley's objection.** The theme Berry sets aside begins with
   Berkeley's *The Analyst* (1734), aimed at Newton's evanescent quantities.
   The 1687 Section I scholium already answers an objection of that family,
   that ultimate ratios would imply ultimate magnitudes, by defining ultimate
   ratios as limits (NATP00077.par42).
   *Status:* historical pointer; *The Analyst* is not archived here.

e. **G and curvature.** The user noted that Riemannian geometry, and with it
   G, arrives once the parallel postulate is recognized as unneeded. Berry's
   own parameter for general relativity is Gm/c²a; the 1994 paper does not
   say whether that limit is regular or singular. A related lead, recalled
   from memory and unverified: Lambert and Gauss remarked that non-Euclidean
   geometry carries an absolute unit of length.
   *Status:* lead.
