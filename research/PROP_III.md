# Proposition III: relative motion and force composition

STATE.md: Proposition III. Both printed editions state and prove the proposition in the
same way, so the source map for this order is short and the two stages agree
step for step. Lean results here are modern integer-coordinate
reconstructions (`modern_reconstruction`), not historical proofs.

## What the text asserts

1687 [NATP00077 par53](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par53)
and 1713 [NATP00082 par64](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par64)
are the statements:

> *Corpus omne quod, radio ad centrum corporis alterius utcunque moti ducto,
> describit areas circa centrum illud temporibus proportionales, urgetur vi
> composita ex vi centripeta tendente ad corpus alterum & ex vi omni
> acceleratrice, qua corpus alterum urgetur.*

A body that sweeps areas proportional to the times about the centre of a second,
arbitrarily moving body is urged by a force composed of a centripetal force
toward that second body **and** the whole accelerative force by which the second
body is urged. The 1713 text is the same sentence with expanded punctuation and
*ad corpus illud alterum*.

The proofs are
[1687 par54](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par54)
and
[1713 par65](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par65),
and they run through three named dependencies in both editions:

1. **Corollary VI of the laws.** *si vi nova, quæ æqualis & contraria sit illi
   qua corpus alterum urgetur, urgeatur corpus utrumque secundum lineas
   parallelas, perget corpus primum describere circa corpus alterum areas easdem
   ac prius*: add to both bodies an equal and contrary parallel acceleration;
   the first body goes on describing the same areas about the second. The 1713
   text names the bodies *L* and *T* explicitly.
2. **Law I.** *vis autem qua corpus alterum urgebatur, jam desiit* … the second
   body, now unaccelerated, *movebitur uniformiter in directum* (1687), i.e. the
   reference body becomes a uniformly translating centre.
3. **Proposition II.** The remaining force on the first body is therefore
   centripetal toward that uniformly moving centre, by the proposition already
   proved (with its Case 2, which invokes Corollary V of the laws: 1687 par50,
   1713 par60).

So Proposition III is a *composition* statement, not a new area law: the areas
are unchanged by the common added acceleration, and the force is read off after
the reference body has been made inertial.

## Admissible moving-centre data

The construction needs, and only needs:

- two initial vertex pairs, `p, q` for the body and `s, t` for the reference
  body (the relative radius `q − t` and its predecessor `p − s`);
- two arbitrary deflection histories `d, e : Nat → LatticePoint`, one per body,
  applied at each arrival vertex (the per-cell impulse);
- the equal relative oriented areas, as a hypothesis on the constructed
  relative polygon.

No mass, no force law, no time scale beyond the common cell, and no realized
curve enter. The "accelerative force" of a cell is exactly its deflection
vector, which is the only sense in which a finite polygon can compose forces.

## Checked finite steps

All results are in `Polygon/RelativeMotion.lean`, on the lattice polygon of
`Polygon/Finite.lean` and the Proposition II converse of `Polygon/Converse.lean`.

| Newton's step | Result | Statement |
| --- | --- | --- |
| two-body construction | `pairMotion` | one pair recursion advancing both bodies: each continues inertially from its current pair and then takes its own deflection |
| force composition (statement) | `relative_deflection_difference` | the relative polygon's next vertex is the inertial continuation of the relative pair **plus `d n − e n`**: the relative deflection is the difference of the two deflections |
| Corollary VI | `corVI_relative` | adding one arbitrary history `h` to **both** bodies leaves `relPAt` and `relQAt` unchanged at every stage; `common_deflection_example` shows the common history genuinely changes the absolute deflections while the relative polygon is fixed |
| Law I | `lawI_uniform` | with `e = 0` the reference body's vertices are `centreAt s (t − s) n` and `centreAt s (t − s) (n+1)`; `centre_is_reference_body` identifies that uniform centre with the relative coordinate |
| Proposition II, Newton's route | `propIII_via_moving_centre` | add `−e` to both histories by Corollary VI; Law I identifies the reduced reference body's `.p` at time `n` and `.q` at time `n+1`; transfer the supplied relative areas to that centre and apply `Converse.moving_centre_equal_areas_central` to derive `det (relQAt n) (d n − e n) = 0` |
| Proposition II, relative form | `relative_equal_area_central` | equal relative oriented areas give `det (relQAt n) (d n − e n) = 0` |
| force identification | `relative_rational_central` | at the initial step, with a nonzero relative radius there are `a, b : Int`, `b ≠ 0`, with `b * (d 0 − e 0) = a * (relative radius)` — a rational multiple of the radius; inward sense remains a separate premise |
| bookkeeping | `absolute_deflection`, `difference_not_pair_example` | a body's own deflection is the gap to its inertial continuation; the parallelism constrains the **difference**, not the pair of absolute deflections |
| centre timing regression | `moving_centre_alignment_example` | with an inertial reference body, three correctly timed relative radii give equal areas while the same `.q` vertices paired with centre times one cell earlier give unequal areas |

## What is not discharged

- **No composition of forces as vectors in Newton's sense.** The result composes
  two *deflection histories* cell by cell. Parallelogram composition of
  simultaneous forces (Corollary IV of the laws) is not used and not proved.
- **No acceleration, no mass, no continuous force.** The per-cell deflection is
  an impulse; dividing by a cell duration or a mass is outside this module.
- **Parallelism does not fix inward sense.** The rational coefficient has no
  sign restriction; equal oriented areas also admit outward deflections.
- **The equal relative areas are assumed.** The proposition's hypothesis is a
  realized orbit sweeping areas proportional to times; here it is an hypothesis
  about the constructed relative polygon, exactly as in `Converse.lean`.
- **No limit.** The vanishing-triangle passage from a given curve is the same
  open obligation as for Proposition II (STATE.md: Proposition II) and is not attempted.
- **No De Motu counterpart is claimed.** The inspected De Motu ranges contain no
  counterpart of Proposition III; that absence is a statement about the
  inspected witnesses only (SECTION_II.md).
