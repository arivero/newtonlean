# The existence of the curve: Cauchy and Peano

- Written: 6 October 2026 by Claude Opus 5.5 (Claude Code), from a discussion
  with the user.
- Scope: background on how Newton's passage from polygon to curve became a
  theorem. It supplies no premise to a historical proof. Under the 6 October
  convention the primary route still takes the trajectory as given
  ([GOALS](GOALS.md)); the construction below remains supporting work.
- Sources, public domain, retrieved on 6 October 2026 and kept as links.
  Every quotation was checked against the page images.
  - F.-N.-M. Moigno, *Leçons de calcul différentiel et de calcul intégral,
    rédigées principalement d'après les méthodes de M. A.-L. Cauchy*,
    tome 2 (Paris, 1844). Internet Archive
    [bub_gb_2SLAO2V1Hq4C](https://archive.org/details/bub_gb_2SLAO2V1Hq4C);
    the passages are on PDF pages 20, 39 and 437–448.
  - G. Peano, "Démonstration de l'intégrabilité des équations
    différentielles ordinaires", *Mathematische Annalen* 37 (1890), 182–228,
    doi:10.1007/BF01200235. Internet Archive
    [sim_mathematische-annalen_1890_37](https://archive.org/details/sim_mathematische-annalen_1890_37),
    leaves 185, 211, 229 and 230.

## Cauchy, as published by Moigno in 1844

1. **The method was printed but withheld.** Moigno's introduction, p. xxxv:
   "J'expose dans la vingt-sixième Leçon la méthode rigoureuse à l'aide de
   laquelle M. Cauchy démontre l'existence d'une valeur propre à vérifier
   une équation différentielle du premier ordre, et apprend à calculer cette
   valeur avec un degré d'approximation donné. Cette méthode, qui fut un
   grand pas dans la science, a été imprimée, mais les feuilles qui la
   contenaient n'ont pas été livrées au public; elle est par conséquent
   très-peu connue."

2. **The construction is a polygon.** Lesson 26, §159, pp. 385–386: divide
   the interval from x₀ to X by intermediate values x₁, …, xₙ₋₁, and set
   y₁ − y₀ = (x₁ − x₀) f(x₀, y₀), and so on up to Y. Each step advances by
   the slope at the left end of its cell. This is the polygon now called
   Euler's.

3. **The hypothesis.** §160, p. 388: the derivative ∂f/∂y stays continuous
   in x and y and bounded between ±C on the interval.

4. **Partition independence.** §161, p. 394, after comparing two divisions
   through a third that refines both: "Donc, lorsque les éléments de la
   différence X − x₀ deviennent infiniment petits, le mode de subdivision
   n'a plus, sur la valeur de Y, qu'une influence insensible, et si l'on
   fait décroître indéfiniment les valeurs numériques de ces éléments en
   augmentant leur nombre, la valeur de Y convergera vers une certaine
   limite qui dépendra uniquement de la forme de la fonction f(x, y)…"

5. **Existence.** §162, p. 396: "Donc enfin, lorsque la fonction f(x, y) et
   la dérivée df(x, y)/dy restent finies et continues entre les limites
   x₀, X, il existe une fonction de x propre à vérifier l'équation
   différentielle dy = f(x, y)dx, et de plus à prendre une valeur
   particulière, mais arbitraire y₀, dans le cas où l'on attribue à la
   variable x une valeur donnée x₀."

6. **Systems.** Lesson 33, pp. 513–534, extends the proof to n simultaneous
   first-order equations; its table-of-contents entry, p. xvi, adds that the system
   of general integrals "est essentiellement unique". Newton's motion, in
   position and velocity, has this form.

## Peano, 1890

1. **He credits Cauchy.** P. 182, note: the proof "a été donnée par Cauchy,
   et (incomplétement) publiée par Moigno *Leçons de calcul diff. et de
   calcul intégral*, 1844, Vol. 2°, p. 385—454 et 513—534. Elle suppose
   l'existence et la continuité des dérivées partielles des φ par rapport
   aux x."

2. **His theorem needs only continuity.** P. 182: the right-hand sides "sont
   des fonctions continues aux environs de t = b, x₁ = a₁, …, xₙ = aₙ", and
   solutions exist on some interval (b, b′).

3. **Cauchy and Lipschitz as a special case.** Pp. 207–208: Lipschitz's
   bounded difference-ratio condition follows from continuous partial
   derivatives, and "On a ainsi démontré les théorèmes de Cauchy et de
   Lipschitz." Peano cites Lipschitz in Darboux's *Bulletin* X, p. 149.

4. **Existence without uniqueness.** §8, p. 226: with a continuous
   right-hand side "il existe au moins une fonction ft", and "En supposant
   seulement la continuité de la fonction φ, la classe A(a, b, t) peut
   effectivement contenir plusieurs nombres."

5. **The example.** P. 227: for dx/dt = 3x^(2/3), the solutions vanishing at
   t = 0 are x = t³, x = 0, and "les fonctions qui dans un intervalle 0−t₁
   sont nulles, et qui de t₁ à +∞ ont la valeur (t − t₁)³." A second
   example, dx/dt = 4xt³/(x² + t⁴), has no singular solutions, yet its
   solution through the origin is still undetermined.

6. **His earlier note.** P. 208: the one-equation theorem first appeared in
   *Sull'integrabilità delle equazioni differenziali di primo ordine*, Atti
   Acc. Torino XXI (1886), "avec une démonstration quelque peu différente".

## Newton's own answer: uniqueness asserted

Newton met the question in its uniqueness form at Book I, Proposition XIII,
Corollary 1: a body launched from any point, at any velocity, under an
inverse-square force moves on a conic. The three printed editions differ.

- **1687** (NATP00077.par109) states the claim alone, ending "& contra".
- **1713** (NATP00082.par140) adds a reason: "Nam datis umbilico & puncto
  contactus & positione tangentis, describi potest sectio Conica quæ
  curvaturam datam ad punctum illud habebit. Datur autem curvatura ex data
  vi centripeta: & Orbes duo se mutuo tangentes, eadem vi centripeta
  describi non possunt."
- **1726** (NATP00087.par130) adds the velocity that the claim needs:
  "Datur autem curvatura ex data vi centripeta, & velocitate corporis: &
  orbes duo se mutuo tangentes eadem vi centripeta eademque velocitate
  describi non possunt."

The final clause asserts, without proof, that position, velocity and force
fix the orbit. Cauchy–Lipschitz proves this for forces like the inverse
square away from the centre; Peano's example shows that continuity alone
leaves it open. The quotations are checked against the archived TEI; reading
the clause as a uniqueness postulate is an `editorial_interpretation` with
high confidence.

Moigno's introduction, p. xxxv, also recalls that singular solutions, a
form of non-uniqueness, had been studied by "Euler, Lagrange, Laplace,
Poisson".

Leads recalled from memory and unverified: Johann Bernoulli objected around
1710 that the converse had not been demonstrated, and the 1713 sentence is
usually read as Newton's reply; Weinstock (1982) and Pourciau (1991)
disagree over whether it amounts to a proof. Norton's dome (2008) gives a
Newtonian force, growing as the square root of the distance from an apex,
under which a body at rest may start to move at any time: Peano's
non-uniqueness inside mechanics.

## Bearing on this project

Each item below is our reading, with its status.

a. **What Cauchy and Peano noticed.** Neither text mentions Newton. Cauchy's
   point, as Moigno presents it, is that integrability must be proved and the
   error bounded; Peano's is that continuity secures existence and leaves
   uniqueness open. Reading them as the moment when Newton's "eorum ultima
   perimeter ADF … erit linea curva" (NATP00077.par45) acquired a proof is
   our framing.
   *Status:* `editorial_interpretation`; high confidence for the
   mathematics, medium for the historical framing.

b. **Same construction, a different step.** Cauchy's polygon advances every
   coordinate by the slope at the left end of a cell. Proposition I moves the
   body inertially across the cell and applies the impulse at its end, the
   drift-then-kick convention recorded in
   [TIME_SUBDIVISION](TIME_SUBDIVISION.md#newtons-time-parts-and-boundaries).
   As a first-order system in position and velocity, Newton's cell is a
   semi-implicit variant of Cauchy's step. Cauchy's theorem for systems
   covers it when the force law and its derivative are finite and continuous
   on the region, as for inverse-square attraction away from the centre.
   *Status:* `modern_reconstruction`.

c. **Partition independence.** Cauchy's §161 is the classical template for
   the obligation the time-subdivision note records: compare two divisions
   through a common refinement and show that the subdivision's influence
   vanishes. The repository's coarse and fine schedules make the same move,
   with non-nested endpoints and connectors tracked explicitly.
   *Status:* `modern_reconstruction`.

d. **The regional Lipschitz construction.** The supporting construction
   assumes a Lipschitz bound on the force only on a computed ball
   (`GeneralForceGrowth`). That is Lipschitz's condition in Peano's
   account, implied by Cauchy's continuous-derivative hypothesis. The
   construction is therefore a regional Cauchy–Lipschitz existence proof
   for Newton's polygon.
   *Status:* `modern_reconstruction`; supporting work under the 6 October
   convention.

e. **Continuity gives a curve; uniqueness needs more.** The nearest
   same-stage regularity clause is 1713 Lemma X, a finite force that
   increases or decreases continuously
   ([PROP_I_REALIZATION](PROP_I_REALIZATION.md#regularity-questions-retained-separately-from-existence)).
   Peano's theorem shows that a continuous right-hand side guarantees a
   solution without making it unique; for x′ = 3x^(2/3) a curve leaves the
   rest point at every later time. Newton's definite "linea curva" therefore
   presupposes a Lipschitz-type condition that neither edition states.
   *Status:* `editorial_interpretation`, confidence medium.

f. **Euler.** Recalled from memory and unverified: Euler used the same
   polygon as an approximation method in his *Institutiones calculi
   integralis* (1768) without a convergence proof. That would place the
   method between Newton's construction and Cauchy's theorem.
   *Status:* lead.
