---
title: "Scales, Actions and the Limit in Newton's Proposition I"
subtitle: "What a formal reconstruction of the area law says about the constants it needs, and about the one it cannot see"
author: "A. Rivero, with Claude (Anthropic)"
date: "5 October 2026"
geometry: margin=2.6cm
fontsize: 11pt
header-includes:
  - \usepackage{amsmath}
  - \usepackage{amssymb}
  - \newcommand{\dd}{\mathrm{d}}
  - \newcommand{\vb}[1]{\mathbf{#1}}
---

# Abstract

Newton's proof of the area law (Book I, Proposition I of the *Principia*)
replaces a continuous central force by impulses at equal time intervals,
proves the finite statement by Euclid I.37–38, and passes to the limit in one
sentence. A formal reconstruction of that sentence in Lean, using only
rational arithmetic and no later theorems, now stands at about a million
characters of code. This article records what that reconstruction has taught
about *scales*: the quantities with units that the limit needs in order to
exist. Three results are collected. First, every existence theory for the
limit, from Newton's own finiteness clauses to the Cauchy–Lipschitz and Peano
theorems, assumes a scale, and classical mechanics leaves its value free.
Second, the natural object for comparing a polygon cell with its curve, the
deflection triangle, satisfies an exact relation $m\,\mathcal A = \tau\,\Delta
t\,|\Delta V|$ in which $\tau$ is a time, and the quantity $\Delta t\,\Delta
V$ is the action carried by the deflection, $F^2\Delta t^3/m$. Third, that
action is where quantum mechanics meets Newton's limit: shrinking the time
step at fixed force drives it through $\hbar$ at $t_* = (m\hbar/F^2)^{1/3}$, a
scale that reproduces the measured gravitational quantum states of the
neutron. Classical mathematics cannot see this floor because its scales
rescale away. The hypothesis that the *Principia* itself selects a universal
action is thereby located precisely and left open: the construction fixes the
kind and place of such a constant, and its value comes from outside.

# 1. The one sentence

Proposition I of Book I states that a body moving under a force directed to a
fixed centre $S$ sweeps out, by the radius to $S$, areas proportional to the
times, in a fixed plane. Newton's proof divides the time into equal parts. In
the first part the body moves inertially from $A$ to $B$. In the second it
would continue to $c$ with $Bc = AB$; but at $B$ an impulse toward $S$
deflects it to $C$, with $cC$ parallel to $BS$. The triangles $SAB$, $SBc$,
$SBC$ are then equal, the first two by equal bases on one line, the last two
by equal bases between parallels (Euclid I.37–38). Repeating at $C$, $D$, $E$
gives equal triangles in equal times. Then:

> *Augeatur jam numerus & minuatur latitudo triangulorum in infinitum, & eorum
> ultima perimeter ADF (per Corollarium quartum Lemmatis tertii) erit linea
> curva; adeoque vis centripeta qua corpus de tangente hujus curvæ perpetuo
> retrahitur, aget indesinenter.*

"Let the number of triangles be increased and their width diminished
indefinitely, and their ultimate perimeter will be a curve; and so the
centripetal force, by which the body is perpetually drawn back from the
tangent of this curve, will act uninterruptedly."

In modern notation the finite part is a recurrence. With vertices
$\vb r_k$ at times $kh$ and a central impulse at each vertex,
$$
\vb r_{k+1} = 2\vb r_k - \vb r_{k-1} + \lambda_k\, \vb r_k ,
\qquad\text{hence}\qquad
\vb r_k \times \vb r_{k+1} = \vb r_{k-1} \times \vb r_k .
$$
Every triangle $S\,\vb r_k\,\vb r_{k+1}$ has the same doubled area
$\vb r_k \times \vb r_{k+1}$. This is exact and is the whole of the finite
argument; in the Lean reconstruction it is a short induction, valid for any
central field and any rational cell durations.

The sentence quoted above carries everything else. It asserts four things that
the finite argument does not supply: that the polygons converge to a curve;
that the curve is the motion under the continuous force; that the area law
passes from the polygons to the curve; and that the impulses, in the limit,
are the force. Lemma III Corollary 4, which Newton cites, proves that inscribed
rectilinear figures converge to a *given* curve. Here the curve is the
unknown. Of the roughly 1,500 theorems now in the reconstruction, almost all
serve these four obligations. The present article is about the constants they
require.

# 2. Newton's mathematics: boundaries in every dimension, the theorem in one

The reconstruction keeps to what Newton had. It is worth being explicit about
what that is, because the limit in Proposition I is a one-dimensional device
applied to a two-dimensional region.

Newton's limit theorem is Lemma I of Section I: quantities that approach each
other nearer than any given difference become ultimately equal. This is the
$\varepsilon$ in an $\varepsilon$–$N$ argument, and the reconstruction encodes
it faithfully. His fundamental theorem is Barrow's (1670), which in modern
terms reads
$$
\int_a^b \dd F = F(b) - F(a).
$$
This is Stokes' theorem in one dimension. Cutting $[a,b]$ at an interior point
$k$ works because $k$ enters once with each sign and cancels: $\int_a^k +
\int_k^b = \int_a^b$. The cancellation at the cut is what a modern reader
calls the orientation of the boundary.

Newton had the *concept* of a boundary in every dimension. In the draft *De
motu corporum in mediis regulariter cedentibus* (late 1684/5, Cambridge MS Add.
3965.5) he wrote a definition of moments as the generating principles of
quantities in continuous flux, listing "the present time of past and future,
… centripetal force or any other momentary force of impetus, the point of a
line, the line of a surface, the surface of a solid". He then struck the whole
definition out.[^def16] The point, the line and the surface are the boundaries
of the line, the surface and the solid; the present instant is the boundary of
past and future; and the impulse is the boundary-like agent of the motion. The
same draft shows him moving from instants to intervals: in the definition of
velocity he deletes *momentanea* and adds *certo tempore confecti* ("covered in
a given time"), and he strikes out a definition of force built on *singulis
momentis*. The De Motu of the same months says the body describes its
segments *singulis temporis momentis*; the 1687 text says *particulis*.

[^def16]: Newton Project NATP00091, par. 24, enclosed in `<del>` in the
transcription. The definition is absent from every other witness stored in the
project: both De Motu manuscripts, the 1687 and 1713 Definitions, and Book I of
1687, 1713 and 1726.

What he did not have is the *theorem* in higher dimensions. Green (1828),
Gauss and Ostrogradsky, and Kelvin and Stokes (1850s) need oriented surfaces
and volumes. The classical difficulty is Democritus' cone: cut a cone parallel
to its base, and ask whether the two faces of the cut are equal. If they are,
the cone is a cylinder; if not, it has steps. The dilemma is about shared
faces, which is exactly what orientation resolves, and Dehn's solution of
Hilbert's third problem (1901) shows that in three dimensions the volume of a
pyramid genuinely needs a limiting argument, whereas in the plane Bolyai and
Gerwien had shown that equal areas are cut-and-paste equivalent.

So Newton's two area devices are both one-dimensional partitions lifted to the
plane: strips over a base line (Lemmas II–III) and a fan of triangles from $S$
over a partition of time (Proposition I). The region that the reconstruction
must control, the area *between* a polygon and the curve it converges to, fits
neither device. It is bounded by two paths that may cross, and only oriented
cancellation ties it to them. A modern definition is
$$
D = \int |w(z)|\,\dd A(z),
$$
where $w$ is the winding number of the closed chain "polygon minus curve, plus
endpoint connectors" around $z$. This counts opposite lobes positively and is
the mass of the 2-chain between the paths. The reconstruction already brackets
it between the absolute signed area and a square-cover budget. The point for
this article is that even the definition of the object requires a notion of
orientation that Newton, in 1687, had reason to avoid.

Two further matters of principle belong here. First, Newton's instant $t_0$
and his interval $\dd t$ are different kinds of object, and so are the point
$x_0$ and the increment $\dd x$; the draft definition quoted above places the
instant and the point in the same list, and his method of fluxions makes every
quantity flow in time, so that $\dd x = \dot x\,\dd t$ is a postulate about
generation by motion rather than a theorem. Second, there is no maximum
velocity. Under $x' = x - ut$, $t' = t$, the interval $\dd t$ is the same in
every frame while $\dd x$ is not; Newton's kinematics is the limit $c \to
\infty$. He knew that light has a finite speed: in the Scholium after
Proposition XCVI he gives about ten minutes from the Sun in 1687, revised to
seven or eight in 1713. This is a fact about light as a stream of bodies, and
nothing in the *Principia* bounds the speed of a body.

# 3. The scales that existence needs

The reconstruction's existence argument for the limit curve works for a
general central force given by rational samples with an explicit error, on a
window of time, under a Lipschitz condition
$$
|\vb a(\vb x) - \vb a(\vb y)| \le L\,|\vb x - \vb y| .
$$
Here $\vb a$ is the acceleration field. The constant $L$ has units of
$1/\text{time}^2$. It defines a time,
$$
\tau_L = \frac{1}{\sqrt{L}} ,
$$
which is $1/\omega$ for the harmonic field $\vb a = -\omega^2 \vb x$ and about
$\sqrt{r^3/GM}$ for gravity near radius $r$: the local dynamical time. The
polygon converges once its step satisfies $h \ll \tau_L$. Only the *existence*
of a finite $L$ on the region of motion is assumed. Its value depends on the
law and the region, it rescales with the unit of time, and nothing in the
construction fixes it. For laws singular at the centre, $\tau_L \to 0$ as $r
\to 0$, which is why such laws need a region kept away from $S$; the inverse
cube marks the boundary of what can be confined.

The reconstruction also fixes a unit of time without saying so. Its window
condition reads $T(1 + L) \le \tfrac12$, which adds $1$ to a quantity of units
$1/\text{time}^2$, and its state magnitude $|\vb x| + |\vb v|$ adds a length to
a velocity. The arithmetic is unitless, so the proofs are unaffected; but a
scale read off these bounds may be the hidden unit rather than a property of
the motion. The remedy is to carry a calibration time $\tau_0$ explicitly, as
$|\vb x| + \tau_0 |\vb v|$ with windows on $h^2 L$ and $h/\tau_0$, and to check
that conclusions are invariant under rescaling $\tau_0$. This has since been
done in the code.

Can the Lipschitz constant be dispensed with? Peano's theorem (1886/1890)
gives existence of a solution of $\ddot{\vb x} = \vb a(\vb x)$ for a merely
continuous, bounded $\vb a$. But the bound $M$ on the force is itself a scale,
and the guaranteed time of existence is set by $M$, by a bound on the velocity
and by the size of the region. What is lost without Lipschitz is uniqueness,
which fails in Peano's examples, and constructivity: the proof extracts a
convergent subsequence of the polygons by compactness, and there are
computable continuous equations with no computable solution (Aberth 1971;
Pour-El and Richards 1979). Newton's own premise, in the 1713 revision of
Lemma X, is *vi finita … sive eadem continuo augetur vel continuo diminuatur*:
a finite force, constant or monotone along the path. That is a bound at
Peano's level, with monotonicity in place of modulus, and it says nothing about
uniqueness. Newton's finiteness clauses, in Lemma X for the force and in
Lemma XI for the curvature, assert that a scale *exists* without giving its
size.

The pattern is therefore: no existence theory without a scale; the Lipschitz
scale is the price of uniqueness and of a construction that converges step by
step. Field theories only sharpen this. Existence for partial differential
equations needs function spaces whose norms carry scales, solutions can blow up
in finite time, and in three-dimensional Navier–Stokes the conserved energy is
too weak to control small scales. Classical point charges must be given a
size. Quantum fields need a cutoff, and in QCD a scale, $\Lambda_{\rm QCD}$,
survives in the answer although none appears in the classical equations. In
Newton's mechanics the scale must exist but its value is free; in classical
fields criticality ties it to the dynamics; in quantum fields it is part of
the result.

# 4. Newton's cell, and the quantity $\Delta t\,\Delta V$

The reconstruction's proper object is the region between polygon and curve.
Before that region is controlled, one can ask what Newton's cell itself
carries. Take the kick at $B$ with step $h$:
$$
c = B + \vb v\,h, \qquad C = c + \vb a\,h^2 ,
$$
so that $Bc$ is the inertial continuation and $cC$ the deflection along the
force at $B$. (On the curve the departure from the tangent is $\vb a h^2/2$;
the polygon puts the whole deflection into one kick.)

*The deflection triangle.* The triangle $B\,c\,C$ has doubled area
$$
2\,\mathcal A = h^3\, \vb v \times \vb a .
$$
This is proved in Lean on polygons, and on the constructed curves its
normalized value converges to $\vb v \times \vb a / 2$.[^lean1]

*The potential step.* Let $V$ be the potential energy of the force, so that
$\vb F = m\vb a = -\nabla V$. Define $\Delta V$ as the difference between the
potential at the actual next point and at the inertial continuation,
$$
\Delta V = V(C) - V(c) \approx -\vb F\cdot cC = -m\,|\vb a|^2 h^2 .
$$
This $\Delta V$ is not the change of $V$ along the motion; on a circular orbit
$\dd V = 0$ along the path, while $\Delta V$ as defined is nonzero. For the
uniform field $V = mgy$ the relation is exact, $\Delta V = -mg^2h^2$, and is
checked in Lean; on the constructed harmonic curve $\Delta V/h^2$ converges to
$-m|\vb a|^2/2$.[^lean2]

[^lean1]: `DeflectionPotential.deflection_triangle` and
`GeneralForceTangentTriangle.normalized_triangles_converge`.

[^lean2]: `DeflectionPotential.galilean_potential_step`,
`galilean_area_potential_cross_relation`, and
`ConstructedHarmonicPotential.normalized_potential_steps_converge`.

*Area against potential.* Combining the two,
$$
m\,\mathcal A = \tau\,\Delta t\,|\Delta V| , \qquad
\tau = \frac{v_\perp}{2|\vb a|} ,
$$
where $v_\perp$ is the component of the velocity perpendicular to the force,
and $\tau$ is a time. Its behaviour along a motion is the content of the
relation:

| Motion | $\tau$ | Constant along the motion? |
|---|---|---|
| Uniform gravity (Galilean fall) | $v_0/(2g)$ | Yes, and exact on every polygon cell |
| Circular orbit, any force law | $r/(2v)$ | Yes |
| General central orbit | $\ell/(2\,r\,|f(r)|)$ | Only when $f(r) \propto 1/r$ |

Here $v_0$ is the constant horizontal speed, $\ell = |\vb r \times \vb v|$ the
specific angular momentum, and $f$ the radial acceleration law. A second test
reaches the same exceptional law. In the plane, $\Delta t\,(\Delta\vb x
\times \vb F)$ has the form $\Delta t\,\Delta W$ for a local potential $W$
exactly when $\nabla \cdot \vb F = 0$; among distance-only central laws this
singles out $f \propto 1/r$, and then $W$ is a multiple of the polar angle,
multivalued around $S$.

*What $\Delta t\,\Delta V$ is.* Write the impulse of the cell as $\Delta \vb p
= \vb F\,\Delta t$ and the departure from the tangent as $\delta \vb x =
\vb F\,\Delta t^2/m$. Then
$$
\Delta t\,|\Delta V| \;\approx\; |\Delta \vb p|\,|\delta\vb x| \;=\;
\frac{F^2\,\Delta t^3}{m} .
$$
The quantity is the action carried by the deflection: impulse times sagitta.
For uniform gravity the identity is exact. It is a dot product of a momentum
with a displacement, where the area $\mathcal A$ is a cross product; the
chord–arc lobe of a smooth curve, $(\vb v \times \vb a)\,h^3/12$, has the
same cross structure, and $m \times \text{lobe}/h = (\Delta \vb x \times
\Delta \vb p)/12$ is likewise an action.

# 5. Where quantum mechanics meets the limit

The classical regime of quantum mechanics is the regime in which the action
of a system is large compared with $\hbar$ and the force varies slowly over a
de Broglie wavelength. The second condition has two forms with the same shape
and different force components:
$$
\frac{\hbar\, m\, |F_\parallel|}{p^3} \ll 1 \quad\text{(WKB, along the path)},
\qquad
\frac{\hbar\, m\, |F_\perp|}{p^3} \ll 1 \quad\text{(across the path)} .
$$
The second is the condition $p\,\rho_F \gg \hbar$ on the radius $\rho_F =
p^2/(m|F_\perp|)$ on which the force turns the path, and it is the
quantitative version of Newton's two finiteness clauses, finite force and
finite curvature, read together. For unstable motion the correspondence lasts
only up to the Ehrenfest time, about $\tau \ln(S/\hbar)$ with $\tau$ set by the
force gradient, the same kind of time as $\tau_L$.

Now apply the uncertainty relation to Newton's cell. The deflection $\delta
x = F\Delta t^2/m$ and the impulse $\Delta p = F\Delta t$ can both be sharp
only if their product is at least of order $\hbar$:
$$
\frac{F^2\,\Delta t^3}{m} \gtrsim \hbar
\qquad\Longrightarrow\qquad
\Delta t \gtrsim t_* = \left(\frac{m\hbar}{F^2}\right)^{1/3} .
$$
The same time was reached earlier in this project from the path integral, by
asking when the free-particle spreading $\sqrt{\hbar t/m}$ overtakes the
deflection $Ft^2/m$. Here it is reached from the quantity $\Delta
t\,\Delta V$ of Section 4.

For uniform gravity, $F = mg$ gives
$$
t_* = \left(\frac{\hbar}{m g^2}\right)^{1/3},
\qquad
\ell_* = \left(\frac{\hbar^2}{m^2 g}\right)^{1/3} .
$$
For a neutron these are $t_* \approx 0.87\ \text{ms}$ and $\ell_* \approx 7.4\
\mu\text{m}$. The Schrödinger equation for a neutron bouncing on a horizontal
mirror has the natural length $\ell_0 = (\hbar^2/2m^2g)^{1/3} = \ell_*/2^{1/3}
\approx 5.9\ \mu\text{m}$, and its lowest state turns at $2.34\,\ell_0 \approx
13.7\ \mu\text{m}$, with energy $1.4\ \text{peV}$. These states were observed
by Nesvizhevsky and collaborators at the Institut Laue–Langevin in 2002, with
the first level at about $15\ \mu\text{m}$. Newton's cell, shrunk at fixed
force, reaches the quantum floor at precisely the scale of a real experiment.

What this does and does not show can be stated exactly.

- Classical mechanics needs a scale for its existence theory (Section 3) and
  leaves its value free. Every scale found in Sections 3 and 4, $\tau_L$,
  the Peano bound, the hidden unit, $\tau = v_\perp/2|\vb a|$, depends on
  the system and rescales with the units.
- Quantum mechanics supplies one universal scale, $\hbar$, from outside.
- Newton's construction meets that scale at a definite place: shrinking $h$ at
  fixed force carries the per-cell action $F^2h^3/m$, which is $\Delta
  t\,\Delta V$, through $\hbar$ at $t_*$. The limit $h \to 0$ that the one
  sentence of Section 1 performs has a physical floor there.
- The classical mathematics cannot see the floor. Under a rescaling of units
  the relation $m\mathcal A = \tau\,\Delta t\,|\Delta V|$ is covariant, and
  only an imported $\hbar$ breaks the covariance. Every checked refinement
  residual in the reconstruction vanishes with the mesh, and none selects a
  constant.

# 6. The hypothesis, located

The project's diagnostic question is whether anything in Newton's own
construction, or in his revisions of it between 1684 and 1726, points to a
universal action. The results above locate the hypothesis without deciding
it. They fix the *kind* of constant that could enter, an action, because the
invariants that survive every mesh and every force law (the phase area and the
areal product) are actions. They fix the *place* at which it would enter, the
finiteness premises of Lemmas X and XI and the per-cell deflection action of
Proposition I. And they fix the *form* of the bound it would impose, $t \gtrsim
(m\hbar/F^2)^{1/3}$. What they do not do is produce a value: the construction
is covariant under rescaling, and a value has to be imported. Newton's
revisions, which move the force premise from *regularis* to *finita* and put
finite curvature into the statement of Lemma XI, show him making the
existence of a scale explicit; they do not show him assigning it a size, and
on the present evidence nothing in the *Principia* does.

This is the honest outcome that the project's goals allow: an undetermined
scale, with the dimension of action, entering through a finiteness premise,
and matching a measured quantum phenomenon once the universal value is
supplied.

# 7. The reconstruction as it stands

For the reader who wants to know what the formal work has established, as of
the commit at which this article was written:

- The finite area law holds for any central field and any rational cell
  durations.
- For a general central force given by rational samples with explicit error,
  on a window $T \cdot \text{rate}(\tau_0, L) \le \tfrac12$ and under
  bounds on the sampled force along the polygons, the polygons converge to a
  curve, in a completion of the rationals built inside the project; the
  construction is uniform along whole edges, and the two routes to the curve
  (rescaling a schedule for each rational time, and prefixes of one dyadic
  family) agree at every dyadic rational time.
- The constructed velocity is the limit of position secants, and the force
  evaluated on the curve is the limit of velocity secants.
- The region between polygon and curve is an explicit geometric object whose
  outer content decreases like $4C^2/2^m$ with the dyadic level $m$.
- The deflection triangle and the potential step have the limits stated in
  Section 4.
- The harmonic field, $\vb a = -\omega^2\vb x$, is an instance of all of this,
  with its earlier special-case theorems recovered as corollaries.

Still open, in the order that matters: discharging the assumed sample bounds
from the Lipschitz condition; the swept-area law for the constructed curve,
which is Proposition I's own conclusion; confinement to an annulus and the
gluing of time windows, needed for singular laws and full orbits; independence
of the partition; and the merely continuous classes, where existence is
expected without uniqueness.

The code is about 1.02 million characters, roughly forty times the length of
Newton's Sections I–II and six hundred times the length of Proposition I. It
is not a loop. Statement shapes repeat at a rate of about five per cent, each
increment has closed a distinct obligation, and the harmonic case has been
reduced to a test. It is, however, a tower built upward on a bundle of
assumptions whose discharge keeps being deferred, and the recommendation of
the code review that accompanied this article is to build downward next.

# Sources and status

Newton's texts are cited from the Newton Project transcriptions kept in the
repository: *De motu corporum in gyrum* and its revisions (NATP00089,
NATP00090), the draft *De motu corporum in mediis regulariter cedentibus*
(NATP00091), and the Definitions, Laws and Book I of 1687, 1713 and 1726
(NATP00075–77, NATP00080–82, NATP00085–87). The Lean results named in the
footnotes compile with Lean 4.19 core only and depend on the standard axioms;
they are modern reconstructions and supply no historical premise.

Of the claims in this article: the identities of Section 4 are Lean-checked in
the cases stated; the relations for $\tau$, the divergence test, the
identification of $\Delta t\,\Delta V$ and the bound $t_*$ are derivations;
the neutron arithmetic was computed for this article; and the citations of
Peano, Aberth, Pour-El and Richards, and Nesvizhevsky et al. are from memory
and should be verified against the original papers before being relied upon.
