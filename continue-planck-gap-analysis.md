# Continue Planck Gap Analysis

Source: https://chatgpt.com/c/6aac89de-b890-83eb-9e28-a88caf63ab28

Exported 2026-09-21 — 16 user turns, 15 assistant replies (reasoning traces omitted, as on the page)

---

## User

[https://arivero.github.io/navstokgap/](https://arivero.github.io/navstokgap/) I wonder how to continue this

---

## ChatGPT

I would change direction slightly before extending the paper. There is a real mathematical problem in the current “Planck gap” conclusion, but fixing it actually exposes a more interesting theorem.

The protocol bound itself looks useful. The problematic step is the reduction from the two resource scales $L,P$ to the single “phase-space area” $A=LP$.

From the current Theorem 2 you have, with $c_\epsilon=1-2\epsilon$,

$$
\frac{F\tau L}{\hbar}
+\frac{F\tau^2P}{2m\hbar}\ge c_\epsilon .
\tag{1}
$$

That is a perfectly sensible anisotropic resource bound. But set $A=LP$, as the note does. Then

$$
F\ge
\frac{\hbar c_\epsilon}
{\tau\left(L+\frac{\tau A}{2mL}\right)}.
\tag{2}
$$

The denominator

$$
D(L)=L+\frac{\tau A}{2mL}
$$

has a **minimum**, not a maximum, at

$$
L^2=\frac{\tau A}{2m}.
$$

The draft minimizes $D$ and concludes

$$
\tau\Delta E\ge
\frac{c_\epsilon^2\hbar^2}{4A}.
$$

But for a necessary lower bound you need control of $D$ from **above**. At fixed $A$,

$$
D(L)\longrightarrow\infty
\qquad (L\to0\ {\rm or}\ L\to\infty),
$$

so (1) permits

$$
\tau\Delta E\longrightarrow0.
$$

Thus the claimed fixed-$A$ Planck floor is not valid for arbitrary aperture shape.

This is not merely a loose inequality. Squeezing gives a direct counterexample. Take a minimum-uncertainty Gaussian with

$$
\Delta y=L,\qquad
\Delta p=P=\frac{\hbar}{2L},
\qquad LP=\frac{\hbar}{2}.
$$

For the Galileo displacement

$$
D(\alpha,\beta),\qquad
\alpha=-\frac{F\tau^2}{2m},
\quad
\beta=F\tau,
$$

its overlap has the Gaussian form

$$
\left|\langle\psi|D(\alpha,\beta)|\psi\rangle\right|^2
=
\exp\!\left[
-\frac{\beta^2L^2+\alpha^2P^2}{\hbar^2}
\right]
$$

(up to covariance/convention factors that do not affect the argument).

Now let $L\to\infty$, $P=\hbar/(2L)$. The phase-space area remains exactly $\hbar/2$, while

$$
|\langle D\rangle|^2\to0
$$

for every $\beta\ne0$. Hence one can distinguish an arbitrarily weak force with arbitrarily small Helstrom error while keeping the uncertainty product minimal. This is exactly the standard squeezing mechanism; recent displacement-discrimination work explicitly exploits squeezing to lower state overlap. [DOI](https://doi.org/10.1038/s41534-026-01256-5)

So I think the next note should actually be a **no-go theorem for the scalar aperture**.

Define the dimensionless aspect ratio

$$
r=
\frac{L}{\sqrt{\tau A/(2m)}}.
$$

Then the correct consequence of (1), for a *specified* shape, is

$$
\boxed{
\tau\Delta E
\ge
\frac{c_\epsilon^2\hbar^2}
{A\,(r+r^{-1})^2}.
}
\tag{3}
$$

At $r=1$ this reproduces the current

$$
\frac{c_\epsilon^2\hbar^2}{4A},
$$

but this is the **balanced aperture**, not a shape-independent optimum. As $r\to0$ or $\infty$, the lower bound goes to zero.

That, in my view, gives a much better conceptual result:

$$
\boxed{\text{uncertainty area alone does not produce an action gap.}}
$$

More geometrically, the reason is that $LP$ is symplectic-area-like and invariant under squeezing,

$$
(y,p)\mapsto(\lambda y,p/\lambda),
$$

whereas distinguishability of a particular Weyl displacement depends on a **directional metric quantity**

$$
\Delta(\beta y-\alpha p),
$$

which squeezing can make arbitrarily large while preserving the symplectic area. Quantum mechanics supplies a symplectic form through $[y,p]=i\hbar$, but a single displacement experiment additionally needs a metric/resource ellipsoid. There is no metric encoded by $\hbar$ alone.

That seems to me a substantially deeper result than the current Corollary 3. It says exactly why the attempt to derive a universal Planck action cell from Robertson fails: a symplectic cell is not a Euclidean disk. You can squeeze it indefinitely.

There is then a very natural sequence for continuing the project:

1. **Replace the present Corollary 3 by the aspect-ratio theorem (3), and add the squeezed-Gaussian counterexample.** This should be done before the historical polishing, general-force extension, or constant chasing.

2. **Promote the failure to a general symplectic no-go theorem.** Something along the lines:

> For every nonzero phase-space displacement $z$, every $A\ge\hbar/2$, and every $\epsilon>0$, there exists a state with uncertainty-area bounded by $A$ whose displacement by $z$ is distinguishable from itself with Helstrom error below $\epsilon$.

For pure Gaussians at $A=\hbar/2$, squeezing essentially proves it immediately. This would be a clean foundations result.

3. **Ask what extra physical structure restores a gap.** Equation (1) already answers this: you need separate upper bounds on the two conjugate resources, or equivalently a bounded covariance ellipsoid. A determinant bound is insufficient. Candidates are finite laboratory extent $L$, momentum/energy bandwidth $P$, a confining Hamiltonian, or an imposed bound on the largest covariance eigenvalue. Each introduces additional physics beyond the canonical commutator.

4. **Then remove the rank-one restriction.** This seems straightforward. For a mixed state,
$$
{\cal L}_{B}(\rho,e^{-iG}\rho e^{iG})
\le \frac12\sqrt{F_Q(\rho,G)}
\le \Delta_\rho G ,
$$
since $F_Q(\rho,G)\le4\operatorname{Var}_\rho G$. The Bures/QFI geometry is standard, and together with trace-distance/fidelity inequalities should replace the pure-state Mandelstam–Tamm step. QFI being bounded above by four times the variance is standard for mixed states. [Wikipedia](https://en.wikipedia.org/wiki/Quantum_Fisher_information)

The one subtlety is your hybrid argument: the aperture assumption must cover the conditional **hybrid** states, not merely those realized under the two endpoint hypotheses. An instrument-level condition (“every output branch belongs to the covariance-bounded set”) would make that clean.

5. **Only after that attack sharp constants.** The really meaningful optimization is no longer a number between the current constants; it is an optimization at fixed covariance/resource ellipsoid. The natural exact object is
$$
\inf_{\rho\in{\cal R}}
F\!\left(\rho,D(\alpha,\beta)\rho D^\dagger(\alpha,\beta)\right),
$$
or its trace-distance counterpart, where ${\cal R}$ is a physically specified resource set.

There is also a nice connection back to your earlier negative results. The repo currently says “a larger laboratory lowers the floor”; the stronger statement is: **even a minimal Heisenberg-area state can remove the floor by changing its aspect ratio**. The missing resource is not area but shape.

This also clarifies what has and has not been reconstructed from Newton. The robust theorem is not yet “Newton + finite records $\Rightarrow\hbar$-sized action gap.” It is closer to

$$
\text{Newton's Galileo comparison}
+\text{quantum distinguishability}
\Rightarrow
\frac{F\tau}{\hbar}
\left(L+\frac{\tau P}{2m}\right)\gtrsim1.
$$

That equation is actually quite attractive: sagitta and impulse form the two components of a Weyl displacement, and the admissible laboratory defines its dual norm. The action $F^2\tau^3/m$ appears only after choosing a metric/aspect ratio. I think **that is the point worth developing now**.

And it has a very Newtonian consequence: the missing assumption is no longer mysterious “indeterminacy”. It is the choice of how the two conjugate resolutions are tied together. Robertson supplies an area; Newton's geometric limiting procedure would additionally need something that forbids unlimited squeezing of that area. That is a much sharper place for the programme to stand. [arivero.github.io](https://arivero.github.io/navstokgap/)

---

## User

every non go is distraction

---

## ChatGPT

Yes. Then I would prune the programme accordingly: **only constructive steps that generate the positive action scale belong on the main line**.

The most promising continuation I see is not another measurement bound but the **central-extension/holonomy route**. It starts directly from Newton’s impulse construction and ends in a state-independent phase.

With your convention

$$
D(a,b)=\exp\!\left[\frac{i}{\hbar}(b\hat y-a\hat p)\right],
$$

Weyl composition gives

$$
D(z_1)D(z_2)
=
e^{-\,i\omega(z_1,z_2)/(2\hbar)}
D(z_1+z_2),
\qquad
\omega(z_1,z_2)=a_1b_2-a_2b_1.
$$

So exchanging the order of two Newtonian displacement steps produces

$$
D(z_1)D(z_2)
=
e^{-i\omega(z_1,z_2)/\hbar}
D(z_2)D(z_1).
\tag{1}
$$

This is exactly the Heisenberg/Weyl central extension; the analogous mass cocycle is the central extension of the Galilei group. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0370157397000707) The phase associated with nonparallel phase-space displacements and its dependence on their ordering is also standard. [arXiv](https://arxiv.org/abs/1702.01833)

Now apply it to the Galileo comparison. In the free interaction picture the constant-force evolution traces

$$
z(t)=\left(
-\frac{Ft^2}{2m},\,Ft
\right).
\tag{2}
$$

Cut the trajectory into Newtonian impulse increments

$$
\delta z_j=z(t_j)-z(t_{j-1}).
$$

Compare two constructions from **exactly the same increments**:

$$
U_+=D(\delta z_N)\cdots D(\delta z_1),
$$

and the reverse ordering

$$
U_-=D(\delta z_1)\cdots D(\delta z_N).
$$

Both end at exactly the same phase-space point,

$$
\sum_j\delta z_j=z(\tau),
$$

so all dependence on the initial state cancels. They differ only by the centre:

$$
U_-^\dagger U_+
=
e^{i\Phi_N}\mathbf 1 ,
$$

with

$$
\Phi_N=
\frac1{\hbar}
\sum_{i<j}
\omega(\delta z_i,\delta z_j).
\tag{3}
$$

Take the refinement limit. Equation (3) becomes

$$
\Phi
=
\frac1{\hbar}\int_0^\tau
\left(\alpha\,d\beta-\beta\,d\alpha\right).
\tag{4}
$$

For (2),

$$
\alpha=-\frac{Ft^2}{2m},
\qquad
\beta=Ft,
$$

hence

$$
\alpha\dot\beta-\beta\dot\alpha
=
\frac{F^2t^2}{2m},
$$

and therefore

$$
\boxed{
\Phi
=
\frac{F^2\tau^3}{6m\hbar}
=
\frac{\tau\Delta E}{3\hbar}
}.
\tag{5}
$$

That is the calculation I would make the new centre of the project.

It has several unusually nice properties. There is **no preparation width, no apparatus aperture, no error-disturbance relation, no Gaussian assumption and no squeezing variable**. The particle can start in arbitrary $|\psi\rangle$; both branches finish in the same $D(z(\tau))|\psi\rangle$. All that remains is a central phase.

And the phase is literally a phase-space area,

$$
\hbar\Phi=\int p\,dq-q\,dp,
$$

so the quantity your Newton area programme has been trying to isolate reappears as the holonomy of the quantum lift of Newton's polygon. This is not an analogy: Weyl composition makes it an exact identity.

There is a second strong result hidden in (3). For infinitesimal increments at $t_i<t_j$,

$$
\omega(dz_i,dz_j)
=
\frac{F^2}{m}(t_j-t_i)\,dt_i\,dt_j>0.
\tag{6}
$$

Therefore **reverse ordering is extremal**. Among all permutations of the same Newtonian increments, every inverted pair contributes positively and reversal inverts every pair. Thus

$$
|\Phi_\pi|\le
\Phi_{\rm reverse}
=
\frac{\tau\Delta E}{3\hbar}.
\tag{7}
$$

That is already a respectable theorem: within the whole class of protocols formed by permuting the same impulse elements, the forward/reverse interferometer gives the largest possible state-independent quantum signal.

Put the two orders on the arms of a control qubit. Under $F=0$, the relative phase is zero. Under $F\neq0$,

$$
|+\rangle\longrightarrow
\frac{|0\rangle+e^{i\Phi}|1\rangle}{\sqrt2}.
$$

Consequently the optimal single-shot discrimination error is exactly

$$
\epsilon
=
\frac12\left(1-\left|\sin\frac{\Phi}{2}\right|\right)
=
\frac12\left[
1-\left|
\sin\!\left(\frac{\tau\Delta E}{6\hbar}\right)
\right|
\right].
\tag{8}
$$

For prescribed $\epsilon<1/2$, on the first branch,

$$
\boxed{
\tau\Delta E
\ge
6\hbar\arcsin(1-2\epsilon)
}.
\tag{9}
$$

And perfect single-shot discrimination occurs first at

$$
\boxed{
\tau\Delta E=3\pi\hbar=\frac32h .
}
\tag{10}
$$

The factor $3$ is geometrical, not arbitrary: it comes from integrating the symplectic area of the parabolic Galileo displacement.

I would therefore make the next result something like:

> **Newton–Weyl holonomy theorem.** Refining Newton's constant-force impulse polygon does not erase the distinction between different orderings of its infinitesimal steps. In the quantum central extension, chronological and antichronological refinement converge to operators with identical classical endpoint and relative phase
> $$
> \Phi=\frac{F^2\tau^3}{6m\hbar}.
> $$
> Among permutations of the same increments, reversal maximizes the phase.

That is a **positive construction all the way through**. It also gives a much cleaner path toward your original idea: Newton sends every individual polygonal defect to zero, but the noncommutative composition retains a finite second-order quantity under refinement. That retained quantity is the symplectic area/action, and $\hbar$ is exactly the conversion between that area and observable phase.

The next serious mathematical question is then constructive too: whether the factor $1/3$ is peculiar to constant force or is the first member of a general formula

$$
\Phi[P]
=
\frac1{\hbar}\int \omega(z,dz)
$$

for Newton polygon refinements, and which classical trajectories maximize this holonomy at fixed energy transfer.

---

## User

"Newton's geometric limiting procedure would additionally need something that forbids unlimited squeezing of that area." Go with very detail across the principia, their axioms, and how they justify the squeezing of the area.

---

## ChatGPT

Yes. Reading the *Principia* specifically for this question changes the emphasis. Newton does not merely fail to impose a smallest cell: his mathematical architecture is constructed so that the **deflection, impulse, time interval, and associated areas may all be made arbitrarily small while certain ratios remain finite**.

There is one distinction to keep sharp. The modern quantum squeeze

$$
(\Delta q,\Delta p)\mapsto(\lambda \Delta q,\lambda^{-1}\Delta p),
\qquad
\Delta q\,\Delta p=\text{const},
$$

is not an axiom of the *Principia*; Newton has no uncertainty ellipse or symplectic phase-space formalism. But the *Principia* supplies essentially all the classical ingredients that make such anisotropic squeezing unobjectionable: no minimum time, no minimum displacement, no minimum impulse, linear composition of arbitrarily subdivided impulses, and a limiting procedure explicitly formulated in terms of **divisible quantities diminished without bound**.

The important point is stronger than I suggested before: if we are trying to derive a positive action floor from Newton, the obstacle is not merely that Newton omitted something that would prohibit refinement. **Newton positively builds unrestricted refinement into the deductive machinery.**

## The foundations before Book I

Start even before the Laws.

Newton's Definition II identifies quantity of motion with what we write

$$
p=mv.
$$

Definition IV defines an impressed force as an action which changes the state of rest or uniform rectilinear motion. Crucially, the force does not remain stored in the body after the action; the altered motion persists by inertia. This makes a trajectory naturally decomposable into inertial stretches connected by impressed changes of motion. [Wikisource](https://en.wikisource.org/wiki/The_Mathematical_Principles_of_Natural_Philosophy_%281846%29/Definitions)

Then comes the Scholium on space and time. Newton's mathematical time is deliberately distinguished from its sensible measurement. Absolute mathematical time “flows equably”; hours, days and other observable clocks are merely external measures of it. He even notes elsewhere in the same discussion that actual motions need not provide a perfectly equable clock. Thus the finite resolution of a physical clock cannot, within Newton's foundations, be promoted into a smallest mathematical interval. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00080)

That already removes one possible stopping mechanism:

$$
\text{clock resolution}\neq\text{minimum Newtonian }dt.
$$

The analogous move is made for space. Mathematical space is not constituted from the sensible marks by which we measure it. So neither ruler divisions nor clock ticks supply the ontology of the geometry.

That is significant for your problem. If somebody tells Newton, “eventually the sagitta is smaller than any possible measurement,” Newton's formal response can simply be that this has nothing to do with whether the mathematical sagitta continues to decrease.

## The Axioms themselves make the dynamics refinable

Newton literally titles the next section **“Axioms, or the Laws of Motion.”**

Law I gives the reference trajectory:

$$
q_{\rm inertial}(t)=q_0+v_0t.
$$

Without impressed force, continuation is rectilinear and uniform. That is exactly the tangent trajectory against which all his curvilinear deviations are measured. [Wikisource](https://en.wikisource.org/wiki/Page%3ANewton%27s_Principia_%281846%29.djvu/89)

Law II is more important. Change of motion is proportional to impressed motive force and occurs in the direction of that force. Newton then immediately says that the result is proportional whether the force is impressed at once or **“gradually and successively.”** [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00081)

In modern notation, for a short interval,

$$
\delta p\simeq F\,\delta t .
$$

Therefore under

$$
\delta t\mapsto\lambda\delta t
$$

one gets

$$
\delta p\mapsto\lambda\,\delta p.
$$

Nothing in Law II supplies a lower bound

$$
|\delta p|\ge p_*.
$$

Quite the opposite: because the law is homogeneous, subdivision produces correspondingly smaller changes of motion.

Newton's Corollary I then establishes parallelogram composition. Independent impressed motions add vectorially. So splitting a change of motion into pieces does not change the resulting finite change:

$$
\Delta p
=
\delta p_1+\cdots+\delta p_N.
$$

This is the dynamical algebra required for arbitrary refinement. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00081)

Law III does not rescue a minimum. Every small impulse has an equal and opposite reaction, but if

$$
\delta p\rightarrow\lambda\delta p,
$$

then its reaction goes to

$$
-\lambda\delta p.
$$

The third law makes the recoil exact; it does not quantize it. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00081)

So the first three Laws are completely homogeneous with respect to reducing the elementary mechanical transaction.

## Newton explicitly derives Galileo's $t^2$ scaling from the Laws

The Scholium following the Laws is unusually direct for us. Newton says that from the first two laws and their corollaries Galileo obtained both free fall and the projectile parabola. Under uniform gravity, equal particles of time receive equal increments of motion, velocity therefore grows proportionally to time, and distance grows in the duplicate ratio of time. [Wikisource](https://en.wikisource.org/wiki/Page%3ANewton%27s_Principia_%281846%29.djvu/95)

In our notation,

$$
p_y(t)=Ft,
$$

and

$$
y(t)=\frac{F}{2m}t^2.
$$

Meanwhile Law I supplies

$$
x(t)=vt.
$$

So the two small quantities relevant to the Newton/Galileo comparison have **different refinement orders**:

$$
\delta x=v\,\delta t=O(\delta t),
$$

$$
\delta y=\frac{F}{2m}\delta t^2=O(\delta t^2).
$$

This is already the squeeze.

The trajectory approaches its inertial tangent anisotropically:

$$
\frac{\delta y}{\delta x}
=
\frac{F}{2mv}\delta t
\longrightarrow0.
$$

It becomes arbitrarily long compared with its transverse deviation.

## Book I, Section I makes this into a general limiting calculus

This is where Newton becomes especially explicit.

Lemma I says that if quantities approach equality so closely that their difference can become smaller than **any assigned difference**, their ultimate ratio is equality. This is one reason Pourciau has argued that Newton's treatment contains a recognizably epsilon-style limit argument, though historians disagree over the most appropriate modern reconstruction of Newton's “ultimate ratios.” [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Lemmas II and III then do precisely what we would nowadays call a squeeze argument for areas.

Take inscribed and circumscribed strips. Their discrepancy is bounded by a rectangle whose width is the mesh. Newton says the width is diminished indefinitely, making the error rectangle smaller than any given area. Therefore inscribed, circumscribed and curved figures ultimately agree. Unequal meshes are permitted too: it is sufficient that the **largest** width go to zero. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

In modern language,

$$
0\le
A_{\rm outer}-A_{\rm inner}
\le
H\,\|\mathcal P\| ,
$$

where $\|\mathcal P\|$ is the maximum mesh width. Therefore

$$
\|\mathcal P\|\to0
\quad\Longrightarrow\quad
A_{\rm outer}-A_{\rm inner}\to0.
$$

There is no smallest admissible $\|\mathcal P\|$.

That is already a direct justification of squeezing an area to zero.

## Lemma X: force-generated departure is quadratic

Newton next turns the geometrical limiting machinery into dynamics.

The 1687 Lemma X says that spaces generated at the beginning of motion by a regular force are in the duplicate ratio of the times. In 1713 Newton makes the hypothesis more explicit: for **any finite force**, fixed or continuously increasing or decreasing, the initially generated spaces are in the duplicate ratio of the times. [Wikisource](https://la.wikisource.org/wiki/Philosophiae_Naturalis_Principia_Mathematica/Liber_I/Sect._I._DE_Methodo_rationum_primarum_%26_ultima_rum.)

Thus locally,

$$
\delta_\perp(t)
=
C\,t^2+o(t^2).
$$

For constant force,

$$
C=\frac{F}{2m}.
$$

So halving the interval gives

$$
t\to\frac t2,
\qquad
\delta_\perp\to\frac{\delta_\perp}{4}.
$$

Nothing special happens at any finite iteration.

This is exactly Newton's formal answer to the question “how close can the forced trajectory become to its inertial continuation?”:

$$
\text{closer than any assigned transverse difference.}
$$

## Lemma XI: the relevant areas are cubic

Lemma XI then supplies the decisive power counting.

For finite nonzero curvature, Newton proves that the subtense/sagitta is ultimately quadratic in the adjacent arc or tangent length:

$$
BD\sim C\,AD^2.
$$

Consequently a triangle formed from tangent length $AD$ and deviation $BD$ behaves as

$$
A_\triangle
\sim \frac12 AD\,BD
\sim C'AD^3.
$$

Newton explicitly states that the corresponding curvilinear areas and segments occur in the **triplicate ratio** of the tangent/chord/arc lengths. For the parabolic case the curved area is $2/3$ of the tangent triangle and the chord–curve segment $1/3$. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

For your Galileo geometry,

$$
x=vt,\qquad y=\frac{F}{2m}t^2,
$$

so

$$
A_{\rm inertial,curve}
=
\int_0^\tau y\,dx
=
v\int_0^\tau \frac{F}{2m}t^2dt
=
\boxed{\frac{Fv}{6m}\tau^3}.
$$

The containing tangent triangle is

$$
A_\triangle
=
\frac12(v\tau)
\left(\frac{F\tau^2}{2m}\right)
=
\frac{Fv}{4m}\tau^3,
$$

and therefore indeed

$$
A_{\rm inertial,curve}
=
\frac23A_\triangle.
$$

The matched-endpoint chord lens is

$$
A_{\rm chord,curve}
=
\frac13A_\triangle
=
\frac{Fv}{12m}\tau^3.
$$

So the complete Newtonian squeeze is

$$
\boxed{
\delta t\sim\lambda,\qquad
\delta x\sim\lambda,\qquad
\delta p\sim\lambda,\qquad
\delta y\sim\lambda^2,\qquad
\delta A\sim\lambda^3.
}
$$
That hierarchy comes essentially straight out of Law II + Lemmas X–XI.

## And Newton then expressly denies that “least” means a least magnitude

The Scholium at the end of Section I is probably the most important text for your present question.

Newton says that although the method of indivisibles is shorter, he prefers first and last ratios. When he subsequently speaks as though quantities consist of particles, or uses tiny curved lines as straight ones, they are **not indivisibles** but *evanescent divisible quantities*. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Then he anticipates almost exactly the objection we are interested in: if there are ultimate ratios, perhaps there are ultimate magnitudes and hence indivisible least parts.

His answer is no.

The ratios are limits of quantities **decreasing without limit**. And he concludes that when he says “least,” “evanescent,” or “ultimate,” the reader must not understand quantities having any determinate least magnitude; they are to be conceived as continually diminished without end. This wording is already present in the 1687 first edition, not introduced as a later clarification. [Wikisource](https://la.wikisource.org/wiki/Philosophiae_Naturalis_Principia_Mathematica/Liber_I/Sect._I._DE_Methodo_rationum_primarum_%26_ultima_rum.)

That makes an important historical distinction possible.

Newton is not saying

$$
dx=\text{a tiny but finite atom of length}.
$$

He is saying effectively

$$
dx\rightarrow0
$$

while ratios constructed from it tend to definite values.

Hence a proposal such as

$$
A\ge A_*>0
$$

for every legitimate Newtonian comparison cell runs directly opposite to the methodological declaration at the end of Section I unless $A_*$ comes from some **additional physical restriction not belonging to the limiting geometry**.

One phrase in this Scholium must be handled carefully. Newton says *Neque novit natura limitem*—roughly, nature knows no bound—but there it occurs in his discussion of endlessly interpolable orders of contact between curves. It would be too strong historically to quote that as a general declaration that physical nature has no atomic scale. The much safer evidence for our purpose is his explicit statement that the quantities used in the proofs are divisible and can be diminished without limit. [Wikisource](https://la.wikisource.org/wiki/Philosophiae_Naturalis_Principia_Mathematica/Liber_I/Sect._I._DE_Methodo_rationum_primarum_%26_ultima_rum.)

## Proposition I is where the geometry and mechanics are welded together

This is perhaps the most revealing passage in the entire book.

Newton divides time into equal parts. During the first part the body follows its inertial straight line. At the end of the interval, a centripetal impulse changes its direction. It then follows another straight piece until the next impulse. Law I supplies the inertial legs; Law II and Corollary I supply the impulse composition. The resulting polygon sweeps equal triangles in equal times. [Wikisource](https://en.wikisource.org/wiki/The_Mathematical_Principles_of_Natural_Philosophy_%281846%29/BookI-II)

Then Newton explicitly performs the refinement:

$$
N\to\infty,
\qquad
\Delta t\to0.
$$

The number of triangles is increased indefinitely and their breadth diminished indefinitely. The polygonal perimeter becomes the curve, while the sequence of discrete centripetal impulses becomes a continually acting centripetal force. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00082)

In modern notation the construction is

$$
\Delta p_j
=
F(q_j)\,\Delta t+O(\Delta t^2),
$$

with

$$
|\Delta p_j|\to0,
\qquad
N|\Delta p_j|\sim O(1).
$$

This is an important conceptual point:

**Newton obtains a finite continuous force precisely by taking individual impulses to zero.**

If there were a minimum impulse

$$
|\Delta p|\ge p_*,
$$

his Proposition I construction would stop after finitely many subdivisions.

Likewise, if there were a minimum time

$$
\Delta t\ge t_*,
$$

or a minimum sagitta,

$$
s\ge s_*,
$$

the limiting construction would fail.

So a Planckian lower scale is not hidden inside Newton's proof. It would be a modification of one of its essential limiting assumptions.

There has been historical discussion about whether Newton supplied every convergence detail required by modern standards. Nauenberg and Erlichson reconstructed the passage from impulse polygons to continuous orbits and argued that the limit can be made mathematically sound under the appropriate regularity assumptions. That technical debate does not alter the feature relevant here: Newton's intended construction unequivocally sends the polygon mesh to zero. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0315086002000083)

## Proposition VI makes the point even sharper

This is perhaps the closest Newton gets to writing the precise ratio you are interested in.

For a nascent orbital arc, Proposition VI states that centripetal force is proportional to

$$
\frac{\text{sagitta}}{(\text{time})^2}.
$$

In our notation,

$$
F\propto\lim_{\tau\to0}
\frac{s(\tau)}{\tau^2}.
$$

Newton explicitly obtains this from Lemma XI and Lemma X. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00082)

This is quite profound for the present programme.

The sagitta itself disappears:

$$
s(\tau)\rightarrow0.
$$

The time disappears:

$$
\tau\rightarrow0.
$$

Yet

$$
\frac{s(\tau)}{\tau^2}\rightarrow
\text{finite nonzero force}.
$$

So Newton's mechanics is deliberately constructed so that **physical information survives in ratios of quantities which individually vanish**.

A minimum sagitta would not help Newton define force. It would destroy the limiting procedure by which he determines it.

That is exactly opposite to a naïve Planck-cutoff interpretation.

## What happens to your inertial–parabola area under repeated refinement

Suppose a fixed total duration $T$ is cut into $N$ pieces,

$$
h=\frac TN.
$$

Relative to the tangent at the beginning of each cell, the constant-force trajectory departs by

$$
\delta y(s)=\frac{F}{2m}s^2,
\qquad 0<s<h.
$$

The tangent–curve defect area of one cell is

$$
A_{\rm cell}
=
v\int_0^h\frac{F}{2m}s^2ds
=
\frac{Fv}{6m}h^3.
$$

Therefore the total defect of the $N$-cell tangent polygon is

$$
A_N
=
N A_{\rm cell}
=
\frac{FvT^3}{6mN^2}.
$$

Hence

$$
\boxed{A_N\sim N^{-2}\rightarrow0.}
$$

This is exactly the sort of convergence supplied by Lemmas II–III and X–XI.

Notice an important distinction. The **total area between the original horizontal inertial trajectory and the full falling parabola over fixed $T$** does not disappear merely because we partition it. What disappears is the error between the smooth trajectory and its locally inertial polygonal reconstruction.

That is the Newtonian refinement question.

Each local defect goes as $N^{-3}$; there are $N$ of them; therefore the total unresolved defect goes as $N^{-2}$.

## The famous Keplerian areas behave differently

Newton's Proposition I sectors are not the same area.

For a central orbit,

$$
dA_{\rm sector}
=
\frac12|\mathbf r\times\mathbf v|\,dt,
$$

so

$$
\frac{dA_{\rm sector}}{dt}
=
\frac{L}{2m}.
$$

As

$$
dt\rightarrow0,
$$

each sector satisfies

$$
dA_{\rm sector}\rightarrow0
$$

**linearly**, while

$$
\frac{dA_{\rm sector}}{dt}
$$

stays finite.

Again, Newton retains the finite physical information in a ratio of two vanishing quantities.

There is no elementary sector of nonzero area. Equal areas in equal times do not mean irreducible equal areas; the equal areas become arbitrarily small with the equal times.

This is why I think your inertial–parabola construction is actually more interesting than trying to identify a minimum Kepler sector. Newton's own area law provides no such minimum.

## His relativity corollaries make raw configuration-space area even less fundamental

Corollary V to the Laws gives Newtonian/Galilean relativity: internal motions are the same whether the containing space is at rest or moves uniformly in a straight line—the famous ship argument. [Wikisource](https://en.wikisource.org/wiki/The_Mathematical_Principles_of_Natural_Philosophy_%281846%29/Axioms%2C_or_Laws_of_Motion)

Under a horizontal boost

$$
v\mapsto v-u,
$$

your geometrical area transforms as

$$
A_{\rm inertial,fall}
=
\frac{Fv\tau^3}{6m}
\quad\longmapsto\quad
\frac{F(v-u)\tau^3}{6m}.
$$

With $u=v$, the plotted horizontal area vanishes entirely.

So the bare configuration-space area cannot be Newton's invariant physical quantity.

But your normalized combination survives:

$$
\frac{3F}{v}A
=
\frac{F^2\tau^3}{2m}.
$$

Indeed,

$$
\Delta E_\perp
=
\frac{(F\tau)^2}{2m},
$$

so

$$
\boxed{
\frac{3F}{v}A
=
\tau\Delta E_\perp.
}
$$

That is one reason the action-like combination is much more promising than the geometrical area by itself.

Corollary VI strengthens the point: if all bodies receive equal parallel acceleration, their relative motions are unchanged. Uniform acceleration by itself therefore cannot define an absolute spatial defect without specifying what is and is not accelerated. [Wikisource](https://en.wikisource.org/wiki/Page%3ANewton%27s_Principia_%281846%29.djvu/95)

## There is even a classical analogue of the phase-space squeeze

This is not stated by Newton, so I would label it a modern consequence of his equations, not a Newton quotation.

Consider a one-dimensional Newtonian trajectory and perform

$$
q\mapsto q_\lambda=\lambda q,
$$

$$
t\mapsto t_\lambda=\lambda^2t.
$$

Then

$$
v_\lambda
=
\frac{dq_\lambda}{dt_\lambda}
=
\frac{v}{\lambda},
$$

and therefore

$$
p_\lambda
=
\frac{p}{\lambda}.
$$

Thus

$$
\boxed{q_\lambda p_\lambda=qp.}
$$

This is exactly the anisotropic transformation

$$
(q,p)\mapsto(\lambda q,p/\lambda)
$$

which preserves phase-space area.

Moreover,

$$
p_\lambda\,dq_\lambda
=
\frac p\lambda\,\lambda\,dq
=
p\,dq.
$$

So classical action area is invariant.

For a constant-force problem,

$$
m\ddot q=F,
$$

the transformed trajectory obeys

$$
m\ddot q_\lambda
=
\frac{F}{\lambda^3}.
$$

Thus the family

$$
(q,p,t,F)
\mapsto
\left(
\lambda q,\frac p\lambda,\lambda^2t,\frac F{\lambda^3}
\right)
$$

is an exact scaling of the constant-force Newton problem, and the action is invariant:

$$
S
=
\int\left(\frac{p^2}{2m}+Fq\right)dt
$$

maps to itself.

The kinetic term gives

$$
\frac{p^2}{\lambda^2}\lambda^2dt=p^2dt,
$$

while

$$
\frac F{\lambda^3}(\lambda q)(\lambda^2dt)
=
Fq\,dt.
$$

So Newtonian mechanics has no preferred aspect ratio even at **fixed action** across this similarity family.

That is strikingly close to the modern squeezing issue.

It is not yet the same statement as squeezing one quantum state at fixed $F,m,\tau$. But structurally it tells us that Newton's mechanics contains an action-preserving anisotropic scaling and supplies no metric on the $q,p$ plane that would pick $\lambda=1$.

## Newton also permits squeezing by throwing harder

There is a second, very concrete version actually discussed in the *Principia*.

In Definition V Newton's projectile discussion says that increasing projectile velocity reduces its deviation from rectilinear motion and can increase its range at will, eventually giving orbital or escaping trajectories. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00080)

Hold a horizontal distance $X$ fixed. Since

$$
\tau=\frac Xv,
$$

the falling sagitta is

$$
y(X)
=
\frac{F X^2}{2mv^2},
$$

and the inertial–parabola area is

$$
A(X)
=
\frac{F X^3}{6mv^2}.
$$

Writing $p=mv$,

$$
\boxed{
A(X)
=
\frac{FmX^3}{6p^2}.
}
$$

Therefore

$$
p\to\infty
\quad\Longrightarrow\quad
A(X)\to0.
$$

So even without making the spatial baseline smaller, Newtonian dynamics lets one squeeze the departure from the inertial line by spending arbitrarily large momentum.

This is perhaps the closest classical antecedent to the quantum preparation issue:

$$
\text{small position-space signal}
\quad\leftrightarrow\quad
\text{large momentum resource}.
$$

Newton has no axiom limiting that exchange.

## Therefore the *Principia* is unusually hostile to a naïve minimum-area derivation

Putting the chain together gives

$$
\text{Law I}
\Rightarrow
\text{inertial tangent},
$$

$$
\text{Law II}
\Rightarrow
\delta p=O(dt),
$$

$$
\text{Galileo scholium/Lemma X}
\Rightarrow
\delta q_\perp=O(dt^2),
$$

$$
\text{Lemma XI}
\Rightarrow
\delta A=O(dt^3),
$$

$$
\text{Lemmas I--III}
\Rightarrow
\text{mesh}\to0
\text{ legitimately},
$$

$$
\text{Section I Scholium}
\Rightarrow
\text{no determinate least geometrical piece},
$$

$$
\text{Proposition I}
\Rightarrow
\text{impulse polygon}\to
\text{continuous force},
$$

$$
\text{Proposition VI}
\Rightarrow
F\sim
\frac{\text{vanishing sagitta}}
{(\text{vanishing time})^2}.
$$

This is not merely compatible with squeezing. **The differential content of Newtonian force is extracted by squeezing.**

And that clarifies the exact status of the modern phase-space problem. Newton does **not** give us

$$
\Delta q\,\Delta p\ge h .
$$

Classically he gives something even further away:

$$
q\ \text{and}\ p
$$

can in principle both be specified exactly. There is no nonzero phase-space cell at all. If we insert a fixed action cell $A_0$ by hand, Newtonian mechanics supplies no principle fixing its aspect ratio; its similarity structure naturally tolerates

$$
(q,p)\mapsto(\lambda q,p/\lambda).
$$

So the target cannot be “find the place in the *Principia* where Newton forgot to stop his refinement.” He did not forget. **Unlimited refinement is an explicit premise of his mathematical mechanics.**

The really sharp historical/mathematical tension is consequently this:

$$
\boxed{
\begin{array}{c}
\text{Newton: physical force survives as a finite ratio}\\
\text{of quantities diminished without limit}
\\[4pt]
\text{versus}\\[4pt]
\text{quantum mechanics: conjugate refinements cannot}\\
\text{both be made operationally sharp without introducing }\hbar .
\end{array}}
$$

That is much cleaner than trying to find a hidden Planck cell in Newton. The *Principia* supplies the **zero-limit side of the contradiction in exceptionally explicit form**. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00082)

---

## User

expres the dependence of each lemma until the squeezing

---

## ChatGPT

Yes. Put everything in terms of a single refinement parameter $h=\Delta t$, with finite $m,F$ and nonzero finite tangential velocity $v$. Then the logical chain through Book I §1 becomes very transparent.

The key is that Newton progressively establishes

$$
h
\;\Longrightarrow\;
\Delta p=O(h)
\;\Longrightarrow\;
\Delta v=O(h)
\;\Longrightarrow\;
\Delta q_\perp=O(h^2)
\;\Longrightarrow\;
A=O(h^3),
$$

while Lemmas I–VIII justify that all the geometrical replacements made along the way survive the $h\to0$ limit. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

### Dependency chain

Take a short trajectory interval of duration $h$. I would write Newton's Section I as the following DAG:

$$
\boxed{\mathrm{I}}
\longrightarrow
\boxed{\mathrm{II,III}}
\longrightarrow
\boxed{\mathrm{IV}}
$$

for integration/limiting areas, and

$$
\boxed{\mathrm{VI}}
\longrightarrow
\boxed{\mathrm{VII}}
\longrightarrow
\boxed{\mathrm{VIII}}
$$

for local straightening of curves. Then there are two branches:

$$
\boxed{\mathrm{V}+\mathrm{VI/VII}}
\longrightarrow
\boxed{\mathrm{IX}}
\longrightarrow
\boxed{\mathrm{X}}
$$

which derives the $h^2$ **dynamical displacement**, while

$$
\boxed{\mathrm{I}+\mathrm{VII}}
\longrightarrow
\boxed{\mathrm{XI}}
$$

derives the $h^2$ **geometrical sagitta** and $h^3$ **area**.

They meet in the Galileo/Newton cell.

---

## Lemma I: the limiting rule

Newton's Lemma I says that if two quantities approach one another more closely than any assigned difference, their ultimate ratio is equality. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Introduce

$$
h\to0.
$$

At this point there is no particular power of $h$. Lemma I supplies the logical operator

$$
X(h)-Y(h)\to0
\quad\Longrightarrow\quad
\frac{X(h)}{Y(h)}\to1
$$

when the relevant finite ratios exist.

So:

$$
\boxed{\mathrm{L1}: \qquad o(1)\ {\rm differences}\rightarrow
{\rm exact\ ultimate\ ratios}.}
$$

Every later replacement of arc by chord, curve by polygon, etc., ultimately rests on this rule.

---

## Lemmas II–III: mesh size can go to zero

For a partition whose maximum strip width is $h_x$, Lemma II proves the result for equal widths and Lemma III for unequal widths. The difference between inner and outer figures is bounded by a rectangle proportional to the largest width. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Schematically,

$$
0\le A_{\rm out}-A_{\rm in}
\le C h_x.
$$

Therefore

$$
h_x\to0
\quad\Longrightarrow\quad
A_{\rm out}-A_{\rm in}\to0.
$$

The crucial dependence is only

$$
\boxed{\mathrm{L2/3}: \quad
\delta A_{\rm integration}=O(h_x).}
$$

The exact trajectory may of course converge faster; this is Newton's generic bounding mechanism.

Lemma III is important because there need not even be a uniform partition. Only

$$
\max_j h_j\to0
$$

matters.

This is already the mathematical licence for unlimited local squeezing.

---

## Lemma IV: local ratios can be integrated

Suppose corresponding infinitesimal pieces satisfy

$$
\frac{\delta A_1}{\delta A_2}\to C.
$$

Lemma IV says the wholes inherit that ratio:

$$
\frac{A_1}{A_2}=C.
$$

[Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

In scaling notation:

$$
\delta A_1(h)
=
C\,\delta A_2(h)+o(\delta A_2)
$$

implies, after summation/refinement,

$$
A_1=C A_2.
$$

Thus L4 does not introduce a new power; it **propagates a local scaling law to the finite object**.

---

## Lemma V: ordinary similarity gives $A\sim\ell^2$

For similar figures Newton states

$$
A\propto \ell^2.
$$

[Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Hence under an isotropic geometrical shrink

$$
\ell\mapsto\lambda\ell,
$$

$$
\boxed{A\mapsto\lambda^2 A.}
$$

This is ordinary similarity. It is not yet the dynamically much more interesting $h^3$ scaling, because Newton's dynamical cell is **not similar to itself under time refinement**: its longitudinal and transverse dimensions shrink with different powers.

That distinction is central.

---

## Lemma VI: the curve becomes tangent

For a smooth curve,

$$
\theta_{\rm chord,tangent}\to0.
$$

[Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Newton doesn't yet need an explicit power law here. It means that if the arc length is $\ell$,

$$
\theta=o(1).
$$

With finite curvature one would write in modern notation

$$
\theta=\kappa\ell+O(\ell^2),
$$

but Newton's Lemma VI needs only

$$
\boxed{\theta\to0.}
$$

This permits local replacement of the curved trajectory by its inertial tangent.

---

## Lemma VII: arc, chord and tangent all have the same first-order scale

Lemma VII is where Newton establishes

$$
\text{arc}\sim\text{chord}\sim\text{tangent}.
$$

[Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

For finite tangential velocity $v$,

$$
\ell_{\rm arc}=vh+O(h^2).
$$

Consequently,

$$
AD\sim AB\sim {\rm arc}\sim vh.
$$

Thus:

$$
\boxed{\mathrm{L7}:\qquad
\ell=O(h).}
$$

This supplies the **first coordinate** of the squeezed Newton cell.

Call it

$$
X(h)\sim vh.
$$

---

## Lemma VIII: all the small tangent/chord triangles are asymptotically interchangeable

Newton next proves that the triangles built using arc, chord and tangent become similar and equal in ultimate ratio. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Therefore, once we know one area's scaling, it can be transferred to the geometrically neighbouring versions.

Again, no new exponent:

$$
\boxed{\mathrm{L8}: \quad
A_1/A_2\to1.}
$$

This matters because Newton can calculate using a tangent triangle and then transfer the result to a curved segment.

---

# First branch: Lemma IX $\to$ Lemma X

Now Newton introduces what is essentially a velocity–time diagram.

## Lemma IX: areas generated by a regular graph scale quadratically

For curves meeting the axis at a given angle, Newton proves that the corresponding small areas are ultimately in the duplicate ratio of their sides. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Thus

$$
A(h)\propto h^2.
$$

In the application to dynamics, horizontal coordinate is time and vertical coordinate is the **velocity generated by the force**.

For finite acceleration

$$
a=\frac Fm,
$$

we have locally

$$
\delta v(h)=ah+o(h).
$$

The area beneath that velocity curve is displacement:

$$
\delta q_F(h)
=
\int_0^h\delta v(t)\,dt.
$$

Therefore,

$$
\delta q_F=O(h^2).
$$

Newton's Lemma IX supplies precisely the geometrical step which makes Lemma X possible.

---

## Lemma X: force produces displacement of second order in time

Newton states explicitly:

$$
\boxed{
\delta q_F\propto Fh^2.
}
$$

[Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

For constant force this is exactly

$$
\boxed{
Y(h)=\frac{F}{2m}h^2.
}
$$

And from Law II,

$$
\boxed{
\Delta p(h)=Fh.
}
$$

So already we have three different refinement weights:

$$
h\mapsto\lambda h
$$

gives

$$
\Delta p\mapsto\lambda\Delta p,
$$

$$
X\mapsto\lambda X,
$$

but

$$
Y\mapsto\lambda^2Y.
$$

That is the first genuine squeeze:

$$
\boxed{
(X,Y)\mapsto(\lambda X,\lambda^2Y).
}
$$

The little dynamical cell becomes progressively flatter.

Its aspect ratio behaves as

$$
\frac{Y}{X}
=
\frac{Fh}{2mv}
=O(h),
$$

so

$$
\boxed{\frac{Y}{X}\to0.}
$$

---

# Second branch: Lemma XI

Lemma XI independently encodes the same anisotropic scaling geometrically.

It says that the evanescent subtense of the angle of contact—the sagitta—is in the duplicate ratio of the adjacent arc/chord/tangent. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

From Lemma VII,

$$
AD=O(h).
$$

Lemma XI therefore gives

$$
BD=O(AD^2)=O(h^2).
$$

So

$$
\boxed{
AD\sim vh,\qquad
BD\sim Ch^2.
}
$$

For the constant-force parabola,

$$
C=\frac{F}{2m}.
$$

Thus Lemma XI geometrically reproduces Lemma X:

$$
BD=\frac{F}{2m}h^2.
$$

The dynamical and geometrical branches close.

---

# Lemma XI Corollary 4: the area becomes cubic

Now multiply the two squeezed dimensions.

The tangent triangle has

$$
A_\triangle
=
\frac12 AD\,BD.
$$

Using

$$
AD=O(h),
\qquad
BD=O(h^2),
$$

one obtains

$$
\boxed{
A_\triangle=O(h^3).
}
$$

This is exactly Newton's Corollary 4: the evanescent tangent triangles are in the **triplicate ratio** of their tangent sides. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Explicitly,

$$
A_\triangle
=
\frac12(vh)
\left(\frac{Fh^2}{2m}\right)
=
\boxed{\frac{Fv}{4m}h^3}.
$$

Therefore under refinement

$$
h\mapsto\lambda h,
$$

$$
\boxed{
A_\triangle\mapsto\lambda^3 A_\triangle.
}
$$

This is the crucial exponent.

---

## Lemma XI Corollary 5: the curved area inherits exactly the same $h^3$

For the parabola Newton obtains the fixed $2/3$ relation between the curvilinear tangent area and tangent triangle. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

Thus

$$
A_{\rm inertial,fall}
=
\frac23 A_\triangle
=
\boxed{\frac{Fv}{6m}h^3}.
$$

The chord–curve lens is the remaining third:

$$
A_{\rm lens}
=
\frac13 A_\triangle
=
\boxed{\frac{Fv}{12m}h^3}.
$$
All three areas therefore carry weight $3$.

---

# Put all the Newtonian weights together

Define the refinement transformation

$$
R_\lambda:h\mapsto\lambda h,
\qquad 0<\lambda<1.
$$

At fixed $m,F,v$, Newton's construction gives

$$
\begin{array}{c|c|c}
\text{quantity}&\text{formula}&R_\lambda\\
\hline
h & h & \lambda\\
X & vh & \lambda\\
\Delta p & Fh & \lambda\\
\Delta v & (F/m)h & \lambda\\
Y & Fh^2/(2m)&\lambda^2\\
\text{sagitta}&Fh^2/(2m)&\lambda^2\\
A_\triangle&Fvh^3/(4m)&\lambda^3\\
A_{\rm curve}&Fvh^3/(6m)&\lambda^3\\
A_{\rm lens}&Fvh^3/(12m)&\lambda^3\\
\Delta E_\perp&(Fh)^2/(2m)&\lambda^2\\
h\,\Delta E_\perp&F^2h^3/(2m)&\lambda^3
\end{array}
$$

and therefore

$$
\boxed{
\frac{3F}{v}A_{\rm curve}
=
h\,\Delta E_\perp
=
\frac{F^2h^3}{2m}.
}
$$

So your action quantity carries precisely the same Newtonian scaling weight $3$ as the evanescent geometrical area.

---

# Then the polygonal refinement

For a fixed macroscopic duration $T$, put

$$
h=\frac{T}{N}.
$$

Each cell satisfies

$$
\Delta p_{\rm cell}\sim N^{-1},
$$

$$
Y_{\rm cell}\sim N^{-2},
$$

$$
A_{\rm cell}\sim N^{-3}.
$$

There are $N$ cells. Hence

$$
\sum_j\Delta p_j
\sim
N\times N^{-1}
=
O(1),
$$

while

$$
\sum_jA_j
\sim
N\times N^{-3}
=
\boxed{O(N^{-2})\to0}.
$$

This is the essential Newtonian asymmetry:

$$
\boxed{
\text{finite total impulse survives refinement,}
\qquad
\text{local geometrical/action defect disappears.}
}
$$

The continuous force survives:

$$
N\Delta p_{\rm cell}\sim FT,
$$

while the cumulative departure between the smooth curve and its tangent polygon vanishes:

$$
A_{\rm polygon\ error}\sim \frac1{N^2}.
$$

---

# Where the actual squeeze appears

So there are really **three consecutive squeezes** in Newton.

First, trajectory geometry:

$$
\boxed{
(X,Y)
\mapsto
(\lambda X,\lambda^2Y).
}
$$

Second, impulse versus deviation:

$$
\boxed{
(\Delta p,Y)
\mapsto
(\lambda\Delta p,\lambda^2Y).
}
$$

Third, the area/action defect:

$$
\boxed{
A,\ h\Delta E
\mapsto
\lambda^3(A,\ h\Delta E).
}
$$

Nothing in Lemmas I–XI arrests any of these.

Indeed their logical function is almost exactly the opposite:

$$
\boxed{
\text{I--VIII justify taking the squeeze;}
\quad
\text{IX--X derive its }h^2\text{ dynamics;}
\quad
\text{XI derives its }h^3\text{ area.}
}
$$

And this gives a particularly concise expression of the problem we were circling around:

$$
\boxed{
\underbrace{h}_{1}
\;\xrightarrow{\text{Law II}}\;
\underbrace{\Delta p}_{1},
\qquad
\underbrace{h}_{1}
\;\xrightarrow{\text{L IX--X}}\;
\underbrace{\Delta q_\perp}_{2},
\qquad
\underbrace{h}_{1}
\;\xrightarrow{\text{L VII+XI}}\;
\underbrace{\Delta q_\parallel\Delta q_\perp}_{3}.
}
$$

The subscripts are the Newtonian refinement weights.

So if we want to locate exactly where a Planck-scale modification would have to enter, it has to break this homogeneous grading somewhere:

$$
1\to1,\qquad1\to2,\qquad1+2\to3.
$$

That is much more precise than saying vaguely that Newton assumes continuity. [Matemáticas TCD](https://www.maths.tcd.ie/pub/HistMath/People/Newton/Principia/Bk1Sect1/PrBk1St1.pdf)

---

## User

search online for lean formalisation of this sequence

---

## ChatGPT

I searched fairly broadly. I do **not** find an existing Lean formalization of Newton, Book I §1, Lemmas I–XI *as Newton's sequence*. But a surprisingly large fraction of the chain already exists, and one old Lean project formalizes almost exactly the dynamical Lemma-X branch.

The closest actual predecessor is the ATOMS Lab `LeanChemicalTheories` project. Their paper explicitly says they formalize “equations of motion underlying Newtonian mechanics,” and the Lean-community discussion describes it more specifically as deriving the kinematic equations from the 1D equations of motion for constant acceleration. [arXiv](https://arxiv.org/abs/2210.12150) The relevant source file is `src/physics/kinematic_equations.lean`; it is unfortunately **Lean 3**, not Lean 4. [kinematic_equations.lean](https://github.com/ATOMSLab/LeanChemicalTheories/blob/main/src/physics/kinematic_equations.lean)

It contains, essentially verbatim, the part we need:

```lean
theorem const_accel ...
:
𝕧 = λ t, t • 𝔸 + 𝕧 0
```

followed by

```lean
theorem const_accel' ...
:
𝕩 = λ t, ((t^2/2) • 𝔸) + t • (𝕧 0) + 𝕩 0
```

and the scalar versions

```lean
velocity_eq_const_accel_mul_time
```

and

```lean
pos_eq_const_accel_mul_time_sqr_add_velocity_mul_time
```

So, in our notation,

$$
a=\mathrm{const}
\Longrightarrow
v(t)=v_0+at
\Longrightarrow
x(t)=x_0+v_0t+\frac12at^2
$$

is already machine-checked. That is essentially

$$
\boxed{\mathrm{Law\ II}\rightarrow\mathrm{Lemma\ IX/X}}
$$

in modern analytic form.

What is much better today is that **current Mathlib already has the mathematical machinery for almost all the rest**.

| Newton step | Lean status now | Natural Lean object |
|---|---|---|
| Lemma I: ultimate equality / limit | already generic | `Filter.Tendsto`, `IsLittleO`, `IsBigO` |
| Lemmas II–III: partitions refine and area sums converge | already generic | `BoxIntegral`, tagged partitions, integral-sum convergence |
| IV: pass a local limiting ratio to accumulated quantities | generic analysis | limits + integrals |
| VI–VIII: curve becomes tangent; chord/tangent first-order equivalent | essentially built into differentiability | `HasFDerivAt`, little-$o$ definition |
| IX–X: acceleration integrates to $h^2$ displacement | **already formalized explicitly**, old Lean 3 | ATOMS `kinematic_equations.lean` |
| XI: sagitta $=O(h^2)$ | readily expressible with current Taylor API | `taylor_isLittleO` |
| XI cor. area $=O(h^3)$ | not Newton-named, but immediate composition | asymptotic multiplication or exact integral |
| polygon error $N\times N^{-3}=N^{-2}$ | no Newton-specific theorem found | finite sums + algebra / BoxIntegral |

Mathlib's current Taylor theorem is particularly close to what we called the Newtonian squeeze. It has a theorem

```lean
taylor_isLittleO
```

for vector-valued functions $f:\mathbb R\to E$, proving that the Taylor remainder is little-$o$ of the appropriate power. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Taylor.html) In particular, for a $C^2$ trajectory $q$,

$$
q(h)
=
q(0)+h q'(0)+\frac{h^2}{2}q''(0)+o(h^2).
$$

Thus after subtracting the inertial tangent,

$$
q(h)-q(0)-hq'(0)
=
\frac12q''(0)h^2+o(h^2),
$$

which is almost exactly a modern Lean statement of **Lemma XI's quadratic sagitta**. Mathlib also provides `taylor_tendsto` and explicit remainder bounds. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Taylor.html)

For Newton's Lemmas VI–VIII, you probably would not formalize Newton's separate geometrical lemmas literally unless the historical reconstruction itself is the purpose. In Mathlib, the Fréchet derivative is *defined* by

$$
f(x+h)-f(x)-Df_x(h)=o(h),
$$

so “the curve tends to its tangent” is already encoded directly in `HasFDerivAt`. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Defs.html) Thus

$$
X(h)=vh+o(h)
$$

comes nearly for free.

The area/integration side is also considerably developed. Mathlib has tagged partitions and integral sums over boxes, including convergence of integral sums under refinement. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/BoxIntegral/Basic) For our one-dimensional parabola we do not even need this machinery: the cubic law can be proved exactly from

$$
A(h)=v\int_0^h \frac{F}{2m}t^2\,dt
=\frac{Fv}{6m}h^3,
$$

using the ordinary interval integral and FTC. Mathlib has a mature Fundamental Theorem of Calculus API. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html)

There is also now a serious Lean-4 physics library, **Physlib**. It contains a proper classical-mechanics layer: its harmonic-oscillator development defines the equation of motion and proves its equivalence to Newton's second law, Hamilton's equations and the variational formulation. [GitHub](https://github.com/leanprover-community/physlib/blob/master/Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean) So a new formalization should probably sit on Physlib rather than port the entire old ATOMS infrastructure.

What I did **not** find is more interesting: I find no Lean source corresponding to

> Newton Book I, Section I, Lemma I → … → Lemma XI → cubic evanescent area,

nor a formalized Proposition I polygon-to-continuous-force argument, nor the explicit dependency graph

$$
h
\to \Delta p=O(h)
\to \Delta q_\perp=O(h^2)
\to A=O(h^3).
$$

Searches for Newton's *Principia*, sagitta, Proposition I, Kepler area law, etc. turn up historical analyses, not Lean developments. The obvious GitHub project named `principia` is a red herring: it formalizes **Whitehead and Russell's Principia Mathematica**, not Newton. [GitHub](https://github.com/ndrwnaguib/principia)

So the useful conclusion is that this would **not** be a large formalization from scratch. The missing file is mostly connective tissue.

I would structure it roughly as

```text
NewtonPrincipia/
Limits.lean -- I–IV
Tangent.lean -- VI–VIII
ConstantForce.lean -- IX–X
Sagitta.lean -- XI
Squeeze.lean -- weights 1,1,2,3
Polygon.lean -- N^-3 per cell -> N^-2 total
```

with the main machine-checked theorem eventually being something like

$$
\boxed{
q(h)-q(0)-h\,q'(0)
=
\frac12a\,h^2
}
$$

for constant acceleration, and

$$
\boxed{
A(h)=
v\int_0^h\bigl(q_y(t)-q_y(0)-tq_y'(0)\bigr)\,dt
=
\frac{va}{6}h^3 ,
}
$$

followed by the refinement result

$$
\boxed{
N\,A(T/N)
=
\frac{vaT^3}{6N^2}\longrightarrow0 .
}
$$

That last three-line chain would be the exact Lean certificate of the Newtonian squeezing we have been discussing. The hard analytic infrastructure is already there; even the constant-acceleration integration was formalized once before.

---

## User

I suspect the lemmas depend on previous axioms in the introduction do they?

---

## ChatGPT

Yes. My previous dependency graph started too late. **Section I is not uniformly independent of the Definitions and Axioms/Laws that precede Book I.** Newton deliberately places the order

$$
\text{Definitions}\to\text{Axioms/Laws}\to
\text{Book I, §1 Lemmas}\to\text{§2 dynamics}.
$$

But there are two strands: Lemmas I–IX and most of XI are geometrical; **Lemma X is already mechanics**, and its physical content imports the introductory definitions/laws even though Newton does not re-cite them line by line. Then Proposition I explicitly splices the two strands together. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00084)

The dependency structure I would now use is this.

$$
\boxed{\text{Definitions}}
\qquad
\boxed{\text{Laws I,II + Cor. I}}
$$

feed into

$$
\boxed{\text{Lemma X}}
$$

while independently

$$
\boxed{L1\to L2,L3,\ldots,L9,L11}
$$

constructs the limiting geometry. They first become a single machine in **Proposition I**.

### The introductory assumptions that actually matter

**Definition II** defines quantity of motion as mass times velocity,

$$
p=mv.
$$

**Definition IV** defines impressed force as the action which changes rest or uniform rectilinear motion. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00085)

More importantly, Definitions VII and VIII already contain a differential-looking relationship between force and generated motion. Newton defines accelerative force by the **velocity it generates in a given time**, and motive force by the **quantity of motion it generates in a given time**. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00085)

Schematically,

$$
a \sim \frac{\Delta v}{\Delta t},
\qquad
F_{\rm motive}\sim\frac{\Delta p}{\Delta t}.
$$

Then Law I supplies the unforced tangent:

$$
F=0\quad\Rightarrow\quad q(t)=q_0+vt.
$$

Law II supplies

$$
\Delta p\propto \text{impressed force}.
$$

And Corollary I gives vector composition of impressed motions. Newton explicitly derives the parallelogram result from Laws I and II. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00086)

So the mechanical foundation before Section I is already essentially

$$
\boxed{
p=mv,\qquad
F\propto\frac{\Delta p}{\Delta t},\qquad
F=0\Rightarrow\dot q=\mathrm{const},
\qquad
\Delta\mathbf p\text{ adds vectorially}.
}
$$

### Then Lemmas I–IX are mostly the mathematical engine

Lemmas I–IV establish limiting equality and passage from ever finer pieces to whole areas. Lemmas VI–VIII establish the local tangent/chord equivalences. Lemma IX gives the quadratic scaling of the area beneath a regular curve meeting its axis at a finite angle. None of these needs Newton's physical Laws as part of its proof. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

So one branch is genuinely autonomous:

$$
\boxed{
L1
\to
L2,L3
\to
L4
}
$$

and

$$
\boxed{
L6\to L7\to L8,
\qquad
L5+L6\to L9.
}
$$

That branch establishes what we might call the **limit calculus**.

### Lemma X is where the earlier physics enters

Newton's statement is explicitly physical:

> spaces which a body describes when urged by any finite force ... are, at the very beginning of motion, in the duplicate ratio of the times.

His proof represents time by $AD,AE$, **generated velocities** by ordinates $DB,EC$, and displacement by the areas under that velocity curve; then Lemma IX gives the $t^2$ law. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

The purely geometrical part is

$$
v_{\rm generated}(t)=O(t)
\quad\Longrightarrow\quad
\int_0^t v_{\rm generated}(s)\,ds=O(t^2).
$$

But why is a finite force represented by a velocity curve having a finite nonzero first-order slope? That is not supplied by Lemma IX. It comes from the pre-Book-I concept of force: especially Definition VII/VIII and Law II.

So a more faithful formal dependency is

$$
\boxed{
\text{Def. II}
+\text{Def. IV}
+\text{Def. VII/VIII}
+\text{Law II}
}
$$

giving

$$
\Delta v=O(h),
$$

then

$$
\boxed{L9}
$$

giving

$$
\Delta q=O(h^2).
$$

Thus:

$$
\boxed{
\text{Definitions + Law II + L9}
\Longrightarrow L10.
}
$$

And Newton himself confirms that this is how he views it. In the Scholium to the Laws, **before Book I**, he says that from the first two Laws and their first two corollaries Galileo's result follows: uniform gravity generates equal velocities in equal particles of time, hence total velocity is proportional to time and distance goes as the square of time. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00086)

That passage is extremely valuable because it tells us Newton's own dependency graph:

$$
\text{Laws I,II}
\longrightarrow
v\sim t
\longrightarrow
s\sim t^2.
$$

Lemma X subsequently packages that result into his limit calculus.

### Lemma XI is mostly geometry again

Lemma XI proves

$$
\text{sagitta}\sim(\text{arc})^2
$$

for finite nonzero curvature using geometry plus **Lemma I** explicitly. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

Its internal dependency is roughly

$$
L1 + \text{circle geometry}
\longrightarrow L11.
$$

But its **Corollary 3** says

$$
\text{sagitta}\sim t^2
$$

for an arc traversed at a given velocity. That imports kinematics:

$$
\text{arc}\sim vt.
$$

So even XI develops a physical branch at the corollary level.

Then Corollary 4 gives

$$
A_{\triangle}
\sim
(\text{tangent})(\text{sagitta})
\sim h\,h^2=h^3,
$$

and Corollary 5 transfers this to the parabolic curved area. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

### Proposition I is the decisive merge

Here Newton stops leaving the dependencies implicit.

He divides time into equal parts. In the first interval the body moves in a straight line by its **vis insita**. In the next interval, absent force, it would continue along the same line **“per leg. I.”** A centripetal impulse changes it, and the resultant displacement is found **“per legum corol. 1.”** [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

Then—and this is the other half of the construction—he increases the number of triangles and decreases their width indefinitely, invoking **Corollary 4 of Lemma III** to turn the polygon into the curve. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

So Proposition I has the beautiful explicit dependency

$$
\boxed{
\underbrace{\text{Law I + Law II/Cor. I}}_{\text{mechanics of each polygonal step}}
+
\underbrace{\text{Lemma III}}_{\text{continuum limit}}
\Longrightarrow
\text{continuous central-force trajectory}.
}
$$

This is probably the graph we should formalize.

And its force corollaries add Law II explicitly again: Newton says the small diagonals are generated by the centripetal impulses and therefore are proportional to those impulses. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

### So the complete route to squeezing is actually

I would rewrite our diagram as

$$
\begin{array}{ccccc}
\text{Def. II} && \text{Def. IV,VII,VIII}\\
p=mv && F\leftrightarrow\text{generated }\Delta p,\Delta v\\
&\searrow&\downarrow&\swarrow\\
&&\text{Law II}\\
&&\Delta p=O(h),\quad \Delta v=O(h)\\
&&\downarrow\\
&&L9\\
&&\Delta q_\perp=O(h^2)
\end{array}
$$

while independently

$$
\boxed{
L1\to L2,L3
}
$$

licenses unlimited partition refinement, and

$$
\boxed{
L6\to L7,\qquad L1\to L11
}
$$

gives

$$
\Delta q_\parallel=O(h),
\qquad
\Delta q_\perp=O(h^2).
$$

Those two branches then meet:

$$
\boxed{
A_{\rm cell}
\sim
\Delta q_\parallel\Delta q_\perp
=
O(h^3).
}
$$

And Proposition I says the mechanical polygon itself may be subjected to precisely that unlimited geometrical refinement:

$$
h=\frac TN\to0.
$$

So yes: **a proper Lean formalization ought not begin at Lemma I.** It should begin with a small formalization of Newton's Definitions and Laws—or at least the mathematical content extracted from them—and then prove which lemmas are purely geometric and which depend on that mechanical interface.

In fact the clean formal architecture is probably:

```text
Newton/
Definitions.lean
mass
momentum = mass * velocity
impressedForce
accelerativeForce
motiveForce

Laws.lean
lawI
lawII
parallelogramCorollary

FirstLastRatios.lean
lemmaI ... lemmaIX

GeneratedMotion.lean
lemmaX -- depends on Laws + lemmaIX

Contact.lean
lemmaXI -- geometric
lemmaXI_cor3 -- adds kinematics
cubicArea

PropositionI.lean
-- depends simultaneously on Laws and Lemma III
```

And there is a particularly interesting fact for your programme: **the unlimited squeeze itself does not follow from one Newtonian axiom.** It is produced by the conjunction

$$
\boxed{
\text{linear law of generated motion}
\quad+\quad
\text{unbounded geometric refinement}.
}
$$

The first comes from the introductory physics; the second comes from Section I's limit doctrine. Proposition I is exactly where Newton joins them. That junction looks like the correct place to inspect if we are looking for what has to change when an action scale $h$ is introduced.

---

## User

gregory got some notes on the changes that newton was planning for the second edition, including a new classical scholia. Review what new content was going to go into all this sequence, from Definitions to propositions. Search deeptly to get the exact content from newton sources as transcribed online.

---

## User

hmm continue, And of course I am interesten on the reordering if it affects our props and lemmas

---

## ChatGPT

Yes. The reordering matters substantially for our chain, but there are **three different textual strata** that need to be kept separate: 1687; Newton's much more radical early-1690s reconstruction described by Gregory in 1694; and the conservative compromise actually printed in 1713. Once separated, something rather striking emerges: Newton's revisions increasingly promote the chain

$$
\text{generated motion}
\;\to\;
s\sim t^2
\;\to\;
\text{sagitta}
\;\to\;
F\sim\frac{s}{t^2}
$$

from background machinery into an explicit organizing principle.

Gregory's July 1694 memorandum says that near the beginning Newton had made many corrections, added corollaries, **changed the order of the propositions, and omitted some propositions altogether**. Gregory summarizes the new architecture by saying that focal-conic force was now derived from central-conic force, which in turn was derived from constant force toward the centre of a circle; the old Props. VII–XIII were reduced essentially to corollaries. [dokumen.pub](https://dokumen.pub/the-key-to-newtons-dynamics-the-kepler-problem-and-the-principia-9780520916852.html)

The important qualification is that this radical reordering principally attacks **Book I §§II–III**, not the basic sequence of Lemmas I–XI in §I. Whiteside reports that Newton did intend to remove §§IV–V as independent geometric sections, move **three of their lemmas into §I**, and put the remainder into a separate *Liber geometriae*. I have not yet found an online primary transcription that identifies those three unambiguously, so I would not guess their numbers. [Sage Journals](https://journals.sagepub.com/doi/10.1177/002182867000100203)

Here is the part relevant to us.

| Node | 1687 | Radical scheme c.1690–94 | Published 1713/1726 | Effect on our chain |
|---|---|---|---|---|
| Definitions/Laws | $p=mv$; generated motion; Laws I–III | no evidence of their removal; they remain the mechanics under the new propositions | wording revised in several definitions and Law III; Laws I–II remain structurally intact | foundation survives |
| Lemmas I–IX | limit/tangent/area machinery | apparently retained as basic §I machinery; §I was actually to **gain** geometry from old §§IV–V | retained, with revisions especially I and VI–IX | squeeze machinery survives |
| Lemma X | $s\sim t^2$ for a regular force; only 2 corollaries | still required by the new dynamics | substantially strengthened | becomes explicit $F\sim s/t^2$ machinery |
| Lemma XI | contact subtense $\sim$ arc$^2$; cubic areas already present | curvature becomes much more central | strengthened and explicitly connected to time | becomes second route to $F\sim s/t^2$ |
| Prop. I | polygon → area law | statement retained, **six new corollaries added** | this version essentially published | links impulse polygon to local deflection much more explicitly |
| old Prop. VI | basic linear dynamics ratio | **displaced**; its result moves into new Prop. IX | rebuilt as a powerful general theorem | directly states $F\propto\text{sagitta}/t^2$ |
| old Props. VII–XIII | separate conic problems | mostly collapse into corollaries of new general results | original numbering restored, but new methods inserted as alternate proofs/corollaries | case-by-case geometry becomes consequence of general local theorem |
| old Lemma XII | constant circumscribed parallelogram of conic | replaced by a **curvature lemma** | old Lemma XII restored | unpublished scheme much more curvature-centric |

The crucial thing is what happens to **our Lemma X**. In 1687 Newton says simply

$$
s\propto t^2
$$

at the beginning of motion under a regular force, and has only the two corollaries saying that errors produced by equal/proportional forces scale like $t^2$. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

By 1713/1726 he has made the statement more general—“any finite force,” whether fixed or continuously changing—and adds three more corollaries. In modern notation they say essentially

$$
s\propto Ft^2,
$$

therefore

$$
\boxed{F\propto\frac{s}{t^2}},
$$

and conversely

$$
t^2\propto\frac{s}{F}.
$$

That is not our reconstruction; it is Newton's explicit published Corollaries 3–5 to Lemma X. The Newton Project transcription has:

$$
\text{Cor. 3:}\quad s\sim F t^2,
$$

$$
\text{Cor. 4:}\quad F\sim s/t^2,
$$

$$
\text{Cor. 5:}\quad t^2\sim s/F.
$$

[Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

So the second-edition work turns Lemma X into almost exactly the dimensional/dynamical core we have been extracting.

And **Lemma XI changes in precisely the complementary direction**. In 1687 Newton already has

$$
BD\sim AB^2
$$

and therefore the tangent triangle and curvilinear segment go as the **cube** of the tangent/chord/arc. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

But in the revised version he inserts between those results two new corollaries, notably

$$
\boxed{\text{sagitta}\sim t^2}
$$

when the arc is traversed at a given velocity. He then explicitly numbers the cubic result as Corollary 4:

$$
A_{\triangle}\sim \ell^3,
$$

and the parabolic curved regions as Corollary 5:

$$
A_{\rm curve}\sim \ell^3.
$$

[Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

So the revised §I makes our grading nearly explicit:

$$
t^1
\quad\longrightarrow\quad
s^2
\quad\longrightarrow\quad
A^3 .
$$

More exactly,

$$
\ell\sim t,\qquad
s\sim t^2,\qquad
A\sim t^3.
$$

### The truly important reordering: old Proposition VI becomes new Proposition IX

This is where Gregory's memorandum matters most.

In 1687, Proposition VI is where Newton introduces the basic local-force expression using the deviation $QR$ from the tangent:

$$
F\propto
\frac{QR}{QT^2\,SP^2}
$$

in the appropriate reciprocal form. The following propositions then apply that apparatus one orbit at a time.

In the radical revision Newton moves this material **down to proposed Proposition IX**. But he enlarges it radically: alongside the old “linear dynamics ratio” he puts a second, curvature-based measure,

$$
\boxed{
F\propto\frac{1}{SY^2\,PV}
}
$$

where $SY$ is the perpendicular from the force centre to the tangent and $PV$ is the chord through the force centre of the **circle of curvature** at $P$. [dokumen.pub](https://dokumen.pub/the-key-to-newtons-dynamics-the-kepler-problem-and-the-principia-9780520916852.html)

This is conceptually important for us. Newton is replacing

$$
\text{finite conic construction}
$$

by

$$
\text{local second-order geometry}
\longrightarrow
\text{force}.
$$

Then he inserts a completely new Lemma XII giving the necessary relation between a conic and its **circle of curvature**. The printed Lemma XII about equal circumscribed parallelograms is temporarily thrown out. [dokumen.pub](https://dokumen.pub/the-key-to-newtons-dynamics-the-kepler-problem-and-the-principia-9780520916852.html)

So in the radical version the succession would have looked roughly like

$$
\boxed{
L.X:\ s_{\rm force}\sim Ft^2
}
$$

and

$$
\boxed{
L.XI:\ s_{\rm geom}\sim \ell^2
}
$$

feeding eventually into

$$
\boxed{
P.IX:\ F\sim s/t^2
\quad\text{and}\quad
F\sim 1/(SY^2PV)
}.
$$

That is much closer to our desired dependency graph than the printed 1687 book.

### And new Proposition X collapses the conic calculations

After the new curvature Lemma XII, proposed Proposition X simply asks for the centripetal force for a body moving on a conic when the force tends toward **any given point $S$**. Newton combines the curvature result and the new force theorem, and what previously required several separate propositions becomes a set of short corollaries. [dokumen.pub](https://dokumen.pub/the-key-to-newtons-dynamics-the-kepler-problem-and-the-principia-9780520916852.html)

Hence the old sequence

$$
P.VII,\ P.VIII,\ P.X,\ P.XI,\ P.XII,\ P.XIII
$$

mostly becomes

$$
\boxed{P.X+\text{corollaries}}.
$$

This is exactly what Gregory means by the proofs of old VII–XIII following “like corollaries.” [CDL Pub](https://pub-ucpec2-prd.cdlib.org/ucpressebooks/view?anchor.id=bkd0e19195&brand=eschol&chunk.id=d0e19174&doc.view=content&docId=ft4489n8zn&toc.depth=1)

There is also another new route, proposed Props. VI–VIII. Those are comparison/similarity theorems rather than our sagitta route:

$$
P.VI:\quad\text{similar trajectories},
$$

$$
P.VII:\quad\text{affine/proportional transformation of trajectories},
$$

$$
P.VIII:\quad
\frac{F_S}{F_R}
=
\frac{SP\,PR^2}{PT^3}.
$$

This lets Newton derive the focal inverse-square law from the central ellipse almost trivially. [dokumen.pub](https://dokumen.pub/the-key-to-newtons-dynamics-the-kepler-problem-and-the-principia-9780520916852.html)

Thus the radical edition would actually have contained **three independent local ways to get force**:

$$
\text{linear deflection ratio},
\qquad
\text{circle-of-curvature ratio},
\qquad
\text{comparison theorem}.
$$

That is a much more systematic mechanics than 1687.

### Proposition I is also strengthened in exactly our direction

The radical plan kept Proposition I—the equal-area polygon argument—in place, but added six corollaries. That change survived into 1713. [dokumen.pub](https://dokumen.pub/the-key-to-newtons-dynamics-the-kepler-problem-and-the-principia-9780520916852.html)

These are much more important than they first appear. In the revised printed text Newton now explicitly extracts from his impulse polygon the **local deviation produced by the force**. For example, Corollary 3 states that forces at two places are in the ultimate ratio of the diagonals $BU,EZ$ generated by the respective impulses as the arcs diminish indefinitely; Corollary 4 identifies these with the sagittae of equal-time arcs. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

So there is now a direct bridge

$$
\boxed{\text{Law II impulse}}
\longrightarrow
\boxed{\text{polygon diagonal}}
\longrightarrow
\boxed{\text{sagitta}}
\longrightarrow
\boxed{\text{force}}.
$$

That bridge is much less explicit in 1687.

And then comes the most interesting fact of all: the **published** revised Proposition VI of 1713/1726 is essentially the clean theorem we would have wanted Newton to state.

Newton writes that if a body describes an arbitrarily nascent arc in a minimum time and the sagitta through the force centre bisects its chord, then the centripetal force at the midpoint is

$$
\boxed{
F\propto\frac{\text{sagitta}}{t^2}.
}
$$

He proves it using Proposition I plus Lemma XI, and then remarks that it follows easily also from **Corollary 4 of Lemma X**. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00087)

That gives us two independent dependency paths:

$$
\text{L.X}
\longrightarrow
\boxed{F\sim s/t^2},
$$

and

$$
\text{L.XI}
+
\text{P.I}
\longrightarrow
\boxed{F\sim s/t^2}.
$$

This is exceptionally useful for formalization because it is a built-in consistency diamond:

$$
\begin{array}{ccc}
& F &\\[2mm]
\swarrow && \searrow\\
\text{generated-motion route} &&
\text{geometrical-sagitta route}\\
L.X && L.XI+P.I\\
\searrow && \swarrow\\
& F\sim s/t^2 &
\end{array}
$$

The revised Newton himself therefore cross-checks the result by two routes.

### And this directly touches the squeeze

Put $h=\Delta t$. The revised chain is now almost literally:

$$
\text{Law II}:
\qquad
\Delta p\sim Fh ,
$$

$$
L.X:
\qquad
s\sim Fh^2 ,
$$

$$
L.XI:
\qquad
s\sim \ell^2,\qquad \ell\sim vh ,
$$

$$
L.XI,\ \mathrm{Cor}.4:
\qquad
A\sim \ell s\sim h^3,
$$

while

$$
P.I:
\qquad
\text{polygon impulse}\to\text{continuous central force}
$$

under unlimited refinement.

And revised Proposition VI closes the loop:

$$
\boxed{
F\sim\frac{s}{h^2}.
}
$$

This means that in the revised architecture the squeeze is no longer merely an implication that we infer by combining Newtonian passages. Newton has organized the beginning of Book I so that **the same vanishing sagitta is explicitly the measure of finite force after division by the square of the vanishing time**.

That is almost exactly the issue we are investigating.

### One further complication: Newton considered an even more radical beginning

There is another surviving revision draft, not necessarily identical with the precise July-1694 *Immutanda* scheme Gregory summarized, in which Newton considers replacing the beginning of §II altogether: **uniform circular dynamics would become the new Proposition I**. Cohen/Whiteside print the draft. Newton would start from the force keeping a body in uniform circular motion and compare it directly with terrestrial gravity through the square of the arc, circle diameter, and fall distance. [Scribd](https://www.scribd.com/document/350208842/Bernard-Cohen-1971-Introduction-the-Newton-s-Principia-pdf)

So Newton was experimenting with two possible foundational orders:

$$
\text{area law first}
\rightarrow
\text{force measure},
$$

or

$$
\text{circular force first}
\rightarrow
\text{general central dynamics}.
$$

He ultimately rejected that deepest rearrangement.

This is why we need to treat the manuscripts as a **revision tree**, not as one lost “second edition.”

But Gregory's 1694 snapshot is sufficiently clear: the version Newton showed him strongly favoured **general transformations/comparisons and local curvature**, with the old conic propositions demoted to corollaries.

### What happened in 1713

Newton finally chickened out of the renumbering, in a sense. The radical mathematics was not simply discarded: he restored the 1687 proposition numbers and inserted the new machinery into them. Brackenridge describes this aptly as putting the new results into the existing “nooks and crannies.” [UC Press E-Books Collection](https://publishing.cdlib.org/ucpressebooks/public/book/the-key-to-newton-s-dynamics-the-kepler-problem-and-the-principia.html)

And this is why the final second edition is actually especially interesting for our purpose. It preserves:

$$
L.I\ldots L.XI
$$

and

$$
P.I\ldots
$$

so textual comparison is easy, but it adds the missing arrows:

$$
\boxed{L.X\to F\sim s/t^2},
$$

$$
\boxed{L.XI\to s\sim t^2},
$$

$$
\boxed{P.I\to \text{sagitta as impulse measure}},
$$

$$
\boxed{P.VI\to F\sim s/t^2}.
$$

Those are **exactly** the arrows we care about.

And Gregory's separate May 1694 notes confirm that Newton simultaneously possessed a general force-transformation treatment—Gregory records passing from a uniform circular force to an elliptical central force, and says Newton had a tract on this method. [Gwern](https://gwern.net/doc/history/1694-gregory.pdf) The same May notes record the separate ancient-philosophy project; the surviving nine-sheet Newton manuscript appears to have been intended as commentary on **Book III Props. IV–IX**, not as part of this Book-I reordering. [Gwern](https://gwern.net/doc/history/1694-gregory.pdf)

So I would now change our historical dependency diagram from the 1687 one to a **1694/1713 enhanced graph**:

$$
\boxed{
\begin{array}{ccccc}
\text{Definitions VII,VIII} && \text{Law II}\\
&\searrow&&\swarrow\\
&&\Delta p\sim Fh\\[2mm]
&&\downarrow\\
&&L.X:\;s\sim Fh^2\\
&&\downarrow\\
&&F\sim s/h^2\\[3mm]
L.VII&&L.XI&&P.I\\
\ell\sim h&\searrow& s\sim\ell^2 &\swarrow&\text{impulse polygon}\\
&&\downarrow\\
&&A\sim h^3\\[2mm]
&&\updownarrow\\
&&P.VI:\;F\sim s/h^2
\end{array}}
$$

The significant discovery is that **Newton's own revision process tightened precisely the part of the *Principia* we are using**. It did not weaken the unlimited-refinement argument; it made the finite-force / vanishing-sagitta relation considerably more explicit.

---

## User

so he revised because he found issues.

---

## ChatGPT

Yes—**in the broad sense of “issues,” definitely**. Gregory's 1694 memorandum begins by saying that near the beginning of Book I Newton had made “many corrections,” added corollaries, changed the order of propositions, and omitted some. Newton also knew that several problems in the first edition were incomplete or unsatisfactory, and later editions contain genuine corrections of errors elsewhere in the work. [CDL Pub](https://pub-ucpec2-prd.cdlib.org/ucpressebooks/view?anchor.id=bkd0e19195&brand=eschol&chunk.id=d0e19174&doc.view=content&docId=ft4489n8zn&toc.depth=1)

But for our particular sequence I would make a sharper distinction:

$$
\boxed{\text{Newton seems not to have found the }h\to0\text{ machinery defective.}}
$$

Quite the opposite. He **retained and strengthened it**. What he seems to have found defective was the way the first edition organized the consequences of that machinery.

The 1687 structure is comparatively ad hoc:

$$
\text{Lemmas I--XI}
\rightarrow
\text{Prop. I area construction}
\rightarrow
\text{a series of separate conic-force propositions}.
$$

By 1694 Newton wanted much more of Book I to follow from a few general theorems. Gregory records that old Props. VII–XIII could effectively become corollaries, while Newton planned to reorganize substantial portions of the opening sections and remove §§IV–V as separate sections, moving some of their mathematical lemmas into the introductory section. [Sage Journals](https://journals.sagepub.com/doi/10.1177/002182867000100203)

So the “issue” was approximately:

> **I have a general local mechanics here, but the 1687 book disguises it as a succession of special geometrical solutions.**

That is exactly what the curvature reconstruction fixes. Newton's proposed revision introduces the osculating-circle/curvature method so that force can be inferred directly from the local geometry of an arbitrary orbit. Portions of that new method eventually entered the 1713 edition through new corollaries and alternate proofs rather than through the radical renumbering Newton had contemplated. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0315086089900979)

And for us the direction of revision is remarkably diagnostic.

In 1687 the core relation is present but dispersed:

$$
\Delta p\sim Fh,
$$

$$
s\sim h^2,
$$

$$
s\sim \ell^2,
$$

$$
A\sim \ell s\sim h^3.
$$

In the mature treatment Newton increasingly exposes the missing connecting equation:

$$
\boxed{F\sim\frac{s}{h^2}}.
$$

So he does **not** respond to difficulties by putting a lower bound on $h$, $s$, the impulse, or the area. He responds by making the limiting relation between them **more explicit and more general**.

That distinction matters enormously for your idea.

If Newton had become worried about the legitimacy of the $h\to0$ process, we would expect the revision history to show qualifications around Lemmas I, X, XI or Proposition I: perhaps a finite interval condition, a restriction on subdivision, or some caveat about the last stage of the polygon limit.

Instead, what happens is:

$$
1687:
\qquad s\to0,\quad h\to0,\quad s/h^2\to \text{finite}
$$

becomes, increasingly,

$$
1690s/1713:
\qquad
\boxed{\text{use }s/h^2\text{ itself as a general measure of force}.}
$$

In other words, Newton doubles down on the squeeze.

There **were** genuine errors in the *Principia*. The famous example is Book II Proposition X, whose error Johann Bernoulli exposed shortly before publication of the second edition; Newton corrected it. The second edition also substantially replaced the treatment of fluid resistance because the original treatment had empirical and theoretical problems. [Newton](https://newton.edwardworthlibrary.ie/books-by-newton/principia/) But that is useful as a control: when Newton recognizes an actual error, the text gets replaced or corrected. Nothing analogous happens to Section I's unlimited diminution. The 1713 edition still explicitly has widths “diminished infinitely,” with the inscribed and circumscribed figures converging by Lemma I. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082)

So I would now classify his revisions near our material into three levels.

1. **No detected foundational failure in the limit doctrine.** Lemmas I–III survive. The principle that quantities can be diminished below any assigned magnitude survives.

2. **Strengthening of the local dynamics.** Lemmas X/XI and the propositions built on them acquire more explicit bridges between sagitta, time, curvature and force.

3. **Removal of unnecessary special-case machinery.** Several conic propositions can be compressed into consequences of general comparison/curvature theorems.

And there is a suggestive historical asymmetry here. Newton's front matter to 1713 actually labels the edition *auctior et emendatior*—“enlarged and corrected.” [Newton Project](https://newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00079) Yet the part relevant to our squeeze is “enlarged” much more than “corrected”: the limiting mechanism remains, while its dynamical interpretation becomes stronger.

So I think the revision evidence lets us state something stronger than before:

$$
\boxed{
\text{Newton had twenty-five years in which to notice a problem with }
h\to0;
\text{ his revisions instead made }F=\lim s/h^2
\text{ more central.}
}
$$

That makes the historical question much more interesting. If there is a missing premise that prevents unlimited action squeezing, it is not something Newton was drifting toward in the second edition. **His mature revision programme went in the opposite direction: it purified the continuum-limit argument.**

---

## User

so wait does it mean that a lean formalisation should be actually two differnt ones

---

## ChatGPT

Yes. Minimally **two**, and ideally **two complete formalizations plus one 1694 overlay**.

The reason is not merely historical bookkeeping. The dependency graph itself changed, and that is scientifically relevant to what we are testing.

I would structure it as a shared mathematical kernel with edition-specific theorem graphs:

```text
NewtonPrincipia/
Core/
Geometry.lean
Motion.lean
Limits.lean

Edition1687/
Definitions.lean
Laws.lean
SectionI.lean
SectionII.lean
DependencyGraph.lean

Edition1713/
Definitions.lean
Laws.lean
SectionI.lean
SectionII.lean
DependencyGraph.lean

Draft1694/
GregoryImmutanda.lean
ProposedReordering.lean
CurvatureRoute.lean

Comparison/
Squeeze1687.lean
Squeeze1713.lean
ConservativeChanges.lean
```

The **1687 formalization** should be brutally text-faithful. In particular, don't silently prove stronger modern statements and call them Newton's lemmas. Encode exactly what each lemma says and exactly which prior results its printed proof invokes.

Its schematic route would be something like

$$
\mathrm{Defs}+\mathrm{Laws}
$$

plus the geometrical chain

$$
L1,\ldots,L9
$$

leading to

$$
L10:\qquad s=O(t^2),
$$

and independently

$$
L11:\qquad s=O(\ell^2),\qquad A=O(\ell^3).
$$

Then Proposition I combines the mechanical impulse construction with the limiting geometry.

From that, in a separate modern theorem, prove

$$
\boxed{
h\mapsto
\left(
\Delta p=O(h),\
s=O(h^2),\
A=O(h^3)
\right).
}
$$

Call that something like

```lean
theorem squeeze_1687 ...
```

The important thing is that this theorem is **derived from the 1687 dependency graph**, not put into it.

The **1713 formalization** is genuinely different because Newton has inserted additional arrows. The objects may be mostly the same, but the theorem graph isn't.

For example, the mature Section I gives you much more directly

$$
L10:
\qquad
s\propto Ft^2,
$$

and then its new corollaries give

$$
\boxed{
F\propto \frac{s}{t^2}.
}
$$

Likewise the strengthened Lemma XI explicitly takes you from

$$
s\sim\ell^2
$$

to

$$
s\sim t^2
$$

at given velocity, and then to

$$
A\sim\ell^3.
$$

And the revised Proposition I/VI route supplies a second proof of the same local-force relation.

So in Lean you should be able to prove something very interesting:

```lean
theorem force_from_generated_motion_1713 :
...
→ F = limit (s h / h^2)

theorem force_from_sagitta_geometry_1713 :
...
→ F = limit (s h / h^2)
```

and then

```lean
theorem force_routes_agree_1713 :
force_from_generated_motion ... =
force_from_sagitta_geometry ...
```

That **commuting diamond** does not exist as explicitly in the 1687 textual architecture.

That comparison may itself become a historical result.

The unpublished **1694 scheme should not simply replace the 1713 version**. I would encode it as a third layer, but not necessarily as a complete formalization, because the surviving evidence is incomplete.

Its purpose is to represent the proposed reordering:

$$
\text{general comparison/curvature theorem}
\longrightarrow
\text{old special conic results as corollaries}.
$$

So rather than duplicate every lemma, import the relevant established statements and construct an alternative DAG:

```lean
namespace Draft1694

theorem proposedPropIX
(hSagitta : ...)
(hCurvature : ...) :
ForceMeasure ... := ...

theorem oldPropVII_as_corollary ...
theorem oldPropVIII_as_corollary ...
...
```

The key distinction is therefore:

$$
\boxed{
\text{1687}=
\text{historically original derivation}
}
$$

versus

$$
\boxed{
\text{1713}=
\text{mature strengthened derivation}
}
$$

with

$$
\boxed{
\text{1694}=
\text{counterfactual/revision DAG connecting them}.
}
$$

And there is a very good theorem to ask Lean to establish across editions:

$$
\boxed{
\mathrm{Squeeze}_{1687}
\iff
\mathrm{Squeeze}_{1713}
}
$$

under the common mechanical assumptions.

Not because the texts say the same things—they do not—but because both derive

$$
\Delta p=O(h),\qquad
s=O(h^2),\qquad
A=O(h^3).
$$

Then we can ask a much sharper question:

> **Did Newton's revisions introduce any new premise needed for the $h\to0$ squeeze, or merely make consequences of the old premises explicit?**

My expectation from what we've read is that Lean will show the latter:

$$
\text{1713 adds stronger theorems and shorter dependency paths},
$$

but

$$
\text{the unlimited-squeezing theorem already follows in 1687}.
$$

That would be much stronger than saying it informally. You would have a machine-checked comparison of the logical content of the two editions.

---

## User

and what principia vs de motu

---

## ChatGPT

Yes. And **De Motu vs. Principia is a more fundamental distinction than 1687 vs. 1713** for the Lean project.

The reason is that between *De motu corporum in gyrum* (1684) and the *Principia* (1687), Newton changes the **logical status of the very premise that generates our squeeze**.

In the 1684 *De Motu*, Newton simply posits as **Hypothesis 4**:

$$
\boxed{s\propto t^2}
$$

for the space described at the beginning of motion under a centripetal force. Contemporary reconstruction of the tract confirms the four hypotheses: inertia, composition of forces, and then this quadratic-displacement hypothesis. [Tufts Digital Library](https://dl.tufts.edu/pdfjs/full?file=..%2Fdownloads%2Ffq978600d)

By the *Principia*, the same statement becomes **Lemma X**, generalized from “centripetal force” to a regular/finite force and supplied with a demonstration through the preceding limit geometry, especially Lemma IX. [UC Press E-Books Collection](https://publishing.cdlib.org/ucpressebooks/public/book/the-key-to-newton-s-dynamics-the-kepler-problem-and-the-principia.html)

So we have a remarkable migration:

$$
\boxed{
\text{De Motu 1684: }s\sim t^2\ \text{is an assumption}
}
$$

becomes

$$
\boxed{
\text{Principia 1687: }s\sim t^2\ \text{is a theorem}.
}
$$

That alone justifies two separate Lean developments.

But there is a second, equally important migration.
In *De Motu*, Theorem 1 is already the polygonal equal-area construction. Newton divides time into equal pieces, lets the central force act impulsively at the vertices, proves the triangles equal, and then simply says: make the triangles **infinitely numerous and infinitely small**, with the force acting continuously, and the result follows. That wording is in the surviving transcription. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00089)

There is no preceding Section I supplying Lemmas I–III about ultimate ratios and convergence.

So:

$$
\boxed{
\text{De Motu: polygon }\to\text{ curve}
}
$$

is effectively an infinitesimal limiting postulate/practice.

In the *Principia*, Newton inserts the whole section

> *De Methodo Rationum primarum & ultimarum*

**before** the dynamics. Lemmas I–III supply the formal limiting machinery, and Proposition I then uses it to justify the polygon-to-curve passage. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

Thus another migration is

$$
\boxed{
\text{De Motu: infinitesimal passage used directly}
}
$$

to

$$
\boxed{
\text{Principia: infinitesimal passage derived through a limit calculus}.
}
$$

That is extremely relevant to us.

### The genealogy of our exact chain

In *De Motu* the beginning is approximately

$$
\text{Def. 1: centripetal force}
$$

$$
\text{Def. 2: vis insita}
$$

$$
\text{Hyp. 2: inertial rectilinear motion}
$$

$$
\text{Hyp. 3: parallelogram/composition rule}
$$

$$
\boxed{\text{Hyp. 4: }s\sim t^2}.
$$

Then immediately:

$$
\text{Theorem 1: area law from impulse polygon}
$$

$$
\text{Theorem 2: circular force}
$$

$$
\boxed{\text{Theorem 3: general local force formula}}.
$$

Theorem 3 is particularly revealing. Newton writes for the indefinitely small figure that $QR$, the departure from the tangent, is for a given time proportional to force and for a given force proportional to the square of time. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00089)

In modern notation:

$$
\boxed{QR\sim F\,\Delta t^2}.
$$

So our entire dynamical kernel is already present in 1684:

$$
\Delta t
\longrightarrow
QR\sim F\Delta t^2
\longrightarrow
F\sim\frac{QR}{\Delta t^2}.
$$

But the crucial $t^2$ relation is still a hypothesis.

---

In the *Principia* this becomes something much more elaborate:

$$
\text{Definitions}
\to
\text{Laws}
$$

and independently

$$
L1-L9
$$

then

$$
\boxed{
L9\to L10:\quad s\sim t^2
}
$$

followed by

$$
L11:\quad s\sim\ell^2,\qquad A\sim\ell^3,
$$

and then

$$
P1:\quad\text{impulse polygon}\to\text{continuous central force},
$$

finally

$$
P6:\quad
F\sim\frac{s}{t^2}.
$$

Thus the *Principia* turns a compact assumed structure into a **dependency graph**.

There is a remarkably clean correspondence:

| *De Motu* 1684 | *Principia* 1687 |
|---|---|
| Def. 2, innate force | Def. III + Law I |
| Hyp. 2, uniform rectilinear continuation | Law I |
| Hyp. 3, composition/parallelogram | Laws + Corollary I |
| **Hyp. 4, $s\sim t^2$** | **Lemma X, now proved** |
| Theorem 1, area law | Proposition I |
| Theorem 2, circular force $v^2/r$ | Proposition IV |
| **Theorem 3, general $PQRST$ force formula** | **Proposition VI** |
| direct “infinitely many infinitely small triangles” | Section I limits + Prop. I |

The identification of *De Motu* Theorem 3 with Principia Proposition VI is explicit in the literature. [Didáctica Ciencias Naturales](https://www.ind.ku.dk/begivenheder/2021/yuvita-oktarisa/Thesis_Yuvita.pdf)

### There is even an intermediate stage

So strictly speaking the genealogy is richer than two versions.

In the **first** *De Motu*, Hypothesis 4 has no demonstration. Newton then revises the tract and **promotes it to a lemma with a demonstration**. Herivel's manuscript reconstruction records precisely this development; Brackenridge likewise notes that both the force-composition hypothesis and the $t^2$ hypothesis acquire demonstrations in revisions before the final *Principia*. [Páginas JH](https://pages.jh.edu/rrynasi1/PhysicalPrinciples/literature/Herivel1965TheBackgroundToNewtonsPrincipia.pdf)

Thus:

$$
\boxed{
\begin{array}{ccc}
1684\ De\ Motu_1
&
\longrightarrow
&
revised\ De\ Motu
\\[2mm]
s\sim t^2
&
&
s\sim t^2
\\
\text{Hypothesis}
&&
\text{Lemma + proof}
\\[2mm]
&&\downarrow\\
&&1687\ Principia\\
&&L.X\text{ embedded in }L.I-L.XI
\end{array}}
$$

This is almost a laboratory experiment in Newton's own standards of proof.

And that suggests a much better Lean architecture than simply “1687 versus 1713”:

```text
Newton/
Common/
Geometry.lean
Motion.lean

DeMotu1684/
Definitions.lean
Hypotheses.lean
Theorem1.lean
Theorem2.lean
Theorem3.lean

DeMotuRevised/
HypothesisToLemma.lean

Principia1687/
Definitions.lean
Laws.lean
FirstLastRatios.lean
LemmaX.lean
LemmaXI.lean
PropositionI.lean
PropositionVI.lean

Principia1713/
StrengthenedLemmaX.lean
StrengthenedLemmaXI.lean
StrengthenedPropI.lean
PropositionVI.lean

Genealogy/
QuadraticMotion.lean
AreaLaw.lean
ForceFormula.lean
```

The crucial Lean result would not just be

```lean
theorem squeeze : ...
```

but something like

```lean
theorem deMotu_squeeze
(H4 : QuadraticInitialDeflection ...) :
Squeeze ...
```

versus

```lean
theorem principia_squeeze
(laws : NewtonLaws ...)
(geometry : FirstLastRatioLemmas ...) :
Squeeze ...
```

The conclusions would agree:

$$
s=O(h^2),\qquad A=O(h^3),
$$

but the hypotheses would differ.

Then Lean can establish exactly what Newton accomplished between 1684 and 1687:

$$
\boxed{
\text{Principia premises}
\Longrightarrow
\text{De Motu Hypothesis 4}.
}
$$

In other words, **the Principia discharges one of De Motu's axioms**.

And there is an even more interesting comparison around Theorem 1/Proposition I:

$$
\boxed{
\text{De Motu uses the continuum limit}
}
$$

while

$$
\boxed{
\text{Principia attempts to prove the admissibility of that continuum limit first}.
}
$$

For our Planck-gap question, that is probably the most important textual development we have found so far. The place to interrogate is no longer just “Newton's Lemma X.” It is the historical transformation

$$
\boxed{
\text{Hypothesis 4}
\quad\longrightarrow\quad
\text{Lemma X}
}
$$

together with

$$
\boxed{
\text{informal infinitely-small polygon limit}
\quad\longrightarrow\quad
\text{Section I first/last-ratio machinery}.
}
$$

Those are precisely the two moves by which Newton converts the **squeezing assumptions of De Motu into purported theorems of the Principia**. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00089)

---

## User

this looks as a new project, honestly

---

## ChatGPT

Yes. It has become a distinct project.

The clean research question is no longer “can Newton hint at a Planck gap?” but something much more historical-formal:

**How did Newton turn the dynamical assumptions of *De Motu* into the limit-theoretic theorem architecture of the *Principia*, and what exactly is assumed versus proved at each stage?**

That gives a natural corpus: *De Motu* 1684, its revisions, *Principia* 1687, Gregory’s 1694 revision notes / Newton’s projected reordering, and *Principia* 1713/1726. The central object is the genealogy of the chain

$$
\Delta p\sim F\,dt,\qquad
s\sim F\,dt^2,\qquad
A\sim dt^3,\qquad
F\sim \frac{s}{dt^2},
$$

together with the polygon $\to$ curve limit.

The Lean part then becomes genuinely interesting rather than decorative: formalize each historical dependency graph separately and mechanically compare them. In *De Motu*, $s\sim t^2$ is initially a hypothesis; in the *Principia* it becomes something Newton claims to derive. The formal comparison can tell us exactly which additional premises discharge the earlier hypothesis, which statements merely get renamed or reordered, and whether the 1694/1713 changes actually shorten or strengthen the proof graph.

I would keep the Planck-gap work as a **downstream application**. This new project should stop exactly at the Newtonian theorem:

$$
h\to0
\quad\Rightarrow\quad
\Delta p=O(h),\quad s=O(h^2),\quad A=O(h^3),
$$

and document how Newton acquired the right to assert each arrow. Then the old project can import that result as its classical baseline.

A good working title would be **Formal Genealogy of Newton’s Limit Dynamics: From *De Motu* to the *Principia***. The genuinely publishable novelty would be the combination of textual stemma + dependency DAG + edition-specific Lean verification.

---

## User

how would you prompt seed the new project to codex?

---

## ChatGPT

I would seed Codex with a prompt that forces it to treat this as a **historical-formalization project**, not as another speculative physics branch.

:::writing{variant="document" id="48317" title="Codex seed prompt — Formal Genealogy of Newton’s Limit Dynamics"}
You are starting a new research/software project:

# Formal Genealogy of Newton’s Limit Dynamics
## From *De Motu* (1684) to the *Principia* (1687, projected 1694 revisions, 1713/1726)

The project has two tightly coupled goals:

1. reconstruct, from primary Newton sources, the changing logical dependency graph by which Newton derives local force and limiting motion;
2. formalize those historical dependency graphs in Lean, preserving the distinction between what Newton assumes, what he proves, what he imports from previous definitions/laws, and what later editions strengthen or reorder.

This is NOT presently a project about quantum mechanics, Planck’s constant, Navier–Stokes, Yang–Mills, or proving a physical cutoff. Do not drift into those topics. The downstream motivation may eventually use the Newtonian result, but the project itself stops at the classical limiting architecture.

The central mathematical chain to trace is

$$
\Delta p = O(h),
\qquad
s = O(h^2),
\qquad
A = O(h^3),
\qquad
F \sim \frac{s}{h^2},
$$

where $h$ is a shrinking time interval, $s$ is the departure/sagitta from inertial tangent motion, and $A$ is the corresponding tangent/curve or chord/curve defect area.

The main historical question is:

> How did Newton transform the assumptions used in *De Motu* into the limit-theoretic theorem architecture of the *Principia*, and what exactly is assumed versus derived at each textual stage?

The important textual stages are:

- *De motu corporum in gyrum*, first 1684 state;
- revised *De Motu* states where surviving manuscripts permit reconstruction;
- *Principia*, first edition, 1687;
- Newton’s projected early-1690s / 1694 reorganization recorded by David Gregory, including the proposed reordering of early Book I;
- *Principia*, second edition, 1713;
- 1726 only where it differs materially from 1713 for this chain.

Do not silently merge these stages.

## Primary-source policy

Primary Newton sources have priority over secondary literature.

Prefer:

- Newton Project transcriptions, normalized and diplomatic;
- surviving Latin editions/transcriptions of the *Principia*;
- manuscript transcriptions of *De Motu*;
- Gregory’s surviving memoranda/notebooks where transcribed or reproduced;
- Newton manuscripts relevant to the projected revisions.

Secondary sources such as Whiteside, Herivel, Cohen, Brackenridge, Guicciardini, Pourciau, Nauenberg, etc. are valuable for locating manuscripts and interpreting difficult passages, but a dependency edge should not be attributed to Newton solely because a secondary author says so if the relevant primary text is available.

For every historical claim record:

- textual stage / edition;
- exact passage;
- source URL or bibliographic witness;
- original Latin where useful;
- English translation if needed;
- whether the dependency is explicit, implicit, or reconstructed;
- confidence.

Never write “Newton proves X from Y” when the source only places X after Y. Distinguish:

- `explicit_dependency`
- `implicit_dependency`
- `modern_reconstruction`
- `editorial_interpretation`

## Core objects to trace

The first pass should concentrate only on these:

### De Motu
Identify precisely the status and wording of:

- definitions of force / innate force;
- hypotheses concerning inertial motion;
- composition/parallelogram of motions;
- the hypothesis that initial displacement generated by force varies as the square of time;
- Theorem 1, polygonal equal-area construction;
- the passage from finitely many impulses to continuous central force;
- the early general local-force theorem using tangent departure/sagitta;
- subsequent revisions in which hypotheses become lemmas or receive demonstrations.

The key question is whether the relation

$$
s \propto Fh^2
$$

is assumed, proved, or partly imported from an earlier kinematic premise at each manuscript state.

### Principia 1687 — opening material

Trace:

- Definitions II, III, IV, VII, VIII as relevant;
- Definition Scholium only where it contributes assumptions about mathematical time, space, or measurement;
- Laws I–III;
- Corollary I and any other corollaries directly used in the early Book I proofs;
- Scholium to the Laws, especially the Galileo/projectile argument.

### Principia 1687 — Book I Section I

Formalize the actual logical role of Lemmas I–XI.

Pay special attention to:

- Lemma I: ultimate ratios / limiting equality;
- Lemmas II–III: convergence under indefinitely refined partitions;
- Lemma IV: passage from local ratios to wholes;
- Lemmas VI–VIII: tangent, chord, arc limiting equivalence;
- Lemma IX: quadratic area scaling;
- Lemma X: initial displacement under force proportional to $t^2$;
- Lemma XI: sagitta/contact-subtense scaling as length squared;
- Lemma XI corollaries giving cubic area scaling.

Do not force every lemma into the main dependency chain if Newton does not use it.

### Principia 1687 — Book I Section II

Trace at least:

- Proposition I, including exactly which Laws and previous Lemmas are cited;
- its polygon-to-curve limit;
- Proposition VI / the local force ratio;
- whatever propositions are necessary to understand how the sagitta/deviation becomes a measure of force.

The key structural conjunction is:

$$
\text{mechanical impulse construction}
+
\text{geometrical unlimited refinement}.
$$

### Projected 1694 reordering

Reconstruct Gregory’s evidence for:

- propositions reordered;
- propositions omitted or reduced to corollaries;
- movement of geometrical lemmas into Section I;
- proposed curvature/osculating-circle machinery;
- proposed general comparison theorems;
- new Proposition IX / X structures, if those identifications are supported by primary or well-established manuscript evidence.

Do NOT treat Gregory’s notes as though they describe a completed second edition. Represent this as a proposed dependency DAG with uncertainty annotations.

The “Classical Scholia” project is separate unless a surviving source explicitly connects it to the early Book I restructuring. Do not conflate Book III historical/ancient-philosophy scholia with the mathematical reordering of Sections I–III.

### Principia 1713

Identify every relevant strengthening versus 1687, especially:

- changes to Lemma X;
- new corollaries making explicit
$$
s\propto Ft^2,\qquad
F\propto s/t^2,\qquad
t^2\propto s/F;
$$
- changes to Lemma XI and its corollaries;
- additions to Proposition I;
- revised Proposition VI;
- alternate derivations of the same local force relation.

Look specifically for a commuting dependency diamond:

$$
\text{generated-motion route}
\longrightarrow
F\sim s/t^2
$$

versus

$$
\text{polygon/sagitta geometry route}
\longrightarrow
F\sim s/t^2.
$$

## Lean architecture

Use Lean 4 and current mathlib.

Do not port historical Lean 3 code wholesale, but inspect existing formalizations of constant-acceleration kinematics for ideas.

Create a structure approximately like:

```text
NewtonLimitDynamics/
Common/
BasicMotion.lean
Geometry.lean
Asymptotics.lean

DeMotu1684/
Definitions.lean
Hypotheses.lean
AreaLaw.lean
LocalForce.lean

DeMotuRevisions/
QuadraticMotion.lean

Principia1687/
Definitions.lean
Laws.lean
SectionI/
Lemma01.lean
...
Lemma11.lean
SectionII/
Proposition01.lean
Proposition06.lean
Squeeze.lean

Draft1694/
GregoryEvidence.lean
ProposedDependencyGraph.lean
CurvatureRoute.lean

Principia1713/
SectionI/
SectionII/
Squeeze.lean

Comparison/
DeMotu_vs_1687.lean
Edition1687_vs_1713.lean
DependencyChanges.lean

Sources/
source_index.md
passages/
```

The historical namespaces must remain separate even when they instantiate common mathematical lemmas.

## Formalization discipline

There are two distinct kinds of theorem:

1. `historical theorem`: formal statement matching Newton’s actual proposition closely;
2. `modern consequence`: a cleaner theorem we derive from the historical statements.

Name them accordingly.

Example:

```lean
namespace Principia1687

theorem lemmaX_historical ...
theorem lemmaXI_historical ...

theorem quadraticSagitta_modern ...
theorem cubicArea_modern ...

end Principia1687
```

Do not silently replace Newton’s geometric statement by a Taylor theorem and call that “Lemma XI”. A Taylor-based theorem can establish a modern equivalent or generalization, but the historical theorem should remain separately represented.

Use `Filter.Tendsto`, `IsLittleO`, `IsBigO`, derivatives, interval integrals, and finite sums where appropriate.

For the constant-force model, aim to machine-check at minimum:

$$
p(h)-p(0)=Fh,
$$

$$
q(h)-q(0)-h\,v(0)=\frac{F}{2m}h^2,
$$

$$
A(h)=v\int_0^h\frac{F}{2m}t^2\,dt
=\frac{Fv}{6m}h^3,
$$

and for a fixed total interval $T$ partitioned into $N$ cells,

$$
N A(T/N)=\frac{FvT^3}{6mN^2}\to0.
$$

The final theorem for each edition should make assumptions explicit.

For example:

```lean
theorem squeeze_1687
(hDefs : ...)
(hLaws : ...)
(hLimits : ...)
...
:
IsBigO ... impulse h ∧
IsBigO ... sagitta (h^2) ∧
IsBigO ... area (h^3)
```

For *De Motu*, the analogous theorem should visibly depend on the quadratic-displacement hypothesis:

```lean
theorem squeeze_deMotu1684
(hyp4 : QuadraticInitialDeflection ...)
...
```

Then prove, if supported by the formal reconstruction, something of the form:

```lean
theorem principia1687_discharges_deMotu_hyp4 :
Principia1687Premises → DeMotu1684.QuadraticInitialDeflection
```

This is one of the main targets of the project.

## Dependency graph as data

Do not leave historical dependencies only in prose.

Create a machine-readable file, perhaps YAML or JSON, with nodes such as:

```yaml
- id: DM1684.H4
type: hypothesis
statement: initial force-generated displacement is proportional to time squared

- id: P1687.L10
type: lemma
statement: ...

- id: P1687.P1
type: proposition
```

Edges should contain:

```yaml
from:
to:
status: explicit | implicit | reconstructed
source:
notes:
```

Generate human-readable Mermaid/DOT graphs from this data.

There should eventually be separate DAGs for:

- De Motu 1684;
- revised De Motu;
- Principia 1687;
- proposed 1694 organization;
- Principia 1713.

Then generate a comparison graph showing added, removed and redirected dependencies.

## Research method

Work source-first.

For each target passage:

1. fetch and preserve the primary transcription;
2. record bibliographic/manuscript metadata;
3. extract the exact relevant text;
4. translate only as much as needed;
5. identify explicit cited dependencies;
6. distinguish those from dependencies inferred by us;
7. formalize the mathematical statement;
8. compile Lean;
9. record discrepancies between the formal statement and Newton’s text.

Do not make large speculative interpretive claims before the source table and dependency graph support them.

## Initial milestone

The first milestone is deliberately narrow:

### Milestone M1 — Quadratic Deflection Genealogy

Produce a research note and compiling Lean code answering:

> How does
> $$
> s\propto t^2
> $$
> change in logical status from early *De Motu* to the 1687 *Principia* and then to 1713?

Deliver:

- exact source passages;
- textual comparison;
- dependency DAG for each stage;
- Lean statement of the De Motu hypothesis;
- Lean derivation corresponding to Principia Lemma X;
- proof that the modern mathematical contents agree under the relevant assumptions;
- explicit list of additional premises used by the Principia derivation.

Do not proceed to the whole book until M1 is stable.

### Milestone M2 — Polygon Limit

Then compare:

$$
\text{De Motu Theorem 1}
$$

with

$$
\text{Principia Lemmas I–III + Proposition I}.
$$

Determine precisely what additional limiting assumptions or theorems the *Principia* inserts.

### Milestone M3 — Cubic Squeeze

Combine Lemmas X and XI with the local tangent geometry to establish

$$
s=O(h^2),\qquad A=O(h^3)
$$

and the $N^{-2}$ total polygon-error law.

### Milestone M4 — Revision Graph

Only after M1–M3, reconstruct the 1694 planned reordering and compare it with the actual 1713 dependency graph.

## Non-goals

Do not:

- introduce $\hbar$;
- derive quantum mechanics;
- search for a minimum action;
- generalize immediately to arbitrary manifolds;
- formalize all of the *Principia*;
- modernize every historical statement beyond recognition;
- treat secondary-source reconstructions as primary evidence;
- infer manuscript chronology without evidence.

The value of the project is the exact comparison of Newton’s evolving proof architecture.

## First action

Create:

1. `README.md`;
2. `AGENTS.md` containing the methodological rules above;
3. `research/STATE.md`;
4. `research/sources.md`;
5. `research/dependency-schema.yaml`;
6. Lean 4 project skeleton;
7. `DeMotu1684/QuadraticDeflection.lean`;
8. `Principia1687/LemmaX.lean`.

Before writing substantial Lean code, populate `research/sources.md` with the primary witnesses needed for M1 and quote only short identifying snippets, with stable links/anchors.

The first commit should contain only the project skeleton, source inventory, M1 dependency graph, and the smallest compiling Lean statements necessary to make the intended comparison concrete.
:::

I would give Codex that as the initial prompt and make **M1 the hard stopping point**. It is small enough to prevent the project exploding into “formalize Newton,” while already testing the central historical claim: *De Motu* assumes the quadratic deflection that the *Principia* tries to derive.

---

## User

hey really you seed so much to your subagnets? I am usually briefer

---

## ChatGPT

Usually much briefer.

That long seed was closer to a mini-spec / `AGENTS.md` than a good first Codex prompt. For a new repo, I’d normally seed with the research question, the immediate milestone, and a couple of constraints, then let the agent inspect sources and propose structure.

Something like this is closer to how I’d actually start it:

:::writing{variant="document" id="27164" title="Short Codex seed"}
Start a new Lean 4 + historical research project on the genealogy of Newton’s limit dynamics from *De Motu* (1684) to the *Principia* (1687, 1713), with Gregory’s 1694 revision notes as an intermediate planned architecture.

Main question: how did the relation

$$
s \propto t^2
$$

move from a hypothesis in *De Motu* to a proved lemma in the *Principia*, and how did the dependency graph around polygon limits, sagittae, force, and cubic area change?

First milestone only:

1. Find and preserve the primary online transcriptions for the relevant *De Motu* passage, Principia 1687 Lemma X, and 1713 Lemma X.
2. Build a small dependency graph distinguishing explicit dependencies from modern reconstruction.
3. Create a Lean 4 project and formalize the mathematical content of the three versions.
4. Determine exactly what additional assumptions the 1687 proof uses to discharge the *De Motu* $s\sim t^2$ hypothesis.

Keep editions separate. Do not drift into QM/Planck-gap work. Prefer Newton Project and other primary transcriptions over secondary literature.

Create `README.md`, `AGENTS.md`, `research/STATE.md`, and the minimum compiling Lean skeleton. Stop after the first milestone and report what changed logically between the texts.
:::

That is enough to get a capable Codex agent moving. The longer version is useful **after** the first exploration, when you know which distinctions really need to be frozen into `AGENTS.md`.

---

## User

wait I was thinking... all of the antiquity debate was if time was to be considered as a set of dots or as a set of intervals, what is Newton position in his axioms?

---

## ChatGPT

Yes. If we translate the ancient dispute into your “dots versus intervals” language, **Newton is on the continuous-duration / divisible-interval side**, not the atomic-instants side. But the precise position is slightly subtler: time itself is a continuously flowing magnitude; **intervals are its parts**, while instants function as boundaries/limits or locations *in* time, not as indivisible atoms from which duration is assembled.

That is already visible in the foundational Scholium to the Definitions. Newton refuses to define time because he takes it as familiar, but then says:

> *Tempus absolutum, verum, & mathematicum ... æquabiliter fluit ... alioque nomine dicitur Duratio.*

Absolute mathematical time “flows equably” and is also called **duration**. He then speaks explicitly of the immutable order of the **parts of time**—*partium Temporis ordo est immutabilis*—and even says times and spaces are “as it were places” of themselves and all things. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00075)

That is already very different from

$$
T=\{t_1,t_2,t_3,\ldots\}
$$

as a collection of zero-duration atoms.

## What the mechanics actually uses

The dynamical proofs make the ontology clearer than the metaphysical Scholium.

In Proposition I Newton does **not** say “take successive instants.” He says

$$
\boxed{\textit{Dividatur tempus in partes æquales}}
$$

—“let time be divided into equal parts.”

During the **first part of time** the body describes $AB$; during the second part it would describe $Bc$; forces act at the boundaries of these parts in the polygonal model. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

So the discrete Newton construction is

$$
[t_0,t_1],\quad[t_1,t_2],\quad\ldots,[t_{N-1},t_N],
$$

not

$$
t_0,t_1,\ldots,t_N
$$

considered as the substance of time.

The points $t_i$ are where the impulse occurs. The **duration** over which inertial motion occurs is

$$
\Delta t_i=t_{i+1}-t_i.
$$

And then Newton takes

$$
\max_i\Delta t_i\to0.
$$

That is extremely close to our modern interval/partition picture.

The Scholium to the Laws says the same thing when explaining Galileo: uniform gravity acts equally in **equal particles of time**—*singulis temporis particulis æqualibus*—and therefore generates equal velocity increments. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00086)

Thus

$$
\text{equal duration}
\longrightarrow
\text{equal }\Delta v.
$$

A “particle of time” here plainly cannot mean a zero-length instant: a force acting through it generates a finite increment of motion. It is a little interval.

## And Section I explicitly rejects indivisible constituents

This makes the position considerably stronger.

At the end of Section I Newton directly contrasts his method with the **hypothesis of indivisibles**:

> *durior est indivisibilium Hypothesis*

and says that when he talks as if quantities consisted of particles, those particles are to be understood not as indivisibles but as

> *evanescentia divisibilia*

—**evanescent divisible quantities**. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

He then makes the point absolutely explicit: when he says “least,” “evanescent,” or “ultimate,” one must not understand quantities having some determinate least magnitude; they are quantities

> *semper diminuendas sine limite*

to be continually diminished **without limit**. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

Although this statement is about his mathematical quantities generally, time is one of precisely the continuously varying quantities to which the method is applied.

So if the ancient alternatives are

$$
\text{continuum} =
\underbrace{\bullet\bullet\bullet\bullet}_{\text{indivisible instants}}
$$

versus

$$
\text{continuum} =
\text{divisible duration with boundaries},
$$

Newton's *Principia* is unequivocally the second.

## His “moment” is particularly revealing

The word *moment* can mislead us because modern ears hear “instant.”

But Newton's mathematical usage is very different.

In his later explanation of fluxions he says quantities are generated by **continual increase**, and that their moments are the parts generated during moments of time. More explicitly, in demonstrations he regards the moment $o$ as an **indefinitely small but not infinitely small part of time**, performs the calculation with finite quantities, and only at the end lets $o$ decrease and vanish. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00356)

So Newton's operative picture is:

$$
o>0
$$

during the argument,

then

$$
o\to0.
$$

It is emphatically not

$$
o=\text{an indivisible temporal atom}.
$$

Indeed in another retrospective description he says explicitly that quantities are considered **not as aggregated from indivisibles** but as growing by continual motion. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00352)

This agrees perfectly with the *Principia* Section I language.

---

## There are therefore three different objects

I think this distinction would matter enormously in the Lean project.

Newton effectively has:

$$
\boxed{\text{time}}
$$

as continuous duration;

$$
\boxed{\Delta t}
$$

as a divisible part of that duration;

and

$$
\boxed{t}
$$

as the boundary/location at which something occurs.

Those should not all be represented by the same conceptual object.

Modern elementary mechanics collapses them all into real numbers:

$$
t\in\mathbb R,\qquad
\Delta t\in\mathbb R.
$$

Mathematically that works, but historically it hides Newton's architecture.

A much more Newton-faithful formalization would use an **affine time line**:

$$
\mathcal T
$$

whose elements are temporal locations/instants, together with a vector space of durations

$$
\mathcal D\simeq\mathbb R.
$$

Then

$$
t_1-t_0\in\mathcal D
$$

is a duration, but an instant $t_0$ is not itself a duration.

Schematically:

```text
TimePoint -- affine points
Duration ℝ -- differences between time points

t₁ -ᵥ t₀ : Duration
t₀ +ᵥ Δt : TimePoint
```

This is conceptually much closer to Newton than just declaring

```lean
abbrev Time := ℝ
```

because Newton gives us an **absolute temporal structure without selecting a privileged zero of time**. His absolute time has an invariant duration and order, but the *Principia* does not need “the origin of absolute time.”

That is exactly an affine-line structure.

## And now reconsider Proposition I

It becomes:

$$
t_0<t_1<\cdots<t_N
$$

with equal differences

$$
t_{i+1}-t_i=h.
$$

Law I applies over each **interval**

$$
[t_i,t_{i+1}],
$$

while the impulse is idealized at the common boundary $t_i$.

Then

$$
h\to0.
$$

Thus Newton does something conceptually rather elegant:

$$
\boxed{
\text{finite intervals}
\quad+\quad
\text{forces located at their boundaries}
\quad\xrightarrow{h\to0}\quad
\text{continuous action}.
}
$$

The boundaries do not become the constituent substance of time. They merely become dense as the partition is refined.

And this makes our squeeze more interesting:

$$
\Delta p=Fh,
\qquad
s\sim h^2,
\qquad
A\sim h^3
$$

are all functions of an **interval length $h$**.

There is no corresponding formula attached to a temporal point:

$$
F(t)\times ``dt"
$$

only acquires meaning through the limiting process on intervals.

---

So I would revise the prospective formalization at its very bottom. Instead of starting with

$$
t:\mathbb R,
$$

start with

$$
\boxed{
\texttt{TimePoint}
\quad\text{affine over}\quad
\texttt{Duration}\simeq\mathbb R.
}
$$

And then Newton's first/last-ratio machinery operates on shrinking **durations**

$$
h_n>0,\qquad h_n\to0,
$$

not on a sequence of smaller “time points.”

That may actually expose the historical issue you just noticed: **Newton's entire derivation of force presupposes the ancient continuum answer that a duration is indefinitely divisible without being composed of indivisible nows.** His innovation is to make the physical law live in the limiting ratios of those disappearing intervals. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00077)

---

## User

had not scholia about this

---

## ChatGPT

Yes. And it makes the story more interesting than I said before.

There are **three Newtonian positions/textual usages that have to be distinguished**.

First, the mature *General Scholium* really does say:

> *unumquodque Durationis indivisibile momentum...*
> “every indivisible moment of duration ...”

and immediately afterwards:

> *Partes dantur successivae in duratione*
> “there are successive parts in duration.”

So Newton simultaneously admits **indivisible moments** and **successive parts of duration**. [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00056?mibextid=WaXdOe)

That is extremely close to the Aristotelian architecture:

$$
\text{duration is continuous and divisible},
$$

but

$$
\text{the now }(\nu\nu)\text{ is indivisible}
$$

because it is the **boundary** between two portions of time, not a little temporal brick from which duration is assembled. Aristotle explicitly argues that the now is indivisible while the continuum cannot be composed of indivisibles. [Archivos Clásicos de Internet](https://classics.mit.edu/Aristotle/physics.6.vi.html)

So my previous wording “Newton does not model time as a set of points” was too quick. The better formulation is:

$$
\boxed{\text{mature Newton has indivisible temporal points, but not obviously indivisible temporal intervals.}}
$$

### And there is a scholium which says almost exactly this in calculus language

The really important manuscript is Newton's draft additions to the **Leibniz Scholium** for the second edition.

He writes:

> *Per momenta quantitatum ... particulas momento temporis genitas.*

and then explicitly says these particles

> *non sunt minima indivisibiles ... sed sunt ... in infinitum [divisibiles]*

—not indivisible minima, but divisible without end—and “indefinitely small.” He then describes time as produced by a **continuous and uniform flow**:

> *tempus ut fluxu continuo et æquali genitum.*

[Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00349)

That's extraordinarily pertinent.

Newton is distinguishing:

$$
\boxed{\text{moment of duration}}
$$

in the sense of an instantaneous **now/boundary**, from

$$
\boxed{\text{moment of a fluent quantity}}
$$

in the fluxional sense: a vanishing increment generated during a small duration.

The latter is emphatically **not indivisible**.

His alternative draft says the same thing even more plainly:

> *incrementa momentanea seu particulas momento temporis genitas; easque indefinite parvas & in infinitum divisibiles.*

“momentary increments, or particles generated in a moment of time; indefinitely small and infinitely divisible.” [Newton Project](https://newtonproject.ox.ac.uk/view/texts/normalized/NATP00349)

And the published Book II Lemma II preserves the essential distinction. A finite particle is **not** a moment; moments are the *principia jamjam nascentia*—the just-nascent beginnings—of finite magnitudes. In 1687 he even says that as soon as moments become finite magnitudes, they **cease to be moments**. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/NATP00078)

So there are two very different senses of *momentum* running around Newton.

### But young Newton held a much more atomistic theory!

This is the surprise.

In the youthful *Quæstiones quædam Philosophiæ*, under **“Of Motion”**, Newton explicitly argues:

> “there is a least distance, a least progression in motion & a least degree of time.”

Then:

> “there are soe many least parts of time in an hower as there can be Τὸ νὺν’s.”

And:

> “the least moment of time” has no parts.

[Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/THEM00092)

That's not merely an indivisible now as a boundary. That's very close to an actual **temporal atomism**:

$$
T=\{\text{least moments}\}.
$$

He even links it to his contemporary atomism of matter and argues for the least temporal part analogously to a least material part. The surrounding notebook explicitly discusses atoms, least distances, mathematical points and the constitution of quantities. [Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/normalized/THEM00092)

So we seem to have a genuine intellectual transition:

$$
\boxed{
\text{young Newton: least temporal parts / } \tauὸ\nu\nu\text{'s}
}
$$

to

$$
\boxed{
\text{Principia Newton: indefinitely divisible intervals and evanescent quantities}
}
$$

while retaining

$$
\boxed{
\text{indivisible “now” as temporal boundary}.
}
$$

That is very close to moving from an atomistic solution of the ancient continuum problem toward the Aristotelian distinction

$$
\text{indivisible boundary}\neq\text{indivisible constituent}.
$$

### Another manuscript makes the boundary interpretation very tempting

In a draft *De motu corporum in mediis regulariter cedentibus*, Newton has a remarkable Definition 16:

> *Momenta quantitatum sunt ipsarum principia generantia vel alterantia fluxu continuo*

—moments of quantities are their generating or altering principles in a continuous flux.

His examples include:

> *tempus præsens præteriti et futuri*

the **present time [as the moment] of past and future**,

and then

> the point of a line, the line of a surface, the surface of a solid...

[Newton Project](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00091)

That's practically a table of codimension-one boundaries:

$$
\begin{array}{c|c}
\text{continuum} & \text{moment/boundary}\\
\hline
\text{past/future duration} & \text{present}\\
\text{line} & \text{point}\\
\text{surface} & \text{line}\\
\text{solid} & \text{surface}
\end{array}
$$

This strongly suggests that an **indivisible moment of duration** in the mature metaphysics can play the role that a point plays on a continuous line without implying that the line is assembled from point-atoms.

And that is precisely Aristotle's construction of the *now*.

### What about the “Classical Scholia”?

Here I think we should distinguish your memory carefully.

The unpublished **Classical Scholia proper**, intended around Book III Props. IV–IX, are mainly about ancient cosmology, Pythagorean astronomy/harmony, ancient knowledge of gravitational ideas, prisca sapientia, etc. The Newton Project describes them that way; I don't currently see evidence that their surviving core contains a sustained treatment of the temporal continuum. [Newton Project](https://newtonproject.ox.ac.uk/texts/introduction)

But **two other scholia are directly relevant**:

1. the **General Scholium**, with the phrase
$$
\textit{durationis indivisibile momentum};
$$

2. the proposed additions to the **Leibniz Scholium**, with
$$
\text{continuous flow + indefinitely small, infinitely divisible increments}.
$$

So your recollection of “there were scholia about this” is basically right, but probably mixes those with the Classical Scholia.

### This changes the Lean project quite a bit

We should absolutely **not** formalize Newtonian time simply as

```lean
Time := ℝ
```

and think we've captured the historical distinction.

For mature Newton I'd want:

$$
\mathcal T=\text{affine TimePoints},
\qquad
\mathcal D=\text{Durations},
$$

with

$$
t_1-t_0\in\mathcal D.
$$

Then an indivisible *now* is

$$
t\in\mathcal T,
$$

while a temporal part is

$$
h=t_1-t_0>0,
$$

and it is **$h$** that is indefinitely divisible:

$$
h,\frac h2,\frac h4,\ldots\to0.
$$

There is no smallest positive $h$.

This would let the formalization state exactly the mature Newtonian distinction:

$$
\boxed{
\text{instant is indivisible}
\quad\not\Rightarrow\quad
\text{duration has a least positive part}.
}
$$

And now something potentially important appears for the genealogy project:

$$
\textit{Quæstiones}
\quad\to\quad
\textit{De Motu}
\quad\to\quad
\textit{Principia}
$$

may contain not only the evolution

$$
s\propto t^2:
\quad
\text{hypothesis}\to\text{theorem},
$$

but also a deeper evolution

$$
\boxed{
\text{time made from least moments}
\quad\longrightarrow\quad
\text{continuous duration with indivisible boundaries}.
}
$$

And that evolution sits exactly underneath Newton's ability to let

$$
h\to0,\qquad
s\sim h^2,\qquad
A\sim h^3
$$

without ever arriving at a “next smallest” interval. That is likely worth making a first-class thread of the new project, not a footnote.
