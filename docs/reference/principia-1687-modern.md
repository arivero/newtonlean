---
title: "Newton, *Principia*: Definitions, Laws, and Book I, Sections I–II"
subtitle: "The 1687 text in modern mathematical language, in Newton's order, with the changes of 1713 and 1726"
date: "October 2026"
geometry: margin=2.4cm
fontsize: 11pt
---

# About this rendering

This is a rendering of the first edition (1687) of Newton's *Philosophiæ
Naturalis Principia Mathematica*, made from the Newton Project TEI
transcriptions kept in this repository: the Definitions and their Scholium
(`docs/m1/NATP00075.xml`), the Axioms or Laws of Motion (`NATP00076.xml`) and
Book I (`NATP00077.xml`). It covers the Definitions, the Laws with their
Corollaries and Scholium, Book I Section I (Lemmas I–XI and the Scholium), and
Book I Section II through Proposition IV and its Scholium. Propositions V–X,
which close Section II, are not included.

Every item keeps Newton's number, order and concepts. Statements are put into
modern mathematical language; proofs follow Newton's steps and add none.
Where a modern formula helps, it follows Newton's statement under *In modern
terms*. Newton's figures are not reproduced; the letters refer to them, and
the descriptions are enough to redraw them. Square brackets mark the few notes
added for a modern reader. Long physical or historical explanations are
condensed, in Newton's order.

The changes of the second edition (1713) and the third (1726) follow each
item, marked **1713** and **1726**. They come from the Newton Project TEI of
the 1713 Definitions, Laws and Book I (`NATP00080`–`NATP00082`, in this
repository) and of the 1726 Definitions, Laws and Book I (`NATP00085`–`NATP00087`,
in `docs/m4`). The three editions were aligned paragraph by
paragraph; changes of spelling, punctuation and abbreviation are omitted, and
only changes of content or of mathematical language are given. A summary of
the pattern follows.

**Vocabulary.**

| Newton | Modern meaning |
| --- | --- |
| ratio of equality; *ultimately equal* | $X/Y \to 1$ in the stated limit |
| ultimate ratio of vanishing quantities | $\lim X/Y$ as $X, Y \to 0$ |
| first ratio of nascent quantities | $\lim X/Y$ as $X, Y$ start from $0$ |
| duplicate, triplicate ratio | ratio of squares, of cubes |
| subduplicate, sesquiplicate ratio | ratio of square roots, of $3/2$ powers |
| $A$ *applied to* $B$ | $A/B$ |
| *componendo* | summing proportional terms |
| *in consequentia* | in the direction of motion |

Bold letters are vectors; $\times$ is the planar cross product
$\mathbf a \times \mathbf b = a_1 b_2 - a_2 b_1$.

## How the editions differ

*1713, the limiting arguments are tightened.* Lemma I now says that the
quantities actually come nearer than any given difference before the end of
the finite time. Lemma VI gets a new proof from the continuity of the
curvature. The proofs of Lemmas VII–IX enlarge the vanishing figure so that its
lines stay finite while the original shrinks.

*1713, regularity premises enter the statements.* Lemma X, which assumed a
"regular" force, now assumes a finite force, either constant or continually
increasing or decreasing. Lemma XI is restricted to curves with finite
curvature at the point of contact.

*1713, the sagitta becomes the measure of force.* Lemma XI gains corollaries on
sagittas; Proposition I gains six corollaries measuring force by the sagitta
of arcs described in equal times; Proposition IV is proved anew through the
versed sines of those arcs, and its Scholium compares centripetal force with
gravity through the new Corollary IX.

*1713, the language of proportion is defined, and an error is corrected.* A new
Scholium after Lemma X states what "A is as B directly and C inversely" means,
and Lemma XI defines the sesquiplicate ratio. Proposition IV's Corollary 6 is
corrected and generalized to any power of the radius.

*1713, the Definitions and Laws.* Definition V gains a long explanation (the
sling, the projectile fired from a mountain, the Moon, and the inverse
problems of mathematics). Corollary I of the Laws specifies impulses impressed
at one place, and Law III is extended explicitly to attractions, with a new
argument for the mutual gravity of the parts of the Earth.

*1726, products and quotients give way to compound ratios.* Where 1713 said
"multiplied into" or "applied to", 1726 often says "jointly" or "in the ratio
compounded of" (Definition VIII's explanation, Proposition IV's Corollaries 1
and 2, the reflection argument after Proposition IV). The Scholium to the Laws
gains an explanation of Galileo's results by equal impulses in equal particles
of time.

# Definitions

**Definition I.** *The quantity of matter is its measure, arising from its
density and its volume jointly.*

In modern terms: $m \propto \rho V$.

Air of double density in double the space is quadruple; likewise snow or
powders condensed by compression or melting, and all bodies condensed by any
cause. A medium freely pervading the interstices of the parts, if there is
one, is disregarded. This quantity is meant below by *body* or *mass*. It is
known through each body's weight, to which it is proportional, as very
accurate pendulum experiments show (shown later).

> **1713.** The example adds: in triple the space, sextuple.

**Definition II.** *The quantity of motion is its measure, arising from the
velocity and the quantity of matter jointly.*

In modern terms: $\mathbf p = m \mathbf v$.

The motion of the whole is the sum of the motions of the parts; a body twice
as large with equal velocity has double the motion, and with double velocity
quadruple.

**Definition III.** *The inherent force of matter (vis insita) is a power of
resisting, by which every body, as far as it can, perseveres in its state of
rest or of uniform motion in a straight line.*

It is always proportional to the body and differs from the inertia of mass
only in the way it is conceived; hence it may be called the *force of
inertia*. A body exerts it only when another force impressed on it changes its
state. The exertion is, from different points of view, *resistance* (the body
resists the impressed force to keep its state) and *impetus* (the body,
yielding with difficulty to an obstacle, tries to change the obstacle's
state). Common usage gives resistance to bodies at rest and impetus to moving
ones; but rest and motion, as commonly conceived, differ only relatively.

**Definition IV.** *Impressed force is an action exerted on a body to change
its state of rest or of uniform motion in a straight line.*

It consists in the action alone and does not remain in the body afterwards;
the body perseveres in any new state by the force of inertia alone. Impressed
force has various origins: percussion, pressure, centripetal force.

**Definition V.** *Centripetal force is that by which a body is drawn,
impelled, or in any way tends toward some point as to a centre.*

> **1713.** *Bodies* (plural) are drawn, impelled or tend toward the point
> *from all sides*.

Examples: gravity, toward the centre of the Earth; magnetic force, by which
iron seeks a magnet; and the force, whatever it is, by which the planets are
continually drawn back from rectilinear motions and made to revolve in curved
lines. Its quantity is of three kinds: absolute, accelerative and motive.

> **1713.** The explanation is much expanded. A stone whirled in a sling
> endeavours to leave the hand, stretches the sling the more strongly the
> faster it revolves, and flies off when released; the contrary force by
> which the sling keeps drawing the stone back toward the hand, the centre of
> the orbit, is called centripetal. The same holds for all bodies moving in
> orbits: without a contrary force they would go off in straight lines with
> uniform motion. A projectile without gravity would go off in a straight line
> into the heavens; gravity bends it continually toward the Earth, more or
> less according to its gravity and velocity. A lead ball fired horizontally
> from a mountain top that lands two miles away would, with double or tenfold
> velocity, go about twice or ten times as far (air resistance removed); by
> increasing the velocity, the distance could be increased at will and the
> curvature of its path decreased, so that it would land ten, thirty or ninety
> degrees away, or go round the whole Earth before falling, or never fall and
> go off into the heavens. In the same way the Moon, by gravity or some other
> force urging it toward the Earth, can be drawn continually from its
> rectilinear course and bent into its orbit; with too small a force it would
> not be bent enough, with too great a force too much. It is for
> mathematicians to find the force that keeps a body exactly in a given orbit
> with a given velocity, and conversely to find the curved path into which a
> body leaving a given place with a given velocity is bent by a given force.
>
> **1726.** "The less its gravity *for its quantity of matter*", and the last
> alternative reads simply "or go off into the heavens".

**Definition VI.** *The absolute quantity of a centripetal force is its
measure, greater or less according to the efficacy of the cause propagating it
from the centre through the surrounding regions.*

For instance, magnetic power is greater in one magnet and less in another.

> **1713.** "according to the size of the magnet or the intensity of its
> power".

**Definition VII.** *The accelerative quantity of a centripetal force is its
measure proportional to the velocity it generates in a given time.*

In modern terms: at a given place, $a \propto \Delta v$ for a given
$\Delta t$.

The same magnet acts more strongly at a smaller distance; gravity is greater in
valleys and less on high mountain tops (pendulum experiments), and less still
at greater distances from the Earth (shown later). At equal distances it is
the same on all sides, because all falling bodies, heavy or light, large or
small, are equally accelerated once air resistance is removed.

**Definition VIII.** *The motive quantity of a centripetal force is its
measure proportional to the motion it generates in a given time.*

In modern terms: $F \propto \Delta p$ for a given $\Delta t$.

Weight is greater in a greater body and less in a smaller; in the same body,
greater near the Earth and less in the heavens. This quantity is the
centripetency of the whole body, its propensity toward the centre, its
weight; it is always known by the equal and contrary force that can prevent
the body's descent.

These quantities may be called briefly *absolute*, *accelerative* and
*motive forces*, and referred respectively to the centre, to the place of the
body, and to the body. The motive force belongs to the body as the endeavour
of the whole toward the centre, compounded of the endeavours of all its parts;
the accelerative force belongs to the place, as an efficacy diffused from the
centre through each surrounding place to move the bodies there; the absolute
force belongs to the centre, as endowed with some cause without which motive
forces are not propagated, whether that cause is a central body or something
else that does not appear. The concept is mathematical only; physical causes
and seats of forces are not considered here.

Hence accelerative force is to motive force as velocity is to motion: the
quantity of motion is velocity times quantity of matter, and motive force is
accelerative force times the same quantity of matter.

In modern terms: $F = m a$ (as a proportionality).

> **1726.** Motive force arises from the accelerative force *and* the quantity
> of matter *jointly*, and weight is as the body and the accelerative gravity
> *jointly*, where 1687 and 1713 say "multiplied into".

The sum of the actions of the accelerative force on the single particles of a
body is the motive force of the whole. Near the Earth's surface, where
accelerative gravity is the same in all bodies, weight is as the body; where
accelerative gravity is smaller, weight decreases in proportion and is always
as the body times accelerative gravity. Where accelerative gravity is half as
large, a body half or a third as large weighs four or six times less.

Attractions and impulses are called accelerative and motive in the same
sense. The words attraction, impulse or propensity toward a centre are used
indifferently, the forces being considered mathematically and not physically.
The reader should not take them to define a kind or mode of action or a
physical cause, nor to attribute forces truly and physically to centres, which
are mathematical points.

## Scholium

Time, space, place and motion are not defined, being well known to all. But
the common understanding conceives them only through their relation to
sensible things, which breeds prejudices; to remove these, each is divided
into absolute and relative, true and apparent, mathematical and common.

I. *Absolute, true and mathematical time*, of itself and by its nature without
relation to anything external, flows equably, and is also called *duration*.
*Relative, apparent and common time* is any sensible, external measure of
duration by motion, accurate or not, used in place of true time: an hour, a
day, a month, a year.

II. *Absolute space*, by its nature without relation to anything external,
remains always similar and immovable. *Relative space* is any movable measure
or dimension of this space, determined by our senses through its position
relative to bodies and commonly taken for immovable space, such as the
dimension of a subterranean, aerial or celestial space fixed by its position
relative to the Earth. Absolute and relative space are the same in kind and
magnitude but do not always remain numerically the same: if the Earth moves,
the space of our air, always the same relative to the Earth, is now one part
of absolute space and now another.

III. *Place* is the part of space a body occupies, absolute or relative
according to the space. It is a part of space, not the position of the body or
its surrounding surface: equal solids always have equal places, while their
surfaces, for dissimilar figures, are mostly unequal; positions, properly
speaking, have no quantity and are affections of places rather than places.
Since the motion of the whole equals the sum of the motions of the parts, the
place of the whole equals the sum of the places of the parts, and is internal
and in the whole body.

IV. *Absolute motion* is the translation of a body from one absolute place to
another; *relative motion*, from one relative place to another. In a ship
under sail, a body's relative place is the region of the ship it occupies,
which moves with the ship; relative rest is remaining in that region; true
rest is remaining in the same part of immovable space. If the Earth truly
rests, a body resting relative to the ship moves truly with the ship's
velocity on the Earth; if the Earth also moves, the true motion arises partly
from the Earth's true motion in immovable space and partly from the ship's
relative motion; and if the body moves within the ship, from all three.
Example: if the Earth's surface there moves truly east with 10010 parts of
velocity, the ship west with 10 parts, and a sailor walks east with 1 part,
the sailor moves truly east with 10001 parts and relatively to the Earth west
with 9 parts.

Absolute time is distinguished from relative time in astronomy by the
equation of time: natural days are unequal, and astronomers correct this to
measure celestial motions by a truer time. Perhaps no equable motion exists by
which time can be measured exactly; all motions can speed up or slow down, but
the flow of absolute time cannot change. Duration is the same whether motions
are fast, slow or absent. The need for the equation is shown by pendulum
clocks and by the eclipses of Jupiter's satellites.

As the order of the parts of time is immutable, so is the order of the parts
of space. Times and spaces are, as it were, the places of themselves and of
all things: all things are placed in time as to order of succession and in
space as to order of position. It is of their essence to be places, and for
primary places to move is absurd. These are absolute places, and only
translations from them are absolute motions.

These parts of space cannot be seen or distinguished by our senses, so
sensible measures are used instead: places are defined by positions and
distances from some body regarded as immovable, and motions estimated with
respect to those places. In human affairs this serves; in philosophy one must
abstract from the senses, since possibly no body truly rests to which places
and motions could be referred.

Absolute and relative rest and motion are distinguished by their properties,
causes and effects.

*Properties.* Bodies truly at rest rest among themselves; but since some body
far away, among or beyond the fixed stars, may rest absolutely while the
positions of bodies in our regions cannot tell us whether any of them keeps a
given position to it, true rest cannot be defined from their mutual
positions. Parts that keep given positions in their wholes share the wholes'
motions: the parts of a revolving body endeavour to recede from the axis, and
the impetus of a progressing body arises from the joint impetus of its parts.
Hence when surrounding bodies move, bodies at rest relative to them move too,
and true motion cannot be defined by translation from the neighbourhood of
bodies regarded as resting; those bodies must truly rest. Likewise, when a
place moves, what is in it moves with it; a body moving from a moving place
shares its place's motion. Every whole and absolute motion is compounded of
the motion of the body from its first place, of that place from its place, and
so on, until an immovable place is reached. Whole and absolute motions can
therefore be defined only by immovable places, and immovable places are only
those that keep given positions to each other from infinity to infinity,
which constitute immovable space.

*Causes.* True motion is neither generated nor changed except by forces
impressed on the moving body itself; relative motion can be generated or
changed without forces impressed on it, by forces impressed only on the bodies
of reference. True motion always changes under forces impressed on the moving
body; relative motion need not, if the same forces act on the bodies of
reference so as to keep the relative position.

*Effects.* The forces of receding from the axis of circular motion distinguish
absolute from relative motion: in purely relative circular motion they are
null, in true motion greater or less according to the quantity of motion. A
bucket hung by a long cord is turned until the cord is stiffly twisted, filled
with water, and released. At first the surface of the water is flat, as before
the motion; as the bucket gradually communicates its motion to the water, the
water recedes from the middle and rises at the sides, becoming concave, and
rises more as its motion grows, until it revolves in equal times with the
bucket and rests relative to it. The rise shows the endeavour to recede from
the axis, and by it the true and absolute circular motion of the water is
known and measured, quite contrary to the relative motion: at the start, when
the relative motion was greatest, there was no such endeavour and no true
circular motion.

Relative quantities are therefore not the quantities whose names they bear but
their sensible measures. Those who read these words in Scripture as the
measured quantities do it violence, and those who confuse true quantities with
their relations and common measures corrupt mathematics and philosophy.

To know the true motions of single bodies and distinguish them from apparent
ones is very difficult, because the parts of immovable space do not come
under the senses. But the matter is not hopeless: arguments are available
partly from apparent motions, which are differences of true motions, and
partly from forces, which are causes and effects of true motions. Two globes
joined by a cord at a given distance and revolving about their common centre
of gravity show, by the cord's tension, their endeavour to recede from the
axis, from which the quantity of circular motion can be computed. Impressing
equal forces on alternate faces to increase or decrease the motion, the
change in tension shows which faces must be pushed to increase the motion
most, namely the trailing faces, and hence the direction of the motion. In
this way the quantity and direction of the circular motion could be found
even in an immense vacuum with nothing external and sensible to compare. How
true motions are inferred from their causes, effects and apparent differences,
and conversely, is taught more fully in what follows; the treatise was
composed for this purpose.

# Axioms, or Laws of Motion

**Law I.** *Every body perseveres in its state of rest or of uniform motion in
a straight line, except insofar as it is compelled by impressed forces to
change that state.*

In modern terms: with no impressed force, $\mathbf v$ is constant.

Projectiles persevere in their motions except as air resistance retards them
and gravity impels them downward. A top, whose cohering parts continually draw
each other back from rectilinear motions, keeps spinning except as the air
retards it. The greater bodies of planets and comets keep their progressive
and circular motions longer in less resisting spaces.

**Law II.** *The change of motion is proportional to the motive force
impressed, and takes place along the straight line in which that force is
impressed.*

In modern terms: $\Delta \mathbf p \propto \mathbf J$, with $\mathbf J$ the
impressed motive force (an impulse) and $\Delta \mathbf p$ parallel to it.

If a force generates some motion, double the force generates double the
motion and triple the force triple, whether impressed all at once or
gradually and successively. This motion, always directed with the generating
force, is added to the body's earlier motion if they conspire, subtracted if
contrary, and compounded obliquely if oblique, according to both directions.

**Law III.** *To every action there is always an equal and contrary reaction;
or, the mutual actions of two bodies on each other are always equal and
directed to contrary parts.*

In modern terms: $\mathbf F_{AB} = -\mathbf F_{BA}$.

Whatever presses or pulls another is pressed or pulled by it as much. If you
press a stone with your finger, the finger is pressed by the stone. If a horse
pulls a stone tied to a rope, the horse is pulled back equally toward the
stone: the rope, stretched both ways, urges each toward the other with the
same endeavour to relax. If a body striking another changes its motion, it
undergoes the same change of its own motion in the contrary direction. The
equal changes are of motions, not velocities (for bodies not otherwise
impeded); the changes of velocities, also contrary, are inversely
proportional to the bodies.

In modern terms: $m_A \Delta \mathbf v_A = -m_B \Delta \mathbf v_B$.

> **1713.** The explanation ends: this law also holds in attractions, as will be
> proved in the next Scholium.

**Corollary I.** *A body acted on by two forces jointly describes the diagonal
of a parallelogram in the same time in which it would describe the sides by
the forces separately.*

*Proof.* Let the body in a given time be carried by force $M$ alone from $A$
to $B$, and by force $N$ alone from $A$ to $C$; complete the parallelogram
$ABDC$. Since $N$ acts along $AC$, parallel to $BD$, it does not change the
velocity of approach to the line $BD$ generated by $M$. So the body reaches
the line $BD$ in the same time whether $N$ acts or not, and at the end of that
time it is somewhere on $BD$. By the same argument it is somewhere on $CD$, so
it is at their intersection $D$.

In modern terms: $\overrightarrow{AD} = \overrightarrow{AB} + \overrightarrow{AC}$.

> **1713.** The forces $M$ and $N$ are *impressed at the place $A$*, the motion
> from $A$ to $B$ is *uniform*, the invariance of the velocity of approach is
> *by Law II*, and the proof ends: the body proceeds in a straight line from
> $A$ to $D$ by Law I. The corollary is thereby stated for impulses given at
> one place, followed by inertial motion.

**Corollary II.** *Hence the composition of a direct force $AD$ out of any
oblique forces $AB$ and $BD$, and conversely the resolution of any direct force
$AD$ into any oblique forces $AB$ and $BD$.* This is abundantly confirmed by
mechanics.

Weights $A$ and $P$ hung by threads from unequal spokes $OM$, $ON$ of a wheel
balance when they are inversely as the perpendicular distances $OK$, $OL$ of
their threads from the centre (the property of the balance, the lever and the
wheel and axle): resolving the weight $A$, represented by $AD$, into $AC$
along the spoke $OD$, which does nothing to turn the wheel, and $DC$
perpendicular to it, gives $P : A = DC : DA = OK : OL$ by the similar
triangles $ADC$, $DOK$. A weight $p$ resting partly on an inclined plane and
partly hung by a thread resolves likewise, which gives the tensions of oblique
threads, the forces of the wedge between the faces of a split body, of the
mallet, and of the screw, which is a wedge driven by a lever. From these
follow the forces of all machines built from wheels, drums, pulleys, levers,
taut strings and weights, and of the muscles moving the bones of animals.

**Corollary III.** *The quantity of motion, obtained by taking the sum of the
motions directed to the same side and the difference of those directed to
contrary sides, is not changed by the actions of bodies on each other.*

In modern terms: $\sum_i m_i \mathbf v_i$ is invariant under mutual
interactions.

*Proof.* Action and reaction are equal (Law III), so by Law II they produce
equal changes of motion toward contrary sides. If the motions are to the same
side, whatever is added to the motion of the body fleeing is taken from the
body pursuing, so the sum stays the same; if the bodies meet, equal amounts
are taken from both, so the difference stays the same.

Example: a sphere $A$ three times as large as a sphere $B$ moves with 2 parts
of velocity, and $B$ follows on the same line with 10, so the motions are 6
and 10, total 16. Whatever $A$ gains in the collision, 3, 4 or 5 parts, $B$
loses, leaving $A$ with 9, 10 or 11 and $B$ with 7, 6 or 5; if $A$ gains 9 to
12, $B$ continues with 1, stops, or recoils with 1 or 2. The sum of conspiring
motions or the difference of contrary ones is always 16. For non-spherical
bodies or oblique collisions, find the plane touching both at the point of
contact, resolve each motion (Corollary II) into components perpendicular and
parallel to that plane, keep the parallel components, and give the
perpendicular components equal and contrary changes so that the sum or
difference is unchanged. Collisions also produce rotations about the bodies'
own centres, which are not considered here.

**Corollary IV.** *The common centre of gravity of two or more bodies does not
change its state of motion or rest by the actions of the bodies among
themselves; therefore the common centre of gravity of all bodies acting on
each other (external actions and impediments excluded) either rests or moves
uniformly in a straight line.*

In modern terms: with no external forces,
$\mathbf R = \sum_i m_i \mathbf r_i / \sum_i m_i$ satisfies
$\ddot{\mathbf R} = 0$.

> **1713.** "The common centre of gravity *of two or more bodies*". The proof
> treats points moving in one plane and adds that the same holds if their
> motions are not in one plane. **1726** cites Lemma XXIII *and its corollary*.

*Proof.* If two points move uniformly in straight lines and their distance is
divided in a given ratio, the dividing point rests or moves uniformly in a
straight line (proved later in Lemma XXIII for the plane; the same holds in
space). So if any number of bodies move uniformly in straight lines, the
common centre of any two rests or moves uniformly, since it divides in a given
ratio the line joining their centres; likewise the common centre of these two
and any third, and so on to infinity. Hence in a system of bodies free of
mutual actions and of all external forces, each moving uniformly in a straight
line, the common centre of all rests or moves uniformly in a straight line.
Further, for two bodies acting on each other, their distances from the common
centre are inversely as the bodies, so their relative motions of approach to
or recession from the centre are equal; the centre is neither advanced nor
retarded by equal changes of motion in contrary directions, that is, by the
mutual actions. In a system of many bodies, the common centre of any two
acting on each other keeps its state, and the common centre of the rest is
unaffected by that action; the distance between these two centres is divided
by the common centre of all inversely as the total bodies whose centres they
are; so the common centre of all keeps its state. All mutual actions are
between pairs of bodies or compounded of such, so the common centre of all is
never changed by them.

**Corollary V.** *The motions of bodies contained in a given space are the same
among themselves whether that space rests or moves uniformly in a straight
line without circular motion.*

*Proof.* The differences of motions toward the same side and the sums of
motions toward contrary sides are the same at the start in both cases (by
hypothesis), and from them arise the collisions and impulses by which the
bodies strike each other; so by Law II the effects are equal in both cases,
and the motions among themselves stay equal. A clear experiment confirms it:
all motions behave the same in a ship at rest or moving uniformly in a
straight line.

In modern terms: the laws are invariant under
$\mathbf r' = \mathbf r - \mathbf u t$, $t' = t$, with $\mathbf u$ constant.

**Corollary VI.** *If bodies move in any way among themselves and are urged
along parallel lines by equal accelerative forces, they all continue to move
among themselves as if those forces did not act.*

*Proof.* The forces, acting equally (in proportion to the quantities of the
bodies) along parallel lines, move all bodies equally as to velocity (Law II),
and so never change their positions and motions among themselves.

## Scholium

These principles are received by mathematicians and confirmed by many
experiments. By the first two Laws and Corollaries Galileo found that the
descent of heavy bodies is in the duplicate ratio of the time and that the
motion of projectiles is in a parabola, as experiment agrees except for the
small retardation by air. On the same Laws and Corollaries depend the
demonstrations about the times of oscillating pendulums, confirmed daily by
clocks. From these and the third Law, Wren, Wallis and Huygens independently
found the rules of the collision and reflection of two bodies and communicated
them to the Royal Society at about the same time, in full agreement. Wren
confirmed them by an experiment with pendulums before the Society, and
Mariotte soon devoted a whole book to it. For exact agreement one must allow
for the air's resistance and for the elastic force of the colliding bodies.
Newton describes how to correct a pendulum-collision experiment for air
resistance by measuring the loss over swings, and reports his own trials with
bodies of various hardness, including tightly wound wool balls: the bodies
separate with a relative velocity in a given ratio to the relative velocity of
approach, and the rules hold for soft bodies as well as hard ones.

> **1713.** The description of the pendulum experiment is made exact: the arcs
> are marked so that $RS = TV$ and $RS : ST = 3 : 2$, and the equal changes of
> motion are stated for the bodies.
>
> **1726.** A passage is inserted after the mention of Galileo. Uniform gravity,
> acting equally in equal particles of time, impresses equal forces on a
> falling body and generates equal velocities; in the whole time it impresses
> the whole force and generates the whole velocity, proportional to the time;
> and the spaces described in proportional times are as the velocities and
> times jointly, that is, in the duplicate ratio of the times. For a body
> thrown upward, uniform gravity impresses forces and takes away velocities
> proportional to the times; the times of ascent to the greatest heights are as
> the velocities to be taken away, and the heights as the velocities and times
> jointly, or in the duplicate ratio of the velocities. A body thrown along any
> straight line compounds the motion from the projection with the motion from
> gravity: if by projection alone it would describe $AB$ in a given time and
> by falling alone the height $AC$, completing the parallelogram $ABDC$ puts
> it at $D$ at the end of the time, and the curve $AED$ it describes is a
> parabola touching $AB$ at $A$ whose ordinate $BD$ is as $AB^2$.

For attractions, suppose two bodies $A$ and $B$ attract each other and an
obstacle is placed between them. If $A$ were drawn toward $B$ more than $B$
toward $A$, the obstacle would be pressed more by $A$ than by $B$ and would not
stay in equilibrium; the stronger pressure would make the system of the two
bodies and the obstacle move toward $B$ and, accelerating forever in free
space, go off to infinity, which is absurd and contrary to the first Law. So
the bodies press the obstacle equally and attract each other equally. Newton
tried this with a lodestone and iron floating in separate vessels on still
water: neither pushed the other, and they came to rest in equilibrium.

> **1713.** A new paragraph: gravity between the Earth and its parts is mutual.
> Cut the Earth by any plane $EG$ into parts $EGF$ and $EGI$. Cut the larger
> part $EGI$ by a parallel plane $HK$ into $EGKH$ and $HKI$, with $HKI$ equal
> to $EGF$. The middle part $EGKH$ inclines by its own weight toward neither
> extreme part and rests between them in equilibrium; the extreme part $HKI$
> presses with its whole weight on the middle part and urges it toward
> $EGF$. So the force with which $EGI$ tends toward $EGF$ equals the weight of
> $HKI$, that is, of $EGF$, and the two parts weigh equally on each other.
> Otherwise the whole Earth, floating in the free aether, would yield to the
> greater weight and go off to infinity.

As bodies are equipollent in collision when their velocities are inversely as
their inherent forces, so in mechanical instruments agents are equipollent and
sustain each other when their velocities, estimated along the forces, are
inversely as the forces. So for the balance, the pulley, trains of wheels, the
screw and the wedge. The use of machines lies only in increasing force by
diminishing velocity and conversely; this solves, for every suitable
instrument, the problem of moving a given weight by a given force. If the
action of the agent is estimated by its force and velocity jointly, and the
reaction of the resistance by the velocities of its parts and their forces of
resisting (from friction, cohesion, weight and acceleration), action and
reaction are always equal in every use of instruments. Mechanics is not the
subject here; this only shows how widely and how surely the third Law holds.

# Book I: On the Motion of Bodies

## Section I. On the method of first and last ratios, by whose help what follows is demonstrated

**Lemma I.** *Quantities, and also ratios of quantities, which in a given
finite time tend constantly to equality, and before the end of that time
approach nearer to each other than by any given difference, become ultimately
equal.*

In modern terms: if $X(t), Y(t)$ on $[0, T)$ approach each other so that for
every $\varepsilon > 0$ there is $t < T$ beyond which $|X - Y| < \varepsilon$,
then their ultimate values at $T$ are equal.

*Proof.* If not, let their ultimate difference be $D > 0$. Then they cannot
approach nearer to equality than by the given difference $D$, contrary to the
hypothesis.

> **1713.** The statement reads "in *any finite* time" and replaces "can
> approach nearer" by "*before the end of that time* approach nearer than by
> any given difference": the approach is asserted to happen within the time,
> not merely to be possible. The proof begins "If you deny it, let them be
> ultimately unequal".

**Lemma II.** *If in any figure $AacE$, bounded by the straight lines $Aa$,
$AE$ and the curve $acE$, any number of parallelograms $Ab$, $Bc$, $Cd$, … are
inscribed on equal bases $AB$, $BC$, $CD$, … with sides $Bb$, $Cc$, $Dd$, …
parallel to the side $Aa$, and the parallelograms $aKbl$, $bLcm$, $cMdn$, …
are completed; and if then the width of the parallelograms is diminished and
their number increased indefinitely: the ultimate ratios which the inscribed
figure $AKbLcMdD$, the circumscribed figure $AalbmcndoE$ and the curvilinear
figure $AabcdE$ have to one another are ratios of equality.*

In modern terms: for the region under a monotone curve over $[a, b]$, with
lower and upper step sums $L_n$, $U_n$ on $n$ equal subintervals and area
$\mathcal A$, the ratios $L_n : U_n : \mathcal A$ tend to $1 : 1 : 1$.
[In Newton's figure the curve is monotone, and the curvilinear figure's area
is taken as given.]

*Proof.* The difference of the inscribed and circumscribed figures is the sum
of the parallelograms $Kl + Lm + Mn + Do$, that is (the bases being equal) the
rectangle under one base $Kb$ and the sum of the heights $Aa$, the rectangle
$ABla$. Since its width $AB$ is diminished indefinitely, it becomes less than
any given rectangle. So by Lemma I the inscribed and circumscribed figures,
and still more the curvilinear figure between them, become ultimately equal.

In modern terms: $U_n - L_n = \Delta x \,(f(a) - f(b)) \to 0$.

**Lemma III.** *The same ultimate ratios are also ratios of equality when the
widths $AB$, $BC$, $CD$, … of the parallelograms are unequal and all are
diminished indefinitely.*

*Proof.* Let $AF$ equal the greatest width and complete the parallelogram
$FAaf$. It is greater than the difference of the inscribed and circumscribed
figures, and as its width $AF$ is diminished indefinitely it becomes less than
any given rectangle.

In modern terms: $U - L \le \max_i \Delta x_i \,(f(a) - f(b)) \to 0$ as the
mesh tends to $0$.

*Corollary 1.* Hence the ultimate sum of the vanishing parallelograms
coincides in every part with the curvilinear figure.

*Corollary 2.* Still more does the rectilinear figure bounded by the chords
$ab$, $bc$, $cd$, … of the vanishing arcs coincide ultimately with the
curvilinear figure.

*Corollary 3.* So does the rectilinear figure circumscribed by the tangents of
the same arcs.

*Corollary 4.* And therefore these ultimate figures (as to their perimeters
$acE$) are not rectilinear, but curvilinear limits of rectilinear figures.

**Lemma IV.** *If in two figures $AacE$, $PprT$ two series of parallelograms are
inscribed (as above), equal in number, and when the widths are diminished
indefinitely the ultimate ratios of the parallelograms of one figure to those
of the other, each to each, are the same: the two figures are to each other in
that same ratio.*

*Proof.* As the parallelograms are to each other one by one, so (*componendo*)
is the sum of all to the sum of all, and so is figure to figure, each figure
being to its sum in the ratio of equality (Lemma III).

In modern terms: if $a_i / b_i \to r$ for all $i$ as the mesh tends to $0$,
then $\lim \sum a_i / \lim \sum b_i = r$. [The convergence is tacitly uniform
in $i$.]

*Corollary.* Hence if two quantities of any kind are divided into the same
number of parts, and those parts, as their number is increased and their
magnitude diminished indefinitely, have a given ratio to each other, first to
first, second to second and so on in order, the wholes are to each other in
that given ratio. For if parallelograms are taken in the figures of this Lemma
proportional to the parts, the sums of the parts are always as the sums of the
parallelograms, and so, in the limit, in the ultimate ratio of parallelogram
to parallelogram, that is (by hypothesis) of part to part.

**Lemma V.** *All corresponding sides of similar figures, curvilinear as well as
rectilinear, are proportional, and the areas are in the duplicate ratio of the
sides.*

In modern terms: under a similarity of ratio $\lambda$, lengths scale by
$\lambda$ and areas by $\lambda^2$.

**Lemma VI.** *If any arc $AB$, given in position, is subtended by its chord
$AB$, and at some point $A$ in the middle of a continuous curvature it is
touched by a straight line $AD$ produced both ways; and if then the points $A$
and $B$ approach each other and coincide: the angle $BAD$ contained by the
chord and the tangent is diminished indefinitely and ultimately vanishes.*

In modern terms: at a point where the curve has a tangent, the direction of
the chord $AB$ tends to the direction of the tangent as $B \to A$.

*Proof.* Produce $AB$ to $b$ and $AD$ to $d$. As $A$ and $B$ coincide, no part
$AB$ of the line $Ab$ lies any longer inside the curve, so the line $Ab$ either
coincides with the tangent $Ad$ or passes between the tangent and the curve.
The latter is contrary to the nature of curvature, so the former holds.

> **1713.** A new proof replaces this one: if the angle does not vanish, the arc
> $AB$ will contain with the tangent $AD$ an angle equal to a rectilinear
> angle, and so the curvature at $A$ will not be continuous, contrary to the
> hypothesis. **1726** names the arc $ACB$, through an intermediate point $C$,
> here and in Lemmas VII and VIII.

**Lemma VII.** *Under the same suppositions, the ultimate ratio of the arc, the
chord and the tangent to each other is the ratio of equality.*

*Proof.* Produce $AB$ and $AD$ to $b$ and $d$, draw $bd$ parallel to the secant
$BD$, and let the arc $Ab$ be similar to the arc $AB$. As $A$ and $B$
coincide, the angle $dAb$ vanishes (Lemma VI), so the straight lines $Ab$,
$Ad$ and the arc between them coincide and are equal. Hence $AB$, $AD$ and the
arc $AB$, always proportional to these, ultimately have the ratio of
equality.

In modern terms: $\text{arc}\,AB / \text{chord}\,AB \to 1$ and
$AD / \text{chord}\,AB \to 1$ as $B \to A$.

> **1713.** The proof is reorganized as a rescaling: while $B$ approaches $A$,
> the lines $AB$, $AD$ are imagined always produced to *distant* points $b$,
> $d$, so that the enlarged lines $Ab$, $Ad$ and the arc between them stay
> *always finite* while the angle $dAb$ vanishes; they coincide and are equal,
> and the proportional small lines $AB$, $AD$ and the arc $AB$ *vanish* with
> ultimate ratio of equality.

*Corollary 1.* If through $B$ a line $BF$ is drawn parallel to the tangent,
meeting any straight line $AF$ through $A$ in $F$, then $BF$ ultimately has
the ratio of equality to the vanishing arc $AB$, because, completing the
parallelogram $AFBD$, it always has that ratio to $AD$.

*Corollary 2.* If through $B$ and $A$ more lines $BE$, $BD$, $AF$, $AG$ are
drawn cutting the tangent $AD$ and its parallel $BF$, the ultimate ratio of
all the abscissas $AD$, $AE$, $BF$, $BG$, and of the chord and arc $AB$, to
each other is the ratio of equality.

*Corollary 3.* Therefore all these lines may be used for one another in any
argument about ultimate ratios.

**Lemma VIII.** *If the given straight lines $AR$, $BR$ form with the arc $AB$,
the chord $AB$ and the tangent $AD$ three triangles $RAB$, $RAB$, $RAD$ (the
first with the arc as a side), and then the points $A$ and $B$ approach each
other: the ultimate form of the vanishing triangles is that of similarity, and
their ultimate ratio is that of equality.*

*Proof.* Produce $AB$, $AD$, $AR$ to $b$, $d$, $r$; draw $rbd$ parallel to $RD$,
and the arc $Ab$ similar to the arc $AB$. As $A$ and $B$ coincide, the angle
$bAd$ vanishes, so the three triangles $rAb$, $rAb$, $rAd$ coincide and are
therefore similar and equal. Hence $RAB$, $RAB$, $RAD$, always similar and
proportional to these, become ultimately similar and equal to each other.

> **1713.** The same rescaling: $AB$, $AD$, $AR$ are always produced to distant
> points $b$, $d$, $r$, and the three triangles $rAb$, $rAb$, $rAd$ stay
> *always finite* while they coincide.

*Corollary.* Hence those triangles may be used for one another in any
argument about ultimate ratios.

**Lemma IX.** *If a straight line $AE$ and a curve $AC$, given in position, cut
each other at a given angle $A$, and to that line, at another given angle,
ordinates $BD$, $EC$ are applied meeting the curve in $B$, $C$, and then the
points $B$, $C$ approach the point $A$: the areas of the triangles $ADB$,
$AEC$ will be ultimately to each other in the duplicate ratio of the sides.*

In modern terms: $\text{area}(ADB) / \text{area}(AEC) \to (AD/AE)^2$ as
$B, C \to A$, the triangles having the curved side.

*Proof.* On $AD$ produced take $Ad$, $Ae$ proportional to $AD$, $AE$, and
erect ordinates $db$, $ec$ parallel and proportional to $DB$, $EC$. Produce
$AC$ to $c$, draw the curve $Abc$ similar to $ABC$, and the straight line $Ag$
touching both curves at $A$ and cutting the ordinates in $F$, $G$, $f$, $g$.
Then let $B$ and $C$ coincide with $A$: the angle $cAg$ vanishes, the
curvilinear areas $Abd$, $Ace$ coincide with the rectilinear $Afd$, $Age$, and
so (Lemma V) are in the duplicate ratio of the sides $Ad$, $Ae$. But the areas
$ABD$, $ACE$ are always proportional to these, and the sides $AD$, $AE$ to
these sides. So the areas $ABD$, $ACE$ are ultimately in the duplicate ratio of
the sides $AD$, $AE$.

> **1713.** The enlarged figure is again kept finite: while $B$, $C$ approach
> $A$, the line $AD$ is always produced to distant points $d$, $e$, and the
> points $B$, $C$ coalesce with $A$ *while the length $Ae$ stays fixed*.

**Lemma X.** *The spaces which a body describes, urged by any regular force,
are at the very beginning of the motion in the duplicate ratio of the times.*

> **1713.** *The spaces which a body describes, urged by any finite force,
> whether that force is determinate and immutable or is continually increased
> or continually decreased, are at the very beginning of the motion in the
> duplicate ratio of the times.* The 1687 "regular force" becomes a finite
> force that is constant or monotone; Corollaries 1 and 2 are reworded
> accordingly ("by any equal forces", "measured by the distances of the bodies
> from those places of the similar figures").

In modern terms: $s(t_1)/s(t_2) \to (t_1/t_2)^2$ as $t_1, t_2 \to 0$; that
is, $s(t) \sim c\, t^2$ at the start.

*Proof.* Represent the times by the lines $AD$, $AE$ and the velocities
generated by the ordinates $DB$, $EC$. The spaces described with these
velocities are as the areas $ABD$, $ACE$ described by these ordinates, that is,
at the very beginning of the motion (Lemma IX), in the duplicate ratio of the
times $AD$, $AE$.

In modern terms: $s(t) = \int_0^t v(\tau)\, d\tau$, the area under the
velocity graph, whose initial piece is the curvilinear triangle of Lemma IX.

*Corollary 1.* Hence the errors of bodies describing similar parts of similar
figures in proportional times, generated by equal forces similarly applied to
the bodies in those parts, and measured from the places of the figures which
the bodies would reach in the same proportional times without those forces,
are very nearly as the squares of the times in which they are generated.

*Corollary 2.* The errors generated by proportional forces similarly applied
are as the forces and the squares of the times jointly.

In modern terms: the deviation from the force-free path is
$\delta \approx \tfrac12 a\, t^2$, so $\delta \propto F t^2$ for a given
body.

> **1713.** Three new corollaries and a Scholium.
>
> *Corollary 3.* The same holds for any spaces that bodies describe under
> different forces: at the very beginning of the motion they are as the forces
> and the squares of the times jointly, $s \propto F t^2$.
>
> *Corollary 4.* So the forces are as the spaces described at the very
> beginning directly and the squares of the times inversely, $F \propto
> s/t^2$.
>
> *Corollary 5.* And the squares of the times are as the spaces directly and
> the forces inversely, $t^2 \propto s/F$.
>
> *Scholium.* When indeterminate quantities of different kinds are compared,
> and one is said to be as another directly or inversely, the meaning is that
> the first increases or decreases in the same ratio as the second or as its
> reciprocal. When one is said to be as two or more others directly or
> inversely, it increases or decreases in the ratio compounded of the ratios in
> which the others, or their reciprocals, increase or decrease. So "$A$ is as
> $B$ directly and $C$ directly and $D$ inversely" means that $A$ changes in
> the same ratio as $B \cdot C / D$, that is, $A$ and $BC/D$ are in a given
> ratio.

**Lemma XI.** *The vanishing subtense of the angle of contact is ultimately in
the duplicate ratio of the subtense of the conterminous arc.*

In modern terms: with $BD$ the distance from $B$ on the curve to the tangent
at $A$, measured in a fixed direction, $BD \propto AB^2$ ultimately; for
finite curvature $\kappa$, $BD \approx \tfrac12 \kappa\, AB^2$.

> **1713.** The statement is restricted: *in all curves having finite curvature
> at the point of contact*.

*Case 1.* Let the arc be $AB$, its tangent $AD$, the subtense $BD$ of the angle
of contact perpendicular to the tangent, and $AB$ the subtense of the arc.
Erect $AG$ perpendicular to the subtense $AB$ and $BG$ perpendicular to the
tangent $AD$, meeting in $G$. Then let the points $D$, $B$, $G$ go to $d$, $b$,
$g$, and let $I$ be the intersection of the lines $BG$, $AG$ ultimately formed
when $D$, $B$ reach $A$. The distance $GI$ can be made less than any assigned
length. By the nature of circles through $A$, $B$, $G$ and through $A$, $b$,
$g$, $AB^2 = AG \cdot BD$ and $Ab^2 = Ag \cdot bd$, so the ratio $AB^2 : Ab^2$
is compounded of $AG : Ag$ and $BD : bd$. Since $GI$ can be taken less than
any assigned length, the ratio $AG : Ag$ can differ from equality by less than
any assigned difference, and so $AB^2 : Ab^2$ can differ from $BD : bd$ by
less than any assigned difference. By Lemma I the ultimate ratio $AB^2 : Ab^2$
equals the ultimate ratio $BD : bd$.

*Case 2.* Let $BD$ be inclined to $AD$ at any given angle; the ultimate ratio
$BD : bd$ is the same as before, and so the same as $AB^2 : Ab^2$.

*Case 3.* Even if the angle $D$ is not given, the angles $D$, $d$ always tend to
equality and approach each other nearer than by any assigned difference, so
they are ultimately equal (Lemma I), and the lines $BD$, $bd$ are in the same
ratio as before.

> **1713.** Case 3 also covers the line $BD$ converging to a given point, or
> placed by any other law, provided the angles $D$, $d$ are placed by a common
> law.

*Corollary 1.* Since the tangents $AD$, $Ad$, the arcs $AB$, $Ab$ and their
sines $BC$, $bc$ become ultimately equal to the chords $AB$, $Ab$, their
squares too are ultimately as the subtenses $BD$, $bd$.

> **1713.** Two new corollaries follow, and the old Corollaries 2 and 3 become
> Corollaries 4 and 5.
>
> *Corollary 2.* Their squares are also ultimately as the sagittas of the arcs
> that bisect the chords and converge to a given point, for those sagittas
> are as the subtenses $BD$, $bd$.
>
> *Corollary 3.* Hence the sagitta is in the duplicate ratio of the time in
> which a body describes the arc with a given velocity.

*Corollary 2.* The rectilinear triangles $ADB$, $Adb$ are ultimately in the
triplicate ratio of the sides $AD$, $Ad$, and in the sesquiplicate ratio of
the sides $DB$, $db$, being in the ratio compounded of $AD$ and $DB$, $Ad$ and
$db$. Likewise the triangles $ABC$, $Abc$ are ultimately in the triplicate
ratio of the sides $BC$, $bc$.

> **1713** (now Corollary 4) adds a definition: the sesquiplicate ratio is the
> subduplicate of the triplicate, compounded of the simple and the
> subduplicate ratio, which others call sesquialteral; that is, the ratio of
> $3/2$ powers.

*Corollary 3.* Since $DB$, $db$ are ultimately parallel and in the duplicate
ratio of $AD$, $Ad$, the ultimate curvilinear areas $ADB$, $Adb$ are (by the
nature of the parabola) two thirds of the rectilinear triangles $ADB$, $Adb$,
and the segments $AB$, $Ab$ one third of the same triangles. Hence these areas
and segments are in the triplicate ratio both of the tangents $AD$, $Ad$ and of
the chords and arcs $AB$, $Ab$.

### Scholium

In all this we suppose the angle of contact neither infinitely greater than
the angles of contact which circles make with their tangents, nor infinitely
less; that is, the curvature at the point $A$ neither infinitely small nor
infinitely great, or the interval $AI$ of finite magnitude. For $DB$ can be
taken as $AD^3$, in which case no circle can be drawn through $A$ between the
tangent $AD$ and the curve $AB$, and the angle of contact is infinitely less
than circular ones. By a similar argument, taking $DB$ successively as $AD^4$,
$AD^5$, $AD^6$, $AD^7$, … gives a series of angles of contact going on to
infinity, each infinitely less than the one before. Taking $DB$ successively
as $AD^2$, $AD^{3/2}$, $AD^{4/3}$, $AD^{5/4}$, $AD^{6/5}$, $AD^{7/6}$, … gives
another infinite series, the first of the same kind as the circular ones, the
second infinitely greater, and each infinitely greater than the one before.
Between any two of these angles a series going on to infinity both ways can be
inserted, each infinitely greater than the one before: for instance, between
the terms $AD^2$ and $AD^3$ the series $AD^{13/6}$, $AD^{11/5}$, $AD^{9/4}$,
$AD^{7/3}$, $AD^{5/2}$, $AD^{8/3}$, $AD^{11/4}$, $AD^{14/5}$, $AD^{17/6}$, ….
And again between any two angles of this series a new series of intermediate
angles can be inserted, differing from each other by infinite intervals.
Nature knows no limit.

In modern terms: $DB \propto AD^p$ near $A$ has curvature $0$ for $p > 2$,
finite nonzero curvature for $p = 2$, and infinite curvature for $1 < p < 2$;
the orders $p$ are dense.

What has been shown about curved lines and the surfaces they enclose applies
easily to curved surfaces and contents of solids. These lemmas were set down
first to avoid the tedium of long proofs by reduction to absurdity in the
manner of the ancient geometers. Proofs are shorter by the method of
indivisibles; but the hypothesis of indivisibles is harsher, and that method
is therefore reckoned less geometrical. So the proofs of what follows are
reduced to the ultimate sums and ratios of vanishing quantities and the first
ratios of nascent ones, that is, to the limits of sums and ratios, and the
proofs of those limits are given first as briefly as possible. This achieves
what the method of indivisibles achieves, with principles now proved. Hence
in what follows, whenever quantities are considered as made of particles, or
small curved lines are used for straight ones, what is meant is not
indivisibles but vanishing divisible quantities, not sums and ratios of
determinate parts but always limits of sums and ratios, and the force of such
proofs always rests on the method of the preceding lemmas.

*Objection:* vanishing quantities have no ultimate proportion, since before
they vanish it is not ultimate, and when they have vanished there is none. By
the same argument a body arriving at a place would have no ultimate velocity:
before it arrives the velocity is not ultimate, and when it has arrived there
is none. The answer is easy. The ultimate velocity is that with which the body
moves neither before it reaches the last place and the motion stops, nor
after, but at the moment it arrives. Likewise the ultimate ratio of vanishing
quantities is the ratio with which they vanish, neither before nor after; the
first ratio of nascent quantities is the ratio with which they begin; and the
first and last sum is that with which they begin and cease to be (or to
increase and decrease). There is a limit which the velocity can reach at the
end of the motion but not exceed; this is the ultimate velocity. The same holds
for the limit of all beginning and ceasing quantities and proportions. Since
this limit is certain and definite, finding it is a truly geometrical problem,
and geometrical things may legitimately be used to determine and prove other
geometrical things.

*Objection:* if the ultimate ratios of vanishing quantities are given, their
ultimate magnitudes are given too, and so every quantity consists of
indivisibles, contrary to what Euclid proved about incommensurables in Book X
of the *Elements*. This objection rests on a false hypothesis. The ultimate
ratios with which quantities vanish are not ratios of ultimate quantities, but
limits which the ratios of quantities decreasing without limit always
approach, nearer than by any given difference, never passing them and never
reaching them before the quantities are diminished indefinitely. This is
clearer with infinitely great quantities: if two quantities with a given
difference are increased indefinitely, their ultimate ratio, equality, is
given, though no ultimate or greatest quantities of which it is the ratio are
given. So in what follows, whenever for ease of imagination quantities are
called least, vanishing or ultimate, do not understand quantities of
determinate magnitude, but think of them as always to be diminished without
limit.

In modern terms: an ultimate ratio is $\lim X/Y$, and Lemma I supplies its
defining property.

## Section II. On finding centripetal forces

**Proposition I. Theorem I.** *The areas which bodies made to move in orbits
describe by radii drawn to an immovable centre of forces lie in immovable
planes and are proportional to the times.*

In modern terms: for a centripetal force toward a fixed point $S$, the motion
stays in one plane and $\tfrac12\, \mathbf r \times \dot{\mathbf r}$ is
constant, so swept area is proportional to time.

*Proof.* Divide the time into equal parts, and in the first part let the body
describe the straight line $AB$ by its inherent force. In the second part, if
nothing impeded it, it would go straight on to $c$ (Law I), describing $Bc$
equal to $AB$, so that with radii $AS$, $BS$, $cS$ drawn to the centre, the
areas $ASB$ and $BSc$ would be equal. But when the body reaches $B$, let a
centripetal force act with a single but great impulse and make the body
deviate from the line $Bc$ and go on in the line $BC$. Draw $cC$ parallel to
$BS$, meeting $BC$ in $C$; at the end of the second part of time the body
(Corollary I of the Laws) will be at $C$, in the same plane as the triangle
$ASB$. Join $SC$; the triangle $SBC$ equals the triangle $SBc$, because of the
parallels $SB$, $Cc$, and so it also equals the triangle $SAB$. By a similar
argument, if the centripetal force acts successively at $C$, $D$, $E$, …,
making the body describe in the single particles of time the single straight
lines $CD$, $DE$, $EF$, …, these lie in the same plane, and the triangle $SCD$
equals the triangle $SBC$, $SDE$ equals $SCD$, and $SEF$ equals $SDE$. So in
equal times equal areas are described in an immovable plane, and
*componendo*, any sums of areas $SADS$, $SAFS$ are to each other as the times
of description. Now let the number of triangles be increased and their width
diminished indefinitely: their ultimate perimeter $ADF$ (Corollary 4 of
Lemma III) will be a curved line; so the centripetal force, by which the body
is perpetually drawn back from the tangent of this curve, will act
uninterruptedly, and any areas described, $SADS$, $SAFS$, being always
proportional to the times of description, will be proportional to those times
in this case too.

In modern terms: with vertices $\mathbf r_k$ and impulses toward $S$,
$\mathbf r_{k+1} = 2\mathbf r_k - \mathbf r_{k-1} + \lambda_k \mathbf r_k$.
Then $\mathbf r_k \times \mathbf r_{k+1} = \mathbf r_{k-1} \times \mathbf r_k$,
so every triangle $S\,\mathbf r_k\,\mathbf r_{k+1}$ has the same area (Newton:
triangles on the same base between parallels, Euclid I.37–38). The final step
passes to the limit of the polygons.

*Corollary 1.* In non-resisting media, if the areas are not proportional to the
times, the forces do not tend to the point where the radii meet.

*Corollary 2.* In all media, if the description of areas is accelerated, the
forces do not tend to the point where the radii meet, but decline from it *in
consequentia*.

> **1713.** These two corollaries move, expanded, to Proposition II. In their
> place come six new ones.
>
> *Corollary 1.* The velocity of a body attracted to an immovable centre is, in
> non-resisting spaces, inversely as the perpendicular let fall from the
> centre onto the rectilinear tangent of the orbit; for the velocities at $A$,
> $B$, $C$, $D$, $E$ are as the bases $AB$, $BC$, $CD$, $DE$, $EF$ of equal
> triangles, and these bases are inversely as the perpendiculars on them.
> In modern terms: $v \cdot p$ is constant, with $p$ the distance from $S$ to
> the tangent.
>
> *Corollary 2.* If the chords $AB$, $BC$ of two arcs described successively in
> equal times by the same body in non-resisting spaces are completed into a
> parallelogram $ABCU$, its diagonal $BU$, in the position it has ultimately
> when the arcs are diminished indefinitely, passes through the centre of
> forces when produced both ways.
>
> *Corollary 3.* If the chords $AB$, $BC$ and $DE$, $EF$ of arcs described in
> equal times are completed into parallelograms $ABCU$, $DEFZ$, the forces at
> $B$ and $E$ are in the ultimate ratio of the diagonals $BU$, $EZ$ as the arcs
> are diminished indefinitely; for the motions $BC$, $EF$ are compounded
> (Corollary I of the Laws) of $Bc$, $BU$ and $Ef$, $EZ$, and $BU$, $EZ$, equal
> to $Cc$, $Ff$, were generated in the proof of this Proposition by the
> impulses of the centripetal force at $B$ and $E$, and so are proportional to
> those impulses.
>
> *Corollary 4.* The forces by which any bodies in non-resisting spaces are
> drawn from rectilinear motions and bent into curved orbits are to each
> other as the sagittas of arcs described in equal times that converge to the
> centre of forces and bisect the chords, as the arcs are diminished
> indefinitely; for these sagittas are halves of the diagonals of
> Corollary 3.
>
> *Corollary 5.* So these forces are to the force of gravity as these sagittas
> are to the vertical sagittas of the parabolic arcs that projectiles describe
> in the same time.
>
> *Corollary 6.* All the same holds, by Corollary V of the Laws, when the planes
> in which the bodies move, together with the centres of forces in them, are
> not at rest but move uniformly in a straight line.

**Proposition II. Theorem II.** *Every body that moves in some curved line and,
by a radius drawn to a point either immovable or moving uniformly in a
straight line, describes about that point areas proportional to the times, is
urged by a centripetal force tending to that same point.*

In modern terms: if $\mathbf r \times \dot{\mathbf r}$ is constant about $S$,
the force is parallel to $\mathbf r$.

*Case 1.* Every body moving in a curved line is turned from a rectilinear
course by some force acting on it (Law I). The force by which the body is
turned from its rectilinear course and made to describe, about the immovable
point $S$, the least triangles $SAB$, $SBC$, $SCD$, … equal in equal times,
acts at the place $B$ along a line parallel to $cC$ (Euclid I.40 and Law II),
that is, along the line $BS$; and at the place $C$ along a line parallel to
$dD$, that is, along the line $CS$; and so on. It therefore always acts along
lines tending to that immovable point $S$.

*Case 2.* By Corollary V of the Laws it makes no difference whether the surface
on which the body describes the curvilinear figure rests, or moves uniformly in
a straight line together with the body, the figure described and its point
$S$.

> **1713.** The statement specifies a curved line *described in a plane*. Two
> corollaries are added, rewritten from the old corollaries of Proposition I.
>
> *Corollary 1.* In non-resisting spaces or media, if the areas are not
> proportional to the times, the forces do not tend to the point where the
> radii meet, but decline from it *in consequentia*, toward the direction of
> motion, if the description of areas is accelerated, and *in antecedentia* if
> it is retarded.
>
> *Corollary 2.* In resisting media too, if the description of areas is
> accelerated, the directions of the forces decline from the point where the
> radii meet toward the direction of motion.

### Scholium

A body may be urged by a centripetal force compounded of several forces. In
that case the meaning of the Proposition is that the force compounded of them
all tends to the point $S$. Further, if some force acts along a line
perpendicular to the surface described, it will make the body deviate from the
plane of its motion, but it will neither increase nor diminish the quantity of
the surface described, and so it may be neglected in the composition of
forces.

**Proposition III. Theorem III.** *Every body that, by a radius drawn to the
centre of another body moving in any way, describes about that centre areas
proportional to the times, is urged by a force compounded of the centripetal
force tending to that other body and of all the accelerative force by which
that other body is urged.*

In modern terms: if $\mathbf r_{12} \times \dot{\mathbf r}_{12}$ is constant
for the relative position $\mathbf r_{12} = \mathbf r_1 - \mathbf r_2$, then
$\mathbf a_1 - \mathbf a_2$ is parallel to $\mathbf r_{12}$.

*Proof.* By Corollary VI of the Laws, if both bodies are urged along parallel
lines by a new force equal and contrary to the force urging the other body,
the first body continues to describe the same areas about the other as
before. The force urging the other body is now destroyed by its equal and
contrary force, so (Law I) that other body either rests or moves uniformly in a
straight line, and the first body, urged by the difference of the forces,
continues to describe areas proportional to the times about it. So (Theorem
II) the difference of the forces tends to that other body as its centre.

> **1713.** The proof names the bodies $L$ and $T$; $T$, left to itself once its
> force is cancelled, rests or moves uniformly, and $L$ moves under "the
> difference of the forces, that is, the remaining force". The argument is
> unchanged.

*Corollary 1.* Hence if one body, by a radius drawn to another, describes areas
proportional to the times, and from the total force urging the first (simple,
or compounded of several forces by Corollary II of the Laws) the whole
accelerative force urging the other is subtracted (by the same Corollary), all
the remaining force urging the first tends to the other body as centre.

*Corollary 2.* And if those areas are very nearly proportional to the times,
the remaining force tends very nearly to the other body.

*Corollary 3.* And conversely, if the remaining force tends very nearly to the
other body, those areas are very nearly proportional to the times.

*Corollary 4.* If a body, by a radius drawn to another body, describes areas
that are very unequal compared with the times, and that other body rests or
moves uniformly in a straight line, the action of the centripetal force
tending to that other body is either null or mixed and compounded with very
powerful actions of other forces; and the total force compounded of them all,
if there are several, is directed to another centre (immovable or moving)
about which the description of areas is uniform. The same holds when the other
body moves in any way, provided the centripetal force taken is what remains
after subtracting the total force acting on that other body.

### Scholium

Since the uniform description of areas indicates the centre to which the force
that most affects the body is directed, and the body is retained in its orbit
by a force toward that centre, and every circular motion is rightly said to be
performed about the centre by whose force the body is drawn back from
rectilinear motion and retained in its orbit: why should we not use the
uniform description of areas, in what follows, as the index of the centre
about which every circular motion in free spaces is performed?

**Proposition IV. Theorem IV.** *The centripetal forces of bodies describing
different circles with uniform motion tend to the centres of those circles,
and are to each other as the squares of the arcs described in the same time
applied to the radii of the circles.*

In modern terms: for arcs $s$ described in a common time on circles of
radius $r$, $F \propto s^2/r$; that is, $F \propto v^2/r$.

*Proof.* Let the bodies $B$, $b$, revolving in the circumferences of the
circles $BD$, $bd$, describe the arcs $BD$, $bd$ in the same time. By their
inherent force alone they would describe tangents $BC$, $bc$ equal to these
arcs; so it is the centripetal forces that perpetually draw the bodies back
from the tangents to the circumferences, and they are to each other in the
first ratio of the nascent spaces $CD$, $cd$. They tend to the centres of the
circles by Theorem II, because the areas described by the radii are taken
proportional to the times. Make the figure $tkb$ similar to the figure $DCB$.
By Lemma V the line $CD$ is to the line $kt$ as the arc $BD$ to the arc $bt$;
by Lemma XI the nascent line $tk$ is to the nascent line $dc$ as $bt^2$ to
$bd^2$; so *ex aequo* the nascent line $DC$ is to the nascent line $dc$ as
$BD \cdot bt$ to $bd^2$, or equivalently as $BD \cdot bt / Sb$ to $bd^2/Sb$,
and so (the ratios $bt/Sb$ and $BD/SB$ being equal) as $BD^2/SB$ to
$bd^2/Sb$.

In modern terms: the departure from the tangent over the arc $s$ is the
sagitta $CD \approx s^2/(2r)$ (Lemma XI), and the force is as that departure
in a given time (Lemma X, Corollary 2).

> **1713.** A new proof replaces this one. The forces tend to the centres of the
> circles by Proposition II and Corollary 2 of Proposition I, and are to each
> other as the versed sines of the least arcs described in equal times
> (Corollary 4 of Proposition I), that is, as the squares of those arcs
> applied to the diameters of the circles (Lemma VII). Since these arcs are as
> the arcs described in any equal times, and the diameters as the radii, the
> forces are as the squares of arcs described in the same time applied to the
> radii.

*Corollary 1.* Hence the centripetal forces are as the squares of the
velocities applied to the radii of the circles: $F \propto v^2/r$.

*Corollary 2.* And they are inversely as the squares of the periodic times
applied to the radii: $F \propto r/T^2$. That is, in the language of the
geometers, these forces are in the ratio compounded of the duplicate ratio of
the velocities directly and the simple ratio of the radii inversely; and also
in the ratio compounded of the simple ratio of the radii directly and the
duplicate ratio of the periodic times inversely.

*Corollary 3.* So if the periodic times are equal, both the centripetal forces
and the velocities are as the radii, and conversely.

*Corollary 4.* If the squares of the periodic times are as the radii, the
centripetal forces are equal and the velocities are in the subduplicate ratio
of the radii, and conversely: $T^2 \propto r \iff F = \text{const},\ v \propto
r^{1/2}$.

*Corollary 5.* If the squares of the periodic times are as the squares of the
radii, the centripetal forces are inversely as the radii and the velocities
equal, and conversely: $T \propto r \iff F \propto 1/r,\ v = \text{const}$.

*Corollary 6.* If the squares of the periodic times are as the cubes of the
radii, the centripetal forces are inversely as the squares of the radii, and
the velocities in the subduplicate ratio of the radii; and conversely:
$T^2 \propto r^3 \iff F \propto 1/r^2$. [As printed in 1687 the velocity clause
lacks "inversely"; by Corollary 1 the consistent relation is
$v \propto r^{-1/2}$.]

*Corollary 7.* All the same holds for the times, velocities and forces with
which bodies describe similar parts of any similar figures having similarly
placed centres, by applying the preceding proof to those cases.

> **1713.** The corollaries are rewritten and extended to nine.
>
> *Corollary 1.* Therefore, since those arcs are as the velocities of the
> bodies, the forces are as the squares of the velocities applied to the radii,
> or, as the geometers say, in the ratio compounded of the duplicate ratio of
> the velocities directly and the simple ratio of the radii inversely.
>
> *Corollary 2.* And since the periodic times are in the ratio compounded of the
> radii directly and the velocities inversely, the forces are inversely as the
> squares of the periodic times applied to the radii, that is, in the ratio
> compounded of the radii directly and the duplicate ratio of the periodic
> times inversely: $F \propto r/T^2$.
>
> *Corollary 3.* So if the periodic times are equal, and therefore the
> velocities are as the radii, the forces are also as the radii, and
> conversely.
>
> *Corollary 4.* If both the periodic times and the velocities are in the
> subduplicate ratio of the radii, the forces are equal, and conversely.
>
> *Corollary 5.* If the periodic times are as the radii, and therefore the
> velocities are equal, the forces are inversely as the radii, and conversely.
>
> *Corollary 6.* If the periodic times are in the sesquiplicate ratio of the
> radii, and therefore the velocities inversely in the subduplicate ratio of
> the radii, the forces are inversely as the squares of the radii, and
> conversely: $T \propto r^{3/2} \iff v \propto r^{-1/2} \iff F \propto
> r^{-2}$. This corrects the 1687 velocity clause.
>
> *Corollary 7.* And universally, if the periodic time is as any power $R^n$ of
> the radius $R$, and therefore the velocity inversely as $R^{n-1}$, the
> centripetal force is inversely as $R^{2n-1}$, and conversely.
>
> *Corollary 8.* The old Corollary 7, with the addition that it is applied by
> substituting the uniform description of areas for uniform motion, and the
> distances of the bodies from the centres for the radii.
>
> *Corollary 9.* From the same proof it also follows that the arc which a body
> describes in any time, revolving uniformly in a circle under a given
> centripetal force, is a mean proportional between the diameter of the
> circle and the descent of the body falling under the same force in the same
> time: $s^2 = d \cdot h$.
>
> **1726.** Corollaries 1 and 2 drop the "applied to the radii" formulation and
> keep only the compound ratios: in the ratio compounded of the duplicate ratio
> of the velocities directly and the simple ratio of the radii inversely; and
> in the ratio compounded of the radii directly and the duplicate ratio of the
> periodic times inversely.

### Scholium

The case of Corollary 6 holds in the celestial bodies (as Wren, Hooke and
Halley also gathered separately), and so what concerns a centripetal force
decreasing in the duplicate ratio of the distances from the centres is set out
more fully in what follows.

The preceding proof also gives the proportion of a centripetal force to any
known force, such as gravity. In the time the body traverses the arc $BC$ the
force impels it through the space $CD$, which at the very beginning of the
motion equals the square of the arc $BD$ applied to the diameter of the
circle; and every body urged by the same force continued always in the same
direction describes spaces in the duplicate ratio of the times. So the force,
in the time the revolving body describes any given arc, would make the same
body, going straight on, describe a space equal to the square of that arc
applied to the diameter of the circle; it is therefore to gravity as that space
is to the space a heavy body describes falling in the same time. By
propositions of this kind Huygens, in his excellent treatise *De Horologio
oscillatorio*, compared the force of gravity with the centrifugal forces of
revolving bodies.

In modern terms: $CD \approx s^2/d$ with $d = 2r$, so the force is to gravity
as $s^2/d$ is to the distance $\tfrac12 g t^2$ fallen in the same time.

> **1713.** This paragraph is replaced. By the preceding Proposition and its
> corollaries one also obtains the proportion of a centripetal force to any
> known force, such as gravity: if a body revolves by its gravity in a circle
> concentric with the Earth, that gravity is its centripetal force, and from
> the descent of heavy bodies both the time of one revolution and the arc
> described in any given time are given, by Corollary 9. Huygens compared
> gravity with the centrifugal forces of revolving bodies by propositions of
> this kind.

The preceding can also be proved this way. In any circle inscribe a polygon of
any number of sides. If a body moving along the sides with a given velocity is
reflected from the circle at each vertex, the force with which it strikes the
circle at each reflection is as its velocity; so the sum of the forces in a
given time is as that velocity and the number of reflections jointly, that is
(the polygon being given in kind) as the length described in that time and the
same length applied to the radius, that is, as the square of that length
applied to the radius; and so, if the polygon, its sides diminished
indefinitely, coincides with the circle, as the square of the arc described in
the given time applied to the radius. This is the force with which the body
presses on the circle, and equal to it is the contrary force with which the
circle continually repels the body toward the centre.

> **1713.** "This is the *centrifugal force* with which the body presses on the
> circle." **1726** replaces "the same length applied to the radius" by "the
> same length increased or diminished in the ratio of that length to the
> radius of the circle".

In modern terms: on a regular $n$-gon the body makes about $vt\,n/(2\pi r)$
reflections in the time $t$, each of impulse about $m v \cdot 2\pi/n$, so the
total impulse is about $m v^2 t/r$. For a given $t$ the length described is as
$v$, so this is as $(vt)^2/r$, Newton's square of the length applied to the
radius.
