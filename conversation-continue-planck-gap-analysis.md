# Continue Planck Gap Analysis

> Source: https://chatgpt.com/share/6ab090f9-6958-83ed-ba44-a9eee20b2d58

> Downloaded: 2026-09-21

## Assistant

Usually much briefer.

That long seed was closer to a mini-spec / AGENTS.md than a good first Codex prompt. For a new repo, I’d normally seed with the research question, the
immediate milestone, and a couple of constraints, then let the agent inspect sources and propose structure.

Something like this is closer to how I’d actually start it:

Short Codex seed

Start a new Lean 4 + historical research project on the genealogy of Newton’s limit dynamics from De Motu (1684) to the Principia (1687, 1713), with Gregory’s
1694 revision notes as an intermediate planned architecture.

Main question: how did the relation

[
s \propto t^2
]

move from a hypothesis in De Motu to a proved lemma in the Principia, and how did the dependency graph around polygon limits, sagittae, force, and cubic area
change?

First milestone only:

 1. Find and preserve the primary online transcriptions for the relevant De Motu passage, Principia 1687 Lemma X, and 1713 Lemma X.

 2. Build a small dependency graph distinguishing explicit dependencies from modern reconstruction.

 3. Create a Lean 4 project and formalize the mathematical content of the three versions.

 4. Determine exactly what additional assumptions the 1687 proof uses to discharge the De Motu (s\sim t^2) hypothesis.

Keep editions separate. Do not drift into QM/Planck-gap work. Prefer Newton Project and other primary transcriptions over secondary literature.

Create README.md, AGENTS.md, research/STATE.md, and the minimum compiling Lean skeleton. Stop after the first milestone and report what changed logically
between the texts.

That is enough to get a capable Codex agent moving. The longer version is useful after the first exploration, when you know which distinctions really need to
be frozen into AGENTS.md.



## User


wait I was thinking... all of the antiquity debate was if time was to be considered as a set of dots or as a set of intervals, what is Newton position in his
axioms?



## Assistant


Ha pensado durante 1m 20s

Yes. If we translate the ancient dispute into your “dots versus intervals” language, Newton is on the continuous-duration / divisible-interval side, not the
atomic-instants side. But the precise position is slightly subtler: time itself is a continuously flowing magnitude; intervals are its parts, while instants
function as boundaries/limits or locations in time, not as indivisible atoms from which duration is assembled.

That is already visible in the foundational Scholium to the Definitions. Newton refuses to define time because he takes it as familiar, but then says:

    Tempus absolutum, verum, & mathematicum ... æquabiliter fluit ... alioque nomine dicitur Duratio.

Absolute mathematical time “flows equably” and is also called duration. He then speaks explicitly of the immutable order of the parts of time—partium Temporis
ordo est immutabilis—and even says times and spaces are “as it were places” of themselves and all things. [www]Newton Project+1

That is already very different from

T={t1​,t2​,t3​,…}

as a collection of zero-duration atoms.

What the mechanics actually uses

The dynamical proofs make the ontology clearer than the metaphysical Scholium.

In Proposition I Newton does not say “take successive instants.” He says

Dividatur tempus in partes æquales​

—“let time be divided into equal parts.”

During the first part of time the body describes AB; during the second part it would describe Bc; forces act at the boundaries of these parts in the polygonal
model. [www]Newton Project

So the discrete Newton construction is

[t0​,t1​],[t1​,t2​],…,[tN−1​,tN​],

not

t0​,t1​,…,tN​

considered as the substance of time.

The points ti​ are where the impulse occurs. The duration over which inertial motion occurs is

Δti​=ti+1​−ti​.

And then Newton takes

imax​Δti​→0.

That is extremely close to our modern interval/partition picture.

The Scholium to the Laws says the same thing when explaining Galileo: uniform gravity acts equally in equal particles of time—singulis temporis particulis
æqualibus—and therefore generates equal velocity increments. [www]Newton Project

Thus

equal duration⟶equal Δv.

A “particle of time” here plainly cannot mean a zero-length instant: a force acting through it generates a finite increment of motion. It is a little interval.

And Section I explicitly rejects indivisible constituents

This makes the position considerably stronger.

At the end of Section I Newton directly contrasts his method with the hypothesis of indivisibles:

    durior est indivisibilium Hypothesis

and says that when he talks as if quantities consisted of particles, those particles are to be understood not as indivisibles but as

    evanescentia divisibilia

—evanescent divisible quantities. [www]Newton Project

He then makes the point absolutely explicit: when he says “least,” “evanescent,” or “ultimate,” one must not understand quantities having some determinate
least magnitude; they are quantities

    semper diminuendas sine limite

to be continually diminished without limit. [www]Newton Project

Although this statement is about his mathematical quantities generally, time is one of precisely the continuously varying quantities to which the method is
applied.

So if the ancient alternatives are

continuum=indivisible instants∙∙∙∙​​

versus

continuum=divisible duration with boundaries,

Newton's Principia is unequivocally the second.

His “moment” is particularly revealing

The word moment can mislead us because modern ears hear “instant.”

But Newton's mathematical usage is very different.

In his later explanation of fluxions he says quantities are generated by continual increase, and that their moments are the parts generated during moments of
time. More explicitly, in demonstrations he regards the moment o as an indefinitely small but not infinitely small part of time, performs the calculation with
finite quantities, and only at the end lets o decrease and vanish. [www]Newton Project+1

So Newton's operative picture is:

o>0

during the argument,

then

o→0.

It is emphatically not

o=an indivisible temporal atom.

Indeed in another retrospective description he says explicitly that quantities are considered not as aggregated from indivisibles but as growing by continual
motion. [newtonproject]Newton Project

This agrees perfectly with the Principia Section I language.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

There are therefore three different objects

I think this distinction would matter enormously in the Lean project.

Newton effectively has:

time​

as continuous duration;

Δt​

as a divisible part of that duration;

and

t​

as the boundary/location at which something occurs.

Those should not all be represented by the same conceptual object.

Modern elementary mechanics collapses them all into real numbers:

t∈R,Δt∈R.

Mathematically that works, but historically it hides Newton's architecture.

A much more Newton-faithful formalization would use an affine time line:

T

whose elements are temporal locations/instants, together with a vector space of durations

D≃R.

Then

t1​−t0​∈D

is a duration, but an instant t0​ is not itself a duration.

Schematically:

TimePoint     -- affine points
Duration ℝ    -- differences between time points

t₁ -ᵥ t₀ : Duration
t₀ +ᵥ Δt : TimePoint

This is conceptually much closer to Newton than just declaring

abbrev Time := ℝ

because Newton gives us an absolute temporal structure without selecting a privileged zero of time. His absolute time has an invariant duration and order, but
the Principia does not need “the origin of absolute time.”

That is exactly an affine-line structure.

And now reconsider Proposition I

It becomes:

t0​<t1​<⋯<tN​

with equal differences

ti+1​−ti​=h.

Law I applies over each interval

[ti​,ti+1​],

while the impulse is idealized at the common boundary ti​.

Then

h→0.

Thus Newton does something conceptually rather elegant:

finite intervals+forces located at their boundariesh→0​continuous action.​

The boundaries do not become the constituent substance of time. They merely become dense as the partition is refined.

And this makes our squeeze more interesting:

Δp=Fh,s∼h2,A∼h3

are all functions of an interval length h.

There is no corresponding formula attached to a temporal point:

F(t)×‘‘dt"

only acquires meaning through the limiting process on intervals.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

So I would revise the prospective formalization at its very bottom. Instead of starting with

t:R,

start with

TimePointaffine overDuration≃R.​

And then Newton's first/last-ratio machinery operates on shrinking durations

hn​>0,hn​→0,

not on a sequence of smaller “time points.”

That may actually expose the historical issue you just noticed: Newton's entire derivation of force presupposes the ancient continuum answer that a duration is
indefinitely divisible without being composed of indivisible nows. His innovation is to make the physical law live in the limiting ratios of those disappearing
intervals. [www]Newton Project+1

[new]
Sources



## User


had not scholia about this



## Assistant


Ha pensado durante 1m 3s

Yes. And it makes the story more interesting than I said before.

There are three Newtonian positions/textual usages that have to be distinguished.

First, the mature General Scholium really does say:

    unumquodque Durationis indivisibile momentum...
    “every indivisible moment of duration ...”

and immediately afterwards:

    Partes dantur successivae in duratione
    “there are successive parts in duration.”

So Newton simultaneously admits indivisible moments and successive parts of duration. [newtonproject]Newton Project+1

That is extremely close to the Aristotelian architecture:

duration is continuous and divisible,

but

the now (νν) is indivisible

because it is the boundary between two portions of time, not a little temporal brick from which duration is assembled. Aristotle explicitly argues that the now
is indivisible while the continuum cannot be composed of indivisibles. [classics]Archivos Clásicos de Internet

So my previous wording “Newton does not model time as a set of points” was too quick. The better formulation is:

mature Newton has indivisible temporal points, but not obviously indivisible temporal intervals.​

And there is a scholium which says almost exactly this in calculus language

The really important manuscript is Newton's draft additions to the Leibniz Scholium for the second edition.

He writes:

    Per momenta quantitatum ... particulas momento temporis genitas.

and then explicitly says these particles

    non sunt minima indivisibiles ... sed sunt ... in infinitum [divisibiles]

—not indivisible minima, but divisible without end—and “indefinitely small.” He then describes time as produced by a continuous and uniform flow:

    tempus ut fluxu continuo et æquali genitum.

[www]Newton Project

That's extraordinarily pertinent.

Newton is distinguishing:

moment of duration​

in the sense of an instantaneous now/boundary, from

moment of a fluent quantity​

in the fluxional sense: a vanishing increment generated during a small duration.

The latter is emphatically not indivisible.

His alternative draft says the same thing even more plainly:

    incrementa momentanea seu particulas momento temporis genitas; easque indefinite parvas & in infinitum divisibiles.

“momentary increments, or particles generated in a moment of time; indefinitely small and infinitely divisible.” [newtonproject]Newton Project

And the published Book II Lemma II preserves the essential distinction. A finite particle is not a moment; moments are the principia jamjam nascentia—the
just-nascent beginnings—of finite magnitudes. In 1687 he even says that as soon as moments become finite magnitudes, they cease to be moments. [www]Newton
Project+1

So there are two very different senses of momentum running around Newton.

But young Newton held a much more atomistic theory!

This is the surprise.

In the youthful Quæstiones quædam Philosophiæ, under “Of Motion”, Newton explicitly argues:

    “there is a least distance, a least progression in motion & a least degree of time.”

Then:

    “there are soe many least parts of time in an hower as there can be Τὸ νὺν’s.”

And:

    “the least moment of time” has no parts.

[www]Newton Project

That's not merely an indivisible now as a boundary. That's very close to an actual temporal atomism:

T={least moments}.

He even links it to his contemporary atomism of matter and argues for the least temporal part analogously to a least material part. The surrounding notebook
explicitly discusses atoms, least distances, mathematical points and the constitution of quantities. [www]Newton Project

So we seem to have a genuine intellectual transition:

young Newton: least temporal parts / τοˋνν’s​

to

Principia Newton: indefinitely divisible intervals and evanescent quantities​

while retaining

indivisible “now” as temporal boundary.​

That is very close to moving from an atomistic solution of the ancient continuum problem toward the Aristotelian distinction

indivisible boundary=indivisible constituent.

Another manuscript makes the boundary interpretation very tempting

In a draft De motu corporum in mediis regulariter cedentibus, Newton has a remarkable Definition 16:

    Momenta quantitatum sunt ipsarum principia generantia vel alterantia fluxu continuo

—moments of quantities are their generating or altering principles in a continuous flux.

His examples include:

    tempus præsens præteriti et futuri

the present time [as the moment] of past and future,

and then

    the point of a line, the line of a surface, the surface of a solid...

[www]Newton Project

That's practically a table of codimension-one boundaries:

continuumpast/future durationlinesurfacesolid​moment/boundarypresentpointlinesurface​​

This strongly suggests that an indivisible moment of duration in the mature metaphysics can play the role that a point plays on a continuous line without
implying that the line is assembled from point-atoms.

And that is precisely Aristotle's construction of the now.

What about the “Classical Scholia”?

Here I think we should distinguish your memory carefully.

The unpublished Classical Scholia proper, intended around Book III Props. IV–IX, are mainly about ancient cosmology, Pythagorean astronomy/harmony, ancient
knowledge of gravitational ideas, prisca sapientia, etc. The Newton Project describes them that way; I don't currently see evidence that their surviving core
contains a sustained treatment of the temporal continuum. [newtonproject]Newton Project+1

But two other scholia are directly relevant:

 1. the General Scholium, with the phrase

    durationis indivisibile momentum;
 2. the proposed additions to the Leibniz Scholium, with

    continuous flow + indefinitely small, infinitely divisible increments.

So your recollection of “there were scholia about this” is basically right, but probably mixes those with the Classical Scholia.

This changes the Lean project quite a bit

We should absolutely not formalize Newtonian time simply as

Time := ℝ

and think we've captured the historical distinction.

For mature Newton I'd want:

T=affine TimePoints,D=Durations,

with

t1​−t0​∈D.

Then an indivisible now is

t∈T,

while a temporal part is

h=t1​−t0​>0,

and it is h that is indefinitely divisible:

h,2h​,4h​,…→0.

There is no smallest positive h.

This would let the formalization state exactly the mature Newtonian distinction:

instant is indivisible⇒duration has a least positive part.​

And now something potentially important appears for the genealogy project:

Quæstiones→De Motu→Principia

may contain not only the evolution

s∝t2:hypothesis→theorem,

but also a deeper evolution

time made from least moments⟶continuous duration with indivisible boundaries.​

And that evolution sits exactly underneath Newton's ability to let

h→0,s∼h2,A∼h3

without ever arriving at a “next smallest” interval. That is likely worth making a first-class thread of the new project, not a footnote.

If you want, I can:

  • Explore distinctions among Newton's three temporal concepts

  • Explain Newton's transition from temporal atomism to continuous intervals

  • Clarify role of Newton's scholia on time's divisibility and moments

[cla]
[rea]
[www]
Sources
ChatGPT is AI and can make mistakes.
[                    ]
[                    ]


[                    ][                    ][                    ]

We use cookies

Cookies help this site function, measure usage, and support marketing. Manage your cookie preferences anytime. Learn more about our cookie policy.

Reject non-essential
Accept all
