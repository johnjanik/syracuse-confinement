# The Way Is Shut

### I went looking for a proof of the Collatz conjecture. I found a door instead — and learned, the hard way, exactly why it won't open.

---

> *"The way is shut. It was made by those who are Dead, and the Dead keep it, until the time comes. The way is shut."*
> — J.R.R. Tolkien, *The Return of the King*

---

There is a problem a child can understand and no one can solve. Take any whole number. If it's even, halve it. If it's odd, triple it and add one. Repeat. The Collatz conjecture says that no matter where you start, you always tumble down to one. Try it. Seventeen goes to fifty-two, then twenty-six, thirteen, forty, twenty, ten, five, sixteen, eight, four, two, one. Every number anyone has ever checked — and that is a great many numbers — comes home to one.

It looks like it should be easy. It is not. It has defeated everyone for ninety years, and a famous mathematician once said it may simply be out of reach of present-day mathematics.

I didn't set out to prove it. I'm not that foolish — or rather, I am exactly that foolish, but I had the sense to aim at a smaller target. My plan was to *reduce* it: to take the conjecture and chip away at it, step by honest step, replacing one mystery with a smaller one, until what remained was the single hardest thing inside it. Then to look at that thing directly and ask what it would actually take to crack it. I wanted a map of the wall, not a hole in it.

I got the map. This essay is what it shows.

## What I built

I treated the problem like an engineering teardown. I wrote manuscripts, I formalized the load-bearing pieces in a proof assistant so a computer could check them, and I wrote roughly a hundred small programs to test every claim against the actual numbers — billions of them — and to produce certificates anyone can re-run. The rule I held to, without exception, was honesty about status: every step was labeled *proved*, *computed*, *imported from the literature*, or *open*. I never let myself write "and so Collatz follows." Only "Collatz follows *if* these named things hold."

That discipline is the whole point. It's easy to fool yourself in a problem like this. The history of Collatz is a graveyard of arguments that felt like proofs and weren't.

## Five roads, one gate

Here is the strange and beautiful thing I did not expect.

I attacked the reduced problem from five different directions, with five different kinds of mathematics, at different times over the work. One direction was about the two-adic structure — the hidden binary skeleton of the integers. Another modeled the orbits as a branching, dying random process. Another was an operator and spectral analysis. Another was a graph of how high "excursions" can chain together. Another was the elimination of cycles.

Every single one of them bottomed out at the *same place*.

There was a particular afternoon when I realized that the deepest object in the branching-process picture, and the equilibrium-hovering orbit in the valuation picture, and the original obstruction in the two-adic picture, were not similar. They were *identical* — the same thing, wearing different clothes in different chapters. And independently, the proof assistant, grinding away on its own, had isolated its one unfinished lemma at exactly that spot.

Five roads do not arrive at one gate by accident. When that happens, you are no longer staring at a list of separate difficulties. You are staring at a single thing the problem is *made of*.

## The gate, in plain words

So what is it?

Strip away every layer and Collatz becomes a statement about *balance*. As a number runs its course, its private sequence of moves — how often it's tripled, how often and how deeply it's halved — has to stay balanced around a certain fixed, irrational rate. Not roughly. Bounded, forever, for every starting number. If that balance ever drifts off and stays off, the number escapes to infinity and the conjecture is false. So Collatz, at bottom, is the claim that this balance never fails.

Now here is the heart of it.

If you ask whether a *typical* number stays balanced — if you average over all numbers, or use the natural notion of randomness on this two-adic skeleton — the answer is yes, and it's almost easy. The moves look random, randomness balances out, the rare escapes are vanishingly rare, the books close. Mathematicians have a word for this: the *annealed*, or averaged, picture. On average, everything is fine.

But Collatz isn't about the average number. It's about *this* number. And *that* number. And *every* number, with no exceptions allowed, ever. Each integer is not a random draw — it is one fixed, fully determined trajectory threading its way through a rigidly constrained object. The demand is that this single deterministic path obey, on its own, the statistics that randomness would predict. The averaged version is a lemma; the every-orbit version is the conjecture. Mathematicians call this the *quenched*, or pointwise, picture.

The gap between those two — between "almost every number behaves" and "every number behaves" — is the entire problem. That is the way that is shut.

## Why the way is shut

This is the part I had to learn by walking into it, and it is the part worth telling.

You would think there's a theory for this. There almost is. In fact there are three, each of which looks, at a squint, like exactly the right tool. Each one fails — and fails for a reason that is itself a discovery.

The first is the theory of *rare events in dynamical systems* — the precise study of how often a wandering trajectory lands in a shrinking target. This is the closest named field to what I need, and its theorems require the system to *mix*: to scramble its own history, to behave randomly enough that correlations decay. The deterministic Collatz map does no such thing, and no one has shown it does. Worse, even when these theorems apply, they conclude "almost everywhere" — and I need *everywhere*. I tested the soft, summable version of this directly, expecting it to work, and the numbers refused: the orbits are not independent samplers. The hits are excluded *exactly*, deterministically, not merely rarely.

The second is *measure rigidity* — the deep theory, descended from Furstenberg, of systems acted on simultaneously by multiplication-by-two and multiplication-by-three. It is the natural home for a problem built out of twos and threes, and its theorems can force a system to be perfectly uniform. But they need *two independent rich directions*. And here I found the single most important structural fact of the whole program: Collatz is rich in the doubling direction but utterly *rigid*, rank-one, in the tripling direction — it advances by exactly one factor of three per step, deterministically, with no room for the second kind of randomness the rigidity theorems demand. The machinery has nothing to grip. It slides off.

The third is *homogeneous dynamics and nondivergence* — the theory that controls how trajectories in certain symmetric spaces escape toward infinity. It would apply beautifully if someone could encode the Collatz map as a flow on the right kind of space. No one has. Until they do, it is an analogy, not a tool.

So the obstruction has the *shape* of all three theories and the *hypotheses* of none of them. That is why, again and again, my local certificates succeeded and the global statement did not budge. And it is why a long line of tempting shortcuts — a finite pattern that would settle it, a clever piece of modular arithmetic, a single decreasing quantity, a spectral gap, a Fourier obstruction, a fractal target — each, in turn, dissolved. Several of them I refuted in an afternoon, by writing a program to test the clean-looking idea the moment I had it. The negative space, the catalog of what cannot work, turned out to be the truest picture of what the answer must be.

## The company it keeps

If you want the most honest description of the obstruction, it is this: it is the same *kind* of statement as "the digits of pi are random" or "the square root of two is normal." We believe these. They are trivially true in the averaged sense. And they are, for any specific number, completely beyond every method mathematics currently has. A *particular* deterministic object realizing the statistics of randomness is one of the oldest and deepest walls in the subject. Collatz is one instance of it, pinned down very precisely.

The frontier marker is Terence Tao's 2019 result (published in 2022), which proves that *almost all* Collatz orbits come almost all the way down. It is a masterpiece, and reading it with one question in mind — *where does the proof lose track of the individual starting number?* — shows you the exact location of the wall. That loss is the quenched barrier. His method, by its nature, cannot cross it.

People had told me, for years, that Collatz needs genuinely new mathematics. I believed them the way you believe a weather report for a city you'll never visit. I had to walk up to the gate myself, put my hand on it, and read the inscription before I understood *which* new mathematics, and *why* the existing tools stop precisely where they do. That is the difference between knowing a thing and finding it out the hard way.

## What new mathematics might open it

I don't have the key. But the work points, with surprising clarity, at the shape of the key.

The most promising direction is an *inverse theorem*. The model is the Green–Tao theory of structured sequences, which proves, in its own setting, a statement of exactly the form one wants: *if a sequence fails to be equidistributed, then it must secretly carry a low-complexity algebraic structure.* The Collatz analogue would say: *if a number's balance persistently fails, it must be trapped in an explicit, finite, structured obstruction* — and the certificate machinery I built is designed precisely to rule such obstructions out. The ambient system is wrong (Collatz is not the kind of object Green–Tao handle), but the *logical architecture* — failure of randomness forces structure — is the right one.

For anyone who wants to chase this, here is the company to keep. Think of it as a map of the surrounding country.

**The Collatz and normality frontier.** Terence Tao, *Almost all orbits of the Collatz map attain almost bounded values* — the benchmark, and the place to see exactly what current methods can't do. Daniel Bernstein and Jeffrey Lagarias, *The 3x+1 conjugacy map* — the natural two-adic coordinate system for the whole problem; also Lagarias's survey writing for the classical background. Yann Bugeaud, *Expansions of algebraic numbers*, and Boris Adamczewski with Bugeaud, *On the complexity of algebraic numbers* — the normality barrier and an early prototype of the very inverse-theorem shape we need.

**Rare events in dynamics.** Nikolai Chernov and Dmitry Kleinbock on dynamical Borel–Cantelli lemmas; Jayadev Athreya's survey on logarithm laws and shrinking targets for orientation; Dmitry Dolgopyat, Bassam Fayad, and Sixu Liu on multiple Borel–Cantelli and clustered rare events; Kleinbock and Shucheng Zheng on shrinking targets under Lipschitz twists. Read these to understand exactly what *mixing* buys you — and what it costs you to lack it.

**Rigidity and entropy.** The survey literature on Furstenberg's times-two, times-three conjecture (Rudolph, Johnson, Host, Lyons); the measure-rigidity work of Manfred Einsiedler, Anatole Katok, and Elon Lindenstrauss; and Michael Hochman and Pablo Shmerkin on local entropy averages — relevant less for their conclusions than for their *method* of turning multiscale structure into hard quantitative facts.

**Inverse theorems.** Ben Green and Terence Tao, *The quantitative behaviour of polynomial orbits on nilmanifolds* — the cleanest available model of the theorem-shape; the Green–Tao–Ziegler inverse theory for the Gowers norms; and Tao's expository note on the toolkit of Jean Bourgain, for the sum-product and entropy-growth machinery that may be what's actually needed.

**Pressure and dying random walks.** For the thermodynamic and large-deviation backbone — because the rare excursions in Collatz are governed by a pressure law — William Parry and Mark Pollicott on zeta functions and periodic orbits, and Amir Dembo and Ofer Zeitouni's standard text on large deviations. And for the branching-and-killing mechanism, the work of Elie Aïdékon, Yueyun Hu and Zhan Shi, and Andreas Kyprianou.

**And what to leave alone.** Schmidt games and fractal-dimension questions look relevant and aren't central — they describe large sets of *exceptional* points, where the problem needs *every* point. Pure transcendence theory (Baker and his successors) is the right hammer for ruling out near-cycles, but it does not give the deterministic theorem the problem actually requires. I spent time on each. I'm saving you some.

The thesis the whole program points to, stated plainly: *develop a Collatz-specific inverse theorem in which the deterministic failure of the averaged law is forced to produce a finite, structured obstruction.* That is the mathematics that would open the door. As far as I can tell, it does not yet exist.

## The honest end

So I'll say what this is and isn't. It is not a proof of Collatz, and it claims nothing of the kind. It is a map: a reduction of the conjecture to one precisely-named obstruction, a structural explanation of why that obstruction sits in the blind spot of every tool we have, and a certified catalog of the shortcuts that don't work. If there is a contribution, it is in having walked all the way to the gate and written down, carefully, what the inscription says.

The way is shut. And the inscription, when you finally read it, is almost gentle: the way is kept not by chaos or by randomness, but by the *deterministic* structure of the numbers themselves — patient, rigid, and complete. It will open when the time comes — when someone builds the theory of deterministic equidistribution that does not yet exist.

If you would like to find out the hard way too, everything is there for you. The manuscripts, the proof-assistant formalization, the hundred programs, the certificates — all of it, public, named, with nothing hidden:

**https://github.com/johnjanik/thisisnotaproof**

The name of the repository is the most honest line I wrote.
