import Linglib.Core.Order.Normality
import Linglib.Core.Logic.TweetyNixon
import Linglib.Studies.Cohen1999

/-!
# Asher & Pelletier (2013): More Truths about Generic Truth

[asher-pelletier-2013] (ch. 12 of *Genericity*, Mari, Beyssade & Del Prete eds., OUP)
defends the modal-quantifier analysis of generics of [asher-morreau-1995] and
[pelletier-asher-1997] — "φs ψ" is ∀x(φ(x) > ψ(x)), with > the weak conditional of
[asher-morreau-1991]'s commonsense entailment — refined so that the consequent is
evaluated **per individual**: for each a, in the worlds where a is a *normal φ*.

We render per-individual evaluation with restrictor-indexed normality orderings:
each restrictor class carries its own `Preorder` (its default processed by
`Normality.refine`), and a generic holds iff its scope holds throughout
`Normality.optimal` of its own restrictor's ordering. On `TweetyWorld` this makes
"Birds fly" and "Penguins don't fly" simultaneously true of Opus the penguin
(exx. 7–8), checked at disjoint world sets — "the normal Opus-penguin worlds are
not normal Opus-bird worlds." Normality itself has contextual "give" (ex. 9):
"Turtles live to be 100" is true under an Aristotelian/teleological construal and
false under a statistical one. §12.4 argues probability is too weak a basis for
generic truth — with tails in just over half of the normal cat-cases (the chapter
puts it at 50.05%), [cohen-1999a]'s majority GEN verifies "Cats have tails" while
the modal account rejects it; we state that divergence against `Cohen1999.cohenGEN`.
The chapter's accommodation and double-genericity responses to "Ducks lay eggs" and
"Mosquitoes carry the West Nile Virus" (exx. 4–5, [leslie-2008]) are not covered.
-/

namespace AsherPelletier2013

open Core.Order
open Core.Logic.TweetyNixon

/-! ### Per-individual evaluation (§12.3, exx. 7–8)

For ∀x(φ(x) > ψ(x)), the consequent ψ is evaluated for each individual a at the
worlds where a is a normal φ. Each restrictor class brings its own normality
ordering, obtained by processing that class's default into the total order. -/

/-- Worlds in which Opus is a bird (all of them, by taxonomy). -/
def birdDomain : Set TweetyWorld := {w | isBird w}

/-- Worlds in which Opus is a penguin. -/
def penguinDomain : Set TweetyWorld := {w | isPenguin w}

/-- Bird-normality: the bird default "birds fly" processed into the ordering. -/
@[reducible] def birdNormality : Preorder TweetyWorld :=
  Normality.refine Normality.total flies

/-- Penguin-normality: the penguin default "penguins don't fly" processed into
    the ordering. -/
@[reducible] def penguinNormality : Preorder TweetyWorld :=
  Normality.refine Normality.total (¬ flies ·)

/-- Ex. (8): "Birds fly" — Opus flies throughout the normal Opus-bird worlds. -/
theorem birds_fly : ∀ w ∈ Normality.optimal birdNormality birdDomain, flies w :=
  fun _ hw =>
    (hw.2 (show TweetyWorld.birdFlies ∈ birdDomain from trivial)
      ⟨trivial, fun _ => trivial⟩).2 trivial

/-- Ex. (7): "Penguins don't fly" — Opus is grounded throughout the normal
    Opus-penguin worlds. With `birds_fly`, both generics hold simultaneously:
    they are evaluated at different normal-world sets. -/
theorem penguins_dont_fly :
    ∀ w ∈ Normality.optimal penguinNormality penguinDomain, ¬ flies w :=
  fun _ hw =>
    (hw.2 (show TweetyWorld.penguinNoFly ∈ penguinDomain from trivial)
      ⟨trivial, fun _ hf => hf⟩).2 fun hf => hf

/-- "The normal Opus-penguin worlds are not normal Opus-bird worlds": the two
    evaluation sets are disjoint, so neither generic disturbs the other. -/
theorem normal_penguin_not_normal_bird :
    Disjoint (Normality.optimal penguinNormality penguinDomain)
      (Normality.optimal birdNormality birdDomain) :=
  Set.disjoint_left.mpr fun _ hp hb => penguins_dont_fly _ hp (birds_fly _ hb)

/-! ### Contextual construals of normality (§12.3, ex. 9)

"Turtles live to be 100": under the Aristotelian/teleological construal (the
natural telos of a turtle, if everything goes right) the generic is true; under
the statistical construal (most turtles die within hours of hatching) it is
false. The "give" in which worlds count as normal is located in the choice of
ordering, fixed by context and discourse. -/

/-- Tim the turtle's possible fates. -/
inductive TurtleWorld where
  | reachesCentury
  | diesYoung
  deriving DecidableEq

/-- Tim lives to be 100 in this world. -/
def livesTo100 : TurtleWorld → Prop
  | .reachesCentury => True
  | .diesYoung => False

/-- Teleological construal: promotes telos-fulfilling worlds. -/
@[reducible] def teleological : Preorder TurtleWorld :=
  Normality.refine Normality.total livesTo100

/-- Statistical construal: promotes the statistically typical early death. -/
@[reducible] def statistical : Preorder TurtleWorld :=
  Normality.refine Normality.total (¬ livesTo100 ·)

/-- Under the teleological construal the generic is true. -/
theorem turtles_teleological_true :
    ∀ w ∈ Normality.optimal teleological Set.univ, livesTo100 w :=
  fun _ hw =>
    (hw.2 (Set.mem_univ TurtleWorld.reachesCentury) ⟨trivial, fun _ => trivial⟩).2
      trivial

/-- Under the statistical construal the same generic is false. -/
theorem turtles_statistical_false :
    ¬ ∀ w ∈ Normality.optimal statistical Set.univ, livesTo100 w := fun h =>
  h .diesYoung ⟨Set.mem_univ _, fun _ _ _ => ⟨trivial, fun _ hf => hf⟩⟩

/-! ### Against the probabilistic account (§12.4)

[cohen-1999a] proposes that "φs ψ" is true iff Pr(ψ | φ) > 1/2. The chapter's
"too weak" argument: suppose the normal cases as far as cats are concerned have
tails in just over half of them — the chapter puts it at 50.05%, and the margin
can be made arbitrarily thin (a coin biased 50.000000001% toward heads is not
one that *normally comes up heads*). The majority account verifies "Cats have
tails"; the modal account rejects it, since the normal cases do not settle
tails. We model 11 tailed cases out of 20 equally normal ones and state the
divergence against the formalized `Cohen1999.cohenGEN`. -/

/-- Tails in 11 of the 20 equally normal cat-cases: just over half. -/
def tailed : Fin 20 → Prop := fun w => w.val < 11

instance : DecidablePred tailed := fun w => Nat.decLt w.val 11

/-- Cohen's majority GEN verifies "Cats have tails", but the generic fails on
    the modal account: some normal case lacks tails. -/
theorem cohen_too_weak :
    Cohen1999.cohenGEN (Finset.univ : Finset (Fin 20)) (fun _ => True) tailed ∧
    ¬ ∀ w ∈ Normality.optimal Normality.total (Set.univ : Set (Fin 20)), tailed w := by
  refine ⟨(Cohen1999.cohen_iff_thresholdGt (Finset.univ : Finset (Fin 20)) (fun _ => True)
    tailed (by decide)).mpr (by decide), fun h => ?_⟩
  rw [Normality.total_all_optimal] at h
  exact absurd (h ⟨11, by omega⟩ (Set.mem_univ _)) (Nat.lt_irrefl 11)

end AsherPelletier2013
