import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Attitudes.Intensional
import Mathlib.Tactic.DeriveFintype

/-!
# RSA Attitude Verb Embedding

Models scalar implicatures embedded under attitude verbs like "believe".

## The Phenomenon

"John believes some students passed"

Can have two readings:
1. **Global**: John believes [some passed] - speaker implicates "not all"
2. **Local**: John believes [some-but-not-all passed] - John's belief includes "not all"

Unlike DE contexts, attitude verbs allow BOTH interpretations.

## Theoretical Background

Attitude verbs create INTENSIONAL contexts:
- The embedded clause is evaluated at John's belief worlds, not the actual world
- Implicatures can be computed globally (about the speaker's assertion) or
  locally (about John's belief content)

This differs from DE contexts where:
- Local implicature strengthens the embedded clause
- Which weakens the overall sentence (due to downward monotonicity)
- So global is pragmatically preferred

With attitude verbs:
- Local implicature changes what John believes
- This doesn't weaken the overall sentence
- Both interpretations are felicitous

## References

- Geurts (2010). Quantity Implicatures. Ch. 4.
- Sauerland (2004). Scalar implicatures in complex sentences.
- Chierchia, Fox & Spector (2012). Scalar implicature as a grammatical phenomenon.
-/

namespace RSA.AttitudeEmbedding

open Semantics.Attitudes.Intensional

-- World Structure for Belief Contexts

/--
Student outcomes in the actual world and John's beliefs.

For "John believes some students passed", we need to track:
1. How many students ACTUALLY passed
2. How many students JOHN BELIEVES passed
-/
inductive StudentOutcome where
  | noneO     -- no students passed
  | someO     -- some but not all passed
  | allO      -- all students passed
  deriving DecidableEq, Repr, BEq, Inhabited

/--
World state tracking both reality and John's beliefs.

Key insight: John's beliefs may differ from reality!
- John might believe "some passed" when actually "all passed"
- John might believe "all passed" when actually "some passed"
-/
structure BeliefWorld where
  /-- What actually happened -/
  actual : StudentOutcome
  /-- What John believes happened -/
  johnBelieves : StudentOutcome
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The actual world determines what's true at the matrix level -/
def BeliefWorld.actuallyNone (w : BeliefWorld) : Bool := w.actual == .noneO
def BeliefWorld.actuallySome (w : BeliefWorld) : Bool := w.actual == .someO || w.actual == .allO
def BeliefWorld.actuallyAll (w : BeliefWorld) : Bool := w.actual == .allO

/-- John's beliefs determine what's true in embedded contexts -/
def BeliefWorld.johnBelievesNone (w : BeliefWorld) : Bool := w.johnBelieves == .noneO
def BeliefWorld.johnBelievesSome (w : BeliefWorld) : Bool :=
  w.johnBelieves == .someO || w.johnBelieves == .allO
def BeliefWorld.johnBelievesAll (w : BeliefWorld) : Bool := w.johnBelieves == .allO
def BeliefWorld.johnBelievesSomeNotAll (w : BeliefWorld) : Bool := w.johnBelieves == .someO

-- Interpretations of Embedded Scalars

/--
Two possible interpretations of "John believes some students passed":

1. **Global**: The "some" gets its weak meaning; implicature computed at matrix
   - Literal: John believes [∃x. student(x) ∧ passed(x)]
   - Implicature: Speaker implicates John doesn't believe all passed

2. **Local**: The "some" gets strong meaning inside the belief
   - Literal: John believes [∃x. student(x) ∧ passed(x) ∧ ¬∀y. student(y) → passed(y)]
   - = John believes some-but-not-all passed
-/
inductive AttitudeInterpretation where
  | global  -- "some" is weak, implicature at matrix level
  | local_  -- "some" is strong (some-but-not-all) inside belief
  deriving DecidableEq, Repr, BEq, Inhabited, Fintype

-- Truth Conditions

/--
Truth conditions for "John believes some students passed".

- **Global**: True iff John believes at least one passed
  (The "not all" is an implicature about the speaker's claim)

- **Local**: True iff John believes some-but-not-all passed
  (The "not all" is part of what John believes)
-/
def believesSomeMeaning (interp : AttitudeInterpretation) (w : BeliefWorld) : Bool :=
  match interp with
  | .global => w.johnBelievesSome  -- John believes ≥1 passed
  | .local_ => w.johnBelievesSomeNotAll  -- John believes exactly some-not-all

/--
For comparison: "John believes all students passed" (unambiguous).
-/
def believesAllMeaning (w : BeliefWorld) : Bool := w.johnBelievesAll

/--
For comparison: "John believes no students passed" (unambiguous).
-/
def believesNoneMeaning (w : BeliefWorld) : Bool := w.johnBelievesNone

-- World Space

/--
Relevant worlds for the attitude embedding scenario.

We focus on cases where John has a definite belief about the students.
(More complex models could include uncertainty in John's beliefs.)
-/
def attitudeWorlds : List BeliefWorld := [
  -- John correctly believes none
  ⟨.noneO, .noneO⟩,
  -- John correctly believes some-not-all
  ⟨.someO, .someO⟩,
  -- John correctly believes all
  ⟨.allO, .allO⟩,
  -- John believes some when all (underestimate)
  ⟨.allO, .someO⟩,
  -- John believes all when some (overestimate)
  ⟨.someO, .allO⟩,
  -- John believes some when none (false positive)
  ⟨.noneO, .someO⟩
]

instance : Fintype StudentOutcome where
  elems := ⟨[StudentOutcome.noneO, StudentOutcome.someO, StudentOutcome.allO], by decide⟩
  complete := λ x => by cases x <;> decide

instance : Fintype BeliefWorld :=
  Fintype.ofEquiv (StudentOutcome × StudentOutcome)
    { toFun := λ ⟨a, b⟩ => ⟨a, b⟩
      invFun := λ ⟨a, b⟩ => ⟨a, b⟩
      left_inv := λ _ => rfl
      right_inv := λ _ => rfl }

-- RSA Model

/--
Utterances for the attitude scenario.
-/
inductive AttitudeUtterance where
  | believesSome   -- "John believes some students passed"
  | believesAll    -- "John believes all students passed"
  | believesNone   -- "John believes no students passed"
  deriving DecidableEq, Repr, BEq, Inhabited, Fintype

/--
Truth under an interpretation (for "believes some" only).
-/
def utteranceMeaning (u : AttitudeUtterance) (interp : AttitudeInterpretation)
    (w : BeliefWorld) : Bool :=
  match u with
  | .believesSome => believesSomeMeaning interp w
  | .believesAll => believesAllMeaning w
  | .believesNone => believesNoneMeaning w

-- Key Predictions

/--
Under **global** interpretation:
- "John believes some" is true in worlds where John believes ≥1 passed
- This includes both johnBelieves = .someO AND johnBelieves = .allO
-/
theorem global_includes_all_belief :
    believesSomeMeaning .global ⟨.allO, .allO⟩ = true := rfl

/--
Under **local** interpretation:
- "John believes some" is true only when John believes some-but-not-all
- johnBelieves = .allO makes it FALSE
-/
theorem local_excludes_all_belief :
    believesSomeMeaning .local_ ⟨.allO, .allO⟩ = false := rfl

/--
The key difference: global and local differ when John believes all.
-/
theorem global_local_differ_at_all_belief :
    believesSomeMeaning .global ⟨.allO, .allO⟩ ≠
    believesSomeMeaning .local_ ⟨.allO, .allO⟩ := by decide

/--
Local entails global for attitude embedding (unlike DE contexts).
-/
theorem local_entails_global :
    ∀ w : BeliefWorld, believesSomeMeaning .local_ w = true →
      believesSomeMeaning .global w = true := by
  intro ⟨actual, johnBelieves⟩ h
  cases actual <;> cases johnBelieves <;> simp_all [believesSomeMeaning,
    BeliefWorld.johnBelievesSome, BeliefWorld.johnBelievesSomeNotAll]

/--
But global does NOT entail local.
-/
theorem global_not_entails_local :
    ∃ w : BeliefWorld, believesSomeMeaning .global w = true ∧
      believesSomeMeaning .local_ w = false := by
  use ⟨.allO, .allO⟩
  decide

-- Semantic Grounding

/--
Semantic grounding for "some students passed" as a proposition.

At a world, "some students passed" is true iff ≥1 student passed.
We model this with StudentOutcome:
- `.noneO` → false
- `.someO` → true (some but not all)
- `.allO` → true (all, which entails some)
-/
def somePassedProp (outcome : StudentOutcome) : Bool :=
  outcome == .someO || outcome == .allO

/--
Semantic grounding for "some-but-not-all students passed".
-/
def someNotAllPassedProp (outcome : StudentOutcome) : Bool :=
  outcome == .someO

/--
Semantic grounding for "all students passed".
-/
def allPassedProp (outcome : StudentOutcome) : Bool :=
  outcome == .allO

/--
**Grounding Theorem 1**: The global meaning corresponds to Montague semantics.

Global interpretation: "John believes some passed"
= John's belief state satisfies "some passed"
= somePassedProp(johnBelieves) = true

This theorem proves the stipulated `johnBelievesSome` equals the
compositional evaluation `somePassedProp`.
-/
theorem global_grounded :
    ∀ w : BeliefWorld, believesSomeMeaning .global w = somePassedProp w.johnBelieves := by
  intro ⟨_, johnBelieves⟩
  cases johnBelieves <;> rfl

/--
**Grounding Theorem 2**: The local meaning corresponds to Montague semantics.

Local interpretation: "John believes some-but-not-all passed"
= John's belief state satisfies "some-but-not-all passed"
= someNotAllPassedProp(johnBelieves) = true
-/
theorem local_grounded :
    ∀ w : BeliefWorld, believesSomeMeaning .local_ w = someNotAllPassedProp w.johnBelieves := by
  intro ⟨_, johnBelieves⟩
  cases johnBelieves <;> rfl

/--
**Grounding Theorem 3**: The unambiguous "believes all" is grounded.
-/
theorem believes_all_grounded :
    ∀ w : BeliefWorld, believesAllMeaning w = allPassedProp w.johnBelieves := by
  intro ⟨_, johnBelieves⟩
  cases johnBelieves <;> rfl

/--
**Semantic entailment grounding**: "some-not-all" entails "some" at the propositional level.

This explains why local_entails_global holds: it follows from the semantics.
-/
theorem prop_entailment :
    ∀ o : StudentOutcome, someNotAllPassedProp o = true → somePassedProp o = true := by
  intro o h
  cases o <;> simp_all [someNotAllPassedProp, somePassedProp]

/--
The local→global entailment is grounded in propositional semantics.
-/
theorem local_entails_global_grounded :
    ∀ w : BeliefWorld, believesSomeMeaning .local_ w = true →
      believesSomeMeaning .global w = true := by
  intro w h
  rw [local_grounded] at h
  rw [global_grounded]
  exact prop_entailment w.johnBelieves h

end RSA.AttitudeEmbedding
