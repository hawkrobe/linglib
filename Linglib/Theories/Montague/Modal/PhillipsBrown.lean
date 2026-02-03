/-
# Phillips-Brown (2025): Question-Based Desire Semantics

⟦S wants p⟧^c = 1 iff all best answers in Q_c-Bel_S are p-answers.

Reference: Phillips-Brown, M. (2025). Some-things-considered desire. S&P.
-/

import Linglib.Theories.Montague.Modal.Kratzer
import Linglib.Theories.Montague.Question.Hamblin
import Linglib.Core.SatisfactionOrdering

namespace Montague.Modal.PhillipsBrown

open Montague.Verb.Attitude.Examples
open Montague.Modal.Kratzer
open Montague.Question.Hamblin

/-- p entails q iff every p-world is a q-world.
    Uses Core.SatisfactionOrdering.propEntails with global allWorlds. -/
def propEntails (p q : Prop') : Bool :=
  Core.SatisfactionOrdering.propEntails allWorlds p q

/-- Propositions overlap iff they share at least one world. -/
def propOverlap (p q : Prop') : Bool :=
  allWorlds.any fun w => p w && q w

/-- Desires from G_S that proposition a satisfies (a entails p). -/
def satisfiedBy (GS : List Prop') (a : Prop') : List Prop' :=
  GS.filter fun p => propEntails a p

/-- S prefers a to a' iff a satisfies strictly more desires. -/
def preferAnswer (GS : List Prop') (a a' : Prop') : Bool :=
  let desiresA := satisfiedBy GS a
  let desiresA' := satisfiedBy GS a'
  (desiresA'.all fun p => desiresA.any fun q => allWorlds.all fun w => p w == q w) &&
  (desiresA.any fun p => desiresA'.all fun q => allWorlds.any fun w => p w != q w)

/-- a ≥ a' iff a satisfies all desires that a' satisfies. -/
def atLeastAsPreferred (GS : List Prop') (a a' : Prop') : Bool :=
  let desiresA := satisfiedBy GS a
  let desiresA' := satisfiedBy GS a'
  desiresA'.all fun p => desiresA.any fun q => allWorlds.all fun w => p w == q w

/-- Q-Bel_S: answers compatible with S's beliefs. -/
def questionRelativeBelief (answers : List Prop') (belS : Prop') : List Prop' :=
  answers.filter fun a => propOverlap a belS

/-- Extensional equivalence of propositions. -/
def propEquiv (p q : Prop') : Bool :=
  allWorlds.all fun w => p w == q w

/-- Best answers: those not strictly dominated by any other. -/
def bestAnswers (GS : List Prop') (answers : List Prop') : List Prop' :=
  answers.filter fun a =>
    answers.all fun a' => propEquiv a' a || !preferAnswer GS a' a

/-- ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def wantQuestionBased (belS : Prop') (GS : List Prop')
    (answers : List Prop') (p : Prop') : Bool :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  best.all fun a => propEntails a p

/-- Convenience: extract desires from BouleticFlavor. -/
def wantBouletic (belS : Prop') (flavor : BouleticFlavor) (w : World)
    (answers : List Prop') (p : Prop') : Bool :=
  wantQuestionBased belS (flavor.desires w) answers p

-- Metasemantic constraints (felicity conditions on Q_c)

/-- Considering: Q must have both p-answers and ¬p-answers. -/
def considering (answers : List Prop') (p : Prop') : Bool :=
  (answers.any fun a => propEntails a p) &&
  (answers.any fun a => propEntails a (fun w => !p w))

/-- Diversity: |Q-Bel_S| ≥ 2. -/
def diversity (answers : List Prop') (belS : Prop') : Bool :=
  (questionRelativeBelief answers belS).length ≥ 2

/-- Anti-deckstacking: question shouldn't trivially favor p.

This prevents "rigged" questions that make the desire ascription vacuously true.
-/
def antiDeckstacking (answers : List Prop') (belS : Prop') (GS : List Prop') (p : Prop') : Bool :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  (best.any fun a => !propEntails a p) ||
  (qBelS.any fun a => propEntails a (fun w => !p w) &&
    qBelS.any fun a' => propEntails a' p && preferAnswer GS a' a)

/--
**Belief-sensitivity**: S's beliefs affect the truth value.

This is built into the semantics via Q-Bel_S, but we can test whether
the desire ascription is sensitive to belief changes.
-/
def beliefSensitive (answers : List Prop') (GS : List Prop') (p : Prop')
    (belS belS' : Prop') : Bool :=
  wantQuestionBased belS GS answers p != wantQuestionBased belS' GS answers p

-- ============================================================================
-- Key Theorems
-- ============================================================================

/--
**Theorem: Preference between answers is transitive.**

If S prefers a to a' and a' to a'', then S prefers a to a''.
-/
theorem prefer_answer_transitive (GS : List Prop') (a a' a'' : Prop')
    (h1 : atLeastAsPreferred GS a a' = true)
    (h2 : atLeastAsPreferred GS a' a'' = true) :
    atLeastAsPreferred GS a a'' = true := by
  unfold atLeastAsPreferred at *
  simp only [List.all_eq_true] at *
  intro p hp
  obtain ⟨q, hq, hpq⟩ := List.any_eq_true.mp (h2 p hp)
  obtain ⟨r, hr, hqr⟩ := List.any_eq_true.mp (h1 q hq)
  apply List.any_eq_true.mpr
  use r, hr
  simp only [List.all_eq_true] at hpq hqr ⊢
  intro w hw
  have hpq_w := hpq w hw
  have hqr_w := hqr w hw
  simp only [beq_iff_eq] at hpq_w hqr_w ⊢
  rw [← hqr_w, ← hpq_w]

/--
**Theorem: Empty desires make all answers equivalent.**

When G_S = ∅, no answer is preferred over another, so the agent is indifferent.
-/
theorem empty_desires_indifferent (a a' : Prop') :
    atLeastAsPreferred [] a a' = true := by
  unfold atLeastAsPreferred satisfiedBy
  simp

/--
**Theorem: With empty desires, want reduces to belief compatibility.**

If G_S = ∅, then ⟦S wants p⟧ = 1 iff every answer in Q-Bel_S entails p.
-/
theorem empty_desires_belief_only (belS : Prop') (answers : List Prop') (p : Prop') :
    wantQuestionBased belS [] answers p =
    (questionRelativeBelief answers belS).all fun a => propEntails a p := by
  unfold wantQuestionBased bestAnswers preferAnswer satisfiedBy
  simp only [List.filter_nil, List.all_nil, List.any_nil, Bool.and_false,
             Bool.not_false, Bool.or_true]
  congr 1
  have : ∀ (L : List Prop'), L.filter (fun _ => L.all fun _ => true) = L := by
    intro L
    rw [List.filter_eq_self]
    intros
    simp only [List.all_eq_true]
    intros
    trivial
  exact this _

-- ============================================================================
-- C-distributivity (Phillips-Brown §4)
-- ============================================================================

/-!
## C-distributivity

A key diagnostic for question-sensitivity: whether ⟦x V Q⟧ ↔ ∃p ∈ Q. ⟦x V p⟧.

"Want" is NOT c-distributive in Phillips-Brown's analysis, while
"know" and "wonder" are.
-/

/--
Test whether a predicate is c-distributive for a given scenario.

Returns true iff semantics(Q, p) = ∃a ∈ Q. semantics({a}, p)
-/
def isCDistributive (semantics : List Prop' → Prop' → Bool)
    (answers : List Prop') (p : Prop') : Bool :=
  let wholeQ := semantics answers p
  let existsSingle := answers.any fun a => semantics [a] p
  wholeQ == existsSingle

-- ============================================================================
-- Connection to Core.SatisfactionOrdering Framework
-- ============================================================================

open Core.SatisfactionOrdering

/-- Proposition ordering: a satisfies p iff a entails p. -/
def propositionOrdering (GS : List Prop') : SatisfactionOrdering Prop' Prop' where
  satisfies := fun a p => propEntails a p
  ideals := GS

-- Connection theorems: local definitions = generic framework

/-- satisfiedBy matches SatisfactionOrdering.satisfiedBy. -/
theorem satisfiedBy_eq_generic (GS : List Prop') (a : Prop') :
    satisfiedBy GS a = (propositionOrdering GS).satisfiedBy a := by
  unfold satisfiedBy propositionOrdering SatisfactionOrdering.satisfiedBy
  rfl

/-- Preorder derived from proposition ordering. -/
def propositionPreorder (GS : List Prop') : Preorder Prop' :=
  (propositionOrdering GS).toPreorder

end Montague.Modal.PhillipsBrown

-- ============================================================================
-- BouleticFlavor Extension: Question-Based Desire Semantics
-- ============================================================================

namespace Montague.Modal.Kratzer.BouleticFlavor

open Montague.Verb.Attitude.Examples
open Montague.Modal.Kratzer
open Montague.Modal.PhillipsBrown

/-- Question-based desire: ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def evalWant (self : BouleticFlavor) (w : World)
    (belS : Prop') (question : List Prop') (p : Prop') : Bool :=
  wantQuestionBased belS (self.desires w) question p

/-- Preference ordering on propositions at world w. -/
def preferenceOrdering (self : BouleticFlavor) (w : World) :
    Core.SatisfactionOrdering.SatisfactionOrdering Prop' Prop' :=
  propositionOrdering (self.desires w)

/-- Best answers according to S's desires at world w. -/
def getBestAnswers (self : BouleticFlavor) (w : World) (answers : List Prop') :
    List Prop' :=
  bestAnswers (self.desires w) answers

/-- Answers compatible with S's beliefs. -/
def liveAnswers (_self : BouleticFlavor) (question : List Prop') (belS : Prop') :
    List Prop' :=
  questionRelativeBelief question belS

end Montague.Modal.Kratzer.BouleticFlavor

namespace Montague.Modal.PhillipsBrown

open Montague.Verb.Attitude.Examples
open Montague.Modal.Kratzer

/--
**Theorem: BouleticFlavor.evalWant = wantQuestionBased.**

The extension is definitionally equal to the standalone function.
-/
theorem bouletic_evalWant_eq (flavor : BouleticFlavor) (w : World)
    (belS : Prop') (question : List Prop') (p : Prop') :
    flavor.evalWant w belS question p =
    wantQuestionBased belS (flavor.desires w) question p := rfl

/--
**Corollary: Empty bouletic desires → agent is indifferent.**
-/
theorem empty_bouletic_indifferent (w : World) (a a' : Prop') :
    preferAnswer (emptyBackground w) a a' = false := by
  unfold preferAnswer satisfiedBy emptyBackground
  simp

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Summary: Phillips-Brown (2025) Integration

### Core Functions
- `satisfiedBy GS a`: desires that proposition a satisfies
- `preferAnswer GS a a'`: S prefers a to a'
- `bestAnswers GS answers`: optimal answers under preference
- `questionRelativeBelief answers belS`: Q-Bel_S, live answers
- `wantQuestionBased belS GS answers p`: main semantics
- `wantBouletic`: convenience wrapper using BouleticFlavor

### Metasemantic Constraints
- `considering`: prejacent under consideration
- `diversity`: multiple live answers
- `antiDeckstacking`: question not rigged
- `beliefSensitive`: beliefs affect truth

### Key Properties
- Preference is transitive (`prefer_answer_transitive`)
- Empty desires → indifference (`empty_desires_indifferent`)
- Automatically inherits from Kratzer's `BouleticFlavor`

### The Unified Framework

| Concept | Kratzer (Worlds) | Phillips-Brown (Props) | Generic |
|---------|-----------------|------------------------|---------|
| Type | `World` | `Prop'` | `α` |
| Ideals | `List Prop'` | `List Prop'` | `List Ideal` |
| Satisfies | `p w` | `propEntails a p` | `o.satisfies` |
| Ordering | `atLeastAsGoodAs` | `atLeastAsPreferred` | `atLeastAsGood` |
| Best | `bestWorlds` | `bestAnswers` | `best` |
-/

end Montague.Modal.PhillipsBrown
