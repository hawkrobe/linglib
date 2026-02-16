/-
# Phillips-Brown (2025): Question-Based Desire Semantics

⟦S wants p⟧^c = 1 iff all best answers in Q_c-Bel_S are p-answers.

Reference: Phillips-Brown, M. (2025). Some-things-considered desire. S&P.
-/

import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Theories.Semantics.Modality.SatisfactionOrdering

namespace IntensionalSemantics.Modal.PhillipsBrown

open IntensionalSemantics.Attitude.Intensional
open IntensionalSemantics.Modal.Kratzer
open QuestionSemantics.Hamblin

/-- p entails q iff every p-world is a q-world. -/
def propEntails (p q : BProp World) : Bool :=
  IntensionalSemantics.Modal.propEntails allWorlds p q

/-- Propositions overlap iff they share at least one world. -/
def propOverlap (p q : BProp World) : Bool :=
  allWorlds.any λ w => p w && q w

/-- Desires from G_S that proposition a satisfies (a entails p). -/
def satisfiedBy (GS : List (BProp World)) (a : BProp World) : List (BProp World) :=
  GS.filter λ p => propEntails a p

/-- S prefers a to a' iff a satisfies strictly more desires. -/
def preferAnswer (GS : List (BProp World)) (a a' : BProp World) : Bool :=
  let desiresA := satisfiedBy GS a
  let desiresA' := satisfiedBy GS a'
  (desiresA'.all λ p => desiresA.any λ q => allWorlds.all λ w => p w == q w) &&
  (desiresA.any λ p => desiresA'.all λ q => allWorlds.any λ w => p w != q w)

/-- a ≥ a' iff a satisfies all desires that a' satisfies. -/
def atLeastAsPreferred (GS : List (BProp World)) (a a' : BProp World) : Bool :=
  let desiresA := satisfiedBy GS a
  let desiresA' := satisfiedBy GS a'
  desiresA'.all λ p => desiresA.any λ q => allWorlds.all λ w => p w == q w

/-- Q-Bel_S: answers compatible with S's beliefs. -/
def questionRelativeBelief (answers : List (BProp World)) (belS : BProp World) : List (BProp World) :=
  answers.filter λ a => propOverlap a belS

/-- Extensional equivalence of propositions. -/
def propEquiv (p q : BProp World) : Bool :=
  allWorlds.all λ w => p w == q w

/-- Best answers: those not strictly dominated by any other. -/
def bestAnswers (GS : List (BProp World)) (answers : List (BProp World)) : List (BProp World) :=
  answers.filter λ a =>
    answers.all λ a' => propEquiv a' a || !preferAnswer GS a' a

/-- ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def wantQuestionBased (belS : BProp World) (GS : List (BProp World))
    (answers : List (BProp World)) (p : BProp World) : Bool :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  best.all λ a => propEntails a p

/-- Convenience: extract desires from BouleticFlavor. -/
def wantBouletic (belS : BProp World) (flavor : BouleticFlavor) (w : World)
    (answers : List (BProp World)) (p : BProp World) : Bool :=
  wantQuestionBased belS (flavor.desires w) answers p

-- Metasemantic constraints (felicity conditions on Q_c)

/-- Considering: Q must have both p-answers and ¬p-answers. -/
def considering (answers : List (BProp World)) (p : BProp World) : Bool :=
  (answers.any λ a => propEntails a p) &&
  (answers.any λ a => propEntails a (λ w => !p w))

/-- Diversity: |Q-Bel_S| ≥ 2. -/
def diversity (answers : List (BProp World)) (belS : BProp World) : Bool :=
  (questionRelativeBelief answers belS).length ≥ 2

/-- Anti-deckstacking: question shouldn't trivially favor p.

This prevents "rigged" questions that make the desire ascription vacuously true.
-/
def antiDeckstacking (answers : List (BProp World)) (belS : BProp World) (GS : List (BProp World)) (p : BProp World) : Bool :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  (best.any λ a => !propEntails a p) ||
  (qBelS.any λ a => propEntails a (λ w => !p w) &&
    qBelS.any λ a' => propEntails a' p && preferAnswer GS a' a)

/--
**Belief-sensitivity**: S's beliefs affect the truth value.

This is built into the semantics via Q-Bel_S, but we can test whether
the desire ascription is sensitive to belief changes.
-/
def beliefSensitive (answers : List (BProp World)) (GS : List (BProp World)) (p : BProp World)
    (belS belS' : BProp World) : Bool :=
  wantQuestionBased belS GS answers p != wantQuestionBased belS' GS answers p

-- Key Theorems

/--
**Theorem: Preference between answers is transitive.**

If S prefers a to a' and a' to a'', then S prefers a to a''.
-/
theorem prefer_answer_transitive (GS : List (BProp World)) (a a' a'' : BProp World)
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
theorem empty_desires_indifferent (a a' : BProp World) :
    atLeastAsPreferred [] a a' = true := by
  unfold atLeastAsPreferred satisfiedBy
  simp

/--
**Theorem: With empty desires, want reduces to belief compatibility.**

If G_S = ∅, then ⟦S wants p⟧ = 1 iff every answer in Q-Bel_S entails p.
-/
theorem empty_desires_belief_only (belS : BProp World) (answers : List (BProp World)) (p : BProp World) :
    wantQuestionBased belS [] answers p =
    (questionRelativeBelief answers belS).all λ a => propEntails a p := by
  unfold wantQuestionBased bestAnswers preferAnswer satisfiedBy
  simp only [List.filter_nil, List.all_nil, List.any_nil, Bool.and_false,
             Bool.not_false, Bool.or_true]
  congr 1
  have : ∀ (L : List (BProp World)), L.filter (λ _ => L.all λ _ => true) = L := by
    intro L
    rw [List.filter_eq_self]
    intros
    simp only [List.all_eq_true]
    intros
    trivial
  exact this _

-- C-distributivity (Phillips-Brown §4)

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
def isCDistributive (semantics : List (BProp World) → BProp World → Bool)
    (answers : List (BProp World)) (p : BProp World) : Bool :=
  let wholeQ := semantics answers p
  let existsSingle := answers.any λ a => semantics [a] p
  wholeQ == existsSingle

-- Connection to Core.SatisfactionOrdering

open Core.SatisfactionOrdering

/-- Proposition ordering: a satisfies p iff a entails p. -/
def propositionOrdering (GS : List (BProp World)) : SatisfactionOrdering (BProp World) (BProp World) where
  satisfies := λ a p => propEntails a p
  criteria := GS

-- Connection theorems: local definitions = generic framework

/-- satisfiedBy matches SatisfactionOrdering.satisfiedBy. -/
theorem satisfiedBy_eq_generic (GS : List (BProp World)) (a : BProp World) :
    satisfiedBy GS a = (propositionOrdering GS).satisfiedBy a := by
  unfold satisfiedBy propositionOrdering SatisfactionOrdering.satisfiedBy
  rfl

/-- Preorder derived from proposition ordering. -/
def propositionPreorder (GS : List (BProp World)) : Preorder (BProp World) :=
  (propositionOrdering GS).toPreorder

end IntensionalSemantics.Modal.PhillipsBrown

-- BouleticFlavor Extension: Question-Based Desire Semantics

namespace IntensionalSemantics.Modal.Kratzer.BouleticFlavor

open IntensionalSemantics.Attitude.Intensional
open IntensionalSemantics.Modal.Kratzer
open IntensionalSemantics.Modal.PhillipsBrown

/-- Question-based desire: ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def evalWant (self : BouleticFlavor) (w : World)
    (belS : BProp World) (question : List (BProp World)) (p : BProp World) : Bool :=
  wantQuestionBased belS (self.desires w) question p

/-- Preference ordering on propositions at world w. -/
def preferenceOrdering (self : BouleticFlavor) (w : World) :
    Core.SatisfactionOrdering.SatisfactionOrdering (BProp World) (BProp World) :=
  PhillipsBrown.propositionOrdering (self.desires w)

/-- Best answers according to S's desires at world w. -/
def getBestAnswers (self : BouleticFlavor) (w : World) (answers : List (BProp World)) :
    List (BProp World) :=
  bestAnswers (self.desires w) answers

/-- Answers compatible with S's beliefs. -/
def liveAnswers (_self : BouleticFlavor) (question : List (BProp World)) (belS : BProp World) :
    List (BProp World) :=
  questionRelativeBelief question belS

end IntensionalSemantics.Modal.Kratzer.BouleticFlavor

namespace IntensionalSemantics.Modal.PhillipsBrown

open IntensionalSemantics.Attitude.Intensional
open IntensionalSemantics.Modal.Kratzer

/--
**Theorem: BouleticFlavor.evalWant = wantQuestionBased.**

The extension is definitionally equal to the standalone function.
-/
theorem bouletic_evalWant_eq (flavor : BouleticFlavor) (w : World)
    (belS : BProp World) (question : List (BProp World)) (p : BProp World) :
    flavor.evalWant w belS question p =
    wantQuestionBased belS (flavor.desires w) question p := rfl

/--
**Corollary: Empty bouletic desires → agent is indifferent.**
-/
theorem empty_bouletic_indifferent (w : World) (a a' : BProp World) :
    preferAnswer (emptyBackground w) a a' = false := by
  unfold preferAnswer satisfiedBy emptyBackground
  simp

-- Summary

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
| Type | `World` | `BProp World` | `α` |
| Ideals | `List (BProp World)` | `List (BProp World)` | `List Ideal` |
| Satisfies | `p w` | `propEntails a p` | `o.satisfies` |
| Ordering | `atLeastAsGoodAs` | `atLeastAsPreferred` | `atLeastAsGood` |
| Best | `bestWorlds` | `bestAnswers` | `best` |
-/

end IntensionalSemantics.Modal.PhillipsBrown
