/-
# @cite{phillips-brown-2025}: Question-Based Desire Semantics

⟦S wants p⟧^c = 1 iff all best answers in Q_c-Bel_S are p-answers.

Reference: Phillips-Brown, M. (2025). Some-things-considered desire. S&P.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Core.Semantics.Presupposition
import Mathlib.Order.Basic

-- ============================================================================
-- §1. Generic question-based desire semantics
-- ============================================================================

namespace Semantics.Modality.Desire

open Core.Proposition (FiniteWorlds)
open Core.Presupposition (PrProp)
open Core.Order (SatisfactionOrdering)

section Generic

variable {W : Type*} [FiniteWorlds W] [DecidableEq W]

/-- p entails q iff every p-world is a q-world.
    Delegates to `FiniteWorlds.entails` from `Core/Semantics/Proposition.lean`. -/
abbrev propEntails (p q : (W → Bool)) : Bool :=
  FiniteWorlds.entails W p q

/-- Propositions overlap iff they share at least one world.
    Delegates to `FiniteWorlds.overlap` from `Core/Semantics/Proposition.lean`. -/
abbrev propOverlap (p q : (W → Bool)) : Bool :=
  FiniteWorlds.overlap W p q

-- ============================================================================
-- §1a. Satisfaction orderings
-- ============================================================================

/-- Proposition ordering: a satisfies desire p iff a entails p.
    This is the core ordering that drives Phillips-Brown's preference relation:
    answer a is at least as preferred as a' iff a satisfies every desire
    that a' satisfies (subset inclusion on satisfied desires).

    Parallel to `Kratzer.worldOrdering` but for propositions rather than worlds. -/
def propositionOrdering (GS : List ((W → Bool))) : SatisfactionOrdering ((W → Bool)) ((W → Bool)) :=
  SatisfactionOrdering.ofCriteria (fun a p => propEntails a p) GS

/-- World ordering as a `SatisfactionOrdering`. Parallels `Kratzer.worldOrdering`
    but generic over any `[FiniteWorlds W]`. A world w satisfies proposition p
    iff p(w) = true. -/
def worldSatisfactionOrdering (GS : List ((W → Bool))) :
    SatisfactionOrdering W ((W → Bool)) :=
  SatisfactionOrdering.ofCriteria (fun w p => p w) GS

-- ============================================================================
-- §1b. Derived definitions (thin wrappers over satisfaction orderings)
-- ============================================================================

/-- Desires from G_S that proposition a satisfies (a entails p). -/
abbrev satisfiedBy (GS : List ((W → Bool))) (a : (W → Bool)) : List ((W → Bool)) :=
  (propositionOrdering GS).satisfiedBy a

/-- a ≥ a' iff a satisfies all desires that a' satisfies. -/
abbrev atLeastAsPreferred (GS : List ((W → Bool))) (a a' : (W → Bool)) : Prop :=
  (propositionOrdering GS).le a a'

/-- Kratzer-style world ordering: w at least as good as z iff w satisfies
    every ordering source proposition that z satisfies. -/
abbrev worldAtLeastAsGood (GS : List ((W → Bool))) (w z : W) : Prop :=
  (worldSatisfactionOrdering GS).le w z

/-- Q-Bel_S: answers compatible with S's beliefs. -/
def questionRelativeBelief (answers : List ((W → Bool))) (belS : (W → Bool)) : List ((W → Bool)) :=
  answers.filter λ a => propOverlap a belS

/-- Best answers: those not strictly dominated (Pareto frontier).
    Derived from `SatisfactionOrdering.undominated`. -/
abbrev bestAnswers (GS : List ((W → Bool))) (answers : List ((W → Bool))) : List ((W → Bool)) :=
  (propositionOrdering GS).undominated answers

-- ============================================================================
-- §1c. Core semantics
-- ============================================================================

/-- ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def wantQuestionBased (belS : (W → Bool)) (GS : List ((W → Bool)))
    (answers : List ((W → Bool))) (p : (W → Bool)) : Prop :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  ∀ a ∈ best, propEntails a p = true

instance (belS : (W → Bool)) (GS answers : List ((W → Bool))) (p : (W → Bool)) :
    Decidable (wantQuestionBased belS GS answers p) :=
  inferInstanceAs (Decidable (∀ a ∈ _, _))

/-- Standard von Fintel semantics (not question-based):
    ⟦S wants p⟧ = all best worlds in Bel_S are p-worlds.
    Best = undominated under Kratzer ordering.

    This is the baseline that the question-based semantics generalizes:
    when Q_c is the finest question (singleton cells), `wantQuestionBased`
    reduces to `wantVF`. -/
def wantVF (belS : (W → Bool)) (GS : List ((W → Bool))) (p : (W → Bool)) : Prop :=
  let belWorlds := FiniteWorlds.worlds.filter belS
  let best := (worldSatisfactionOrdering GS).undominated belWorlds
  ∀ w ∈ best, p w = true

instance (belS : (W → Bool)) (GS : List ((W → Bool))) (p : (W → Bool)) :
    Decidable (wantVF belS GS p) :=
  inferInstanceAs (Decidable (∀ w ∈ _, _))

-- ============================================================================
-- §2. Metasemantic constraints
-- ============================================================================

/-- p is *considered* relative to Q iff every answer settles p.
**Considering Constraint** (§3.6): ⟦S wants p⟧^c is defined only if p is
considered relative to Q_c. -/
def isConsidered (answers : List ((W → Bool))) (p : (W → Bool)) : Prop :=
  ∀ a ∈ answers, propEntails a p = true ∨ propEntails a (λ w => !p w) = true

instance (answers : List ((W → Bool))) (p : (W → Bool)) : Decidable (isConsidered answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Diversity** (§3.7): Q_c must contain both p-answers and ¬p-answers. -/
def isDiverse (answers : List ((W → Bool))) (p : (W → Bool)) : Prop :=
  (∃ a ∈ answers, propEntails a p = true) ∧
  (∃ a ∈ answers, propEntails a (λ w => !p w) = true)

instance (answers : List ((W → Bool))) (p : (W → Bool)) : Decidable (isDiverse answers p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Anti-deckstacking Constraint** (§3.7): for all q, if some answer to Q_c
is a q-answer, then q must be considered relative to Q_c. This prevents
questions from "stacking the deck" by letting one side of q entail a
desirable proposition that the other side cannot.

Implementation: enumerate all propositions (power set of worlds) and check
each one. For finite world types this is decidable. -/
def isAntiDeckstacking (answers : List ((W → Bool))) : Prop :=
  -- Generate all 2^|W| propositions as characteristic functions of subsets
  let allProps := FiniteWorlds.worlds.foldr
    (λ w acc => acc.flatMap λ q => [q, λ w' => q w' || (w' == w)])
    [λ _ => false]
  ∀ q ∈ allProps,
    -- If some answer entails q, then q must be considered
    (∀ a ∈ answers, propEntails a q ≠ true) ∨ isConsidered answers q

instance (answers : List ((W → Bool))) : Decidable (isAntiDeckstacking answers) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Belief-sensitivity Constraint** (§4.2): S's beliefs must be sensitive
to Q_c. That is, Q_c must make non-trivial distinctions within S's
belief state — there exist answers that overlap Bel_S and answers that
don't, or the agent's beliefs distinguish among answers.

This blocks inferences like Avoid-war ⊭ Avoid-nuclear-war when the agent
lacks the conceptual resources to grasp nuclear war. -/
def isBelSensitive (belS : (W → Bool)) (answers : List ((W → Bool))) : Prop :=
  -- Q_c-Bel_S is nonempty (agent's beliefs are compatible with some answer)
  -- AND Q_c-Bel_S ≠ Q_c (agent's beliefs rule out at least one answer)
  let live := questionRelativeBelief answers belS
  live ≠ [] ∧ live.length ≠ answers.length

instance (belS : (W → Bool)) (answers : List ((W → Bool))) :
    Decidable (isBelSensitive belS answers) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Full definedness condition for ⟦S wants p⟧^c.
Conjunction of Considering (§3.6), Diversity (§3.7), and Belief-sensitivity
(§4.2). Anti-deckstacking is omitted because the paper's universal
quantification over all propositions is too strong for finite models
(see study file §7 for discussion). -/
def wantDefined (belS : (W → Bool)) (answers : List ((W → Bool))) (p : (W → Bool)) : Prop :=
  isConsidered answers p ∧ isDiverse answers p ∧ isBelSensitive belS answers

instance (belS : (W → Bool)) (answers : List ((W → Bool))) (p : (W → Bool)) :
    Decidable (wantDefined belS answers p) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- §3. PrProp integration
-- ============================================================================

/-- Question-based `want` as a partial proposition.

`presup` = Considering ∧ Diversity ∧ Belief-sensitivity (p must be
settled by every answer, both p-answers and ¬p-answers must exist,
and S's beliefs must be sensitive to Q_c).

`assertion` = all best answers in Q_c-Bel_S are p-answers.

The presupposition and assertion are world-independent because the
question-based semantics is evaluated at a fixed contextual question Q_c
— the world parameter is vestigial (needed only for `PrProp W`'s type). -/
def wantPrProp (belS : (W → Bool)) (GS : List ((W → Bool)))
    (answers : List ((W → Bool))) (p : (W → Bool)) : PrProp W where
  presup _ := wantDefined belS answers p
  assertion _ := wantQuestionBased belS GS answers p

-- ============================================================================
-- §4. Key theorems (generic)
-- ============================================================================

omit [DecidableEq W] in
/-- Preference between answers is transitive (delegates to framework). -/
theorem prefer_answer_transitive (GS : List ((W → Bool))) (a a' a'' : (W → Bool))
    (h1 : atLeastAsPreferred GS a a')
    (h2 : atLeastAsPreferred GS a' a'') :
    atLeastAsPreferred GS a a'' :=
  (propositionOrdering GS).le_trans a a' a'' h1 h2

omit [DecidableEq W] in
/-- Empty desires make all answers equivalent (delegates to framework). -/
theorem empty_desires_indifferent (a a' : (W → Bool)) :
    atLeastAsPreferred ([] : List ((W → Bool))) a a' :=
  SatisfactionOrdering.ofCriteria_empty_le _ a a'

omit [DecidableEq W] in
/-- With empty desires, want reduces to belief compatibility.
    Delegates to `ofCriteria_empty_undominated` from the framework. -/
theorem empty_desires_belief_only (belS : (W → Bool)) (answers : List ((W → Bool))) (p : (W → Bool)) :
    wantQuestionBased belS [] answers p ↔
    ∀ a ∈ questionRelativeBelief answers belS, propEntails a p = true := by
  unfold wantQuestionBased
  show (∀ a ∈ (propositionOrdering ([] : List ((W → Bool)))).undominated _, _) ↔ _
  rw [show propositionOrdering ([] : List ((W → Bool))) =
        SatisfactionOrdering.ofCriteria (fun a p => propEntails a p) [] from rfl,
      SatisfactionOrdering.ofCriteria_empty_undominated]

-- ============================================================================
-- §4a. Preorder instances
-- ============================================================================

/-- The proposition preference ordering as a `NormalityOrder`.
    Connects desire semantics to the default reasoning infrastructure. -/
def propositionNormality (GS : List ((W → Bool))) : Core.Order.NormalityOrder ((W → Bool)) :=
  (propositionOrdering GS).toNormalityOrder

/-- The proposition preference ordering as a Mathlib `Preorder`.
    Parallel to `Kratzer.kratzerPreorder` for worlds.

    This enables Mathlib's order-theoretic lemmas (monotonicity, chains,
    `le_trans`, etc.) for the desire preference relation. -/
@[reducible] def propositionPreorder (GS : List ((W → Bool))) : Preorder ((W → Bool)) :=
  (propositionOrdering GS).toPreorder

/-- The world ordering as a `NormalityOrder` (generic over `[FiniteWorlds W]`).
    Parallel to `Kratzer.kratzerNormality` but not restricted to `World4`. -/
def worldNormality (GS : List ((W → Bool))) : Core.Order.NormalityOrder W :=
  (worldSatisfactionOrdering GS).toNormalityOrder

/-- The world ordering as a Mathlib `Preorder` (generic over `[FiniteWorlds W]`). -/
@[reducible] def worldPreorder (GS : List ((W → Bool))) : Preorder W :=
  (worldSatisfactionOrdering GS).toPreorder

end Generic

end Semantics.Modality.Desire

-- ============================================================================
-- §5. BouleticFlavor Extension (specialized to World = World4)
-- ============================================================================

namespace Semantics.Modality.Kratzer.BouleticFlavor

open Semantics.Attitudes.Intensional
open Semantics.Modality.Kratzer
open Semantics.Modality.Desire
open Core.Order (SatisfactionOrdering)

/-- Question-based desire: ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def evalWant (self : BouleticFlavor World) (w : World)
    (belS : (World → Bool)) (question : List ((World → Bool))) (p : (World → Bool)) : Prop :=
  wantQuestionBased belS (self.desires w) question p

instance (self : BouleticFlavor World) (w : World)
    (belS : (World → Bool)) (question : List ((World → Bool))) (p : (World → Bool)) :
    Decidable (self.evalWant w belS question p) :=
  inferInstanceAs (Decidable (wantQuestionBased _ _ _ _))

/-- Preference ordering on propositions at world w. -/
def preferenceOrdering (self : BouleticFlavor World) (w : World) :
    SatisfactionOrdering ((World → Bool)) ((World → Bool)) :=
  Desire.propositionOrdering (self.desires w)

/-- Best answers according to S's desires at world w. -/
def getBestAnswers (self : BouleticFlavor World) (w : World) (answers : List ((World → Bool))) :
    List ((World → Bool)) :=
  bestAnswers (self.desires w) answers

/-- Answers compatible with S's beliefs. -/
def liveAnswers (_self : BouleticFlavor World) (question : List ((World → Bool))) (belS : (World → Bool)) :
    List ((World → Bool)) :=
  questionRelativeBelief question belS

end Semantics.Modality.Kratzer.BouleticFlavor

namespace Semantics.Modality.Desire

open Semantics.Attitudes.Intensional
open Semantics.Modality.Kratzer
open Core.Order (SatisfactionOrdering)

/-- BouleticFlavor.evalWant = wantQuestionBased (definitionally equal). -/
theorem bouletic_evalWant_eq (flavor : BouleticFlavor World) (w : World)
    (belS : (World → Bool)) (question : List ((World → Bool))) (p : (World → Bool)) :
    flavor.evalWant w belS question p ↔
    wantQuestionBased belS (flavor.desires w) question p := Iff.rfl

/-- Empty bouletic desires → no proposition strictly dominates another. -/
theorem empty_bouletic_no_strict_preference (w : World) (a a' : (World → Bool)) :
    ¬ (propositionOrdering (emptyBackground w)).strictlyBetter a a' := by
  rintro ⟨_, hnle⟩
  exact hnle (by unfold emptyBackground; exact empty_desires_indifferent a' a)

-- Summary

/-!
## Summary: @cite{phillips-brown-2025} Integration

### Architecture

All preference and ordering definitions derive from `SatisfactionOrdering`:

```
SatisfactionOrdering (generic framework)
  ├── propositionOrdering GS     — propositions ranked by desire satisfaction
  │   ├── .satisfiedBy a         = satisfiedBy GS a
  │   ├── .atLeastAsGood a a'    = atLeastAsPreferred GS a a'
  │   ├── .undominated answers   = bestAnswers GS answers
  │   ├── .toNormalityOrder      = propositionNormality GS
  │   └── propositionPreorder GS : Preorder ((W → Bool))
  │
  └── worldSatisfactionOrdering GS — worlds ranked by proposition satisfaction
      ├── .atLeastAsGood w z     = worldAtLeastAsGood GS w z
      ├── .undominated belWorlds → used by wantVF
      ├── .toNormalityOrder      = worldNormality GS
      └── worldPreorder GS      : Preorder W
```

### Core Functions (generic over `[FiniteWorlds W]`)
- `wantQuestionBased belS GS answers p`: main semantics
- `wantVF belS GS p`: standard von Fintel baseline

### Metasemantic Constraints
- `isConsidered Q p`: every answer settles p (§3.6)
- `isDiverse Q p`: both p-answers and ¬p-answers exist (§3.7)
- `isAntiDeckstacking Q`: no deck-stacking (§3.7)
- `isBelSensitive belS Q`: beliefs sensitive to Q (§4.2)

### PrProp Integration
- `wantPrProp belS GS answers p`: `want` as a partial proposition

### Key Properties
- Preference is transitive (`prefer_answer_transitive` — delegates to `atLeastAsGood_trans`)
- Empty desires → indifference (`empty_desires_indifferent`)
- `Preorder` instances for both proposition and world orderings
- Automatically inherits from Kratzer's `BouleticFlavor`

### The Unified Framework

| Concept | Kratzer (Worlds) | Phillips-Brown (Props) | Generic |
|---------|-----------------|------------------------|---------|
| Type | `World` | `(W → Bool)` | `α` |
| Ideals | `List ((W → Bool))` | `List ((W → Bool))` | `List Criterion` |
| Satisfies | `p w` | `propEntails a p` | `o.satisfies` |
| Ordering | `worldAtLeastAsGood` | `atLeastAsPreferred` | `atLeastAsGood` |
| Best | `wantVF` (undominated) | `bestAnswers` (undominated) | `undominated` |
| Preorder | `worldPreorder` | `propositionPreorder` | `toNormalityOrder` |
-/

end Semantics.Modality.Desire
