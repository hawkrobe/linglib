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

open Core.Proposition (BProp FiniteWorlds)
open Core.Presupposition (PrProp)
open Core.SatisfactionOrdering

section Generic

variable {W : Type*} [FiniteWorlds W] [DecidableEq W]

/-- p entails q iff every p-world is a q-world.
    Delegates to `FiniteWorlds.entails` from `Core/Semantics/Proposition.lean`. -/
abbrev propEntails (p q : BProp W) : Bool :=
  FiniteWorlds.entails W p q

/-- Propositions overlap iff they share at least one world.
    Delegates to `FiniteWorlds.overlap` from `Core/Semantics/Proposition.lean`. -/
abbrev propOverlap (p q : BProp W) : Bool :=
  FiniteWorlds.overlap W p q

-- ============================================================================
-- §1a. Satisfaction orderings
-- ============================================================================

/-- Proposition ordering: a satisfies desire p iff a entails p.
    This is the core ordering that drives Phillips-Brown's preference relation:
    answer a is at least as preferred as a' iff a satisfies every desire
    that a' satisfies (subset inclusion on satisfied desires).

    Parallel to `Kratzer.worldOrdering` but for propositions rather than worlds. -/
def propositionOrdering (GS : List (BProp W)) : SatisfactionOrdering (BProp W) (BProp W) where
  satisfies := λ a p => propEntails a p
  criteria := GS

/-- World ordering as a `SatisfactionOrdering`. Parallels `Kratzer.worldOrdering`
    but generic over any `[FiniteWorlds W]`. A world w satisfies proposition p
    iff p(w) = true. -/
def worldSatisfactionOrdering (GS : List (BProp W)) :
    SatisfactionOrdering W (BProp W) where
  satisfies := λ w p => p w
  criteria := GS

-- ============================================================================
-- §1b. Derived definitions (thin wrappers over satisfaction orderings)
-- ============================================================================

/-- Desires from G_S that proposition a satisfies (a entails p). -/
abbrev satisfiedBy (GS : List (BProp W)) (a : BProp W) : List (BProp W) :=
  (propositionOrdering GS).satisfiedBy a

/-- a ≥ a' iff a satisfies all desires that a' satisfies. -/
abbrev atLeastAsPreferred (GS : List (BProp W)) (a a' : BProp W) : Bool :=
  (propositionOrdering GS).atLeastAsGood a a'

/-- Kratzer-style world ordering: w at least as good as z iff w satisfies
    every ordering source proposition that z satisfies. -/
abbrev worldAtLeastAsGood (GS : List (BProp W)) (w z : W) : Bool :=
  (worldSatisfactionOrdering GS).atLeastAsGood w z

/-- Q-Bel_S: answers compatible with S's beliefs. -/
def questionRelativeBelief (answers : List (BProp W)) (belS : BProp W) : List (BProp W) :=
  answers.filter λ a => propOverlap a belS

/-- Best answers: those not strictly dominated (Pareto frontier).
    Derived from `SatisfactionOrdering.undominated`. -/
abbrev bestAnswers (GS : List (BProp W)) (answers : List (BProp W)) : List (BProp W) :=
  (propositionOrdering GS).undominated answers

-- ============================================================================
-- §1c. Core semantics
-- ============================================================================

/-- ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def wantQuestionBased (belS : BProp W) (GS : List (BProp W))
    (answers : List (BProp W)) (p : BProp W) : Bool :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  best.all λ a => propEntails a p

/-- Standard von Fintel semantics (not question-based):
    ⟦S wants p⟧ = all best worlds in Bel_S are p-worlds.
    Best = undominated under Kratzer ordering.

    This is the baseline that the question-based semantics generalizes:
    when Q_c is the finest question (singleton cells), `wantQuestionBased`
    reduces to `wantVF`. -/
def wantVF (belS : BProp W) (GS : List (BProp W)) (p : BProp W) : Bool :=
  let belWorlds := FiniteWorlds.worlds.filter belS
  let best := (worldSatisfactionOrdering GS).undominated belWorlds
  best.all p

-- ============================================================================
-- §2. Metasemantic constraints
-- ============================================================================

/-- p is *considered* relative to Q iff every answer settles p.
**Considering Constraint** (§3.6): ⟦S wants p⟧^c is defined only if p is
considered relative to Q_c. -/
def isConsidered (answers : List (BProp W)) (p : BProp W) : Bool :=
  answers.all λ a => propEntails a p || propEntails a (λ w => !p w)

/-- **Diversity** (§3.7): Q_c must contain both p-answers and ¬p-answers. -/
def isDiverse (answers : List (BProp W)) (p : BProp W) : Bool :=
  (answers.any λ a => propEntails a p) &&
  (answers.any λ a => propEntails a (λ w => !p w))

/-- **Anti-deckstacking Constraint** (§3.7): for all q, if some answer to Q_c
is a q-answer, then q must be considered relative to Q_c. This prevents
questions from "stacking the deck" by letting one side of q entail a
desirable proposition that the other side cannot.

Implementation: enumerate all propositions (power set of worlds) and check
each one. For finite world types this is decidable. -/
def isAntiDeckstacking (answers : List (BProp W)) : Bool :=
  -- Generate all 2^|W| propositions as characteristic functions of subsets
  let allProps := FiniteWorlds.worlds.foldr
    (λ w acc => acc.flatMap λ q => [q, λ w' => q w' || (w' == w)])
    [λ _ => false]
  allProps.all λ q =>
    -- If some answer entails q...
    !(answers.any λ a => propEntails a q) ||
    -- ...then q must be considered (every answer settles q)
    isConsidered answers q

/-- **Belief-sensitivity Constraint** (§4.2): S's beliefs must be sensitive
to Q_c. That is, Q_c must make non-trivial distinctions within S's
belief state — there exist answers that overlap Bel_S and answers that
don't, or the agent's beliefs distinguish among answers.

This blocks inferences like Avoid-war ⊭ Avoid-nuclear-war when the agent
lacks the conceptual resources to grasp nuclear war. -/
def isBelSensitive (belS : BProp W) (answers : List (BProp W)) : Bool :=
  -- Q_c-Bel_S is nonempty (agent's beliefs are compatible with some answer)
  -- AND Q_c-Bel_S ≠ Q_c (agent's beliefs rule out at least one answer)
  let live := questionRelativeBelief answers belS
  !live.isEmpty && (live.length != answers.length)

/-- Full definedness condition for ⟦S wants p⟧^c.
Conjunction of Considering (§3.6), Diversity (§3.7), and Belief-sensitivity
(§4.2). Anti-deckstacking is omitted because the paper's universal
quantification over all propositions is too strong for finite models
(see study file §7 for discussion). -/
def wantDefined (belS : BProp W) (answers : List (BProp W)) (p : BProp W) : Bool :=
  isConsidered answers p && isDiverse answers p && isBelSensitive belS answers

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
def wantPrProp (belS : BProp W) (GS : List (BProp W))
    (answers : List (BProp W)) (p : BProp W) : PrProp W where
  presup := λ _ => wantDefined belS answers p
  assertion := λ _ => wantQuestionBased belS GS answers p

-- ============================================================================
-- §4. Key theorems (generic)
-- ============================================================================

omit [DecidableEq W] in
/-- Preference between answers is transitive (delegates to framework). -/
theorem prefer_answer_transitive (GS : List (BProp W)) (a a' a'' : BProp W)
    (h1 : atLeastAsPreferred GS a a' = true)
    (h2 : atLeastAsPreferred GS a' a'' = true) :
    atLeastAsPreferred GS a a'' = true :=
  SatisfactionOrdering.atLeastAsGood_trans (propositionOrdering GS) a a' a'' h1 h2

omit [DecidableEq W] in
/-- Empty desires make all answers equivalent (delegates to framework). -/
theorem empty_desires_indifferent (a a' : BProp W) :
    atLeastAsPreferred ([] : List (BProp W)) a a' = true := by
  show (propositionOrdering ([] : List (BProp W))).atLeastAsGood a a' = true
  unfold SatisfactionOrdering.atLeastAsGood SatisfactionOrdering.satisfiedBy propositionOrdering
  simp

omit [DecidableEq W] in
/-- With empty desires, want reduces to belief compatibility.
    Delegates to `empty_criteria_all_undominated` from the framework. -/
theorem empty_desires_belief_only (belS : BProp W) (answers : List (BProp W)) (p : BProp W) :
    wantQuestionBased belS [] answers p =
    (questionRelativeBelief answers belS).all λ a => propEntails a p := by
  unfold wantQuestionBased
  show ((propositionOrdering ([] : List (BProp W))).undominated _).all _ = _
  rw [SatisfactionOrdering.empty_criteria_all_undominated
    (propositionOrdering ([] : List (BProp W))) rfl]

-- ============================================================================
-- §4a. Preorder instances
-- ============================================================================

/-- The proposition preference ordering as a `NormalityOrder`.
    Connects desire semantics to the default reasoning infrastructure. -/
def propositionNormality (GS : List (BProp W)) : Core.Order.NormalityOrder (BProp W) :=
  (propositionOrdering GS).toNormalityOrder

/-- The proposition preference ordering as a Mathlib `Preorder`.
    Parallel to `Kratzer.kratzerPreorder` for worlds.

    This enables Mathlib's order-theoretic lemmas (monotonicity, chains,
    `le_trans`, etc.) for the desire preference relation. -/
def propositionPreorder (GS : List (BProp W)) : Preorder (BProp W) where
  le := (propositionNormality GS).le
  lt a b := (propositionNormality GS).le a b ∧ ¬(propositionNormality GS).le b a
  le_refl := (propositionNormality GS).le_refl
  le_trans a b c := (propositionNormality GS).le_trans a b c
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- The world ordering as a `NormalityOrder` (generic over `[FiniteWorlds W]`).
    Parallel to `Kratzer.kratzerNormality` but not restricted to `World4`. -/
def worldNormality (GS : List (BProp W)) : Core.Order.NormalityOrder W :=
  (worldSatisfactionOrdering GS).toNormalityOrder

/-- The world ordering as a Mathlib `Preorder` (generic over `[FiniteWorlds W]`). -/
def worldPreorder (GS : List (BProp W)) : Preorder W where
  le := (worldNormality GS).le
  lt a b := (worldNormality GS).le a b ∧ ¬(worldNormality GS).le b a
  le_refl := (worldNormality GS).le_refl
  le_trans a b c := (worldNormality GS).le_trans a b c
  lt_iff_le_not_ge _ _ := Iff.rfl

end Generic

end Semantics.Modality.Desire

-- ============================================================================
-- §5. BouleticFlavor Extension (specialized to World = World4)
-- ============================================================================

namespace Semantics.Modality.Kratzer.BouleticFlavor

open Semantics.Attitudes.Intensional
open Semantics.Modality.Kratzer
open Semantics.Modality.Desire
open Core.SatisfactionOrdering

/-- Question-based desire: ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def evalWant (self : BouleticFlavor World) (w : World)
    (belS : BProp World) (question : List (BProp World)) (p : BProp World) : Bool :=
  wantQuestionBased belS (self.desires w) question p

/-- Preference ordering on propositions at world w. -/
def preferenceOrdering (self : BouleticFlavor World) (w : World) :
    SatisfactionOrdering (BProp World) (BProp World) :=
  Desire.propositionOrdering (self.desires w)

/-- Best answers according to S's desires at world w. -/
def getBestAnswers (self : BouleticFlavor World) (w : World) (answers : List (BProp World)) :
    List (BProp World) :=
  bestAnswers (self.desires w) answers

/-- Answers compatible with S's beliefs. -/
def liveAnswers (_self : BouleticFlavor World) (question : List (BProp World)) (belS : BProp World) :
    List (BProp World) :=
  questionRelativeBelief question belS

end Semantics.Modality.Kratzer.BouleticFlavor

namespace Semantics.Modality.Desire

open Semantics.Attitudes.Intensional
open Semantics.Modality.Kratzer
open Core.SatisfactionOrdering

/-- BouleticFlavor.evalWant = wantQuestionBased (definitionally equal). -/
theorem bouletic_evalWant_eq (flavor : BouleticFlavor World) (w : World)
    (belS : BProp World) (question : List (BProp World)) (p : BProp World) :
    flavor.evalWant w belS question p =
    wantQuestionBased belS (flavor.desires w) question p := rfl

/-- Empty bouletic desires → no proposition strictly dominates another. -/
theorem empty_bouletic_no_strict_preference (w : World) (a a' : BProp World) :
    (propositionOrdering (emptyBackground w)).strictlyBetter a a' = false := by
  unfold SatisfactionOrdering.strictlyBetter
  have : (propositionOrdering (emptyBackground w)).atLeastAsGood a' a = true := by
    show atLeastAsPreferred (emptyBackground w) a' a = true
    unfold emptyBackground
    exact empty_desires_indifferent a' a
  simp [this]

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
  │   └── propositionPreorder GS : Preorder (BProp W)
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
| Type | `World` | `BProp W` | `α` |
| Ideals | `List (BProp W)` | `List (BProp W)` | `List Criterion` |
| Satisfies | `p w` | `propEntails a p` | `o.satisfies` |
| Ordering | `worldAtLeastAsGood` | `atLeastAsPreferred` | `atLeastAsGood` |
| Best | `wantVF` (undominated) | `bestAnswers` (undominated) | `undominated` |
| Preorder | `worldPreorder` | `propositionPreorder` | `toNormalityOrder` |
-/

end Semantics.Modality.Desire
