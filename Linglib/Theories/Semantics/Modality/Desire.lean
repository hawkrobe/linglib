/-
# @cite{phillips-brown-2025}: Question-Based Desire Semantics

⟦S wants p⟧^c = 1 iff all best answers in Q_c-Bel_S are p-answers.

Reference: Phillips-Brown, M. (2025). Some-things-considered desire. S&P.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Order.Satisfaction
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

-- ============================================================================
-- §1. Generic question-based desire semantics
-- ============================================================================

namespace Semantics.Modality.Desire

open Core.Presupposition (PrProp)
open Core.Order (SatisfactionOrdering)

section Generic

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A decidable proposition: a `Set W` bundled with its `DecidablePred`
    instance. Used as the element type of partition cells (answers) and
    desire lists, which need decidability for `decide`-based reasoning
    while keeping their semantic content `Prop`-valued.

    Defined as a structure (rather than a subtype) because `DecidablePred`
    lives in `Type`, not `Prop`. -/
structure DecProp (W : Type*) where
  /-- The underlying `Prop`-valued proposition. -/
  prop : Set W
  /-- Decidability witness. -/
  dec : DecidablePred prop

/-- Smart constructor for a `DecProp` from a `Set W` whose decidability
    can be inferred. -/
@[reducible] def mkDec (p : Set W) [h : DecidablePred p] : DecProp W := ⟨p, h⟩

instance (a : DecProp W) : DecidablePred a.prop := a.dec

/-- p entails q iff every world satisfies p → q (Prop-valued).

    Decidability follows from `Fintype W` + `DecidablePred p` + `DecidablePred q`
    via `Fintype.decidableForallFintype`. -/
def propEntails (p q : Set W) : Prop :=
  ∀ w, p w → q w

instance (p q : Set W) [DecidablePred p] [DecidablePred q] : Decidable (propEntails p q) :=
  Fintype.decidableForallFintype

/-- Propositions overlap iff some world satisfies both. -/
def propOverlap (p q : Set W) : Prop := ∃ w, p w ∧ q w

instance (p q : Set W) [DecidablePred p] [DecidablePred q] : Decidable (propOverlap p q) :=
  Fintype.decidableExistsFintype

-- ============================================================================
-- §1a. Satisfaction orderings
-- ============================================================================

/-- Proposition ordering: a satisfies desire p iff a entails p.
    This is the core ordering that drives Phillips-Brown's preference relation:
    answer a is at least as preferred as a' iff a satisfies every desire
    that a' satisfies (subset inclusion on satisfied desires).

    Parallel to `Kratzer.worldOrdering` but for propositions rather than worlds.

    The `SatisfactionOrdering` framework requires a `Bool`-valued `satisfies`
    relation, so we feed in `decide (propEntails …)` using the `DecidablePred`
    instance carried by each `DecProp`. -/
def propositionOrdering (GS : List (DecProp W)) :
    SatisfactionOrdering (DecProp W) (DecProp W) :=
  SatisfactionOrdering.ofCriteria (fun a p => decide (propEntails a.prop p.prop)) GS

/-- World ordering as a `SatisfactionOrdering`. Parallels `Kratzer.worldOrdering`
    but generic over any `[Fintype W]`. A world w satisfies proposition p
    iff p w. -/
def worldSatisfactionOrdering (GS : List (DecProp W)) :
    SatisfactionOrdering W (DecProp W) :=
  SatisfactionOrdering.ofCriteria (fun w p => decide (p.prop w)) GS

-- ============================================================================
-- §1b. Derived definitions (thin wrappers over satisfaction orderings)
-- ============================================================================

/-- Desires from G_S that proposition a satisfies (a entails p). -/
abbrev satisfiedBy (GS : List (DecProp W)) (a : DecProp W) : List (DecProp W) :=
  (propositionOrdering GS).satisfiedBy a

/-- a ≥ a' iff a satisfies all desires that a' satisfies. -/
abbrev atLeastAsPreferred (GS : List (DecProp W)) (a a' : DecProp W) : Prop :=
  (propositionOrdering GS).le a a'

/-- Kratzer-style world ordering: w at least as good as z iff w satisfies
    every ordering source proposition that z satisfies. -/
abbrev worldAtLeastAsGood (GS : List (DecProp W)) (w z : W) : Prop :=
  (worldSatisfactionOrdering GS).le w z

/-- Q-Bel_S: answers compatible with S's beliefs. -/
def questionRelativeBelief (answers : List (DecProp W))
    (belS : Set W) [DecidablePred belS] : List (DecProp W) :=
  answers.filter fun a => decide (propOverlap a.prop belS)

/-- Best answers: those not strictly dominated (Pareto frontier).
    Derived from `SatisfactionOrdering.undominated`. -/
abbrev bestAnswers (GS answers : List (DecProp W)) : List (DecProp W) :=
  (propositionOrdering GS).undominated answers

-- ============================================================================
-- §1c. Core semantics
-- ============================================================================

/-- ⟦S wants p⟧ = all best answers in Q-Bel_S entail p. -/
def wantQuestionBased (belS : Set W) [DecidablePred belS]
    (GS answers : List (DecProp W)) (p : Set W) [DecidablePred p] : Prop :=
  let qBelS := questionRelativeBelief answers belS
  let best := bestAnswers GS qBelS
  ∀ a ∈ best, propEntails a.prop p

instance (belS : Set W) [DecidablePred belS]
    (GS answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (wantQuestionBased belS GS answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Standard von Fintel semantics (not question-based):
    ⟦S wants p⟧ = all best worlds in Bel_S are p-worlds.
    Best = undominated under Kratzer ordering.

    A world is "best" iff it is in Bel_S and no other Bel_S world strictly
    dominates it under the world satisfaction ordering induced by `GS`.

    This is the baseline that the question-based semantics generalizes:
    when Q_c is the finest question (singleton cells), `wantQuestionBased`
    reduces to `wantVF`. -/
def wantVF (belS : Set W) [DecidablePred belS]
    (GS : List (DecProp W)) (p : Set W) [DecidablePred p] : Prop :=
  ∀ w, belS w →
    (∀ w', belS w' → ¬ (worldSatisfactionOrdering GS).strictlyBetter w' w) →
    p w

instance (belS : Set W) [DecidablePred belS]
    (GS : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (wantVF belS GS p) :=
  inferInstanceAs (Decidable (∀ _, _))

-- ============================================================================
-- §2. Metasemantic constraints
-- ============================================================================

/-- p is *considered* relative to Q iff every answer settles p.
**Considering Constraint** (§3.6): ⟦S wants p⟧^c is defined only if p is
considered relative to Q_c. -/
def isConsidered (answers : List (DecProp W))
    (p : Set W) [DecidablePred p] : Prop :=
  ∀ a ∈ answers, propEntails a.prop p ∨ propEntails a.prop (fun w => ¬ p w)

instance (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (isConsidered answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Diversity** (§3.7): Q_c must contain both p-answers and ¬p-answers. -/
def isDiverse (answers : List (DecProp W))
    (p : Set W) [DecidablePred p] : Prop :=
  (∃ a ∈ answers, propEntails a.prop p) ∧
  (∃ a ∈ answers, propEntails a.prop (fun w => ¬ p w))

instance (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (isDiverse answers p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Anti-deckstacking Constraint** (§3.7): for all q, if some answer to Q_c
is a q-answer, then q must be considered relative to Q_c. This prevents
questions from "stacking the deck" by letting one side of q entail a
desirable proposition that the other side cannot.

Implementation: enumerate all subsets of an explicit world list as decidable
characteristic predicates and check each one. The world enumeration is taken
explicitly (rather than via `Finset.univ.toList`) so that `decide` can reduce
through it for concrete `Fintype` instances built from `{...}` literals. -/
def isAntiDeckstacking (worlds : List W) (answers : List (DecProp W)) : Prop :=
  let allBoolProps : List (W → Bool) := worlds.foldr
    (fun w acc => acc.flatMap fun q => [q, fun w' => q w' || decide (w' = w)])
    [fun _ => false]
  let allProps : List (DecProp W) :=
    allBoolProps.map fun q => ⟨fun w => q w = true, fun _ => inferInstance⟩
  ∀ q ∈ allProps,
    (∀ a ∈ answers, ¬ propEntails a.prop q.prop) ∨ isConsidered answers q.prop

instance (worlds : List W) (answers : List (DecProp W)) :
    Decidable (isAntiDeckstacking worlds answers) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Belief-sensitivity Constraint** (§4.2): S's beliefs must be sensitive
to Q_c. That is, Q_c must make non-trivial distinctions within S's
belief state — there exist answers that overlap Bel_S and answers that
don't, or the agent's beliefs distinguish among answers.

This blocks inferences like Avoid-war ⊭ Avoid-nuclear-war when the agent
lacks the conceptual resources to grasp nuclear war. -/
def isBelSensitive (belS : Set W) [DecidablePred belS]
    (answers : List (DecProp W)) : Prop :=
  -- Q_c-Bel_S is nonempty (agent's beliefs are compatible with some answer)
  -- AND Q_c-Bel_S ≠ Q_c (agent's beliefs rule out at least one answer)
  let live := questionRelativeBelief answers belS
  live ≠ [] ∧ live.length ≠ answers.length

instance (belS : Set W) [DecidablePred belS] (answers : List (DecProp W)) :
    Decidable (isBelSensitive belS answers) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Full definedness condition for ⟦S wants p⟧^c.
Conjunction of Considering (§3.6), Diversity (§3.7), and Belief-sensitivity
(§4.2). Anti-deckstacking is omitted because the paper's universal
quantification over all propositions is too strong for finite models
(see study file §7 for discussion). -/
def wantDefined (belS : Set W) [DecidablePred belS]
    (answers : List (DecProp W)) (p : Set W) [DecidablePred p] : Prop :=
  isConsidered answers p ∧ isDiverse answers p ∧ isBelSensitive belS answers

instance (belS : Set W) [DecidablePred belS]
    (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
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
def wantPrProp (belS : Set W) [DecidablePred belS]
    (GS answers : List (DecProp W)) (p : Set W) [DecidablePred p] : PrProp W where
  presup _ := wantDefined belS answers p
  assertion _ := wantQuestionBased belS GS answers p

-- ============================================================================
-- §4. Key theorems (generic)
-- ============================================================================

omit [DecidableEq W] in
/-- Preference between answers is transitive (delegates to framework). -/
theorem prefer_answer_transitive (GS : List (DecProp W)) (a a' a'' : DecProp W)
    (h1 : atLeastAsPreferred GS a a')
    (h2 : atLeastAsPreferred GS a' a'') :
    atLeastAsPreferred GS a a'' :=
  (propositionOrdering GS).le_trans a a' a'' h1 h2

omit [DecidableEq W] in
/-- Empty desires make all answers equivalent (delegates to framework). -/
theorem empty_desires_indifferent (a a' : DecProp W) :
    atLeastAsPreferred ([] : List (DecProp W)) a a' :=
  SatisfactionOrdering.ofCriteria_empty_le _ a a'

omit [DecidableEq W] in
/-- With empty desires, want reduces to belief compatibility.
    Delegates to `ofCriteria_empty_undominated` from the framework. -/
theorem empty_desires_belief_only (belS : Set W) [DecidablePred belS]
    (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    wantQuestionBased belS [] answers p ↔
    ∀ a ∈ questionRelativeBelief answers belS, propEntails a.prop p := by
  unfold wantQuestionBased
  show (∀ a ∈ (propositionOrdering ([] : List _)).undominated _, _) ↔ _
  rw [show propositionOrdering ([] : List (DecProp W)) =
        SatisfactionOrdering.ofCriteria
          (fun a p => decide (propEntails a.prop p.prop)) [] from rfl,
      SatisfactionOrdering.ofCriteria_empty_undominated]

-- ============================================================================
-- §4a. Preorder instances
-- ============================================================================

/-- The proposition preference ordering as a `NormalityOrder`.
    Connects desire semantics to the default reasoning infrastructure. -/
def propositionNormality (GS : List (DecProp W)) : Core.Order.NormalityOrder (DecProp W) :=
  (propositionOrdering GS).toNormalityOrder

/-- The proposition preference ordering as a Mathlib `Preorder`.
    Parallel to `Kratzer.kratzerPreorder` for worlds.

    This enables Mathlib's order-theoretic lemmas (monotonicity, chains,
    `le_trans`, etc.) for the desire preference relation. -/
@[reducible] def propositionPreorder (GS : List (DecProp W)) : Preorder (DecProp W) :=
  (propositionOrdering GS).toPreorder

/-- The world ordering as a `NormalityOrder` (generic over `[Fintype W]`).
    Parallel to `Kratzer.kratzerNormality` but not restricted to `World4`. -/
def worldNormality (GS : List (DecProp W)) : Core.Order.NormalityOrder W :=
  (worldSatisfactionOrdering GS).toNormalityOrder

/-- The world ordering as a Mathlib `Preorder` (generic over `[Fintype W]`). -/
@[reducible] def worldPreorder (GS : List (DecProp W)) : Preorder W :=
  (worldSatisfactionOrdering GS).toPreorder

end Generic

-- Summary

/-!
## Summary: @cite{phillips-brown-2025} Integration

### Architecture

All propositions are `Set W = W → Prop`. Where decidability is needed
(partition cells, desire lists), propositions are bundled with a
`DecidablePred` witness via `DecProp W := { p : Set W // DecidablePred p }`.
Bare proposition arguments use the ambient `[DecidablePred p]` typeclass.
Preference and ordering definitions derive from `SatisfactionOrdering`:

```
SatisfactionOrdering (generic framework)
  ├── propositionOrdering GS     — propositions ranked by desire satisfaction
  │   ├── .satisfiedBy a         = satisfiedBy GS a
  │   ├── .atLeastAsGood a a'    = atLeastAsPreferred GS a a'
  │   ├── .undominated answers   = bestAnswers GS answers
  │   ├── .toNormalityOrder      = propositionNormality GS
  │   └── propositionPreorder GS : Preorder (DecProp W)
  │
  └── worldSatisfactionOrdering GS — worlds ranked by proposition satisfaction
      ├── .atLeastAsGood w z     = worldAtLeastAsGood GS w z
      ├── .undominated belWorlds → used by wantVF
      ├── .toNormalityOrder      = worldNormality GS
      └── worldPreorder GS      : Preorder W
```

### Core Functions (generic over `[Fintype W]`)
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
-/

end Semantics.Modality.Desire
