/-
# Conditional Semantics

Compositional semantics for conditional sentences.

## Overview

This module provides the semantic building blocks for conditionals:
1. **Material conditional**: p → q = ¬p ∨ q (classical logic)
2. **Strict conditional**: □(p → q) - necessity of material conditional
3. **Variably strict conditional**: Stalnaker/Lewis-style conditionals

## The Material Conditional Problem

The material conditional (p → q ≡ ¬p ∨ q) has well-known problems:
- "If pigs fly, then the moon is cheese" comes out true
- It doesn't capture "If A, then C" as speakers use it

However, following Grusdt et al. (2022), we can maintain classical semantics
while deriving apparent exceptions through RSA pragmatics. The key is that
conditionals assert high conditional probability, not material implication.

## References

- Stalnaker (1968). A Theory of Conditionals.
- Lewis (1973). Counterfactuals.
- Kratzer (1991). Modality / Conditionals.
- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
-/

import Linglib.Core.Proposition

namespace Montague.Sentence.Conditional

open Core.Proposition

-- ============================================================================
-- Material Conditional
-- ============================================================================

/--
Material conditional: p → q ≡ ¬p ∨ q

This is the classical truth-functional conditional.
True whenever the antecedent is false or the consequent is true.

Note: The material conditional is already defined in Core.Proposition as `pimp`.
We re-export it here for convenience.
-/
def materialImp {W : Type*} (p q : Prop' W) : Prop' W :=
  Classical.pimp W p q

/-- Decidable version of material implication -/
def materialImpB {W : Type*} (p q : BProp W) : BProp W :=
  fun w => !p w || q w

-- ============================================================================
-- Strict Conditional
-- ============================================================================

/--
Strict conditional: true at w iff the material conditional holds at all
accessible worlds.

□(p → q) ≡ ∀w' ∈ R(w). p(w') → q(w')

This is the modal "necessitation" of the material conditional.
Used in deontic and epistemic conditionals.

Parameters:
- `access`: The accessibility relation R : W → Set W
- `p`: The antecedent proposition
- `q`: The consequent proposition
-/
def strictImp {W : Type*} (access : W → Set W) (p q : Prop' W) : Prop' W :=
  fun w => ∀ w' ∈ access w, p w' → q w'

/-- Strict implication with finite accessibility (for computation) -/
def strictImpFinite {W : Type*} (access : W → List W) (p q : BProp W) : BProp W :=
  fun w => (access w).all fun w' => !p w' || q w'

-- ============================================================================
-- Variably Strict Conditional (Stalnaker-Lewis)
-- ============================================================================

/--
A similarity ordering on worlds.

For variably strict conditionals, we need a notion of "closest" p-worlds.
This is typically modeled as a preorder on worlds centered at each world.

`closer w w₁ w₂` means w₁ is at least as similar to w as w₂ is.
-/
structure SimilarityOrdering (W : Type*) where
  /-- w₁ is at least as close to w as w₂ -/
  closer : W → W → W → Prop
  /-- Reflexivity: every world is maximally similar to itself -/
  refl : ∀ w, closer w w w
  /-- Transitivity -/
  trans : ∀ w w₁ w₂ w₃, closer w w₁ w₂ → closer w w₂ w₃ → closer w w₁ w₃

/--
Variably strict conditional (Stalnaker-Lewis style):

"If p, then q" is true at w iff:
- Either there are no p-worlds (vacuous truth), or
- Some p-world is such that q holds at all p-worlds at least as close

This captures the intuition that conditionals quantify over "nearby" worlds
where the antecedent holds.
-/
def variablyStrictImp {W : Type*} (sim : SimilarityOrdering W)
    (allWorlds : Set W) (p q : Prop' W) : Prop' W :=
  fun w =>
    let pWorlds := { w' ∈ allWorlds | p w' }
    -- Vacuously true if no p-worlds
    pWorlds = ∅ ∨
    -- Otherwise: some closest p-world makes q true
    ∃ w' ∈ pWorlds, ∀ w'' ∈ pWorlds, sim.closer w w'' w' → q w''

-- ============================================================================
-- Conditional Entailment
-- ============================================================================

/--
Conditional perfection: the inference from "if A then C" to "if not A then not C".

This is NOT valid for material conditionals but IS observed pragmatically.
The RSA model in GrusdtLassiterFranke2022 derives this as an implicature.
-/
def conditionalPerfection {W : Type*} (p q : Prop' W) : Prop' W :=
  materialImp (Classical.pnot W p) (Classical.pnot W q)

/--
Modus ponens: from (p → q) and p, derive q.
-/
theorem modus_ponens {W : Type*} (p q : Prop' W) (w : W)
    (h_imp : materialImp p q w) (h_p : p w) : q w := by
  unfold materialImp Classical.pimp at h_imp
  exact h_imp h_p

/--
Contraposition: (p → q) entails (¬q → ¬p).
-/
theorem contraposition {W : Type*} (p q : Prop' W) :
    Classical.entails W (materialImp p q) (materialImp (Classical.pnot W q) (Classical.pnot W p)) := by
  intro w h_imp h_nq h_p
  unfold materialImp Classical.pimp at h_imp
  have h_q := h_imp h_p
  exact h_nq h_q

-- ============================================================================
-- Kratzer-Style Conditionals (Modal Base + Ordering Source)
-- ============================================================================

/--
Kratzer's semantics for conditionals uses:
1. A modal base f : W → Set W (epistemic, circumstantial, etc.)
2. An ordering source g : W → Set (Prop' W) (stereotypical, deontic, etc.)

The conditional "if p, then q" is true at w iff
q holds at the "best" p-worlds according to the ordering.
-/
structure KratzerContext (W : Type*) where
  /-- Modal base: accessible worlds from w -/
  modalBase : W → Set W
  /-- Ordering source: propositions that induce a preference -/
  orderingSource : W → Set (Prop' W)

/--
"Best" worlds according to an ordering source.

A world w₁ is at least as good as w₂ if w₁ satisfies at least as many
ordering source propositions as w₂.
-/
def kratzerBetter {W : Type*} (os : Set (Prop' W)) (w₁ w₂ : W) : Prop :=
  { p ∈ os | p w₂ } ⊆ { p ∈ os | p w₁ }

/--
Kratzer-style conditional semantics.

"If p, then q" is true at w iff at the best p-worlds (in the modal base,
according to the ordering source), q holds.
-/
def kratzerConditional {W : Type*} (ctx : KratzerContext W) (p q : Prop' W) : Prop' W :=
  fun w =>
    let accessible := ctx.modalBase w
    let pWorlds := { w' ∈ accessible | p w' }
    let os := ctx.orderingSource w
    -- All p-worlds that are "best" according to the ordering source satisfy q
    ∀ w' ∈ pWorlds, (∀ w'' ∈ pWorlds, kratzerBetter os w' w'' → kratzerBetter os w'' w' → q w'')

-- ============================================================================
-- Connection to Assertability
-- ============================================================================

/-!
## Assertability vs Truth

The key insight from Grusdt et al. (2022) is that the ASSERTABILITY of a
conditional depends on P(C|A), not its truth conditions.

A conditional "if A then C" is assertable when P(C|A) is high (> θ).

This is formalized in `Assertability.lean`, where we define:
- `conditionalProbability : WorldState → ℚ`
- `assertable : WorldState → ℚ → Bool`

The RSA model then explains pragmatic phenomena (conditional perfection,
missing-link infelicity) through reasoning about assertability.
-/

end Montague.Sentence.Conditional
