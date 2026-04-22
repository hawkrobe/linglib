import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Filter
import Linglib.Core.Order.SimilarityOrdering

/-!
# Conditional Semantics

@cite{lewis-1973} @cite{stalnaker-1968}

Compositional semantics for conditional sentences.

## Overview

This module provides the semantic building blocks for conditionals:
1. **Material conditional**: p → q = ¬p ∨ q (classical logic)
2. **Strict conditional**: □(p → q) - necessity of material conditional
3. **Variably strict conditional**: @cite{stalnaker-1968}/@cite{lewis-1973}-style conditionals

## The Material Conditional Problem

The material conditional (p → q ≡ ¬p ∨ q) has well-known problems:
- "If pigs fly, then the moon is cheese" comes out true
- It doesn't capture "If A, then C" as speakers use it

However, following @cite{grusdt-lassiter-franke-2022}, we can maintain
classical semantics while deriving apparent exceptions through RSA
pragmatics. The key is that conditionals assert high conditional
probability, not material implication.
-/

namespace Semantics.Conditionals

open Core.Order (SimilarityOrdering)

-- Material Conditional

/--
Material conditional: p → q ≡ ¬p ∨ q

This is the classical truth-functional conditional.
True whenever the antecedent is false or the consequent is true.

Equivalent to `pᶜ ∪ q` in mathlib's `Set` algebra; written here in
set-builder form to keep the conditional name discourse-meaningful.
-/
def materialImp {W : Type*} (p q : Set W) : Set W :=
  {w | p w → q w}

-- Strict Conditional

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
def strictImp {W : Type*} (access : W → Set W) (p q : Set W) : Set W :=
  λ w => ∀ w' ∈ access w, p w' → q w'

-- Variably Strict Conditional (@cite{stalnaker-1968}–@cite{lewis-1973})

/-! `SimilarityOrdering` and its constructors (`ofBool`, `atCenter`) live
    in `Core.Order.SimilarityOrdering` since they are general-purpose
    primitives used by counterfactuals, alternative-sensitive operators,
    and causal psycholinguistic models. They are re-exported above via
    `open Core.Order`. -/

/--
Variably strict conditional (@cite{stalnaker-1968}/@cite{lewis-1973}):

"If p, then q" is true at w iff:
- Either there are no p-worlds (vacuous truth), or
- Some p-world is such that q holds at all p-worlds at least as close

This captures the intuition that conditionals quantify over "nearby" worlds
where the antecedent holds.
-/
def variablyStrictImp {W : Type*} (sim : SimilarityOrdering W)
    (allWorlds : Set W) (p q : Set W) : Set W :=
  λ w =>
    let pWorlds := { w' ∈ allWorlds | p w' }
    -- Vacuously true if no p-worlds
    pWorlds = ∅ ∨
    -- Otherwise: some closest p-world makes q true
    ∃ w' ∈ pWorlds, ∀ w'' ∈ pWorlds, sim.closer w w'' w' → q w''

-- Conditional Entailment

/--
Conditional perfection: the inference from "if A then C" to "if not A then not C".

This is NOT valid for material conditionals but IS observed pragmatically.
The RSA model in GrusdtLassiterFranke2022 derives this as an implicature.
-/
def conditionalPerfection {W : Type*} (p q : Set W) : Set W :=
  materialImp pᶜ qᶜ

/--
Modus ponens: from (p → q) and p, derive q.
-/
theorem modus_ponens {W : Type*} (p q : Set W) (w : W)
    (h_imp : materialImp p q w) (h_p : p w) : q w := by
  unfold materialImp at h_imp
  exact h_imp h_p

/--
Contraposition: (p → q) entails (¬q → ¬p).
-/
theorem contraposition {W : Type*} (p q : Set W) :
    materialImp p q ⊆ materialImp qᶜ pᶜ := by
  intro w h_imp h_nq h_p
  unfold materialImp at h_imp
  have h_q := h_imp h_p
  exact h_nq h_q

/--
**Conditional perfection is NOT semantically entailed**.

There exists a world where (p → q) is true but (¬p → ¬q) is false.
This shows that "perfection" (the biconditional reading) is a pragmatic inference,
not a semantic entailment.

Counterexample: World where p is false, q is true.
Then (p → q) is vacuously true, but (¬p → ¬q) = (true → false) = false.
-/
theorem perfection_not_entailed : ∃ (W : Type) (p q : Set W) (w : W),
    materialImp p q w ∧ ¬(conditionalPerfection p q w) := by
  -- Use a simple 2-world type
  use Bool
  -- p = (w = true), q = constantly true
  use (λ w => w = true)
  use (λ _ => True)
  use false
  constructor
  · -- (p → q)(false) = (false = true → True) = True (vacuously)
    intro h
    -- h : false = true, which is absurd
    cases h
  · -- ¬(¬p → ¬q)(false) = ¬(¬(false = true) → ¬True)
    simp only [conditionalPerfection, materialImp, Set.mem_setOf_eq, Set.mem_compl_iff]
    intro h
    -- h : ¬(false = true) → ¬True, i.e., True → False
    have hnot_false_eq_true : ¬(false = true) := Bool.false_ne_true
    exact h hnot_false_eq_true trivial

/--
**Conditional perfection is NOT semantically entailed** (variably strict).

Even under @cite{stalnaker-1968}/@cite{lewis-1973} variably strict semantics (stronger than material
implication), the conditional does not entail its converse. There exist a
similarity ordering, propositions p and q, and a world w such that
"if p then q" holds but "if ¬p then ¬q" does not.

Counterexample: W = Bool, p = (· = true), q = (fun _ => True), w = false.
The conditional holds (the only p-world is `true`, where q holds trivially),
but perfection fails (¬p(false) is true but ¬q(false) is false).
-/
theorem perfection_not_entailed_variablyStrict :
    ∃ (W : Type) (sim : SimilarityOrdering W) (domain : Set W)
      (p q : Set W) (w : W),
      variablyStrictImp sim domain p q w ∧ ¬(conditionalPerfection p q w) := by
  use Bool
  exact ⟨⟨fun _ _ _ => True, fun _ _ => trivial, fun _ _ _ _ _ _ => trivial,
    fun _ _ _ => .isTrue trivial⟩,
    Set.univ, (· = true), (fun _ => True), false,
    Or.inr ⟨true, ⟨Set.mem_univ _, rfl⟩, fun _ _ _ => trivial⟩,
    fun h => h Bool.false_ne_true trivial⟩

/--
**Strict conditional implies material conditional**.

If w is accessible from itself (reflexive accessibility), then □(p → q) at w implies (p → q) at w.
-/
theorem strict_implies_material {W : Type*} (R : W → Set W) (p q : Set W) (w : W) :
    w ∈ R w → strictImp R p q w → materialImp p q w := by
  intro h_refl h_strict h_p
  exact h_strict w h_refl h_p

/-! `SimilarityOrdering.isCentered` lives in `Core.Order.SimilarityOrdering`
    (re-exported above). -/

/--
**Variably strict conditional implies material conditional** (with centered similarity).

If there is a p-world, the similarity ordering is centered, and the variably strict
conditional holds, then the material conditional holds at the actual world.

The centering axiom ensures that if p holds at w, then w is the unique closest p-world
to itself, so q must hold at w.
-/
theorem variably_strict_implies_material {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (p q : Set W) (w : W) (hw : w ∈ domain) (hp : p w)
    (h_centered : sim.isCentered) :
    variablyStrictImp sim domain p q w → materialImp p q w := by
  intro h_variably _h_p'
  simp only [variablyStrictImp] at h_variably
  cases h_variably with
  | inl h_empty =>
    -- p-worlds empty, but we have p w, contradiction
    have hw_in_pWorlds : w ∈ { w' ∈ domain | p w' } := Set.mem_sep hw hp
    rw [h_empty] at hw_in_pWorlds
    simp at hw_in_pWorlds
  | inr h_exists =>
    -- There's a closest p-world w' such that all equally close p-worlds satisfy q
    obtain ⟨w', hw'_in, h_q_close⟩ := h_exists
    -- w is also a p-world
    have hw_in_pWorlds : w ∈ { w' ∈ domain | p w' } := Set.mem_sep hw hp
    -- By centering, w is closer to itself than w' (if w ≠ w')
    -- So sim.closer w w w' holds
    by_cases h_eq : w = w'
    · -- w = w', so we need to show q w = q w'
      subst h_eq
      -- Apply h_q_close to w itself
      exact h_q_close w hw_in_pWorlds (sim.closer_refl w w)
    · -- w ≠ w', so by centering, w is strictly closer to itself
      have ⟨h_closer, _⟩ := h_centered w w' h_eq
      exact h_q_close w hw_in_pWorlds h_closer

/-! `KratzerContext`/`kratzerBetter`/`kratzerConditional` previously
    lived here as a Set-based parallel to the canonical List-based
    Kratzer machinery in `Theories/Semantics/Modality/Kratzer/`. They
    were a third parallel formalization (alongside Kratzer/Operators
    and the late lumping CF in `Conditionals/PremiseSemantic.lean`)
    and have been deleted in favour of `Restrictor.conditionalNecessity`
    (which calls the canonical `Kratzer.necessity` directly). The sole
    consumer (`LeftNested.lean`) now uses `conditionalNecessity`. -/


end Semantics.Conditionals
