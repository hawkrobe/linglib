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

-/

import Linglib.Core.Semantics.Proposition

namespace Semantics.Conditionals

open Core.Proposition

-- Material Conditional

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
  λ w => !p w || q w

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
def strictImp {W : Type*} (access : W → Set W) (p q : Prop' W) : Prop' W :=
  λ w => ∀ w' ∈ access w, p w' → q w'

/-- Strict implication with finite accessibility (for computation) -/
def strictImpFinite {W : Type*} (access : W → List W) (p q : BProp W) : BProp W :=
  λ w => (access w).all λ w' => !p w' || q w'

-- Variably Strict Conditional (Stalnaker-Lewis)

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

/--
**Conditional perfection is NOT semantically entailed**.

There exists a world where (p → q) is true but (¬p → ¬q) is false.
This shows that "perfection" (the biconditional reading) is a pragmatic inference,
not a semantic entailment.

Counterexample: World where p is false, q is true.
Then (p → q) is vacuously true, but (¬p → ¬q) = (true → false) = false.
-/
theorem perfection_not_entailed : ∃ (W : Type) (p q : Prop' W) (w : W),
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
    simp only [conditionalPerfection, materialImp, Classical.pimp, Classical.pnot]
    intro h
    -- h : ¬(false = true) → ¬True, i.e., True → False
    have hnot_false_eq_true : ¬(false = true) := Bool.false_ne_true
    exact h hnot_false_eq_true trivial

/--
**Strict conditional implies material conditional**.

If w is accessible from itself (reflexive accessibility), then □(p → q) at w implies (p → q) at w.
-/
theorem strict_implies_material {W : Type*} (R : W → Set W) (p q : Prop' W) (w : W) :
    w ∈ R w → strictImp R p q w → materialImp p q w := by
  intro h_refl h_strict h_p
  exact h_strict w h_refl h_p

/--
A centered similarity ordering: the actual world is always strictly closest to itself.

This is the "strong centering" axiom: w is strictly closer to itself than any other world.
-/
def SimilarityOrdering.isCentered {W : Type*} (sim : SimilarityOrdering W) : Prop :=
  ∀ w w' : W, w ≠ w' → sim.closer w w w' ∧ ¬sim.closer w w' w

/--
**Variably strict conditional implies material conditional** (with centered similarity).

If there is a p-world, the similarity ordering is centered, and the variably strict
conditional holds, then the material conditional holds at the actual world.

The centering axiom ensures that if p holds at w, then w is the unique closest p-world
to itself, so q must hold at w.
-/
theorem variably_strict_implies_material {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (p q : Prop' W) (w : W) (hw : w ∈ domain) (hp : p w)
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
      exact h_q_close w hw_in_pWorlds (sim.refl w)
    · -- w ≠ w', so by centering, w is strictly closer to itself
      have ⟨h_closer, _⟩ := h_centered w w' h_eq
      exact h_q_close w hw_in_pWorlds h_closer

-- Kratzer-Style Conditionals (Modal Base + Ordering Source)

/-!
## Kratzer Conditionals
@cite{nadathur-lauer-2020}

This section provides a **polymorphic, Set-based** version of Kratzer's
conditional semantics for use in mathematical proofs.

For the **computable, List-based** version with concrete examples and
proven properties (preorder, duality, K axiom, etc.), see:
  `Linglib.Theories.Semantics.Modality.Kratzer`

Both use the same CORRECT subset-based ordering from @cite{kratzer-1981}:
  w₁ ≤_A w₂ iff {p ∈ A : w₂ ∈ p} ⊆ {p ∈ A : w₁ ∈ p}
-/

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
Kratzer's ordering relation (Set-based version for proofs).

w₁ is at least as good as w₂ according to ordering source `os` iff
every proposition in `os` satisfied by w₂ is also satisfied by w₁.

This is the **correct** subset-based ordering from @cite{kratzer-1981}.
Equivalent to `atLeastAsGoodAs` in `Kratzer.lean` (which uses Lists for computation).

**NOT** a counting-based ordering (which would be incorrect).
-/
def kratzerBetter {W : Type*} (os : Set (Prop' W)) (w₁ w₂ : W) : Prop :=
  { p ∈ os | p w₂ } ⊆ { p ∈ os | p w₁ }

/--
Kratzer-style conditional semantics.

"If p, then q" is true at w iff at the best p-worlds (in the modal base,
according to the ordering source), q holds.

Best worlds are those maximal under `kratzerBetter`: w' is best if
for all w'' in pWorlds, if w' ≤ w'' then w'' ≤ w' (i.e., they're equivalent).
-/
def kratzerConditional {W : Type*} (ctx : KratzerContext W) (p q : Prop' W) : Prop' W :=
  λ w =>
    let accessible := ctx.modalBase w
    let pWorlds := { w' ∈ accessible | p w' }
    let os := ctx.orderingSource w
    -- All p-worlds that are "best" according to the ordering source satisfy q
    ∀ w' ∈ pWorlds, (∀ w'' ∈ pWorlds, kratzerBetter os w' w'' → kratzerBetter os w'' w' → q w'')

-- Indicative vs Subjunctive Conditionals

/--
**Indicative conditional** (epistemic, open).

"If A, then C" in the indicative mood - the standard conditional for
reasoning about what we expect to be true if A turns out to be true.

This is just the material conditional: ¬A ∨ C.
-/
def indicativeConditional {W : Type*} (p q : Prop' W) : Prop' W :=
  materialImp p q

/--
**Subjunctive conditional** (counterfactual).

"If A were the case, then C would be the case" - the conditional for
reasoning about non-actual possibilities.

This uses the variably strict semantics: at the closest A-worlds, C holds.
-/
def subjunctiveConditional {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (p q : Prop' W) : Prop' W :=
  variablyStrictImp sim domain p q

/--
**Subjunctive implies indicative** (when the antecedent holds at the actual world).

If "if p were, then q would" is true at w, and p holds at w, then q holds at w.
This shows that subjunctive conditionals are stronger than indicatives in this sense.

Requires a centered similarity ordering (the actual world is closest to itself).
-/
theorem subjunctive_implies_indicative {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (p q : Prop' W) (w : W) (hw : w ∈ domain) (hp : p w)
    (h_centered : sim.isCentered) :
    subjunctiveConditional sim domain p q w → indicativeConditional p q w := by
  exact variably_strict_implies_material sim domain p q w hw hp h_centered

-- Selection Functions (Stalnaker 1968, Ramotowska et al. 2025)

/-!
## Selection Functions

Stalnaker's selection function approach to counterfactuals:
- A selection function `s : W × 𝒫(W) → W` selects THE closest antecedent-world
- "If A were, C would be" is true iff C holds at s(w, ⦃A⦄)

Key distinction from Lewis:
- Lewis: Universal quantification over all closest A-worlds
- Stalnaker: Selection of a single A-world (with supervaluation for ties)

This is formalized for use in @cite{ramotowska-santorio-2025} analysis of
counterfactual force under quantifiers.
-/

/--
A **selection function** picks the unique closest antecedent-world.

`s w A` returns the closest A-world to w, or w itself if no A-worlds exist.

Constraints (from Stalnaker 1968):
1. Success: If A is non-empty, s(w, A) ∈ A
2. Strong Centering: If w ∈ A, then s(w, A) = w
-/
structure SelectionFunction (W : Type*) where
  /-- The selection function -/
  select : W → Set W → W
  /-- Success: selected world is in the antecedent (if nonempty) -/
  success : ∀ w A, A.Nonempty → select w A ∈ A
  /-- Strong centering: if actual world satisfies antecedent, select it -/
  centering : ∀ w A, w ∈ A → select w A = w

/--
**Candidate selection functions** induced by a comparative similarity ordering.

Given an ordering, a selection function is "legitimate" iff it always
selects a world that is closest (minimal w.r.t. the ordering).

This is the connection between Lewis/Kratzer orderings and Stalnaker selection.
-/
def candidateSelections {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (w : W) (A : Set W) : Set W :=
  let pWorlds := A ∩ domain
  { w' ∈ pWorlds | ∀ w'' ∈ pWorlds, sim.closer w w' w'' }

/--
**Counterfactual via selection function** (Stalnaker semantics).

"If A were, C would be" is true at w iff C holds at the selected A-world.
-/
def selectionalCounterfactual {W : Type*} (s : SelectionFunction W)
    (allWorlds : Set W) (p q : Prop' W) : Prop' W :=
  λ w =>
    let pWorlds := { w' ∈ allWorlds | p w' }
    pWorlds = ∅ ∨ q (s.select w pWorlds)

/--
**Comparative closeness** relation derived from a similarity ordering.

`w₁ ≤_w₀ w₂` means w₁ is at least as similar to w₀ as w₂ is.
This is the Lewis notation.
-/
def comparativeCloseness {W : Type*} (sim : SimilarityOrdering W)
    (w₀ w₁ w₂ : W) : Prop :=
  sim.closer w₀ w₁ w₂

notation:50 w₁ " ≤[" sim "," w₀ "] " w₂ => comparativeCloseness sim w₀ w₁ w₂

-- Connection to Causal Models

/-!
## Selection via Intervention

A key insight: selection functions can be grounded in causal models.

Given a causal model, `s(w, A)` = the world resulting from intervening
to make A true at w (Pearl's do(A)).

This connects:
- Stalnaker selection → Causal intervention
- "If A were" → do(A)
- Counterfactual dependence → Causal necessity

See `Theories/NadathurLauer2020/` for the causal model infrastructure.
-/

-- Connection to Assertability

/-!
## Assertability vs Truth

The key insight from @cite{grusdt-lassiter-franke-2022} is that the ASSERTABILITY of a
conditional depends on P(C|A), not its truth conditions.

A conditional "if A then C" is assertable when P(C|A) is high (> θ).

This is formalized in `Assertability.lean`, where we define:
- `conditionalProbability : WorldState → ℚ`
- `assertable : WorldState → ℚ → Bool`

The RSA model then explains pragmatic phenomena (conditional perfection,
missing-link infelicity) through reasoning about assertability.
-/

end Semantics.Conditionals
