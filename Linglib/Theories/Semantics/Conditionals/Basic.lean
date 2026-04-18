/-
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

However, following @cite{grusdt-lassiter-franke-2022}, we can maintain classical semantics
while deriving apparent exceptions through RSA pragmatics. The key is that
conditionals assert high conditional probability, not material implication.

-/

import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Order.Normality
import Linglib.Core.Mood.Basic

namespace Semantics.Conditionals

open Core.Proposition
open Core.CommonGround (ContextSet)
open Core.Mood (GramMood)

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

-- Variably Strict Conditional (@cite{stalnaker-1968}–@cite{lewis-1973})

/--
A similarity ordering on worlds.

For variably strict conditionals, we need a notion of "closest" p-worlds.
This is typically modeled as a preorder on worlds centered at each world.

`closer w w₁ w₂` means w₁ is at least as similar to w as w₂ is.
-/
structure SimilarityOrdering (W : Type*) where
  /-- `closer w₀ w₁ w₂` means w₁ is at least as close to w₀ as w₂ is -/
  closer : W → W → W → Prop
  /-- Reflexivity: every world is as close to any center as itself -/
  closer_refl (w₀ w : W) : closer w₀ w w
  /-- Transitivity -/
  closer_trans (w₀ w₁ w₂ w₃ : W) :
    closer w₀ w₁ w₂ → closer w₀ w₂ w₃ → closer w₀ w₁ w₃
  /-- Decidability of the similarity relation -/
  closerDec (w₀ w₁ w₂ : W) : Decidable (closer w₀ w₁ w₂)

instance {W : Type*} (sim : SimilarityOrdering W) (w₀ w₁ w₂ : W) :
    Decidable (sim.closer w₀ w₁ w₂) :=
  sim.closerDec w₀ w₁ w₂

/-- Construct a `SimilarityOrdering` from a `Bool`-valued function.
    Proofs can typically be discharged by `decide` on finite types. -/
def SimilarityOrdering.ofBool {W : Type*}
    (f : W → W → W → Bool)
    (hrefl : ∀ w₀ w, f w₀ w w = true)
    (htrans : ∀ w₀ w₁ w₂ w₃, f w₀ w₁ w₂ = true → f w₀ w₂ w₃ = true →
      f w₀ w₁ w₃ = true) :
    SimilarityOrdering W where
  closer w₀ w₁ w₂ := f w₀ w₁ w₂ = true
  closer_refl := hrefl
  closer_trans w₀ w₁ w₂ w₃ := htrans w₀ w₁ w₂ w₃
  closerDec _ _ _ := inferInstance

/-- The `NormalityOrder` centered at world `w₀`: `le w₁ w₂` iff `w₁` is
    at least as close to `w₀` as `w₂` is. Connects Lewis/Stalnaker
    conditionals to the default reasoning infrastructure (`optimal`,
    `refine`, `respects`, CR1–CR4). -/
def SimilarityOrdering.atCenter {W : Type*} (sim : SimilarityOrdering W)
    (w₀ : W) : Core.Order.NormalityOrder W where
  le := sim.closer w₀
  le_refl w := sim.closer_refl w₀ w
  le_trans w₁ w₂ w₃ := sim.closer_trans w₀ w₁ w₂ w₃

/--
Variably strict conditional (@cite{stalnaker-1968}/@cite{lewis-1973}):

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
      (p q : Prop' W) (w : W),
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
      exact h_q_close w hw_in_pWorlds (sim.closer_refl w w)
    · -- w ≠ w', so by centering, w is strictly closer to itself
      have ⟨h_closer, _⟩ := h_centered w w' h_eq
      exact h_q_close w hw_in_pWorlds h_closer

-- Kratzer-Style Conditionals (Modal Base + Ordering Source)

/-!
## Kratzer Conditionals
@cite{nadathur-lauer-2020} @cite{stalnaker-1968}

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

-- (Indicative/subjunctive definitions moved below `SelectionFunction`,
--  see `## Stalnakerian indicative/subjunctive split` further down.)

-- Selection Functions (@cite{stalnaker-1968}, @cite{ramotowska-marty-romoli-santorio-2025})

/-!
## Selection Functions

Stalnaker's selection function approach to counterfactuals:
- A selection function `s : W × 𝒫(W) → W` selects THE closest antecedent-world
- "If A were, C would be" is true iff C holds at s(w, ⦃A⦄)

Key distinction from @cite{lewis-1973}:
- @cite{lewis-1973}: Universal quantification over all closest A-worlds
- @cite{stalnaker-1968}: Selection of a single A-world (with supervaluation for ties)

This is formalized for use in @cite{ramotowska-marty-romoli-santorio-2025} analysis of
counterfactual force under quantifiers.
-/

/--
A **selection function** picks the unique closest antecedent-world.

`s w A` returns the closest A-world to w, or w itself if no A-worlds exist.

Constraints (from @cite{stalnaker-1968}):
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

This is the connection between @cite{lewis-1973}/Kratzer orderings and @cite{stalnaker-1968} selection.
-/
def candidateSelections {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (w : W) (A : Set W) : Set W :=
  let pWorlds := A ∩ domain
  { w' ∈ pWorlds | ∀ w'' ∈ pWorlds, sim.closer w w' w'' }

/--
**Comparative closeness** relation derived from a similarity ordering.

`w₁ ≤_w₀ w₂` means w₁ is at least as similar to w₀ as w₂ is.
This is the @cite{lewis-1973} notation.
-/
def comparativeCloseness {W : Type*} (sim : SimilarityOrdering W)
    (w₀ w₁ w₂ : W) : Prop :=
  sim.closer w₀ w₁ w₂

notation:50 w₁ " ≤[" sim "," w₀ "] " w₂ => comparativeCloseness sim w₀ w₁ w₂

-- Closest Worlds

/--
The closest A-worlds to w₀: minimal elements of `A` under the similarity
preorder centered at `w₀`.

In @cite{lewis-1973}'s notation: min_{≤_w}(A) = {w' ∈ A : ¬∃w'' ∈ A. w'' <_w w'}.
-/
def SimilarityOrdering.closestWorlds {W : Type*} [DecidableEq W]
    (sim : SimilarityOrdering W) (w₀ : W) (A : Finset W) : Finset W :=
  A.filter fun w' => ∀ w'' ∈ A, sim.closer w₀ w' w'' ∨ ¬sim.closer w₀ w'' w'

@[simp]
theorem SimilarityOrdering.closestWorlds_empty {W : Type*} [DecidableEq W]
    (sim : SimilarityOrdering W) (w₀ : W) :
    sim.closestWorlds w₀ ∅ = ∅ := by
  simp [closestWorlds]

theorem SimilarityOrdering.closestWorlds_subset {W : Type*} [DecidableEq W]
    (sim : SimilarityOrdering W) (w₀ : W) (A : Finset W) :
    sim.closestWorlds w₀ A ⊆ A :=
  Finset.filter_subset _ A

theorem SimilarityOrdering.mem_closestWorlds {W : Type*} [DecidableEq W]
    (sim : SimilarityOrdering W) (w₀ : W) (A : Finset W) (w' : W) :
    w' ∈ sim.closestWorlds w₀ A ↔
    w' ∈ A ∧ ∀ w'' ∈ A, sim.closer w₀ w' w'' ∨ ¬sim.closer w₀ w'' w' := by
  simp [closestWorlds, Finset.mem_filter]

-- Selection ↔ Similarity Bridge

/-!
## Selection Function ↔ Similarity Ordering
@cite{stalnaker-1981}

A selection function induces a comparative similarity relation that is
*stronger* than what Lewis requires.

- **Similarity → Selection**: `candidateSelections` extracts the set of
  minimally close worlds under a similarity ordering. Any selection
  function that always picks from this set is "legitimate."

- **Selection → Similarity**: A selection function `s` determines a
  pairwise preference: `w₁ ≤_{w₀} w₂` iff `s(w₀, {w₁, w₂}) = w₁`.
  This is reflexive (by `success`) and total (by definition), but
  transitivity requires additional coherence constraints on `s` beyond
  `success` + `centering` — specifically, the selection function must be
  rationalizable by a total preorder on worlds. See `isCoherent` below.
-/

/--
**Pairwise preference induced by a selection function.**

`w₁` is preferred to `w₂` from center `w₀` iff when choosing between
just the two of them, the selection function picks `w₁`. -/
def selectionPrefers {W : Type*} (s : SelectionFunction W)
    (w₀ w₁ w₂ : W) : Prop :=
  s.select w₀ {w₁, w₂} = w₁

/--
**A selection function is coherent** iff its induced pairwise preference
is transitive. This is the content of @cite{stalnaker-1981}'s claim that
selection functions determine a *well-ordering* of possible worlds.

Not all selection functions satisfying `success` + `centering` are
coherent — coherence is an additional rationality constraint. -/
def SelectionFunction.isCoherent {W : Type*} (s : SelectionFunction W) : Prop :=
  ∀ w₀ w₁ w₂ w₃ : W,
    selectionPrefers s w₀ w₁ w₂ → selectionPrefers s w₀ w₂ w₃ →
    selectionPrefers s w₀ w₁ w₃

/--
**Coherent selection functions induce similarity orderings.**

Given a coherent selection function, its pairwise preference relation
is a valid `SimilarityOrdering`: reflexive (from `success`) and
transitive (from coherence). -/
def coherentSelectionToSimilarity {W : Type*} [DecidableEq W]
    (s : SelectionFunction W)
    (h_coherent : s.isCoherent) : SimilarityOrdering W where
  closer := selectionPrefers s
  closer_refl w₀ w := by
    show s.select w₀ {w, w} = w
    have h_eq : ({w, w} : Set W) = {w} := Set.insert_eq_of_mem (Set.mem_singleton w)
    rw [h_eq]
    have h_ne : ({w} : Set W).Nonempty := ⟨w, Set.mem_singleton w⟩
    have h_in := s.success w₀ {w} h_ne
    exact Set.mem_singleton_iff.mp h_in
  closer_trans w₀ w₁ w₂ w₃ := h_coherent w₀ w₁ w₂ w₃
  closerDec w₀ w₁ w₂ := inferInstanceAs (Decidable (s.select w₀ {w₁, w₂} = w₁))

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

See `Theories/Semantics/Causation/` for the causal model infrastructure.
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

-- Stalnakerian indicative/subjunctive split (@cite{stalnaker-1975})

/-!
## Stalnakerian indicative/subjunctive split

@cite{stalnaker-1975} argues that the indicative/subjunctive distinction is
*pragmatic*, not semantic: both have the same selection-based truth condition.
Indicatives require the selection function to obey the **pragmatic constraint**
(stay inside the context set when possible); subjunctives signal that the
constraint is suspended.

The previous identification `indicativeConditional := materialImp` was
inaccurate per @cite{stalnaker-1975} §IV ("This equivalence explains the
plausibility of the truth-functional analysis ... but it does not justify
that analysis"). We now derive the equivalence within an appropriate context
rather than stipulate it.
-/

/--
**Selection-based conditional**: "if p, then q" is true at w iff q holds at
the world selected by `s` from the p-worlds. This is the common semantic
core of @cite{stalnaker-1975} indicatives and subjunctives. -/
def selectionConditional {W : Type*} (s : SelectionFunction W)
    (p q : BProp W) : BProp W :=
  λ w => q (s.select w {w' | p w' = true})

/--
**Pragmatic constraint on selection** (@cite{stalnaker-1975} §III).

If the conditional is being evaluated at a context-set world `w`, and some
antecedent-world is also in the context set, then the selected world must
be in the context set. Equivalently: context-set worlds are closer to each
other than to non-context-set worlds whenever a context-set option is
available.

This is the central new contribution of @cite{stalnaker-1975}: it is what
makes the indicative inference forms behave the way they do, without
changing the semantic clause. -/
def pragmaticConstraint {W : Type*} (s : SelectionFunction W)
    (C : ContextSet W) : Prop :=
  ∀ w (A : Set W), C w → (∃ w' ∈ A, C w') → C (s.select w A)

/--
**Mooded conditional** (@cite{stalnaker-1975}): the truth-conditional clause
is `selectionConditional` regardless of grammatical mood. The mood index `m`
is metadata at the call site, documenting whether an indicative or subjunctive
is being interpreted; the *semantic* mood difference is captured by which
selection functions are admissible in the context — see `admissibleSelection`.

Single source of truth: indicative and subjunctive conditionals do not have
distinct semantic clauses. Replacing two parallel defs (`indicativeConditional`,
`subjunctiveConditional`) with one mood-keyed wrapper makes Stalnaker's actual
claim explicit at the type level. -/
def moodedConditional {W : Type*} (_m : GramMood) (s : SelectionFunction W)
    (p q : BProp W) : BProp W :=
  selectionConditional s p q

/--
**Mood-indexed admissibility on selection functions** (@cite{stalnaker-1975}).

Stalnaker's mood distinction lives here, not in the truth-conditional clause:
- `.indicative` requires the selection function to obey `pragmaticConstraint`
  on the context — the central new contribution of @cite{stalnaker-1975}.
- `.subjunctive` imposes no such constraint; the selection function may reach
  outside the context set, which is precisely what subjunctive mood signals.

This makes "indicative vs subjunctive" a property of the *selection-function /
context pairing*, not a separate semantic operator. -/
def Mood.admissibleSelection {W : Type*} (m : GramMood) (s : SelectionFunction W)
    (C : ContextSet W) : Prop :=
  match m with
  | .indicative  => pragmaticConstraint s C
  | .subjunctive => True

/-- Indicative admissibility unfolds to the pragmatic constraint. -/
theorem admissibleSelection_indicative {W : Type*} (s : SelectionFunction W)
    (C : ContextSet W) :
    Mood.admissibleSelection .indicative s C = pragmaticConstraint s C := rfl

/-- Subjunctive admissibility imposes no constraint. -/
theorem admissibleSelection_subjunctive {W : Type*} (s : SelectionFunction W)
    (C : ContextSet W) :
    Mood.admissibleSelection .subjunctive s C = True := rfl

/--
**Mood is irrelevant to the truth-conditional clause** (@cite{stalnaker-1975}).

For any grammatical mood, the mooded conditional reduces to the bare
selection conditional. This is the rfl-equation that previously had to be
stated as `indicative_eq_subjunctive` between two parallel defs. -/
theorem moodedConditional_eq_selectionConditional {W : Type*} (m : GramMood)
    (s : SelectionFunction W) (p q : BProp W) :
    moodedConditional m s p q = selectionConditional s p q := rfl

/--
**Selection conditional ≡ material within an appropriate context**
(@cite{stalnaker-1975} §IV).

In any context `C` evaluated at a context-set world `w`, given that the
antecedent is open in `C`, the selection function obeys the pragmatic
constraint, and the material conditional holds throughout `C`, the
selection conditional is true. This is the contextually-mediated equivalence
Stalnaker defends in place of the semantic identification.

Specialised to `.indicative` mood, this is exactly the Stalnakerian claim
that indicative conditionals reduce to the material conditional within an
appropriate context. The hypothesis `h_constraint` is precisely
`Mood.admissibleSelection .indicative s C` per `admissibleSelection_indicative`.

Hypotheses encode the "appropriate context" conditions:
- `hC_w`: `w` is in the context set;
- `h_open_p`: some context-set world satisfies `p` (antecedent is open);
- `h_constraint`: `s` obeys the pragmatic constraint relative to `C`;
- `h_C_imp`: in the context, the material conditional holds. -/
theorem selectionConditional_eq_material_within_context {W : Type*}
    (s : SelectionFunction W) (C : ContextSet W) (p q : BProp W) (w : W)
    (hC_w : C w)
    (h_open_p : ∃ w' ∈ {w' | p w' = true}, C w')
    (h_constraint : pragmaticConstraint s C)
    (h_C_imp : ∀ w', C w' → p w' = true → q w' = true) :
    selectionConditional s p q w = true := by
  unfold selectionConditional
  have h_nonempty : ({w' | p w' = true} : Set W).Nonempty := by
    obtain ⟨w', hw'_p, _⟩ := h_open_p
    exact ⟨w', hw'_p⟩
  have h_sel_C : C (s.select w {w' | p w' = true}) :=
    h_constraint w {w' | p w' = true} hC_w h_open_p
  have h_sel_p : p (s.select w {w' | p w' = true}) = true :=
    s.success w {w' | p w' = true} h_nonempty
  exact h_C_imp _ h_sel_C h_sel_p

/--
**Indicative-mood specialisation**: when the mood is indicative and the
selection function is admissible, the mooded conditional reduces to the
material conditional within the context. -/
theorem moodedConditional_indicative_eq_material_within_context {W : Type*}
    (s : SelectionFunction W) (C : ContextSet W) (p q : BProp W) (w : W)
    (hC_w : C w)
    (h_open_p : ∃ w' ∈ {w' | p w' = true}, C w')
    (h_admissible : Mood.admissibleSelection .indicative s C)
    (h_C_imp : ∀ w', C w' → p w' = true → q w' = true) :
    moodedConditional .indicative s p q w = true :=
  selectionConditional_eq_material_within_context s C p q w hC_w h_open_p
    h_admissible h_C_imp

end Semantics.Conditionals
