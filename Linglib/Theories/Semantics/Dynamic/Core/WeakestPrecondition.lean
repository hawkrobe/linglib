import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2

/-!
# Weakest Precondition Calculus
@cite{muskens-1996}

§III.6 (pp. 172–175): The weakest precondition calculus provides a
compositional algorithm for extracting first-order truth conditions
from DRS meanings. Given a DRS `D` and a postcondition `χ`,
`wp D χ` characterizes the input states from which `D` can
transition to a state satisfying `χ`.

## Compositional Rules

| Rule | Theorem | Paper ref |
|------|---------|-----------|
| `wp [C] χ = C ∧ χ` | `wp_test` | WP_{[]} |
| `wp (D₁ ⨟ D₂) χ = wp D₁ (wp D₂ χ)` | `wp_seq` | WP_{;} |
| `wp [u] χ = ∃e, χ(extend i u e)` | `wp_randomAssign` | WP_{[]} (∃ clause) |
| `wp D ⊤ = closure D` | `wp_true_eq_closure` | Proposition 2 |

## Key Results

- **Proposition 2**: `wp(K, ⊤) = ∃j K(i)(j)` (truth = existential closure)
- **Proposition 3**: DRT entailment = entailment of truth conditions
- **Corollary**: DPL entailment = validity of dynamic implication
-/

namespace Semantics.Dynamic.Core.WeakestPrecondition

open DynamicTy2

variable {S E : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. Definition
-- ════════════════════════════════════════════════════════════════

/-- Weakest precondition of DRS `D` with postcondition `χ`.

`wp D χ i` holds iff there exists an output state `j` such that
`D` transitions from `i` to `j` and `χ` holds at `j`. -/
def wp (D : DRS S) (χ : Condition S) : Condition S :=
  λ i => ∃ j, D i j ∧ χ j

-- ════════════════════════════════════════════════════════════════
-- § 2. Compositional Rules
-- ════════════════════════════════════════════════════════════════

/-- WP of a test: `wp [C] χ = C ∧ χ`.

A test checks `C` and passes the state through unchanged. -/
theorem wp_test (C : Condition S) (χ : Condition S) :
    wp (test C) χ = λ i => C i ∧ χ i := by
  ext i
  simp only [wp, test]
  constructor
  · rintro ⟨j, ⟨rfl, hC⟩, hχ⟩; exact ⟨hC, hχ⟩
  · rintro ⟨hC, hχ⟩; exact ⟨i, ⟨rfl, hC⟩, hχ⟩

/-- WP of sequencing: `wp (D₁ ⨟ D₂) χ = wp D₁ (wp D₂ χ)`.

Corresponds to WP_{;} (p. 173): the postcondition threads through. -/
theorem wp_seq (D₁ D₂ : DRS S) (χ : Condition S) :
    wp (dseq D₁ D₂) χ = wp D₁ (wp D₂ χ) := by
  ext i
  simp only [wp, dseq]
  constructor
  · rintro ⟨j, ⟨h, hD₁, hD₂⟩, hχ⟩
    exact ⟨h, hD₁, j, hD₂, hχ⟩
  · rintro ⟨h, hD₁, j, hD₂, hχ⟩
    exact ⟨j, ⟨h, hD₁, hD₂⟩, hχ⟩

/-- WP of random assignment: `wp [u] χ = ∃e, χ(extend i u e)`.

Introducing a discourse referent existentially quantifies over values.
Corresponds to the ∃ clause in WP_{[]} (p. 173). -/
theorem wp_randomAssign [AssignmentStructure S E] (u : S → E) (χ : Condition S) :
    wp (AssignmentStructure.randomAssign u) χ =
    λ i => ∃ e : E, χ (AssignmentStructure.extend i u e) := by
  ext i
  simp only [wp, AssignmentStructure.randomAssign]
  constructor
  · rintro ⟨j, ⟨e, rfl⟩, hχ⟩; exact ⟨e, hχ⟩
  · rintro ⟨e, hχ⟩; exact ⟨_, ⟨e, rfl⟩, hχ⟩

/-- WP of existential DRS: `wp (∃u. D) χ = ∃e, wp D χ (extend i u e)`. -/
theorem wp_dexists [AssignmentStructure S E] (u : S → E) (D : DRS S) (χ : Condition S) :
    wp (AssignmentStructure.dexists u D) χ =
    λ i => ∃ e : E, wp D χ (AssignmentStructure.extend i u e) := by
  simp only [AssignmentStructure.dexists]
  rw [wp_seq, wp_randomAssign]

-- ════════════════════════════════════════════════════════════════
-- § 3. Propositions 2 and 3
-- ════════════════════════════════════════════════════════════════

/-- Proposition 2 (@cite{muskens-1996}, p. 175):

`wp(K, ⊤)` is equivalent to `∃j K(i)(j)` — the existential closure.
In the semantic formulation, this is definitional. -/
theorem wp_true_eq_closure (D : DRS S) :
    wp D (λ _ => True) = closure D := by
  ext i; simp only [wp, closure, and_true]

/-- DRT entailment (@cite{muskens-1996}, p. 175):

`K₁,...,Kₙ ⊨_DRT K` iff for every state `i`, if all premises
are true at `i`, then the conclusion is true at `i`. -/
def drtEntails (premises : List (DRS S)) (conclusion : DRS S) : Prop :=
  ∀ i, (∀ D ∈ premises, closure D i) → closure conclusion i

/-- Proposition 3 (@cite{muskens-1996}, p. 175):

DRT entailment reduces to entailment of truth conditions.
`K₁,...,Kₙ ⊨_DRT K` iff `wp(K₁, ⊤),...,wp(Kₙ, ⊤)` entail `wp(K, ⊤)`. -/
theorem proposition_3 (premises : List (DRS S)) (conclusion : DRS S) :
    drtEntails premises conclusion ↔
    (∀ i, (∀ D ∈ premises, wp D (λ _ => True) i) → wp conclusion (λ _ => True) i) := by
  simp only [drtEntails, wp_true_eq_closure]

/-- DPL-style entailment: every output of `D₁` can be extended by `D₂`. -/
def dplEntails (D₁ D₂ : DRS S) : Prop :=
  ∀ i j, D₁ i j → ∃ k, D₂ j k

/-- Corollary (@cite{muskens-1996}, p. 175):

DPL entailment = validity of dynamic implication.
`K₁,...,Kₙ ⊨_DPL K` iff `⊢ tr((K₁;...;Kₙ) ⇒ K)`. -/
theorem dpl_entailment_eq_dimpl_valid (D₁ D₂ : DRS S) :
    dplEntails D₁ D₂ ↔ ∀ i, dimpl D₁ D₂ i := by
  simp only [dplEntails, dimpl]

-- ════════════════════════════════════════════════════════════════
-- § 4. Truth-Condition Extraction Rules
-- ════════════════════════════════════════════════════════════════

/-- TR of negation: `tr(not K) = ¬wp(K, ⊤)`.

The truth of `¬D` at state `i` is the negation of `D`'s satisfiability.
Corresponds to TR_{not} (p. 173). -/
theorem tr_neg_eq (D : DRS S) :
    dneg D = λ i => ¬ wp D (λ _ => True) i := by
  simp only [wp_true_eq_closure]; rfl

/-- TR of disjunction: `tr(K₁ or K₂) = wp(K₁, ⊤) ∨ wp(K₂, ⊤)`.

Corresponds to TR_{or} (p. 173). The existential distributes over disjunction. -/
theorem tr_disj_eq (D₁ D₂ : DRS S) :
    ddisj D₁ D₂ = λ i => wp D₁ (λ _ => True) i ∨ wp D₂ (λ _ => True) i := by
  ext i
  simp only [ddisj, wp, and_true]
  constructor
  · rintro ⟨k, hk⟩
    cases hk with
    | inl h => left; exact ⟨k, h⟩
    | inr h => right; exact ⟨k, h⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr hk⟩

/-- TR of implication: `tr(K₁ ⇒ K₂) = ¬wp(K₁, ¬wp(K₂, ⊤))`.

Dynamic implication = no way to satisfy antecedent without satisfying
consequent. Corresponds to TR_{⇒} (p. 173). -/
theorem tr_impl_eq (D₁ D₂ : DRS S) :
    dimpl D₁ D₂ = λ i => ¬ wp D₁ (λ j => ¬ wp D₂ (λ _ => True) j) i := by
  ext i
  simp only [dimpl, wp, and_true]
  constructor
  · intro h ⟨j, hD₁, hNot⟩
    exact hNot (h j hD₁)
  · intro h j hD₁
    by_contra hNot
    exact h ⟨j, hD₁, hNot⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Semantic Properness
-- ════════════════════════════════════════════════════════════════

/-- A DRS is semantically proper if its truth condition is uniform
across input states: satisfiability doesn't depend on the input
assignment.

This is the semantic counterpart of @cite{muskens-1996}'s syntactic
notion of properness (§III.5, p. 171): a DRS with no free discourse
referents. Proposition 1 (p. 174) connects the two: K is proper iff
`wp(K, ⊤)` is a closed formula. -/
def isProper (D : DRS S) : Prop :=
  ∀ i₁ i₂, closure D i₁ ↔ closure D i₂

/-- Proper DRSes have state-independent weakest preconditions. -/
theorem proper_wp_uniform (D : DRS S) (h : isProper D) :
    ∀ i₁ i₂, wp D (λ _ => True) i₁ ↔ wp D (λ _ => True) i₂ := by
  simp only [wp_true_eq_closure]; exact h

end Semantics.Dynamic.Core.WeakestPrecondition
