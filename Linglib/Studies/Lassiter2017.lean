import Linglib.Semantics.Attitudes.Desire.ExpectedValue

/-!
# Lassiter (2017): Graded Modality

This file formalizes the scalar semantics of *good* and *ought* in chapters 7 and 8 of
[lassiter-2017]. Goodness is expected value, the probability-weighted average of world
values over a proposition (`Desire.ExpectedValue.expectedValue`); it is an interval scale
and intermediate on disjoint unions. *Ought* is constrained rather than defined
(`Constraints`): Sloman's Principle relates it to goodness (an obligatory proposition is
strictly better than each of its alternatives, after [sloman-1970]), the Smith Principle
restricts agglomeration to exhaustive pairs, and Weakening closes obligation under
disjunction.

Sloman's Principle alone excludes conflicting oughts, `ought φ` together with `ought ¬φ`
(`Constraints.not_compl`), and the Smith Principle carries the Smith argument from
`ought (M ∨ S)` and `ought ¬M` to `ought S` (`Smith.ought_S`), on a sample model that meets
the Sloman requirements of all three. On [cariani-2016]'s four-world counter-model to
Weakening, where `A` and `B` each beat their negations in expected value but `A ∨ B` ties
with its negation, Sloman's Principle and Weakening together make `ought A` and `ought B`
incompatible (`Cariani.not_ought_and`). The scalar reading of *ought* as a threshold on an
intermediate scale derives Weakening and, given ought-exclusivity, the Smith Principle; both
derivations live with the expected-value substrate.

## Implementation notes

The goodness scale and the alternative sets of the constraint set are parameters; the
consequences take the needed alternative memberships as hypotheses, the polar sets `{φ, ¬φ}`
being the book's weakest choice. The counter-model instantiates the scale by expected value
over an equiprobable domain of four worlds indexed by the truth values of `A` and `B`.

## References

* [lassiter-2017]
* [cariani-2016]
* [sloman-1970]
-/

namespace Lassiter2017

open Desire.ExpectedValue Core.DecisionTheory

section Constraints

variable {W : Type*} {μ : Set W → ℚ} {ought : Set W → Prop} {alt : Set W → Set (Set W)}

/-- The constraint set on *ought* relative to a goodness scale `μ` and alternative sets
`alt`: Sloman's Principle, the Smith Principle, and Weakening. -/
structure Constraints (μ : Set W → ℚ) (ought : Set W → Prop) (alt : Set W → Set (Set W)) :
    Prop where
  sloman : ∀ ⦃φ⦄, ought φ → ∀ ψ ∈ alt φ, ψ ≠ φ → μ ψ < μ φ
  smith : ∀ ⦃φ ψ⦄, φ ∪ ψ = Set.univ → ought φ → ought ψ → ought (φ ∩ ψ)
  weakening : ∀ ⦃φ ψ⦄, ought φ → ought ψ → ought (φ ∪ ψ)

variable [Nonempty W] (h : Constraints μ ought alt) {φ ψ : Set W}
include h

/-- No conflicting oughts: a proposition and its negation, each an alternative to the
other, cannot both be obligatory. -/
theorem Constraints.not_compl (hφ : φᶜ ∈ alt φ) (hφ' : φ ∈ alt φᶜ) (h₁ : ought φ) :
    ¬ ought φᶜ := λ h₂ =>
  lt_asymm (h.sloman h₁ _ hφ ne_compl_self.symm) (h.sloman h₂ _ hφ' ne_compl_self)

/-- Weakening carries a failure of Sloman's Principle at a disjunction, one no better than
its negation, back to the disjuncts. -/
theorem Constraints.not_and_of_le (hne : (φ ∪ ψ)ᶜ ∈ alt (φ ∪ ψ))
    (hle : μ (φ ∪ ψ) ≤ μ (φ ∪ ψ)ᶜ) : ¬ (ought φ ∧ ought ψ) := λ ⟨h₁, h₂⟩ =>
  (h.sloman (h.weakening h₁ h₂) _ hne ne_compl_self.symm).not_ge hle

end Constraints

section Goodness

variable {W : Type*} [Fintype W]

open Classical in
/-- Goodness as expected value over the whole domain, the book's default `prob(D) = 1`. -/
noncomputable def goodness (pr V : W → ℚ) (φ : Set W) : ℚ := expectedValue pr V Set.univ φ

end Goodness

attribute [local simp] goodness expectedValue cell DecisionProblem.condExpectedUtility
  toDecisionProblem Finset.sum_filter Fintype.sum_prod_type Fintype.sum_bool

/-! ### The Smith scenario -/

/-- Smith's options: military service, alternative service, or neither. -/
inductive Smith
  | military
  | service
  | neither
  deriving DecidableEq

namespace Smith

instance : Fintype Smith := ⟨{military, service, neither}, λ w => by cases w <;> simp⟩

/-- Smith serves in the military. -/
def M : Set Smith := {military}

/-- Smith performs alternative service. -/
def S : Set Smith := {service}

/-- The sample model's prior: the three options are equiprobable. -/
def prior : Smith → ℚ := λ _ => 1 / 3

/-- The sample model's values: alternative service alone is worth anything. -/
def value : Smith → ℚ := λ w => if w = service then 1 else 0

attribute [local simp] M S prior value Finset.univ Fintype.elems Finset.sum_insert

/-- The sample model meets the Sloman requirements of the premises `ought (M ∨ S)` and
`ought ¬M` and of the conclusion `ought S`. -/
theorem sloman :
    goodness prior value (M ∪ S)ᶜ < goodness prior value (M ∪ S) ∧
      goodness prior value M < goodness prior value Mᶜ ∧
      goodness prior value Sᶜ < goodness prior value S := by
  simp [-Finset.sum_const]; norm_num

/-- The Smith argument: the Smith Principle agglomerates the exhaustive premises to
`ought S`. -/
theorem ought_S {μ : Set Smith → ℚ} {ought : Set Smith → Prop} {alt : Set Smith → Set (Set Smith)}
    (h : Constraints μ ought alt) (h₁ : ought (M ∪ S)) (h₂ : ought Mᶜ) : ought S :=
  have : (M ∪ S) ∩ Mᶜ = S := by ext w; cases w <;> simp
  this ▸ h.smith (by ext w; cases w <;> simp) h₁ h₂

end Smith

/-! ### Cariani's counter-model to Weakening -/

namespace Cariani

/-- Four equiprobable worlds, indexed by the truth values of `A` and `B`. -/
abbrev World := Bool × Bool

/-- The uniform prior. -/
def prior : World → ℚ := λ _ => 1 / 4

/-- World values: `100` at `A ∧ B`, `-50` at `A ∧ ¬B` and `¬A ∧ B`, `0` at `¬A ∧ ¬B`. -/
def value : World → ℚ
  | (true, true) => 100
  | (true, false) => -50
  | (false, true) => -50
  | (false, false) => 0

/-- The proposition `A`. -/
def A : Set World := {w | w.1 = true}

/-- The proposition `B`. -/
def B : Set World := {w | w.2 = true}

attribute [local simp] A B prior value

theorem goodness_A : goodness prior value A = 25 := by norm_num [-Finset.sum_const]

theorem goodness_compl_A : goodness prior value Aᶜ = -25 := by norm_num [-Finset.sum_const]

theorem goodness_B : goodness prior value B = 25 := by norm_num [-Finset.sum_const]

theorem goodness_compl_B : goodness prior value Bᶜ = -25 := by norm_num [-Finset.sum_const]

theorem goodness_union : goodness prior value (A ∪ B) = 0 := by norm_num [-Finset.sum_const]

theorem goodness_compl_union : goodness prior value (A ∪ B)ᶜ = 0 := by
  norm_num [-Finset.sum_const]

/-- `A` and `B` each satisfy Sloman's Principle against their negations. -/
theorem sloman :
    goodness prior value Aᶜ < goodness prior value A ∧
      goodness prior value Bᶜ < goodness prior value B := by
  rw [goodness_A, goodness_compl_A, goodness_B, goodness_compl_B]; norm_num

/-- Sloman's Principle and Weakening make `ought A` and `ought B` incompatible: the
disjunction ties with its negation. -/
theorem not_ought_and {ought : Set World → Prop} {alt : Set World → Set (Set World)}
    (h : Constraints (goodness prior value) ought alt) (halt : (A ∪ B)ᶜ ∈ alt (A ∪ B)) :
    ¬ (ought A ∧ ought B) :=
  h.not_and_of_le halt (goodness_compl_union ▸ goodness_union ▸ le_rfl)

end Cariani

end Lassiter2017
