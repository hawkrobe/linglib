import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic

/-!
# Clausal distributivity

A clause-embedding predicate is *clausally distributive* — written
C(lausal)-distributive in [qing-uegaki-2025] — when its question
semantics is existential quantification over its propositional
semantics: ⟦x V Q⟧ ↔ ∃p ∈ Q. ⟦x V p⟧ ([uegaki-sudo-2019];
[uegaki-2022]). `IsDistributive` states the property for a pair of
propositional and question semantics, so it is proved from a
predicate's semantic structure rather than stipulated per predicate.

`degreeComparison_isDistributive` proves it for the degree-comparison
pattern of *hope*, *fear*, *expect*, *wish* ([villalta-2008]):
⟦x V p⟧ = μ(x,p) > θ(C) with the question semantics the pointwise
existential, so clausal distributivity holds by construction.
Predicates whose question semantics outruns the existential — global
uncertainty for *worry*, decision-relevance for *care*
([elliott-etal-2017]) — are not clausally distributive; the
counterexample with actual worry semantics is
`Preferential.worry_not_cDistributive`, and the per-predicate
instantiations live in `Preferential.lean`.

Alternatives are the extensional, list-based `AlternativeList` over
Bool propositions, pending migration of this file and its consumer
`Preferential.lean` to the `Set`-based question substrate
(`Semantics/Questions/`).
-/

namespace Semantics.Attitudes.Distributivity

variable {W E : Type*}

/-- A Hamblin question denotation: a list of possible answers. -/
abbrev AlternativeList (W : Type*) := List (W → Bool)

/-- Preference/attitude degree function: `μ x p` is how strongly `x`
    prefers (or fears) `p`. -/
abbrev DegreeFn (W E : Type*) := E → (W → Bool) → ℚ

/-- Contextual threshold function over a comparison class. -/
abbrev ThresholdFn (W : Type*) := AlternativeList W → ℚ

/-- A predicate with propositional semantics `V_prop` and question
    semantics `V_question` is clausally distributive iff
    `V_question x Q w ↔ ∃ p ∈ Q, V_prop x p w`. -/
def IsDistributive (V_prop : E → (W → Bool) → W → Bool)
    (V_question : E → AlternativeList W → W → Bool) : Prop :=
  ∀ (x : E) (Q : AlternativeList W) (w : W),
    V_question x Q w = true ↔ ∃ p ∈ Q, V_prop x p w = true

/-! ### The degree-comparison pattern -/

/-- Degree-comparison propositional semantics:
    `degreeComparisonProp μ θ C x p w` iff `μ x p > θ C`. -/
def degreeComparisonProp (μ : DegreeFn W E) (θ : ThresholdFn W)
    (C : AlternativeList W) (x : E) (p : W → Bool) (_w : W) : Bool :=
  decide (μ x p > θ C)

/-- Degree-comparison question semantics, the pointwise existential:
    `degreeComparisonQuestion μ θ C x Q w` iff `∃ p ∈ Q, μ x p > θ C`. -/
def degreeComparisonQuestion (μ : DegreeFn W E) (θ : ThresholdFn W)
    (C : AlternativeList W) (x : E) (Q : AlternativeList W) (_w : W) : Bool :=
  Q.any λ p => decide (μ x p > θ C)

/-- Degree-comparison predicates are clausally distributive by
    construction. -/
theorem degreeComparison_isDistributive (μ : DegreeFn W E) (θ : ThresholdFn W)
    (C : AlternativeList W) :
    IsDistributive (degreeComparisonProp μ θ C)
      (degreeComparisonQuestion μ θ C) := by
  intro x Q w
  simp [degreeComparisonProp, degreeComparisonQuestion]

end Semantics.Attitudes.Distributivity
