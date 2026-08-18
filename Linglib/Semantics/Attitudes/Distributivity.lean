import Mathlib.Data.Finset.Basic

/-!
# Clausal distributivity

A clause-embedding predicate is *clausally distributive* — written
C(lausal)-distributive in [qing-uegaki-2025] — when its question
semantics is existential quantification over its propositional
semantics: ⟦x V Q⟧ ↔ ∃p ∈ Q. ⟦x V p⟧ ([uegaki-sudo-2019];
[uegaki-2022]). `IsDistributive` states the property for a pair of
propositional and question semantics, so it is proved from a
predicate's semantic structure rather than stipulated per predicate.

The degree-comparison preferentials of `Preference.lean` are
distributive by construction
(`Preferential.mkDegreeComparison_isDistributive`); predicates whose
question semantics outruns the existential — global uncertainty for
*worry*, decision-relevance for *care* ([elliott-etal-2017]) — are
not (`Preferential.worry_not_distributive`). Veridical preferentials
instantiate the world-sensitive form (`Studies/UegakiSudo2019.lean`).

Questions are alternative lists over `Finset W` propositions,
matching the question representation of
`Semantics/Attitudes/Desire.lean`.
-/

namespace Distributivity

variable {W E : Type*}

/-- A predicate with propositional semantics `Vprop` and question
    semantics `Vquestion` is clausally distributive iff
    `Vquestion x Q w ↔ ∃ p ∈ Q, Vprop x p w`. -/
def IsDistributive (Vprop : E → Finset W → W → Prop)
    (Vquestion : E → List (Finset W) → W → Prop) : Prop :=
  ∀ (x : E) (Q : List (Finset W)) (w : W),
    Vquestion x Q w ↔ ∃ p ∈ Q, Vprop x p w

end Distributivity
