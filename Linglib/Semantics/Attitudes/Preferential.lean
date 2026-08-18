import Mathlib.Data.Rat.Defs
import Linglib.Features.Attitudes
import Linglib.Semantics.Attitudes.Distributivity

/-!
# Preferential attitude semantics

Degree-based semantics for preferential attitude verbs (*hope*,
*fear*, *worry*, *wish*, *expect*), following [villalta-2008]:
⟦x V p⟧(C) = μ(x, p) > θ(C), for a preference degree function μ and a
contextual threshold θ over a comparison class C of propositions.

[qing-uegaki-2025] classify non-veridical preferentials by two
factors — clausal distributivity (`Distributivity.IsDistributive`)
and evaluative valence — and show that only the distributive positive
class (*hope*, *wish*, *expect*) is anti-rogative. The
degree-comparison predicates built here are distributive by
construction (`mkDegreeComparison_isDistributive`); *worry* and
Mandarin *qidai* carry an extra global condition on the question that
breaks distributivity (`worry_not_distributive`).

`ThresholdSignificance` is the presupposition [uegaki-sudo-2019]
posit for degree constructions: some member of the comparison class
clears the threshold. Positive preferentials trigger it while
negative ones do not ([qing-uegaki-2025] §3.2). The anti-rogativity
of the distributive positive class is derived from it in
`Studies/UegakiSudo2019.lean`; the classification's cross-linguistic
support lives in `Studies/QingEtAl2025.lean`; the emotive doxastic
refinement of *hope* and *fear* ([anand-hacquard-2013]) in
`Studies/AnandHacquard2013.lean`.
-/

namespace Preferential

open Features (AttitudeValence)

variable {W E : Type*}

/-- A preferential attitude predicate: an evaluative valence, a
    preference degree function, a contextual threshold, and
    propositional and question semantics relative to a comparison
    class of propositions. -/
structure PreferentialPredicate (W E : Type*) where
  /-- Evaluative valence (positive for *hope*, negative for *fear*). -/
  valence : AttitudeValence
  /-- Preference degree function: `μ x p` is how strongly `x` prefers
      (or, for negative valence, dreads) `p`. -/
  μ : E → Finset W → ℚ
  /-- Contextual threshold over a comparison class. -/
  θ : List (Finset W) → ℚ
  /-- ⟦x V p⟧(C), the propositional semantics. -/
  propSemantics : E → Finset W → List (Finset W) → Prop
  /-- ⟦x V Q⟧(C), the question semantics. -/
  questionSemantics : E → List (Finset W) → List (Finset W) → Prop

/-- A preferential predicate is clausally distributive when its
    question semantics is the existential over its propositional
    semantics — the world-free instance of
    `Distributivity.IsDistributive` (preferential semantics are
    world-independent because the predicates are non-veridical). -/
def PreferentialPredicate.IsDistributive (V : PreferentialPredicate W E) : Prop :=
  ∀ (x : E) (Q C : List (Finset W)),
    V.questionSemantics x Q C ↔ ∃ p ∈ Q, V.propSemantics x p C

/-! ### Degree-comparison predicates -/

/-- Degree-comparison predicate ([villalta-2008]): ⟦x V p⟧(C) =
    μ(x, p) > θ(C), with the question semantics the pointwise
    existential. -/
def mkDegreeComparison (valence : AttitudeValence)
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E where
  valence := valence
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := ∃ p ∈ Q, μ x p > θ C

/-- Degree-comparison predicates are clausally distributive by
    construction: the question semantics is the existential over the
    propositional semantics. -/
theorem mkDegreeComparison_isDistributive (valence : AttitudeValence)
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    (mkDegreeComparison valence μ θ).IsDistributive :=
  fun _ _ _ => Iff.rfl

/-- *hope*: degree comparison, positive valence. What distinguishes
    *hope* from *want* is an additional doxastic component
    ([anand-hacquard-2013]), formalized in
    `Studies/AnandHacquard2013.lean`. -/
def hope (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- *fear*: degree comparison, negative valence. -/
def fear (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .negative μ θ

/-- *expect*: degree comparison, positive valence. -/
def expect (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- *wish*: degree comparison, positive valence. -/
def wish (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- *dread*: degree comparison, negative valence. -/
def dread (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .negative μ θ

/-! ### Non-distributive preferentials -/

/-- *worry*: propositionally a degree comparison, but the question
    semantics adds a global uncertainty condition on the question —
    not reducible to the existential over answers
    ([qing-uegaki-2025] §3.1.2). -/
def worry (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (Uncertain : E → List (Finset W) → Prop) :
    PreferentialPredicate W E where
  valence := .negative
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := Uncertain x Q ∧ ∃ p ∈ Q, μ x p > θ C

/-- Mandarin *qidai* "look forward to": positive valence, with an
    anticipation-of-resolution condition on the question — a positive
    non-distributive preferential ([qing-uegaki-2025] §3.1.1). -/
def qidai (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (AnticipatesResolution : E → List (Finset W) → Prop) :
    PreferentialPredicate W E where
  valence := .positive
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := AnticipatesResolution x Q ∧ ∃ p ∈ Q, μ x p > θ C

/-- *worry* is not clausally distributive: when the agent is not
    uncertain about `Q` but some answer clears the threshold, the
    existential over the propositional semantics holds while the
    question semantics fails. -/
theorem worry_not_distributive (μ : E → Finset W → ℚ)
    (θ : List (Finset W) → ℚ) (Uncertain : E → List (Finset W) → Prop)
    (x : E) (Q C : List (Finset W)) (hu : ¬ Uncertain x Q)
    (h : ∃ p ∈ Q, μ x p > θ C) :
    ¬ (worry μ θ Uncertain).IsDistributive :=
  fun hdist => hu (((hdist x Q C).mpr h).1)

/-! ### Threshold significance -/

/-- The Threshold Significance Presupposition ([uegaki-sudo-2019]):
    some member of the comparison class clears the threshold. Degree
    constructions presuppose it generally; positive preferentials
    trigger it while negative ones do not ([qing-uegaki-2025] §3.2),
    which is how *fear*-type predicates escape the anti-rogativity
    triviality derived in `Studies/UegakiSudo2019.lean`. -/
def ThresholdSignificance (μ : E → Finset W → ℚ)
    (θ : List (Finset W) → ℚ) (x : E) (C : List (Finset W)) : Prop :=
  ∃ p ∈ C, μ x p > θ C

end Preferential
