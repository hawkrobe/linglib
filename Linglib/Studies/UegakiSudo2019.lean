import Linglib.Semantics.Attitudes.Preferential
import Mathlib.Tactic.NormNum

/-!
# Uegaki & Sudo 2019: The *hope*-wh puzzle

[uegaki-sudo-2019] derive the anti-rogativity of non-veridical
preferential predicates (*hope*, *wish*) from triviality. With the
degree semantics ⟦x V p⟧ = μ(x,p) > θ(C) ([villalta-2008]), the
Threshold Significance Presupposition, and clausal distributivity,
combining the predicate with a question whose answers exhaust the
comparison class yields an assertion identical to its presupposition
(`hope_question_iff_significance`) — an L-analytic meaning in the
sense of [gajewski-2002], hence ungrammaticality.

Veridical preferentials (*be surprised*, *be happy*, *be glad*,
*like*, *hate*) escape and take questions: the truth requirement on
the complement makes the assertion world-dependent, so threshold
significance no longer settles it. `veridicalQuestion` is the
world-sensitive semantics — still clausally distributive
(`veridical_isDistributive`) — and `veridicality_breaks_triviality`
exhibits a model where the presupposition holds, the non-veridical
assertion is (trivially) true, and the veridical assertion is false
because the true answer is not the preferred one.
-/

namespace UegakiSudo2019

open Preferential

variable {W E : Type*}

/-! ### Triviality for non-veridical preferentials -/

/-- With the question's answers drawn from the comparison class, the
    *hope*-question assertion entails threshold significance. -/
theorem hope_question_entails_significance
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (x : E) (Q C : List (Finset W)) (hQC : Q ⊆ C)
    (h : (hope μ θ).questionSemantics x Q C) :
    ThresholdSignificance μ θ x C :=
  let ⟨p, hp, hd⟩ := h; ⟨p, hQC hp, hd⟩

/-- Conversely, threshold significance entails the assertion when the
    comparison class is contained in the question. -/
theorem significance_entails_hope_question
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (x : E) (Q C : List (Finset W)) (hCQ : C ⊆ Q)
    (h : ThresholdSignificance μ θ x C) :
    (hope μ θ).questionSemantics x Q C :=
  let ⟨p, hp, hd⟩ := h; ⟨p, hCQ hp, hd⟩

/-- When the question's answers are exactly the comparison class, the
    assertion of *hope* + question is its presupposition: the meaning
    is L-analytic ([gajewski-2002]) — true whenever defined — which
    is the triviality that makes *hope* anti-rogative. -/
theorem hope_question_iff_significance
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (x : E) (Q : List (Finset W)) :
    (hope μ θ).questionSemantics x Q Q ↔ ThresholdSignificance μ θ x Q :=
  Iff.rfl

/-! ### Veridical preferentials -/

/-- Veridical propositional semantics: ⟦x is happy that p⟧(w, C)
    requires the complement to be true at the evaluation world. -/
def veridicalProp (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (C : List (Finset W)) (x : E) (p : Finset W) (w : W) : Prop :=
  w ∈ p ∧ μ x p > θ C

/-- Veridical question semantics: some true answer clears the
    threshold. -/
def veridicalQuestion (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (C : List (Finset W)) (x : E) (Q : List (Finset W)) (w : W) : Prop :=
  ∃ p ∈ Q, w ∈ p ∧ μ x p > θ C

/-- Veridical preferentials are clausally distributive — it is
    veridicality, not a failure of distributivity, that lets them
    take questions. -/
theorem veridical_isDistributive (μ : E → Finset W → ℚ)
    (θ : List (Finset W) → ℚ) (C : List (Finset W)) :
    Distributivity.IsDistributive (veridicalProp μ θ C)
      (veridicalQuestion μ θ C) :=
  fun _ _ _ => Iff.rfl

/-- Veridicality breaks the triviality: a model where threshold
    significance holds and the non-veridical assertion is therefore
    true, but the veridical assertion is false — the true answer is
    not the preferred one. Two worlds, the polar question over them,
    evaluated at the dispreferred world. -/
theorem veridicality_breaks_triviality :
    ∃ (W E : Type) (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
      (x : E) (Q : List (Finset W)) (w : W),
      ThresholdSignificance μ θ x Q ∧
      (hope μ θ).questionSemantics x Q Q ∧
      ¬ veridicalQuestion μ θ Q x Q w := by
  refine ⟨Bool, Unit, (fun _ p => if true ∈ p then 1 else -1), (fun _ => 0),
          (), [{true}, {false}], false, ?_, ?_, ?_⟩
  · exact ⟨{true}, by simp, by norm_num⟩
  · exact ⟨{true}, by simp, by norm_num⟩
  · rintro ⟨p, hp, hw, hd⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp at hw
    · norm_num [Finset.mem_singleton] at hd

end UegakiSudo2019
