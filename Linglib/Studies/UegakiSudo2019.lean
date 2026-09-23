module

public import Linglib.Semantics.Attitudes.Preference
public import Linglib.Data.Examples.UegakiSudo2019
public import Mathlib.Tactic.NormNum

/-!
# Uegaki and Sudo (2019): The *hope*-wh Puzzle

This file formalizes [uegaki-sudo-2019]'s explanation of why the non-veridical preferential
predicates, *hope*, *wish*, *expect*, *fear*, are anti-rogative, (8), while the veridical ones,
*be surprised*, *be happy*, *like*, *hate*, take interrogative complements, (7). Complements
denote sets of propositions, declaratives singletons, and a preferential predicate compares the
subject's degree of preference for an answer with a threshold over a comparison class `C` of
focus alternatives, the degree semantics of [villalta-2008] and [romero-2015], with `C` a subset
of the question by the focus operator, (30). The predicate presupposes Threshold Significance,
that some member of the comparison class clears the threshold, motivated by (41): so *hope*
with a question, (36), asserts no more than it presupposes, `significance_entails_hope_question`,
and is true whenever defined, `hope_question_iff_significance`, an L-analytic meaning in the
sense of [gajewski-2002] and hence ungrammatical. *Hope* with a declarative, (35), is not
trivial, the assertion concerning the one proposition of the complement,
`exists_significance_not_hope_declarative`. The veridical predicates restrict the quantification
over answers to true, believed answers, (26) and (28), `veridicalProp` and `veridicalQuestion`,
which stay clausally distributive, `veridical_isDistributive`, but whose truth depends on the
world even under Threshold Significance, `veridicality_breaks_triviality`: a preferred false
answer does not make *John is happy about who jumped* true.

## Implementation notes

The non-veridical predicates are the substrate's degree-comparison predicates,
`Preferential.hope` and `Preferential.ThresholdSignificance`, whose question semantics is the
existential of (34) without the membership of the answer in the comparison class, which the
subset condition (30) supplies. The veridical semantics keeps the paper's belief component as a
predicate parameter and the membership condition. The doxastic condition of
[anand-hacquard-2013], (39), the selective focus sensitivity and exhaustivity refinements of
section 4, and the *about*-nominalization of section 5 are not formalized. The examples are the
rows of `Data.Examples.UegakiSudo2019`.

## References

* [uegaki-sudo-2019]
* [villalta-2008]
* [romero-2015]
* [gajewski-2002]
* [anand-hacquard-2013]
-/

@[expose] public section

namespace UegakiSudo2019

open Preferential

variable {W E : Type*} (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)

/-! ### Triviality for non-veridical preferentials -/

/-- (36): with the comparison class drawn from the question, (30), Threshold Significance
entails the assertion of *hope* with a question. -/
theorem significance_entails_hope_question (x : E) {Q C : List (Finset W)} (hCQ : C ⊆ Q)
    (h : ThresholdSignificance μ θ x C) : (hope μ θ).questionSemantics x Q C :=
  let ⟨p, hp, hd⟩ := h; ⟨p, hCQ hp, hd⟩

/-- When the comparison class is the question, the assertion of *hope* with a question is its
presupposition: the meaning is true whenever defined, [gajewski-2002]'s L-analyticity, which
makes *hope* anti-rogative. -/
theorem hope_question_iff_significance (x : E) (Q : List (Finset W)) :
    (hope μ θ).questionSemantics x Q Q ↔ ThresholdSignificance μ θ x Q :=
  Iff.rfl

/-- (35): *hope* with a declarative is not trivial. Threshold Significance over the focus
alternatives does not settle whether the subject prefers the one proposition of the complement:
a model with a preferred alternative and a dispreferred complement. -/
theorem exists_significance_not_hope_declarative :
    ∃ (W E : Type) (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) (x : E) (A : Finset W)
      (C : List (Finset W)), A ∈ C ∧ ThresholdSignificance μ θ x C ∧
        ¬ (hope μ θ).questionSemantics x [A] C := by
  refine ⟨Bool, Unit, λ _ p => if true ∈ p then 1 else -1, λ _ => 0, (), {false},
    [{true}, {false}], by simp, ⟨{true}, by simp, by norm_num⟩, ?_⟩
  rintro ⟨p, hp, hd⟩
  simp only [List.mem_singleton] at hp
  subst hp
  norm_num [hope, mkDegreeComparison] at hd

/-! ### Veridical preferentials -/

variable (believes : E → Finset W → W → Prop)

/-- (26): *x is happy that p* at `w` requires the complement to be true at `w`, believed by `x`
and a member of the comparison class. -/
def veridicalProp (C : List (Finset W)) (x : E) (p : Finset W) (w : W) : Prop :=
  w ∈ p ∧ believes x p w ∧ p ∈ C ∧ μ x p > θ C

/-- (28): *x is happy about Q* at `w`: some true, believed answer in the comparison class clears
the threshold. -/
def veridicalQuestion (C : List (Finset W)) (x : E) (Q : List (Finset W)) (w : W) : Prop :=
  ∃ p ∈ Q, w ∈ p ∧ believes x p w ∧ p ∈ C ∧ μ x p > θ C

/-- Veridical preferentials are clausally distributive: it is veridicality, not a failure of
distributivity, that lets them take questions. -/
theorem veridical_isDistributive (C : List (Finset W)) :
    Distributivity.IsDistributive (veridicalProp μ θ believes C)
      (veridicalQuestion μ θ believes C) :=
  λ _ _ _ => Iff.rfl

/-- Veridicality breaks the triviality: a model where Threshold Significance holds, so the
non-veridical assertion is true, but the veridical assertion is false at a world where the true
answer is not the preferred one. Two worlds, the polar question over them, evaluated at the
dispreferred world. -/
theorem veridicality_breaks_triviality :
    ∃ (W E : Type) (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
      (believes : E → Finset W → W → Prop) (x : E) (Q : List (Finset W)) (w : W),
      ThresholdSignificance μ θ x Q ∧ (hope μ θ).questionSemantics x Q Q ∧
        ¬ veridicalQuestion μ θ believes Q x Q w := by
  refine ⟨Bool, Unit, λ _ p => if true ∈ p then 1 else -1, λ _ => 0, λ _ _ _ => True, (),
    [{true}, {false}], false, ⟨{true}, by simp, by norm_num⟩, ⟨{true}, by simp, by norm_num⟩, ?_⟩
  rintro ⟨p, hp, hw, _, _, hd⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp at hw
  · norm_num [Finset.mem_singleton] at hd

end UegakiSudo2019
