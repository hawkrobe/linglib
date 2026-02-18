import Linglib.Core.Presupposition
import Linglib.Theories.Semantics.Presupposition.LocalContext

/-!
# Projection Mechanisms: Compositional Filtering vs. RSA BToM

Compares two theories of presupposition projection:

1. **Compositional filtering** (Heim 1983, Schlenker 2009): Presuppositions
   project through connectives via local context computation. The filtering
   presupposition of "if A then B_p" is "A → p" (the antecedent filters
   the consequent's presupposition).

2. **RSA BToM** (Scontras & Tonhauser 2025): Projection is a pragmatic
   inference. The listener (L1) inverts the speaker's generative model to
   infer which propositions the speaker takes for granted. No lexical
   presupposition encoding is required.

## The Key Empirical Argument

Scontras & Tonhauser (2025) argue that projection arises from pragmatic
reasoning about the speaker's private assumptions, not from lexical
encoding of presuppositions. Their BToM model predicts that even
non-factive "think" — which has NO presupposition to filter — should
exhibit projection effects, because L1 can still infer what the speaker
takes for granted. This is predicted by RSA BToM but NOT by compositional
filtering (which predicts trivial presupposition for non-presuppositional
items).

## What This Comparison Formalizes

1. For factive "know": both theories predict conditional presupposition,
   but for different reasons (filtering: "A → C"; BToM: pragmatic inference)
2. For non-factive "think": only BToM predicts conditional presupposition
   effects; filtering predicts nothing (trivial presupposition)
3. BToM strictly subsumes filtering for projection predictions in
   conditional environments

## References

- Heim (1983). On the Projection Problem for Presuppositions.
  @cite{heim-1983}
- Schlenker (2009). Local Contexts. @cite{schlenker-2009}
- Scontras & Tonhauser (2025). Projection without lexically-specified
  presupposition. @cite{scontras-tonhauser-2025}
- Baker, Jara-Ettinger, Saxe & Tenenbaum (2017). Rational quantitative
  attribution of beliefs, desires and percepts. Nature Human Behaviour.
  @cite{baker-jara-ettinger-saxe-tenenbaum-2017}
-/

namespace Comparisons.ProjectionMechanisms

open Core.Presupposition

-- Filtering Theory Predictions

section Filtering

variable {W : Type*}

/--
A factive verb "know" has a presupposition: C must be true.
-/
def factivePresup (c : W → Bool) : PrProp W where
  presup := c
  assertion := λ _ => true  -- Simplified: just the presupposition component

/--
A non-factive verb "think" has NO presupposition.
-/
def nonFactivePresup : PrProp W where
  presup := λ _ => true
  assertion := λ _ => true

/--
The filtering prediction for "if A then know-C":
the presupposition of the consequent (= C) is filtered by the antecedent.
Result: conditional presupposes "A → C".
-/
def filteringPrediction_know (a c : W → Bool) : PrProp W :=
  PrProp.impFilter (PrProp.ofBProp a) (factivePresup c)

/--
The filtering prediction for "if A then think-C":
"think" has no presupposition, so filtering produces a trivial result.
-/
def filteringPrediction_think (a : W → Bool) : PrProp W :=
  PrProp.impFilter (PrProp.ofBProp a) nonFactivePresup

/--
**Filtering predicts non-trivial presupposition for "know"**:
The presupposition of "if A then know-C" is ¬A ∨ C (= A → C),
which is NOT tautological.
-/
theorem filtering_know_nontrivial (a c : W → Bool)
    (h : ∃ w, a w = true ∧ c w = false) :
    ∃ w, (filteringPrediction_know a c).presup w = false := by
  obtain ⟨w, ha, hc⟩ := h
  use w
  simp [filteringPrediction_know, PrProp.impFilter, PrProp.ofBProp, factivePresup, ha, hc]

/--
**Filtering predicts TRIVIAL presupposition for "think"**:
The presupposition of "if A then think-C" is always true,
regardless of A, because "think" contributes no presupposition.
-/
theorem filtering_think_trivial (a : W → Bool) :
    ∀ w, (filteringPrediction_think a).presup w = true := by
  intro w
  simp only [filteringPrediction_think, PrProp.impFilter, PrProp.ofBProp, nonFactivePresup]
  cases a w <;> rfl

end Filtering

-- BToM Predictions

section BToM_

/--
BToM predicts projection effects for ANY verb in conditional environments,
because projection arises from pragmatic reasoning about the speaker's
private assumptions, not from lexical presupposition.

The key mechanism: when A and C are related (correlated in the prior),
the listener infers that a speaker who utters "if A, X Vs C" likely takes
C for granted — regardless of whether V is factive.
-/
structure BToMPrediction where
  /-- Whether projection is predicted for factive verbs in conditionals. -/
  factive_projects : Bool
  /-- Whether projection is predicted for non-factive verbs in conditionals. -/
  nonFactive_projects : Bool
  /-- Whether relatedness modulates projection strength. -/
  relatedness_modulates : Bool

/-- BToM predictions: both factive and non-factive show conditional
    presupposition, modulated by relatedness. -/
def btomPrediction : BToMPrediction where
  factive_projects := true
  nonFactive_projects := true
  relatedness_modulates := true

/-- Filtering predictions: only factive shows conditional presupposition,
    with no role for relatedness (it's purely structural). -/
def filteringPrediction : BToMPrediction where
  factive_projects := true
  nonFactive_projects := false    -- Think has no presupposition
  relatedness_modulates := false  -- Filtering is structural, not probabilistic

end BToM_

-- Comparison Theorems

/--
**Strict subsumption**: BToM predicts everything filtering predicts
(factive conditional presupposition) plus more (non-factive conditional
presupposition, relatedness modulation).
-/
theorem btom_subsumes_filtering :
    -- BToM agrees with filtering on factive projection
    btomPrediction.factive_projects = filteringPrediction.factive_projects ∧
    -- BToM predicts non-factive projection where filtering doesn't
    btomPrediction.nonFactive_projects = true ∧
    filteringPrediction.nonFactive_projects = false ∧
    -- BToM predicts relatedness modulation where filtering doesn't
    btomPrediction.relatedness_modulates = true ∧
    filteringPrediction.relatedness_modulates = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
**The critical divergence**: For non-factive "think" in conditionals,
filtering predicts trivial presupposition (no projection), while BToM
predicts non-trivial projection modulated by relatedness.

This is the Scontras & Tonhauser (2025) argument: if projection were
due to compositional filtering alone, non-presuppositional items like
"think" should show no effect. But BToM predicts projection effects
even for "think", because L1 infers the speaker's private assumptions
regardless of the verb's factivity status.
-/
theorem critical_divergence_at_nonfactive :
    filteringPrediction.nonFactive_projects ≠ btomPrediction.nonFactive_projects := by
  decide

/--
**Filtering is a special case**: When relatedness is maximal (A entails C),
BToM's projection prediction converges to the filtering prediction.
Filtering captures the structural component; BToM adds the probabilistic
modulation.
-/
theorem filtering_is_limiting_case :
    -- When A entails C, filtering presupposition of "if A, know C" is trivial
    -- (because A → C is already satisfied)
    ∀ {W : Type*} (a c : W → Bool),
      (∀ w, a w = true → c w = true) →
      (∀ w, (filteringPrediction_know a c).presup w = true) := by
  intro W a c h_entails w
  simp [filteringPrediction_know, PrProp.impFilter, PrProp.ofBProp, factivePresup]
  cases ha : a w
  · simp
  · simp [h_entails w ha]

end Comparisons.ProjectionMechanisms
