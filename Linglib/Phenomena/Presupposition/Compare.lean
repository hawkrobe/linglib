import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Presupposition.LocalContext

/-!
# Projection Mechanisms: Compositional Filtering vs. RSA BToM
@cite{scontras-tonhauser-2025} @cite{heim-1983}

Compares two theories of presupposition projection:

1. **Compositional filtering**: Presuppositions
   project through connectives via local context computation. The filtering
   presupposition of "if A then B_p" is "A → p" (the antecedent filters
   the consequent's presupposition).

2. **RSA BToM**: Projection is a pragmatic
   inference. The listener (L1) inverts the speaker's generative model to
   infer which propositions the speaker takes for granted. No lexical
   presupposition encoding is required.

## The Key Empirical Argument

@cite{scontras-tonhauser-2025} argue that projection arises from pragmatic
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

-/

namespace Phenomena.Presupposition.Compare

open Core.Presupposition

open Classical

-- Filtering Theory Predictions

section Filtering

variable {W : Type*}

/--
A factive verb "know" has a presupposition: C must be true.
-/
def factivePresup (c : W → Prop) : PrProp W where
  presup := c
  assertion := λ _ => True  -- Simplified: just the presupposition component

/--
A non-factive verb "think" has NO presupposition.
-/
def nonFactivePresup : PrProp W where
  presup := λ _ => True
  assertion := λ _ => True

/--
The filtering prediction for "if A then know-C":
the presupposition of the consequent (= C) is filtered by the antecedent.
Result: conditional presupposes "A → C".
-/
def filteringPrediction_know (a c : W → Prop) : PrProp W :=
  PrProp.impFilter (PrProp.ofProp' a) (factivePresup c)

/--
The filtering prediction for "if A then think-C":
"think" has no presupposition, so filtering produces a trivial result.
-/
def filteringPrediction_think (a : W → Prop) : PrProp W :=
  PrProp.impFilter (PrProp.ofProp' a) nonFactivePresup

/--
**Filtering predicts non-trivial presupposition for "know"**:
The presupposition of "if A then know-C" is ¬A ∨ C (= A → C),
which is NOT tautological.
-/
theorem filtering_know_nontrivial (a c : W → Prop)
    (h : ∃ w, a w ∧ ¬c w) :
    ∃ w, ¬(filteringPrediction_know a c).presup w := by
  obtain ⟨w, ha, hc⟩ := h
  refine ⟨w, ?_⟩
  simp only [filteringPrediction_know, PrProp.impFilter, PrProp.ofProp', factivePresup,
    not_and]
  intro _
  exact fun h_imp => hc (h_imp ha)

/--
**Filtering predicts TRIVIAL presupposition for "think"**:
The presupposition of "if A then think-C" is always true,
regardless of A, because "think" contributes no presupposition.
-/
theorem filtering_think_trivial (a : W → Prop) :
    ∀ w, (filteringPrediction_think a).presup w := by
  intro w
  simp only [filteringPrediction_think, PrProp.impFilter, PrProp.ofProp', nonFactivePresup]
  exact ⟨trivial, fun _ => trivial⟩

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

This is the @cite{scontras-tonhauser-2025} argument: if projection were
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
    ∀ {W : Type*} (a c : W → Prop),
      (∀ w, a w → c w) →
      (∀ w, (filteringPrediction_know a c).presup w) := by
  intro W a c h_entails w
  refine ⟨trivial, ?_⟩
  intro ha; exact h_entails w ha

end Phenomena.Presupposition.Compare
