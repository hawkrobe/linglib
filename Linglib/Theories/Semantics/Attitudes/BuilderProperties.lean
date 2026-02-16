/-
# Builder Properties: Derived Properties from Fragment Lexical Features

This module connects Fragment lexical entries to Theory-derived properties.
It provides the derivation functions that compute theoretical properties
(C-distributivity, NVP class) from the minimal basis in the Fragment layer.

## Architecture

The Fragment layer defines `PreferentialBuilder` as minimal lexical features:
- `degreeComparison`: Degree-comparison semantics (Villalta 2008)
- `uncertaintyBased`: Uncertainty-based semantics (Elliott et al. 2017)
- `relevanceBased`: Relevance-based semantics

This module derives theoretical properties from those features:
- C-distributivity: from semantic structure (proved in CDistributivity.lean)
- NVP class: from C-distributivity + valence (Qing et al. 2025)

## Why This File Exists

The Fragment layer (`Verbal.lean`) imports the Theory layer (`Preferential.lean`)
to get types like `AttitudeValence` and `NVPClass`. This creates a dependency:

    Fragment → Theory (for types)

To derive properties FROM Fragment features, we need:

    Theory → Fragment (for PreferentialBuilder)

This file breaks the cycle by importing both and defining the derivations.

## References

- Qing et al. (2025). When can NVPs take questions?
- Elliott et al. (2017). Predicates of relevance and theories of question embedding.
- Villalta (2008). Mood and gradability.
-/

import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Attitudes.Preferential

namespace Semantics.Attitudes.BuilderProperties

open Fragments.English.Predicates.Verbal (PreferentialBuilder AttitudeBuilder)
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass)

-- C-Distributivity from Semantic Builder

/--
C-distributivity is derived from the semantic builder structure.

This function mirrors the proved theorems:
- `degreeComparisonPredicate_isCDistributive`: degree-comparison → C-dist
- `worry_not_cDistributive`: uncertainty-based → NOT C-dist
- (analogous for relevance-based)

The computation is justified by the semantic structure:
- Degree-comparison: ⟦x V Q⟧ = ∃p ∈ Q. μ(x,p) > θ — existential over propositional
- Uncertainty-based: ⟦x V Q⟧ involves global uncertainty, not existential
- Relevance-based: ⟦x V Q⟧ involves resolution/relevance, not existential
-/
def PreferentialBuilder.isCDistributive : PreferentialBuilder → Bool
  | .degreeComparison _ => true   -- By degreeComparisonPredicate_isCDistributive
  | .uncertaintyBased => false    -- By worry_not_cDistributive
  | .relevanceBased _ => false    -- By analogous theorem for relevance semantics

-- NVP Classification from C-Distributivity + Valence

/--
NVP class is derived from C-distributivity and valence.

This matches `Preferential.classifyNVP` but computed from the builder:
- Class 1: Non-C-distributive (worry, qidai) — can embed questions regardless of valence
- Class 2: C-distributive + negative (fear, dread) — can embed questions (no TSP)
- Class 3: C-distributive + positive (hope, wish) — anti-rogative (TSP → triviality)

The derivation chain:
1. Builder structure → C-distributivity (this file)
2. Builder → valence (in Fragment, lexical property)
3. C-distributivity + valence → NVP class (this function)
-/
def PreferentialBuilder.nvpClass (b : PreferentialBuilder) : NVPClass :=
  if !PreferentialBuilder.isCDistributive b then .class1_nonCDist
  else if b.valence == .negative then .class2_cDist_negative
  else .class3_cDist_positive

-- AttitudeBuilder Derived Properties

/--
Get C-distributivity for preferential attitudes.
Returns `none` for doxastic attitudes (C-distributivity doesn't apply).
-/
def AttitudeBuilder.cDistributive : AttitudeBuilder → Option Bool
  | .doxastic _ => none
  | .preferential b => some (PreferentialBuilder.isCDistributive b)

/--
Get NVP class for preferential attitudes.
Returns `none` for doxastic attitudes (NVP classification doesn't apply).
-/
def AttitudeBuilder.nvpClass : AttitudeBuilder → Option NVPClass
  | .doxastic _ => none
  | .preferential b => some (PreferentialBuilder.nvpClass b)

-- VerbEntry Derived Properties

open Fragments.English.Predicates.Verbal (VerbEntry)

/-- C-distributivity is derived from the attitude builder -/
def VerbEntry.cDistributive (v : VerbEntry) : Option Bool :=
  v.attitudeBuilder.bind AttitudeBuilder.cDistributive

/-- NVP class is derived from the attitude builder -/
def VerbEntry.nvpClass (v : VerbEntry) : Option NVPClass :=
  v.attitudeBuilder.bind AttitudeBuilder.nvpClass

/--
Can take questions: Derived for preferential verbs, base field for others.

For preferential verbs: determined by NVP class (Class 1, 2 can; Class 3 cannot)
For non-preferential verbs: uses `takesQuestionBase` field
-/
def VerbEntry.takesQuestion (v : VerbEntry) : Bool :=
  match VerbEntry.nvpClass v with
  | some .class1_nonCDist => true
  | some .class2_cDist_negative => true
  | some .class3_cDist_positive => false
  | none => v.takesQuestionBase

/--
Is this verb anti-rogative (cannot take question complements canonically)?

Anti-rogative predicates are Class 3 NVPs: C-distributive + positive + TSP.
-/
def VerbEntry.isAntiRogative (v : VerbEntry) : Bool :=
  match VerbEntry.nvpClass v with
  | some .class3_cDist_positive => true
  | _ => false

/--
Can this verb canonically embed a question?

Based on Qing et al. (2025) classification:
- Class 1 (non-C-distributive): Yes
- Class 2 (C-dist + negative): Yes
- Class 3 (C-dist + positive): No (anti-rogative)
- Non-preferential attitudes with takesQuestion: Yes
-/
def VerbEntry.canEmbedQuestion (v : VerbEntry) : Bool :=
  match VerbEntry.nvpClass v with
  | some .class1_nonCDist => true
  | some .class2_cDist_negative => true
  | some .class3_cDist_positive => false
  | none => VerbEntry.takesQuestion v

-- Filtered Verb Lists (Derived)

open Fragments.English.Predicates.Verbal (allVerbs)

/--
Get all anti-rogative verbs (Class 3 NVPs).
-/
def antiRogativeVerbs : List VerbEntry :=
  allVerbs.filter VerbEntry.isAntiRogative

/--
Get all question-embedding verbs.
-/
def questionEmbeddingVerbs : List VerbEntry :=
  allVerbs.filter VerbEntry.canEmbedQuestion

-- Verification Theorems

/-- Hope (degree-comparison positive) is C-distributive -/
theorem hope_builder_cDistributive :
    PreferentialBuilder.isCDistributive (.degreeComparison .positive) = true := rfl

/-- Fear (degree-comparison negative) is C-distributive -/
theorem fear_builder_cDistributive :
    PreferentialBuilder.isCDistributive (.degreeComparison .negative) = true := rfl

/-- Worry (uncertainty-based) is NOT C-distributive -/
theorem worry_builder_not_cDistributive :
    PreferentialBuilder.isCDistributive .uncertaintyBased = false := rfl

/-- Qidai (relevance-based) is NOT C-distributive -/
theorem qidai_builder_not_cDistributive :
    PreferentialBuilder.isCDistributive (.relevanceBased .positive) = false := rfl

/-- Hope is Class 3 (C-dist + positive → anti-rogative) -/
theorem hope_builder_class3 :
    PreferentialBuilder.nvpClass (.degreeComparison .positive) = .class3_cDist_positive := by
  native_decide

/-- Fear is Class 2 (C-dist + negative → takes questions) -/
theorem fear_builder_class2 :
    PreferentialBuilder.nvpClass (.degreeComparison .negative) = .class2_cDist_negative := by
  native_decide

/-- Worry is Class 1 (non-C-dist → takes questions) -/
theorem worry_builder_class1 :
    PreferentialBuilder.nvpClass .uncertaintyBased = .class1_nonCDist := by
  native_decide

/-- Qidai is Class 1 (non-C-dist → takes questions despite positive valence) -/
theorem qidai_builder_class1 :
    PreferentialBuilder.nvpClass (.relevanceBased .positive) = .class1_nonCDist := by
  native_decide

end Semantics.Attitudes.BuilderProperties
