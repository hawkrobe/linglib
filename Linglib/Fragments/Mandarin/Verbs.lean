/-
# Mandarin Verb Lexicon Fragment

Lexical entries for Mandarin Chinese verbs, with particular focus on
preferential attitude predicates relevant to Qing et al. (2025).

## Key Predicates

- **qidai** (期待, "look forward to"): Class 1 NVP — positive but non-C-distributive
- **danxin** (担心, "worry"): Class 1 NVP — negative, non-C-distributive

## Cross-Linguistic Significance

Mandarin "qidai" is crucial evidence for Qing et al.'s theory because:
- It's **positive** (like English "hope")
- But it **takes questions** (unlike English "hope")
- Explanation: qidai is **non-C-distributive**, avoiding triviality

## Architecture Note

Properties like C-distributivity and NVP class are DERIVED from the
`preferentialBuilder` field, not stipulated. This grounds the Fragment
entries in the Montague semantics via proved theorems.

## References

- Qing et al. (2025). When can NVPs take questions?
-/

import Linglib.Fragments.English.Verbs

namespace Fragments.Mandarin.Verbs

open Fragments.English.Verbs (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder)
open Montague.Lexicon.Attitudes.Doxastic (Veridicality)
open Montague.Lexicon.Attitudes.Preferential (AttitudeValence NVPClass)

-- ============================================================================
-- Mandarin Preferential Attitude Verbs
-- ============================================================================

/--
期待 "qidai" — look forward to (Class 1: takes questions despite positive valence)

Crucially **non-C-distributive**: "qidai Q" ≠ "∃p ∈ Q. qidai p"

Example:
  Zhangsan qidai shei hui lai.
  "Zhangsan looks forward to who will come."
  ✓ Grammatical (unlike English *"hope who")

The semantic builder is `relevanceBased .positive`:
- Positive valence (anticipation)
- NON-C-distributive: involves resolution/relevance, not just existential
- This is DERIVED from the builder via `PreferentialBuilder.isCDistributive`
-/
def qidai : VerbEntry where
  form := "qidai"
  form3sg := "qidai"  -- No morphological inflection in Mandarin
  formPast := "qidai"
  formPastPart := "qidai"
  formPresPart := "qidai"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- relevanceBased .positive → NOT C-distributive → Class 1 (takes questions!)
  preferentialBuilder := some (.relevanceBased .positive)

/--
担心 "danxin" — worry (Class 1: non-C-distributive negative)

Like English "worry", non-C-distributive.

Example:
  Zhangsan danxin shei hui lai.
  "Zhangsan worries about who will come."

The semantic builder is `uncertaintyBased`:
- Negative valence (worry/concern)
- NON-C-distributive (PROVED by worry_not_cDistributive)
- Class 1 regardless of valence
-/
def danxin : VerbEntry where
  form := "danxin"
  form3sg := "danxin"
  formPast := "danxin"
  formPastPart := "danxin"
  formPresPart := "danxin"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- uncertaintyBased → NOT C-distributive (PROVED) → Class 1 (takes questions)
  preferentialBuilder := some .uncertaintyBased

/--
希望 "xiwang" — hope (Class 3: anti-rogative, like English "hope")

C-distributive and positive, so cannot take questions canonically.

The semantic builder is `degreeComparison .positive`:
- Positive valence
- C-distributive (PROVED by degreeComparisonPredicate_isCDistributive)
- Has TSP because positive → Class 3 (anti-rogative)
-/
def xiwang : VerbEntry where
  form := "xiwang"
  form3sg := "xiwang"
  formPast := "xiwang"
  formPastPart := "xiwang"
  formPresPart := "xiwang"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- degreeComparison .positive → C-distributive (PROVED) → Class 3 (anti-rogative)
  preferentialBuilder := some (.degreeComparison .positive)

/--
害怕 "haipa" — fear (Class 2: takes questions)

C-distributive but negative, so no TSP, so takes questions.

The semantic builder is `degreeComparison .negative`:
- Negative valence
- C-distributive (PROVED by degreeComparisonPredicate_isCDistributive)
- No TSP because negative → Class 2
-/
def haipa : VerbEntry where
  form := "haipa"
  form3sg := "haipa"
  formPast := "haipa"
  formPastPart := "haipa"
  formPresPart := "haipa"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- degreeComparison .negative → C-distributive (PROVED) → Class 2 (takes questions)
  preferentialBuilder := some (.degreeComparison .negative)

-- ============================================================================
-- All Mandarin Verbs
-- ============================================================================

def allVerbs : List VerbEntry := [
  qidai, danxin, xiwang, haipa
]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Mandarin.Verbs
