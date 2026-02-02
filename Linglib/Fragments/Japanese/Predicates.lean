/-
# Japanese Predicate Lexicon Fragment

Lexical entries for Japanese predicates, with particular focus on
preferential attitude predicates relevant to Qing et al. (2025).

## Key Predicates

- **tanosimi** (楽しみ, "looking forward to"): Class 1 NVP
- **osore** (恐れ, "fear"): Class 2 NVP
- **kitai** (期待, "expect/hope"): Class 3 NVP

## Cross-Linguistic Significance

Japanese provides evidence for all three NVP classes:
- Class 1: tanosimi (positive, non-C-distributive, takes questions)
- Class 2: osore (negative, C-distributive, takes questions)
- Class 3: kitai (positive, C-distributive, anti-rogative)

## Architecture Note

Properties like C-distributivity and NVP class are DERIVED from the
`preferentialBuilder` field, not stipulated. This grounds the Fragment
entries in the Montague semantics via proved theorems.

## References

- Qing et al. (2025). When can NVPs take questions?
-/

import Linglib.Fragments.English.Predicates.Verbal

namespace Fragments.Japanese.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder)
open Montague.Verb.Attitude.Doxastic (Veridicality)
open Montague.Verb.Attitude.Preferential (AttitudeValence NVPClass)

-- ============================================================================
-- Japanese Preferential Attitude Verbs
-- ============================================================================

/--
楽しみ "tanosimi" — looking forward to (Class 1: positive but non-C-distributive)

Like Mandarin qidai: positive valence but non-C-distributive,
so it can take question complements.

Note: This is the nominal form often used predicatively.

The semantic builder is `relevanceBased .positive`:
- Positive valence (anticipation of good outcome)
- NON-C-distributive: "tanosimi Q" ≠ "∃p ∈ Q. tanosimi p"
- This is DERIVED from the builder via `PreferentialBuilder.isCDistributive`
-/
def tanosimi : VerbEntry where
  form := "tanosimi"
  form3sg := "tanosimi da"
  formPast := "tanosimi datta"
  formPastPart := "tanosimi"
  formPresPart := "tanosimi"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- relevanceBased .positive → NOT C-distributive → Class 1 (takes questions)
  preferentialBuilder := some (.relevanceBased .positive)

/--
恐れ "osore" — fear (Class 2: C-distributive negative)

Like English "fear": C-distributive and negative,
so no TSP, so takes questions.

The semantic builder is `degreeComparison .negative`:
- Negative valence
- C-distributive (PROVED by degreeComparisonPredicate_isCDistributive)
- No TSP because negative → Class 2
-/
def osore : VerbEntry where
  form := "osore"
  form3sg := "osoreru"
  formPast := "osoreta"
  formPastPart := "osorete"
  formPresPart := "osoreteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- degreeComparison .negative → C-distributive (PROVED) → Class 2 (takes questions)
  preferentialBuilder := some (.degreeComparison .negative)

/--
期待 "kitai" — expect/hope (Class 3: anti-rogative)

Like English "hope"/"expect": C-distributive and positive,
so has TSP, so anti-rogative.

The semantic builder is `degreeComparison .positive`:
- Positive valence
- C-distributive (PROVED by degreeComparisonPredicate_isCDistributive)
- Has TSP because positive → Class 3 (anti-rogative)
-/
def kitai : VerbEntry where
  form := "kitai"
  form3sg := "kitai suru"
  formPast := "kitai shita"
  formPastPart := "kitai shite"
  formPresPart := "kitai shiteiru"
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
心配 "shinpai" — worry (Class 1: non-C-distributive)

Like English "worry": non-C-distributive, takes questions.

The semantic builder is `uncertaintyBased`:
- Negative valence (inherited)
- NON-C-distributive (PROVED by worry_not_cDistributive)
- Class 1 regardless of valence
-/
def shinpai : VerbEntry where
  form := "shinpai"
  form3sg := "shinpai suru"
  formPast := "shinpai shita"
  formPastPart := "shinpai shite"
  formPresPart := "shinpai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  attitudeVeridicality := some .nonVeridical
  -- uncertaintyBased → NOT C-distributive (PROVED) → Class 1 (takes questions)
  preferentialBuilder := some .uncertaintyBased

-- ============================================================================
-- All Japanese Verbs
-- ============================================================================

def allVerbs : List VerbEntry := [
  tanosimi, osore, kitai, shinpai
]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Japanese.Predicates
