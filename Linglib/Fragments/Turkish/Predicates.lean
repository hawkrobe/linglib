/-
# Turkish Predicate Lexicon Fragment

Lexical entries for Turkish predicates, with particular focus on
preferential attitude predicates relevant to Qing et al. (2025).

## Key Predicates

- **kork-** (fear): Class 2 NVP — symmetric interpretation
- **um-** (hope): Class 3 NVP — anti-rogative canonically

## Cross-Linguistic Significance

Turkish provides evidence for:
1. Class 2 predicates with symmetric interpretation (kork-)
2. Non-canonical composition via "diye" clauses (um- + diye)

The "diye" construction allows Class 3 predicates to appear with
questions via adjunction rather than canonical complementation.

## Architecture Note

Properties like C-distributivity and NVP class are DERIVED from the
`attitudeBuilder` field, not stipulated. This grounds the Fragment
entries in the Montague semantics via proved theorems.

## References

- Qing et al. (2025). When can NVPs take questions?
- Özyıldız (2017). Turkish diye clauses.
-/

import Linglib.Fragments.English.Predicates.Verbal

namespace Fragments.Turkish.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder AttitudeBuilder)
open Montague.Verb.Attitude.Preferential (AttitudeValence NVPClass)

-- ============================================================================
-- Turkish Preferential Attitude Verbs
-- ============================================================================

/--
"kork-" — fear (Class 2: C-distributive negative, takes questions)

Takes questions with **symmetric** interpretation:
"Ali kork-uyor kim gel-ecek diye"
= Ali fears [who will come]
= Ali fears that person X will come OR fears that person Y will come...

This symmetric interpretation is predicted by negative valence
(no bouletic goal → no asymmetry from Tabatowski's expressive content).

The semantic builder is `degreeComparison .negative`:
- Negative valence
- C-distributive (PROVED by degreeComparisonPredicate_isCDistributive)
- No TSP because negative → Class 2
-/
def kork : VerbEntry where
  form := "kork-"
  form3sg := "korkuyor"
  formPast := "korktu"
  formPastPart := "korkmuş"
  formPresPart := "korkan"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  -- degreeComparison .negative → C-distributive (PROVED) → Class 2 (takes questions)
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/--
"um-" — hope (Class 3: anti-rogative canonically)

Cannot take questions in canonical complement position.
BUT: can appear with questions via "diye" construction (adjunction).

Canonical: *"Ali um-uyor kim gel-ecek"
With diye: ?"Ali kim gel-ecek diye um-uyor" (marginal, non-canonical)

The diye construction provides a workaround for Class 3 predicates.

The semantic builder is `degreeComparison .positive`:
- Positive valence
- C-distributive (PROVED by degreeComparisonPredicate_isCDistributive)
- Has TSP because positive → Class 3 (anti-rogative)
-/
def um : VerbEntry where
  form := "um-"
  form3sg := "umuyor"
  formPast := "umdu"
  formPastPart := "ummuş"
  formPresPart := "uman"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  -- degreeComparison .positive → C-distributive (PROVED) → Class 3 (anti-rogative)
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/--
"merak et-" — wonder/be curious (takes questions)

A rogative predicate (like English "wonder").
Not a preferential attitude verb - it's a question-embedding verb.
-/
def merakEt : VerbEntry where
  form := "merak et-"
  form3sg := "merak ediyor"
  formPast := "merak etti"
  formPastPart := "merak etmiş"
  formPresPart := "merak eden"
  complementType := .question
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  takesQuestionBase := true  -- Non-preferential question-embedding verb

/--
"endişelen-" — worry (Class 1: non-C-distributive)

Like English "worry": non-C-distributive, takes questions.

The semantic builder is `uncertaintyBased`:
- Negative valence (worry/concern)
- NON-C-distributive (PROVED by worry_not_cDistributive)
- Class 1 regardless of valence
-/
def endiselen : VerbEntry where
  form := "endişelen-"
  form3sg := "endişeleniyor"
  formPast := "endişelendi"
  formPastPart := "endişelenmiş"
  formPresPart := "endişelenen"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential properties: linked to Montague via builder
  -- uncertaintyBased → NOT C-distributive (PROVED) → Class 1 (takes questions)
  attitudeBuilder := some (.preferential .uncertaintyBased)

-- ============================================================================
-- All Turkish Verbs
-- ============================================================================

def allVerbs : List VerbEntry := [
  kork, um, merakEt, endiselen
]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Turkish.Predicates
