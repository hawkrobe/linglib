import Linglib.Data.Examples.Schema

/-!
# `TesslerFranke2019` — typed example data

Auto-generated from `Linglib/Data/Examples/TesslerFranke2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TesslerFranke2019.Examples`.
-/

namespace TesslerFranke2019.Examples

open Data.Examples

def happy : LinguisticExample :=
  { id := "tesslerfranke2019_happy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED quadruplet, bare positive"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is happy."
    discourseSegments := []
    glossedTokens := []
    translation := "She is happy."
    context := "Bare positive of the happy/unhappy quadruplet. Baseline against which the three negated forms are compared."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "positive"), ("inner_neg", "none"), ("cost", "0"), ("equivalent_to_positive", "true")]
    comment := "Migrated from Phenomena/Negation/FlexibleNegation.lean. Cost parameters follow the paper's model: C(un-) = 2, C(not) = 3, additive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unhappy : LinguisticExample :=
  { id := "tesslerfranke2019_unhappy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED Experiment 1, morphological negation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is unhappy."
    discourseSegments := []
    glossedTokens := []
    translation := "She is unhappy."
    context := "Morphological negation prefers the contrary (polar-opposite) interpretation: 'unhappy' means positively unhappy (below a low threshold), not merely 'not happy'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "negative"), ("inner_neg", "morphological"), ("interpretation", "contrary"), ("cost", "2"), ("equivalent_to_positive", "false")]
    comment := "Migrated from Phenomena/Negation/FlexibleNegation.lean unhappy_contrary."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def not_happy : LinguisticExample :=
  { id := "tesslerfranke2019_not_happy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED Experiment 1, syntactic negation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is not happy."
    discourseSegments := []
    glossedTokens := []
    translation := "She is not happy."
    context := "Syntactic negation is flexible between contradictory and contrary readings; the costlier two-word form licenses the marked contradictory reading more readily than 'unhappy' (Horn's division of pragmatic labor)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "notPositive"), ("inner_neg", "syntactic"), ("interpretation", "contradictory"), ("cost", "3"), ("equivalent_to_positive", "false")]
    comment := "Migrated from Phenomena/Negation/FlexibleNegation.lean not_happy_ambiguous; 'interpretation' records the preferred (contradictory) reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def not_unhappy : LinguisticExample :=
  { id := "tesslerfranke2019_not_unhappy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED §1, double negation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is not unhappy."
    discourseSegments := []
    glossedTokens := []
    translation := "She is not unhappy."
    context := "The paper's central observation: 'not unhappy' does NOT reduce to 'happy'. The inner morphological negation is contrary, so 'not unhappy' covers the gap region between the negative and positive thresholds, where 'happy' is false."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "notNegative"), ("inner_neg", "morphological"), ("interpretation", "contrary"), ("cost", "5"), ("equivalent_to_positive", "false")]
    comment := "Migrated from Phenomena/Negation/FlexibleNegation.lean not_unhappy_not_happy and happy_double_neg; 'interpretation' records the contrary reading inherited from the inner 'un-'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [happy, unhappy, not_happy, not_unhappy]

end TesslerFranke2019.Examples
