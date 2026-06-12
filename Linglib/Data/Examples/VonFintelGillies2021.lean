import Linglib.Data.Examples.Schema

/-!
# `VonFintelGillies2021` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintelGillies2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintelGillies2021.Examples`.
-/

namespace VonFintelGillies2021.Examples

open Data.Examples

def cant_possible : LinguisticExample :=
  { id := "vonfintelgillies2021_cant_possible"
    source := ⟨"von-fintel-gillies-2021", "UNVERIFIED (5), (22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it's possible the keys are in the drawer but they can't be."
    discourseSegments := []
    glossedTokens := []
    translation := "Suppose it's possible the keys are in the drawer but they can't be."
    context := "Flat-footed conjunction of 'possible phi' with 'can't phi', embedded under suppose."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "cant_possible_contradiction"), ("modal", "cant")]
    comment := "Observation 5: can't phi excludes 'it's possible that phi'; the conditional-antecedent variant ('If it's possible the keys are in the drawer but they can't be, then ...') is equally incoherent. If can't were weak necessity over not-phi, the conjunction should be coherent — the Mantra's dilemma. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean cantPossibleContradiction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def phil_dinner : LinguisticExample :=
  { id := "vonfintelgillies2021_phil_dinner"
    source := ⟨"von-fintel-gillies-2021", "UNVERIFIED (24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinner must be ready."
    discourseSegments := []
    glossedTokens := []
    translation := "Dinner must be ready."
    context := "Phil has cooked the dinner, checking all the food himself, and knows it is ready."
    judgment := .unacceptable
    alternatives := [("Dinner is ready.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "direct"), ("must_entails_prejacent", "true")]
    comment := "Anti-knowledge: Phil's complete checking counts as direct-enough information and blocks must even though no single perceptual event settles 'dinner is ready' — the indirectness signal is about knowledge, not perception. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean philCooksDinner."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def meryl_dinner : LinguisticExample :=
  { id := "vonfintelgillies2021_meryl_dinner"
    source := ⟨"von-fintel-gillies-2021", "UNVERIFIED (25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinner must be ready."
    discourseSegments := []
    glossedTokens := []
    translation := "Dinner must be ready."
    context := "Meryl followed the recipe's instructions but has not checked everything herself and wonders whether anything more was planned."
    judgment := .acceptable
    alternatives := [("Dinner is ready.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")]
    comment := "Meryl's information is indirect: she followed the steps but lacks full direct knowledge of what counts as ready, so must is licensed. Minimal pair with the Phil row. Migrated from Phenomena/Modality/EpistemicEvidentiality.lean merylCooksDinner."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [cant_possible, phil_dinner, meryl_dinner]

end VonFintelGillies2021.Examples
