import Linglib.Data.Examples.Schema

/-!
# `LuPanDegen2025` — typed example data

Auto-generated from `Linglib/Data/Examples/LuPanDegen2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LuPanDegen2025.Examples`.
-/

namespace LuPanDegen2025.Examples

open Data.Examples

def exp1_verbfocus : LinguisticExample :=
  { id := "lupandegen2025_exp1_verbfocus"
    source := ⟨"lu-pan-degen-2025", "UNVERIFIED Experiment 1, verb-focus condition, ex. (9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't WHISPER that Mary met with the lawyer. Then who did John whisper that Mary met with?"
    discourseSegments := ["John didn't WHISPER that Mary met with the lawyer.", "Then who did John whisper that Mary met with?"]
    glossedTokens := []
    translation := "John didn't WHISPER that Mary met with the lawyer. Then who did John whisper that Mary met with?"
    context := "Capitalization marks prosodic focus on the matrix verb, backgrounding the complement."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("focus_condition", "verbFocus"), ("verb_type", "mos"), ("island_condition", "true"), ("mean_acceptability_x100", "57")]
    comment := "Migrated from Phenomena/Islands/MannerOfSpeaking.lean Experiment 1 docstring. MoS island condition: focus on the MoS verb backgrounds the complement and degrades extraction (Figure 4b mean 0.57). Judgment coding mirrors the rating direction within the contrast pair."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_embeddedfocus : LinguisticExample :=
  { id := "lupandegen2025_exp1_embeddedfocus"
    source := ⟨"lu-pan-degen-2025", "UNVERIFIED Experiment 1, embedded-focus condition, ex. (9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't whisper that Mary met with the LAWYER. Then who did John whisper that Mary met with?"
    discourseSegments := ["John didn't whisper that Mary met with the LAWYER.", "Then who did John whisper that Mary met with?"]
    glossedTokens := []
    translation := "John didn't whisper that Mary met with the LAWYER. Then who did John whisper that Mary met with?"
    context := "Capitalization marks prosodic focus on the embedded object, foregrounding the complement."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("focus_condition", "embeddedFocus"), ("verb_type", "mos"), ("island_condition", "false"), ("mean_acceptability_x100", "68")]
    comment := "Migrated from Phenomena/Islands/MannerOfSpeaking.lean Experiment 1 docstring. Ameliorated condition: prosodic focus on the embedded object foregrounds the complement and improves extraction (Figure 4b mean 0.68)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3a_say : LinguisticExample :=
  { id := "lupandegen2025_exp3a_say"
    source := ⟨"lu-pan-degen-2025", "UNVERIFIED Experiment 3a, say condition, ex. (18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say that Mary met with the lawyer. Then who did John say that Mary met with?"
    discourseSegments := ["John didn't say that Mary met with the lawyer.", "Then who did John say that Mary met with?"]
    glossedTokens := []
    translation := "John didn't say that Mary met with the lawyer. Then who did John say that Mary met with?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3a"), ("focus_condition", "none"), ("verb_type", "say"), ("island_condition", "false"), ("mean_acceptability_x100", "77")]
    comment := "Migrated from Phenomena/Islands/MannerOfSpeaking.lean Experiment 3a docstring. Bridge-verb baseline: bare say permits extraction at near-filler level (Figure 14 mean 0.77)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3a_sayadverb : LinguisticExample :=
  { id := "lupandegen2025_exp3a_sayadverb"
    source := ⟨"lu-pan-degen-2025", "UNVERIFIED Experiment 3a, say+adverb condition, ex. (18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say softly that Mary met with the lawyer. Then who did John say softly that Mary met with?"
    discourseSegments := ["John didn't say softly that Mary met with the lawyer.", "Then who did John say softly that Mary met with?"]
    glossedTokens := []
    translation := "John didn't say softly that Mary met with the lawyer. Then who did John say softly that Mary met with?"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3a"), ("focus_condition", "none"), ("verb_type", "sayAdverb"), ("island_condition", "true"), ("mean_acceptability_x100", "53")]
    comment := "Migrated from Phenomena/Islands/MannerOfSpeaking.lean Experiment 3a docstring. Key novel condition: adding a manner adverb to the bridge verb say replicates the MoS island effect without structural change (Figure 14 mean 0.53)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3b_adverbfocus : LinguisticExample :=
  { id := "lupandegen2025_exp3b_adverbfocus"
    source := ⟨"lu-pan-degen-2025", "UNVERIFIED Experiment 3b, adverb-focus condition, ex. (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say SOFTLY that Mary met with the lawyer. Then who did John say softly that Mary met with?"
    discourseSegments := ["John didn't say SOFTLY that Mary met with the lawyer.", "Then who did John say softly that Mary met with?"]
    glossedTokens := []
    translation := "John didn't say SOFTLY that Mary met with the lawyer. Then who did John say softly that Mary met with?"
    context := "Capitalization marks prosodic focus on the manner adverb, backgrounding the complement."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3b"), ("focus_condition", "adverbFocus"), ("verb_type", "sayAdverb"), ("island_condition", "true"), ("mean_acceptability_x100", "50")]
    comment := "Migrated from Phenomena/Islands/MannerOfSpeaking.lean Experiment 3b docstring. Say+adverb island condition: focus on the manner adverb backgrounds the complement and degrades extraction (Figure 17b mean 0.50)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3b_embeddedfocus : LinguisticExample :=
  { id := "lupandegen2025_exp3b_embeddedfocus"
    source := ⟨"lu-pan-degen-2025", "UNVERIFIED Experiment 3b, embedded-focus condition, ex. (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say softly that Mary met with the LAWYER. Then who did John say softly that Mary met with?"
    discourseSegments := ["John didn't say softly that Mary met with the LAWYER.", "Then who did John say softly that Mary met with?"]
    glossedTokens := []
    translation := "John didn't say softly that Mary met with the LAWYER. Then who did John say softly that Mary met with?"
    context := "Capitalization marks prosodic focus on the embedded object, foregrounding the complement."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3b"), ("focus_condition", "embeddedFocus"), ("verb_type", "sayAdverb"), ("island_condition", "false"), ("mean_acceptability_x100", "68")]
    comment := "Migrated from Phenomena/Islands/MannerOfSpeaking.lean Experiment 3b docstring. Ameliorated condition: prosodic focus on the embedded object foregrounds the complement and improves extraction from the say+adverb frame (Figure 17b mean 0.68)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [exp1_verbfocus, exp1_embeddedfocus, exp3a_say, exp3a_sayadverb, exp3b_adverbfocus, exp3b_embeddedfocus]

end LuPanDegen2025.Examples
