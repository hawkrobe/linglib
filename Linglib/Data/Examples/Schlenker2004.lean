import Linglib.Data.Examples.Schema

/-!
# `Schlenker2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Schlenker2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schlenker2004.Examples`.
-/

namespace Schlenker2004.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "schlenker2004_ex1"
    source := ⟨"schlenker-2004", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tomorrow was Monday, Monday, the beginning of another school week!"
    discourseSegments := []
    glossedTokens := []
    translation := "Tomorrow was Monday, Monday, the beginning of another school week!"
    context := "Free Indirect Discourse. Past tense `was` with future adverbial `tomorrow` — a contradiction if both anchored to the same context, but felicitous when `tomorrow` is evaluated against the character's Context of Thought (CT) and `was` against the narrator's Context of Utterance (CU). The thought is the character's; the tense morphology is the narrator's."
    judgment := .acceptable
    alternatives := []
    readings := [("FID (CT/CU split)", .acceptable), ("literal-contradiction", .ungrammatical)]
    paperFeatures := []
    comment := "Schlenker 2004 ex (1), Mind & Language 19(3) p. 280. Literary source via Banfield 1982 p. 98 (a D.H. Lawrence novel; specific novel attribution unverified). Cornerstone of Schlenker's CT vs CU framework: in FID, indexical/tense items split between two contexts."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2 : LinguisticExample :=
  { id := "schlenker2004_ex2"
    source := ⟨"schlenker-2004", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fifty eight years ago to this day, on January 22, 1944, just as the Americans are about to invade Europe, the Germans attack Vercors."
    discourseSegments := []
    glossedTokens := []
    translation := "Fifty eight years ago to this day, on January 22, 1944, just as the Americans are about to invade Europe, the Germans attack Vercors."
    context := "Historical Present. Adverbial `fifty eight years ago` is evaluated against the speaker's CU; the present tense `attack` / `are about to invade` is evaluated against a CT shifted 58 years back. Without the CT/CU split, the sentence would be contradictory; with the split, it produces the impression that the speaker directly witnesses the past event."
    judgment := .acceptable
    alternatives := []
    readings := [("HP (CT/CU split, CT shifted back 58y)", .acceptable), ("literal-contradiction", .ungrammatical)]
    paperFeatures := []
    comment := "Schlenker 2004 ex (2), p. 280. The Historical Present companion to (1)'s FID. Both motivate the same CT/CU split: when temporal indexicals and tense morphology disagree on which context anchors them, FID/HP are the diagnostics."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1, ex2]

end Schlenker2004.Examples
