import Linglib.Data.Examples.Schema

/-!
# `Schlenker2004a` — typed example data

Auto-generated from `Linglib/Data/Examples/Schlenker2004a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schlenker2004a.Examples`.
-/

namespace Schlenker2004a.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "schlenker2004a_ex1"
    source := ⟨"schlenker-2004a", "(1)"⟩
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
    comment := "Schlenker 2004 ex (1), p. 280: Lawrence, Women in Love (p. 185 of the 1971 Heinemann edition), cited via Banfield 1982 p. 98 and Doron 1991. The past tense is evaluated against the Context of Utterance, `tomorrow` against the Context of Thought; evaluated against one context the sentence is contradictory."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2 : LinguisticExample :=
  { id := "schlenker2004a_ex2"
    source := ⟨"schlenker-2004a", "(2)"⟩
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
    comment := "Schlenker 2004 ex (2), p. 281, repeated as (28a). Mirror image of (1): the present tense is evaluated against a Context of Utterance set fifty-eight years in the past, `fifty eight years ago` against the Context of Thought, which is the actual context."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1, ex2]

end Schlenker2004a.Examples
