module

public import Linglib.Data.Examples.Schema

/-!
# `Rudin2025b` — typed example data

Auto-generated from `Linglib/Data/Examples/Rudin2025b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rudin2025b.Examples`.
-/

@[expose] public section

namespace Rudin2025b.Examples

open Data.Examples

def ex6b_wonder : LinguisticExample :=
  { id := "rudin2025b_ex6b_wonder"
    source := ⟨"rudin-2025b", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka wondered, “Polina likes her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka wondered, “Polina likes her job?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wonder"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "The quoted clause is pronounced as its own intonational phrase with the rising tune of a rising declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7b_claim : LinguisticExample :=
  { id := "rudin2025b_ex7b_claim"
    source := ⟨"rudin-2025b", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka claimed, “Polina likes her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka claimed, “Polina likes her job?”"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "claim"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "The quoted clause is pronounced as a rising declarative. Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8_whisper : LinguisticExample :=
  { id := "rudin2025b_ex8_whisper"
    source := ⟨"rudin-2025b", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka whispered, “Polina likes her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka whispered, “Polina likes her job?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "whisper"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "whispered")]
    comment := "The quoted clause is pronounced as a rising declarative, whispered. One of the manner-of-speech verbs listed in (8)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10_shout : LinguisticExample :=
  { id := "rudin2025b_ex10_shout"
    source := ⟨"rudin-2025b", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka shouted, “Does Polina like her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka shouted, “Does Polina like her job?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "shout"), ("material", "sentence"), ("mood", "interrogative"), ("tune", "rising"), ("volume", "loud")]
    comment := "The quoted clause is a polar interrogative, shouted. One of the manner-of-speech verbs listed in (10)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12a : LinguisticExample :=
  { id := "rudin2025b_ex12a"
    source := ⟨"rudin-2025b", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Then Polina asked me, “Are you married?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Then Polina asked me, “Are you married?”"
    context := "Ayka is talking to Bertrand about a conversation she had with Polina."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ask"), ("material", "sentence"), ("mood", "interrogative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "The indexical is interpreted relative to Polina's utterance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18a : LinguisticExample :=
  { id := "rudin2025b_ex18a"
    source := ⟨"rudin-2025b", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, “Polina likes her job.”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka said, “Polina likes her job.”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "neutral")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex37a : LinguisticExample :=
  { id := "rudin2025b_ex37a"
    source := ⟨"rudin-2025b", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I asked Ayka how she felt about the faculty meeting, and she said, *emits guttural howl of frustration*"
    discourseSegments := []
    glossedTokens := []
    translation := "I asked Ayka how she felt about the faculty meeting, and she said, *emits guttural howl of frustration*"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "inarticulate"), ("volume", "neutral")]
    comment := "Nonphonemic noise quoted under say."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42a : LinguisticExample :=
  { id := "rudin2025b_ex42a"
    source := ⟨"rudin-2025b", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, *performs enthusiastic karate gestures*"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka said, *performs enthusiastic karate gestures*"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "none"), ("volume", "neutral")]
    comment := "Marked # in the paper: a performance with no linguistic material."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48 : LinguisticExample :=
  { id := "rudin2025b_ex48"
    source := ⟨"rudin-2025b", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, “Does Polina like her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka said, “Does Polina like her job?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "sentence"), ("mood", "interrogative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "Interpreted as reporting an asking, not the assertion of an answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49 : LinguisticExample :=
  { id := "rudin2025b_ex49"
    source := ⟨"rudin-2025b", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I asked Ayka for the wifi password, and she said, “x231&$8o.”"
    discourseSegments := []
    glossedTokens := []
    translation := "I asked Ayka for the wifi password, and she said, “x231&$8o.”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "inarticulate"), ("volume", "neutral")]
    comment := "A string with no propositional content quoted under say."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex69a : LinguisticExample :=
  { id := "rudin2025b_ex69a"
    source := ⟨"rudin-2025b", "(69a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka yelled, “POLINA LIKES HER JOB!”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka yelled, “POLINA LIKES HER JOB!”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yell"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "loud")]
    comment := "The quoted clause is shouted."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex69b : LinguisticExample :=
  { id := "rudin2025b_ex69b"
    source := ⟨"rudin-2025b", "(69b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka yelled, [in a hoarse whisper] “Polina likes her job.”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka yelled, [in a hoarse whisper] “Polina likes her job.”"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yell"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "whispered")]
    comment := "The quoted clause is whispered. Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex70a : LinguisticExample :=
  { id := "rudin2025b_ex70a"
    source := ⟨"rudin-2025b", "(70a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka whispered, “POLINA LIKES HER JOB.”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka whispered, “POLINA LIKES HER JOB.”"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "whisper"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "loud")]
    comment := "The quoted clause is shouted. Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex70b : LinguisticExample :=
  { id := "rudin2025b_ex70b"
    source := ⟨"rudin-2025b", "(70b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka whispered, [in a hoarse whisper] “Polina likes her job.”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka whispered, [in a hoarse whisper] “Polina likes her job.”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "whisper"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "whispered")]
    comment := "The quoted clause is whispered."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex74a : LinguisticExample :=
  { id := "rudin2025b_ex74a"
    source := ⟨"rudin-2025b", "(74a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, “Polina likes her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka said, “Polina likes her job?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "The quoted clause is pronounced as a rising declarative. Interpreted as reporting an asking."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex75 : LinguisticExample :=
  { id := "rudin2025b_ex75"
    source := ⟨"rudin-2025b", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka yelled, “POLINA LIKES HER JOB?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka yelled, “POLINA LIKES HER JOB?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yell"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "loud")]
    comment := "The quoted clause is a shouted rising declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex78a : LinguisticExample :=
  { id := "rudin2025b_ex78a"
    source := ⟨"rudin-2025b", "(78a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka asserted, “Polina likes her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka asserted, “Polina likes her job?”"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "assert"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "The quoted clause is pronounced as a rising declarative. Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex82a : LinguisticExample :=
  { id := "rudin2025b_ex82a"
    source := ⟨"rudin-2025b", "(82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka asked, “Polina likes her job?”"
    discourseSegments := []
    glossedTokens := []
    translation := "Ayka asked, “Polina likes her job?”"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ask"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")]
    comment := "The quoted clause is pronounced as a rising declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex6b_wonder, ex7b_claim, ex8_whisper, ex10_shout, ex12a, ex18a, ex37a, ex42a, ex48, ex49, ex69a, ex69b, ex70a, ex70b, ex74a, ex75, ex78a, ex82a]

end Rudin2025b.Examples
