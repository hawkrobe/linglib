import Linglib.Data.Examples.Schema

/-!
# `Beaver2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Beaver2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beaver2001.Examples`.
-/

namespace Beaver2001.Examples

open Data.Examples

def e52 : LinguisticExample :=
  { id := "beaver2001_e52"
    source := ⟨"beaver-2001", "E52"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I go to London, my sister will pick me up at the airport."
    discourseSegments := []
    glossedTokens := []
    translation := "If I go to London, my sister will pick me up at the airport."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "definite (my sister)"), ("embedding", "consequent of conditional")]
    comment := "The paradigm conditional presupposition: satisfaction models predict only 'if I go to London I have a sister'; hearers tend to infer the stronger 'I have a sister', which Ch. 9 derives by global accommodation over information orderings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e154 : LinguisticExample :=
  { id := "beaver2001_e154"
    source := ⟨"beaver-2001", "E154"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    discourseSegments := []
    glossedTokens := []
    translation := "If Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "consequent of conditional")]
    comment := "Presupposes only the conditional: if he lands there, his weight is greater. Natural when Spiff hangs weightless in space, so the unconditional presupposition is wrong; structural accommodation accounts cannot produce the conditional reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e155 : LinguisticExample :=
  { id := "beaver2001_e155"
    source := ⟨"beaver-2001", "E155"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is unlikely that if Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    discourseSegments := []
    glossedTokens := []
    translation := "It is unlikely that if Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "conditional under unlikely")]
    comment := "Preferred reading keeps the conditional implication; accommodation into the consequent is unavailable here."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e156 : LinguisticExample :=
  { id := "beaver2001_e156"
    source := ⟨"beaver-2001", "E156"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X and is bothered by the fact that his weight is greater than it would be on Earth, he won't stay long."
    discourseSegments := []
    glossedTokens := []
    translation := "If Spaceman Spiff lands on Planet X and is bothered by the fact that his weight is greater than it would be on Earth, he won't stay long."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "second conjunct of conditional antecedent")]
    comment := "Same conditional presupposition, predicted by the treatment of conjunction; accommodation into the consequent is not even available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e198 : LinguisticExample :=
  { id := "beaver2001_e198"
    source := ⟨"beaver-2001", "E198"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bertha is hiding."
    discourseSegments := []
    glossedTokens := []
    translation := "Bertha is hiding."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "presupposed content for E168'-E173")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e168prime : LinguisticExample :=
  { id := "beaver2001_e168prime"
    source := ⟨"beaver-2001", "E168'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna realises that Bertha is hiding."
    discourseSegments := []
    glossedTokens := []
    translation := "Anna realises that Bertha is hiding."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "none")]
    comment := "Presupposes (and entails) that Bertha is hiding."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e169prime : LinguisticExample :=
  { id := "beaver2001_e169prime"
    source := ⟨"beaver-2001", "E169'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna does not realise that Bertha is hiding."
    discourseSegments := []
    glossedTokens := []
    translation := "Anna does not realise that Bertha is hiding."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "negation")]
    comment := "Projection through negation (Fact 8.1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e172prime : LinguisticExample :=
  { id := "beaver2001_e172prime"
    source := ⟨"beaver-2001", "E172'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Anna realises that Bertha is hiding, then she will find her."
    discourseSegments := []
    glossedTokens := []
    translation := "If Anna realises that Bertha is hiding, then she will find her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "antecedent of conditional")]
    comment := "Projection from the antecedent (Fact 8.1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e173 : LinguisticExample :=
  { id := "beaver2001_e173"
    source := ⟨"beaver-2001", "E173"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna might realise that Bertha is hiding."
    discourseSegments := []
    glossedTokens := []
    translation := "Anna might realise that Bertha is hiding."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "might")]
    comment := "Projection through the epistemic modals (Fact 8.8)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e175 : LinguisticExample :=
  { id := "beaver2001_e175"
    source := ⟨"beaver-2001", "E175"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bertha is not in the kitchen, then Anna realises that Bertha is in the attic."
    discourseSegments := []
    glossedTokens := []
    translation := "If Bertha is not in the kitchen, then Anna realises that Bertha is in the attic."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "consequent of conditional")]
    comment := "Presupposes the conditionalised E175c: if Bertha is not in the kitchen, she is in the attic (Fact 8.3) — the paradigmatically CCP behaviour."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e206 : LinguisticExample :=
  { id := "beaver2001_e206"
    source := ⟨"beaver-2001", "E206"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible there is a happy farmer, but, then again, it is possible that there are no happy farmers."
    discourseSegments := []
    glossedTokens := []
    translation := "It is possible there is a happy farmer, but, then again, it is possible that there are no happy farmers."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "might phi and might not phi")]
    comment := "Consistent as a might-sequence; following it with E207a is consistent, while E207a followed by E206a is not — might is a consistency test on the current state."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def e207 : LinguisticExample :=
  { id := "beaver2001_e207"
    source := ⟨"beaver-2001", "E207"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No farmer is happy."
    discourseSegments := []
    glossedTokens := []
    translation := "No farmer is happy."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "plain assertion")]
    comment := "Order contrast with E206a: assertion then might-sentence is inconsistent, might-sentence then assertion is fine."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [e52, e154, e155, e156, e198, e168prime, e169prime, e172prime, e173, e175, e206, e207]

end Beaver2001.Examples
