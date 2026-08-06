import Linglib.Data.Examples.Schema

/-!
# `Zheng2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Zheng2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zheng2025.Examples`.
-/

namespace Zheng2025.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "zheng2025_ex1"
    source := ⟨"zheng-2025", "(1)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao ta fafeng-le ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("ta", "he"), ("fafeng-le", "go.crazy-PERF"), ("ma", "Y/N-Q")]
    translation := "Is he crazy?"
    context := "A and B are talking about a colleague, Lee, who is going to work on Sunday. B does not think people usually go to work on Sunday."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "true"), ("epistemic_bias", "true"), ("unexpected_evidence", "true")]
    comment := "Rhetorical use: the evidence (Lee working Sunday) contradicts B's norm that people don't work Sundays."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2 : LinguisticExample :=
  { id := "zheng2025_ex2"
    source := ⟨"zheng-2025", "(2)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    translation := "It is not the case that it is raining outside, right?"
    context := "A sits in a windowless room working. A believes it is not raining. At 10, B enters the room with a dripping raincoat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "true"), ("epistemic_bias", "true"), ("unexpected_evidence", "true")]
    comment := "Biased-question use: the evidence contradicts A's prior belief."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3 : LinguisticExample :=
  { id := "zheng2025_ex3"
    source := ⟨"zheng-2025", "(3)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    translation := "Is it raining outside?"
    context := "A sits in a windowless room working. A has no expectation about the weather. At 10, B enters the room with a dripping raincoat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "true"), ("epistemic_bias", "false"), ("unexpected_evidence", "true")]
    comment := "Pure-inquiry use, the paper's novel datum: felicitous with no prior belief about the prejacent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4b : LinguisticExample :=
  { id := "zheng2025_ex4b"
    source := ⟨"xu-2018", "p. 449"⟩
    reportedIn := some ⟨"zheng-2025", "(4b)"⟩
    language := "mand1415"
    primaryText := "Nandao wuli you ren?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("wuli", "room.in"), ("you", "exist"), ("ren", "person")]
    translation := "It is not the case there are people in the room, right?"
    context := "The speaker believes there is no one in the room, and there is no contextual evidence (such as the light being on) that someone is in."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "false"), ("epistemic_bias", "true"), ("unexpected_evidence", "false")]
    comment := "Xu's context supplies only the negative belief; Zheng observes that without contextual evidence the question is still infelicitous, so epistemic bias is not sufficient."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_ctx1 : LinguisticExample :=
  { id := "zheng2025_ex5_ctx1"
    source := ⟨"zheng-2025", "(5) ctx 1"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    translation := "Is it raining outside?"
    context := "A sits in a windowless room with no prior beliefs about the weather. At 10, B enters the room with a dripping raincoat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "true"), ("epistemic_bias", "false"), ("unexpected_evidence", "true")]
    comment := "Evidence without belief: positive evidential bias is sufficient."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_ctx2 : LinguisticExample :=
  { id := "zheng2025_ex5_ctx2"
    source := ⟨"zheng-2025", "(5) ctx 2"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    translation := "Is it raining outside?"
    context := "A sits in a windowless room with no prior beliefs about the weather. At 10, B enters the room normally, without a raincoat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "false"), ("epistemic_bias", "false"), ("unexpected_evidence", "false")]
    comment := "No evidence and no belief: infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_ctx3 : LinguisticExample :=
  { id := "zheng2025_ex5_ctx3"
    source := ⟨"zheng-2025", "(5) ctx 3"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao waimian xiayu-le ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("waimian", "outside"), ("xiayu-le", "fall.rain-PERF"), ("ma", "Y/N-Q")]
    translation := "Is it raining outside?"
    context := "A thinks it will not rain today. At 10, B enters the room normally, without a raincoat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "false"), ("epistemic_bias", "true"), ("unexpected_evidence", "false")]
    comment := "Belief without evidence: negative epistemic bias alone does not license nandao."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_ctx1 : LinguisticExample :=
  { id := "zheng2025_ex6_ctx1"
    source := ⟨"zheng-2025", "(6) ctx 1"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao ta hen.mang ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("ta", "he"), ("hen.mang", "very.busy"), ("ma", "Y/N-Q")]
    translation := "Is he busy?"
    context := "A says Lee is planning to work on weekends too. B does not think that people, including Lee, usually go to work on Sunday."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "true"), ("epistemic_bias", "true"), ("unexpected_evidence", "true")]
    comment := "Unexpected evidence: Lee working Sunday deviates from B's expectation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_ctx2 : LinguisticExample :=
  { id := "zheng2025_ex6_ctx2"
    source := ⟨"zheng-2025", "(6) ctx 2"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nandao ta hen.mang ma?"
    discourseSegments := []
    glossedTokens := [("nandao", "nandao"), ("ta", "he"), ("hen.mang", "very.busy"), ("ma", "Y/N-Q")]
    translation := "Is he busy?"
    context := "A says Lee is planning to work on weekends too. B knows Lee usually goes to work on Sunday."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential_bias", "true"), ("epistemic_bias", "false"), ("unexpected_evidence", "false")]
    comment := "Expected evidence: the same evidence is unremarkable given B's knowledge, so nandao is infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex4b, ex5_ctx1, ex5_ctx2, ex5_ctx3, ex6_ctx1, ex6_ctx2]

end Zheng2025.Examples
