import Linglib.Data.Examples.Schema

/-!
# `Thomas2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Thomas2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Thomas2026.Examples`.
-/

namespace Thomas2026.Examples

open Data.Examples

def ex_2 : LinguisticExample :=
  { id := "thomas2026_2"
    source := ⟨"thomas-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery invited Bailey. She invited Cameron, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who did Avery invite?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "The canonical additive use: two independent answers to a salient question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "thomas2026_3"
    source := ⟨"thomas-2026", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tonight [Sam]F is having dinner in New York, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "antecedent_violation")]
    comment := "Out of the blue there is no salient antecedent answering a relevant question; after Kripke."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5a : LinguisticExample :=
  { id := "thomas2026_5a"
    source := ⟨"thomas-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I like [pizza]F, and I like [spaghetti]F, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "The antecedent is a focus alternative of the host sentence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5b : LinguisticExample :=
  { id := "thomas2026_5b"
    source := ⟨"thomas-2026", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't like [pizza]F, and I don't like [spaghetti]F, either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("use_type", "standard")]
    comment := "The negative additive; its felicity conditions are left to future work in footnote 9."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "thomas2026_11"
    source := ⟨"thomas-2026", "(11), (29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is happy. #He's ecstatic, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "RQ: What is Sam's emotional state?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_i")]
    comment := "The prejacent entails the resolution that the conjunction evidences; after Beaver and Clark."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "thomas2026_12"
    source := ⟨"thomas-2026", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I love you. B: I love you, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who loves whom?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "A response to a multiple wh-question; after Zeevat and Jasinskaja."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "thomas2026_13"
    source := ⟨"thomas-2026", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ate pizza. #Mary ate spaghetti, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who ate what?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard")]
    comment := "Both sentences address the multiple wh-question, yet *too* is degraded where *and* is fine."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18c : LinguisticExample :=
  { id := "thomas2026_18c"
    source := ⟨"thomas-2026", "(18c), (65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a fancy one, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A and companions are looking for a hotel. Q: What would be a good hotel to stay at?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")]
    comment := "The argument-building use: the antecedent and prejacent together argue that this hotel is a good place to stay."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19c : LinguisticExample :=
  { id := "thomas2026_19c"
    source := ⟨"thomas-2026", "(19c), (66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a dingy one, (#too)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A and companions are looking for a nice hotel room to stay in."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "conjunction_violation")]
    comment := "No question relevant to the interlocutors' goal has a resolution that the conjunction evidences."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20b : LinguisticExample :=
  { id := "thomas2026_20b"
    source := ⟨"thomas-2026", "(20b), (67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a dingy one, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A's band is looking for a dingy hotel room in which to shoot a music video. Q: Where would be a good place to shoot our music video?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")]
    comment := "With a goal that makes a dingy room desirable, a relevant question is available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "thomas2026_24"
    source := ⟨"thomas-2026", "(24), (69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I eat a lot of pizza. I like spaghetti, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "RQ: What foods do you like?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "The antecedent evidences an answer without entailing it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "thomas2026_25"
    source := ⟨"thomas-2026", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are mammals. #I had pancakes for breakfast, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "conjunction_violation")]
    comment := "No question has a resolution evidenced more strongly by the conjunction than by the antecedent alone; *by the way* allows an unrelated prejacent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29bA : LinguisticExample :=
  { id := "thomas2026_29bA"
    source := ⟨"thomas-2026", "(29b A)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam's fingerprints were found on the cookie jar. #He stole the cookies, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "RQ: Who stole the cookies?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_i")]
    comment := "The prejacent entails the evidenced resolution although it does not entail the antecedent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29bA2 : LinguisticExample :=
  { id := "thomas2026_29bA2"
    source := ⟨"thomas-2026", "(29b A′)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam's fingerprints were found on the cookie jar. He has crumbs on his shirt, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "RQ: Who stole the cookies?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")]
    comment := "Two pieces of evidence for the resolution that Sam stole the cookies."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30A : LinguisticExample :=
  { id := "thomas2026_30A"
    source := ⟨"thomas-2026", "(30 A)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery plays an instrument. Bailey plays the cello, (#too)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "RQ: Who plays an instrument?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_ii")]
    comment := "A weaker prejacent, that Bailey plays an instrument, would evidence the resolution as strongly."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30A2 : LinguisticExample :=
  { id := "thomas2026_30A2"
    source := ⟨"thomas-2026", "(30 A′)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery plays the cello. Bailey plays an instrument, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "RQ: Who plays an instrument?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "No constraint on the antecedent mirrors the prejacent condition."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_68 : LinguisticExample :=
  { id := "thomas2026_68"
    source := ⟨"thomas-2026", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: She invited Bailey and Cameron. B: She invited Dana, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who are some people Avery invited?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "Mention-some question: the antecedent entails the resolution that Bailey and Cameron were invited, and the conjunction the stronger resolution including Dana."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_70 : LinguisticExample :=
  { id := "thomas2026_70"
    source := ⟨"thomas-2026", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: She invited Bailey, Cameron, and Dana. B: She invited Ellis, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who all did Avery invite?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "Mention-all question: the antecedent resolves it by quantity implicature, which the prejacent cancels in favour of a weaker exhaustive inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_71 : LinguisticExample :=
  { id := "thomas2026_71"
    source := ⟨"thomas-2026", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Well,) she invited Bailey.↑ ... She invited Cameron, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who are some people Avery invited?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "The antecedent does not answer the mention-two question, raising every alternative that entails it equally, but answers the relevant mention-one question of someone Avery invited."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_72 : LinguisticExample :=
  { id := "thomas2026_72"
    source := ⟨"thomas-2026", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: She invited Bailey and Cameron. B: #Dogs are mammals, too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Q: Who are some people Avery invited?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "conjunction_violation")]
    comment := "The prejacent contributes no evidence for any resolution of a relevant question beyond the antecedent's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_2, ex_3, ex_5a, ex_5b, ex_11, ex_12, ex_13, ex_18c, ex_19c, ex_20b, ex_24, ex_25, ex_29bA, ex_29bA2, ex_30A, ex_30A2, ex_68, ex_70, ex_71, ex_72]

end Thomas2026.Examples
