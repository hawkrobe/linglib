import Linglib.Data.Examples.Schema

/-!
# `AnandHardtMcCloskey2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AnandHardtMcCloskey2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AnandHardtMcCloskey2025.Examples`.
-/

namespace AnandHardtMcCloskey2025.Examples

open Data.Examples

def ex_13a : LinguisticExample :=
  { id := "anandhardtmccloskey2025_13a"
    source := ⟨"anand-hardt-mccloskey-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The board believes a one-size-fits-all approach to financial market regulation is inappropriate ... what form [government regulation is necessary IN]."
    discourseSegments := []
    glossedTokens := []
    translation := "The board believes a one-size-fits-all approach to financial market regulation is inappropriate ... what form."
    context := "Corpus-attested sluice with a stranded nonargument preposition in the ellipsis site that has no antecedent source. The bracketed capitalized material is the elided clause, not pronounced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "nonargument")]
    comment := "UNVERIFIED paperLabel: ex. (13a) carried from Studies/AnandHardtMcCloskey2025.lean strandedPrepEx13a, not checked against the published paper. SCSS corpus ID [138195] per the Lean source field. The stranded 'in' marks a nonargument PP merged above vP, outside the argument domain, so the Structural Identity Condition does not require it to match. Lean fields: antecedent = 'government regulation is necessary'; innerAntecedent = 'a one-size-fits-all approach'; whPhrase = 'what form'; elided = 'government regulation is necessary in'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13b : LinguisticExample :=
  { id := "anandhardtmccloskey2025_13b"
    source := ⟨"anand-hardt-mccloskey-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When the officer asked me about her, I remembered meeting her but I couldn't say what date [I MET her ON]."
    discourseSegments := []
    glossedTokens := []
    translation := "When the officer asked me about her, I remembered meeting her but I couldn't say what date."
    context := "Corpus-attested sluice with a stranded nonargument PP 'on' in the ellipsis site that has no antecedent source. The bracketed capitalized material is the elided clause, not pronounced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "nonargument")]
    comment := "UNVERIFIED paperLabel: ex. (13b) carried from Studies/AnandHardtMcCloskey2025.lean strandedPrepEx13b, not checked against the published paper. SCSS corpus ID [F38] per the Lean source field. Lean fields: antecedent = 'I remembered meeting her'; innerAntecedent = 'her'; whPhrase = 'what date'; elided = 'I met her on'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12c : LinguisticExample :=
  { id := "anandhardtmccloskey2025_12c"
    source := ⟨"anand-hardt-mccloskey-2025", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They're furious but it's unclear who."
    discourseSegments := []
    glossedTokens := []
    translation := "They're furious but it's unclear who."
    context := "The argument/nonargument PP contrast: (12a) 'who(m)' with sprouted PP is fine, (12b) pied-piped 'who at' is fine, but the bare sluice fails because the argument-marking preposition 'at' (selected by 'furious') is within the argument domain, has no antecedent source, and fails the Structural Identity Condition."
    judgment := .ungrammatical
    alternatives := [("They're furious but it's unclear who at.", .acceptable)]
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "argument")]
    comment := "UNVERIFIED paperLabel: ex. (12c) carried from Studies/AnandHardtMcCloskey2025.lean argumentPPEx12c, not checked against the published paper. The pied-piped (12b) variant in alternatives and the contrast description are carried from the Lean docstring for ex. (12). Lean fields: antecedent = 'they're furious'; whPhrase = 'who'; elided = 'they are furious at'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15a : LinguisticExample :=
  { id := "anandhardtmccloskey2025_15a"
    source := ⟨"anand-hardt-mccloskey-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is very loyal, but I don't know who."
    discourseSegments := []
    glossedTokens := []
    translation := "He is very loyal, but I don't know who."
    context := "Sluicing fails completely when the argument domain itself has no match: no vP in the antecedent whose argument domain matches 'who [he is loyal to]'."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "argument")]
    comment := "UNVERIFIED paperLabel: ex. (15a) carried from Studies/AnandHardtMcCloskey2025.lean failedSluiceEx15a (docstring 'paper ex. (15a-b)'), not checked against the published paper. Lean fields: antecedent = 'he is very loyal'; whPhrase = 'who'; elided = 'he is loyal to'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_13a, ex_13b, ex_12c, ex_15a]

end AnandHardtMcCloskey2025.Examples
