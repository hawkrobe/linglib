module

public import Linglib.Data.Examples.Schema

/-!
# `AnandHardtMcCloskey2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AnandHardtMcCloskey2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AnandHardtMcCloskey2025.Examples`.
-/

@[expose] public section

namespace AnandHardtMcCloskey2025.Examples

open Data.Examples

def ex_13a : LinguisticExample :=
  { id := "anandhardtmccloskey2025_13a"
    source := ⟨"anand-hardt-mccloskey-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The board believes a one-size-fits-all approach to financial market regulation is inappropriate ... what form [government regulation is necessary IN]."
    glossedTokens := []
    context := "Corpus-attested sluice with a stranded nonargument preposition in the ellipsis site that has no antecedent source. The bracketed capitalized material is the elided clause, not pronounced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "nonargument")] }

def ex_13b : LinguisticExample :=
  { id := "anandhardtmccloskey2025_13b"
    source := ⟨"anand-hardt-mccloskey-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When the officer asked me about her, I remembered meeting her but I couldn't say what date [I MET her ON]."
    glossedTokens := []
    context := "Corpus-attested sluice with a stranded nonargument PP 'on' in the ellipsis site that has no antecedent source. The bracketed capitalized material is the elided clause, not pronounced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "nonargument")] }

def ex_12c : LinguisticExample :=
  { id := "anandhardtmccloskey2025_12c"
    source := ⟨"anand-hardt-mccloskey-2025", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They're furious but it's unclear who."
    glossedTokens := []
    context := "The argument/nonargument PP contrast: (12a) 'who(m)' with sprouted PP is fine, (12b) pied-piped 'who at' is fine, but the bare sluice fails because the argument-marking preposition 'at' (selected by 'furious') is within the argument domain, has no antecedent source, and fails the Structural Identity Condition."
    judgment := .ungrammatical
    alternatives := [("They're furious but it's unclear who at.", .acceptable)]
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "argument")] }

def ex_15a : LinguisticExample :=
  { id := "anandhardtmccloskey2025_15a"
    source := ⟨"anand-hardt-mccloskey-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is very loyal, but I don't know who."
    glossedTokens := []
    context := "Sluicing fails completely when the argument domain itself has no match: no vP in the antecedent whose argument domain matches 'who [he is loyal to]'."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "argument")] }

def all : List LinguisticExample := [ex_13a, ex_13b, ex_12c, ex_15a]

end AnandHardtMcCloskey2025.Examples
