module

public import Linglib.Data.Examples.Schema

/-!
# `Major2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Major2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Major2024.Examples`.
-/

@[expose] public section

namespace Major2024.Examples

open Data.Examples

def ex_2 : Datum :=
  { id := "major2024_2"
    source := ⟨"major-2024", "ex. (2)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-(ni) göshnan-ni et-t-i de-p oyla-y-du."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-(ni)", "Tursun-ACC"), ("göshnan-ni", "meatbread-ACC"), ("et-t-i", "make-PST-3"), ("de-p", "say-CNV"), ("oyla-y-du", "think-NONPST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "dep-clause"), ("matrixVerb", "oyla- 'think'")] }

def ex_38 : Datum :=
  { id := "major2024_38"
    source := ⟨"major-2024", "ex. (38)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p warqiri-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("warqiri-d-i", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "dep-clause"), ("matrixVerb", "warqira- 'scream'")] }

def ex_39a : Datum :=
  { id := "major2024_39a"
    source := ⟨"major-2024", "ex. (39a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni dé-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("dé-d-i", "say-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur dé-d-i.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de- 'say'")] }

def ex_39b : Datum :=
  { id := "major2024_39b"
    source := ⟨"major-2024", "ex. (39b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur birnémi-ler-ni warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira- 'scream'")] }

def ex_40a : Datum :=
  { id := "major2024_40a"
    source := ⟨"major-2024", "ex. (40a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni dé-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("dé-d-i", "say-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur dé-d-i.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de- 'say'")] }

def ex_40b : Datum :=
  { id := "major2024_40b"
    source := ⟨"major-2024", "ex. (40b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur Tursun-ning ket-ken-lik-i-ni warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira- 'scream'")] }

def ex_41a : Datum :=
  { id := "major2024_41a"
    source := ⟨"major-2024", "ex. (41a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni de-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur de-p warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization-persistence"), ("construction", "dep + scream")] }

def ex_41b : Datum :=
  { id := "major2024_41b"
    source := ⟨"major-2024", "ex. (41b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni de-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur de-p warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization-persistence"), ("construction", "dep + scream")] }

def ex_49a : Datum :=
  { id := "major2024_49a"
    source := ⟨"major-2024", "ex. (49a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun-ning ket-ken-lik (xewir)-i méni hayran qal-dur-d-i."
    glossedTokens := [("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik", "leave-PTPL.PST-COMP"), ("(xewir)-i", "(news)-3POSS"), ("méni", "1SG.ACC"), ("hayran", "surprise"), ("qal-dur-d-i", "remain-CAUS-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subject-position"), ("clauseType", "participial")] }

def ex_49b : Datum :=
  { id := "major2024_49b"
    source := ⟨"major-2024", "ex. (49b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun-(ni) ket-t-i de-p (xewer) méni hayran qal-dur-d-i."
    glossedTokens := [("Tursun-(ni)", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("(xewer)", "news"), ("méni", "1SG.ACC"), ("hayran", "surprise"), ("qal-dur-d-i", "remain-CAUS-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subject-position"), ("clauseType", "dep")] }

def all : List Datum := [ex_2, ex_38, ex_39a, ex_39b, ex_40a, ex_40b, ex_41a, ex_41b, ex_49a, ex_49b]

end Major2024.Examples
