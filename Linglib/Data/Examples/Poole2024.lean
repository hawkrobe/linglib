module

public import Linglib.Data.Examples.Schema

/-!
# `Poole2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Poole2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Poole2024.Examples`.
-/

@[expose] public section

namespace Poole2024.Examples

open Data.Examples

def ex15 : LinguisticExample :=
  { id := "poole2024_ex15"
    source := ⟨"poole-2024", "(15)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kinige-ni Masha-qa bier-di-m."
    glossedTokens := [("Min", "I"), ("kinige-ni", "book-ACC"), ("Masha-qa", "Masha-DAT"), ("bier-di-m", "give-PST-1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "yes")] }

def ex15_bare : LinguisticExample :=
  { id := "poole2024_ex15_bare"
    source := ⟨"poole-2024", "(15)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kinige Masha-qa bier-di-m."
    glossedTokens := [("Min", "I"), ("kinige", "book"), ("Masha-qa", "Masha-DAT"), ("bier-di-m", "give-PST-1SG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "yes"), ("licensor", "yes")] }

def ex18 : LinguisticExample :=
  { id := "poole2024_ex18"
    source := ⟨"poole-2024", "(18)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min Masha-qa kinige bier-di-m."
    glossedTokens := [("Min", "I"), ("Masha-qa", "Masha-DAT"), ("kinige", "book"), ("bier-di-m", "give-PST-1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "no"), ("licensor", "yes")] }

def ex18_acc : LinguisticExample :=
  { id := "poole2024_ex18_acc"
    source := ⟨"poole-2024", "(18)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min Masha-qa kinige-ni bier-di-m."
    glossedTokens := [("Min", "I"), ("Masha-qa", "Masha-DAT"), ("kinige-ni", "book-ACC"), ("bier-di-m", "give-PST-1SG")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "no"), ("licensor", "yes")] }

def ex20a : LinguisticExample :=
  { id := "poole2024_ex20a"
    source := ⟨"vinokurova-2005", "(20a)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Keskil Aisen-y kel-bet dien xomoj-do."
    glossedTokens := [("Keskil", "Keskil"), ("Aisen-y", "Aisen-ACC"), ("kel-bet", "come-NEG.AOR.3SG"), ("dien", "that"), ("xomoj-do", "become.sad-PST.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "yes")] }

def ex20b : LinguisticExample :=
  { id := "poole2024_ex20b"
    source := ⟨"poole-2024", "(20b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Aisen-y massyyna atyylah-ar-a naada buol-la."
    glossedTokens := [("Aisen-y", "Aisen-ACC"), ("massyyna", "car"), ("atyylah-ar-a", "buy-AOR-3SG"), ("naada", "need"), ("buol-la", "become-PST.3SG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "no")] }

def ex20b_bare : LinguisticExample :=
  { id := "poole2024_ex20b_bare"
    source := ⟨"poole-2024", "(20b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Aisen massyyna atyylah-ar-a naada buol-la."
    glossedTokens := [("Aisen", "Aisen"), ("massyyna", "car"), ("atyylah-ar-a", "buy-AOR-3SG"), ("naada", "need"), ("buol-la", "become-PST.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "yes"), ("licensor", "no")] }

def all : List LinguisticExample := [ex15, ex15_bare, ex18, ex18_acc, ex20a, ex20b, ex20b_bare]

end Poole2024.Examples
