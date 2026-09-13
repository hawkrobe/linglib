import Linglib.Data.Examples.Schema

/-!
# `Poole2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Poole2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Poole2024.Examples`.
-/

namespace Poole2024.Examples

open Data.Examples

def ex15 : LinguisticExample :=
  { id := "poole2024_ex15"
    source := ⟨"poole-2024", "(15)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kinige-ni Masha-qa bier-di-m."
    discourseSegments := []
    glossedTokens := [("Min", "I"), ("kinige-ni", "book-ACC"), ("Masha-qa", "Masha-DAT"), ("bier-di-m", "give-PST-1SG")]
    translation := "I gave the book to Masha."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "yes")]
    comment := "The shifted direct object is accusative; the accusative is obligatory."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex15_bare : LinguisticExample :=
  { id := "poole2024_ex15_bare"
    source := ⟨"poole-2024", "(15)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kinige Masha-qa bier-di-m."
    discourseSegments := []
    glossedTokens := [("Min", "I"), ("kinige", "book"), ("Masha-qa", "Masha-DAT"), ("bier-di-m", "give-PST-1SG")]
    translation := "I gave the book to Masha."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "yes"), ("licensor", "yes")]
    comment := "The shifted direct object cannot stay unmarked."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex18 : LinguisticExample :=
  { id := "poole2024_ex18"
    source := ⟨"poole-2024", "(18)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min Masha-qa kinige bier-di-m."
    discourseSegments := []
    glossedTokens := [("Min", "I"), ("Masha-qa", "Masha-DAT"), ("kinige", "book"), ("bier-di-m", "give-PST-1SG")]
    translation := "I gave Masha books/a book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "no"), ("licensor", "yes")]
    comment := "The direct object inside VP stays unmarked."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex18_acc : LinguisticExample :=
  { id := "poole2024_ex18_acc"
    source := ⟨"poole-2024", "(18)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min Masha-qa kinige-ni bier-di-m."
    discourseSegments := []
    glossedTokens := [("Min", "I"), ("Masha-qa", "Masha-DAT"), ("kinige-ni", "book-ACC"), ("bier-di-m", "give-PST-1SG")]
    translation := "I gave Masha books/a book."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "no"), ("licensor", "yes")]
    comment := "Accusative on the unshifted direct object is infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex20a : LinguisticExample :=
  { id := "poole2024_ex20a"
    source := ⟨"vinokurova-2005", "(20a)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Keskil Aisen-y kel-bet dien xomoj-do."
    discourseSegments := []
    glossedTokens := [("Keskil", "Keskil"), ("Aisen-y", "Aisen-ACC"), ("kel-bet", "come-NEG.AOR.3SG"), ("dien", "that"), ("xomoj-do", "become.sad-PST.3SG")]
    translation := "Keskil became sad that Aisen is not coming."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "yes")]
    comment := "The raised embedded subject is accusative in the presence of a matrix DP."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex20b : LinguisticExample :=
  { id := "poole2024_ex20b"
    source := ⟨"poole-2024", "(20b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Aisen-y massyyna atyylah-ar-a naada buol-la."
    discourseSegments := []
    glossedTokens := [("Aisen-y", "Aisen-ACC"), ("massyyna", "car"), ("atyylah-ar-a", "buy-AOR-3SG"), ("naada", "need"), ("buol-la", "become-PST.3SG")]
    translation := "It became necessary for Aisen to buy a car."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "no")]
    comment := "No matrix DP unlocks the accusative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex20b_bare : LinguisticExample :=
  { id := "poole2024_ex20b_bare"
    source := ⟨"poole-2024", "(20b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Aisen massyyna atyylah-ar-a naada buol-la."
    discourseSegments := []
    glossedTokens := [("Aisen", "Aisen"), ("massyyna", "car"), ("atyylah-ar-a", "buy-AOR-3SG"), ("naada", "need"), ("buol-la", "become-PST.3SG")]
    translation := "It became necessary for Aisen to buy a car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "yes"), ("licensor", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex15, ex15_bare, ex18, ex18_acc, ex20a, ex20b, ex20b_bare]

end Poole2024.Examples
