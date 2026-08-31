import Linglib.Data.Examples.Schema

/-!
# `Chierchia2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Chierchia2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chierchia2006.Examples`.
-/

namespace Chierchia2006.Examples

open Data.Examples

def ex10a : LinguisticExample :=
  { id := "chierchia2006_ex10a"
    source := ⟨"chierchia-2006", "(10a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Domani interrogherò qualsiasi studente"
    discourseSegments := []
    glossedTokens := []
    translation := "Tomorrow I will examine any student"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "universal"), ("environment", "future"), ("force", "ambiguous")]
    comment := "Both ∀ and ∃ readings available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10b : LinguisticExample :=
  { id := "chierchia2006_ex10b"
    source := ⟨"chierchia-2006", "(10b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Domani interrogherò uno studente qualsiasi"
    discourseSegments := []
    glossedTokens := []
    translation := "Tomorrow I will examine any one student"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "existential"), ("environment", "future"), ("force", "existential")]
    comment := "Only the ∃ reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10c : LinguisticExample :=
  { id := "chierchia2006_ex10c"
    source := ⟨"chierchia-2006", "(10c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Prendi qualunque dolce"
    discourseSegments := []
    glossedTokens := []
    translation := "Take any sweet"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "universal"), ("environment", "imperative"), ("force", "ambiguous")]
    comment := "Both ∀ and ∃ readings available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10d : LinguisticExample :=
  { id := "chierchia2006_ex10d"
    source := ⟨"chierchia-2006", "(10d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Prendi un dolce qualunque"
    discourseSegments := []
    glossedTokens := []
    translation := "Take any one sweet"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "existential"), ("environment", "imperative"), ("force", "existential")]
    comment := "Only the ∃ reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11a : LinguisticExample :=
  { id := "chierchia2006_ex11a"
    source := ⟨"chierchia-2006", "(11a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con un qualsiasi filosofo"
    discourseSegments := []
    glossedTokens := []
    translation := "Yesterday I spoke with any one philosopher"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "existential"), ("environment", "episodicBare"), ("force", "existential")]
    comment := "Marginal without a modifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11b : LinguisticExample :=
  { id := "chierchia2006_ex11b"
    source := ⟨"chierchia-2006", "(11b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con un qualsiasi filosofo che fosse interessato"
    discourseSegments := []
    glossedTokens := []
    translation := "Yesterday I spoke with any one philosopher who was interested"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "existential"), ("environment", "episodicSubtrigged"), ("force", "existential")]
    comment := "Still marginal: a relative clause does not rescue an existential free-choice item."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11c : LinguisticExample :=
  { id := "chierchia2006_ex11c"
    source := ⟨"chierchia-2006", "(11c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con qualsiasi filosofo"
    discourseSegments := []
    glossedTokens := []
    translation := "Yesterday I spoke with any philosopher"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "universal"), ("environment", "episodicBare"), ("force", "universal")]
    comment := "Marginal without a modifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11d : LinguisticExample :=
  { id := "chierchia2006_ex11d"
    source := ⟨"chierchia-2006", "(11d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con qualsiasi filosofo che fosse interessato"
    discourseSegments := []
    glossedTokens := []
    translation := "Yesterday I spoke with any philosopher who was interested"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "universal"), ("environment", "episodicSubtrigged"), ("force", "universal")]
    comment := "Subtrigging rescues the universal free-choice item."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12 : LinguisticExample :=
  { id := "chierchia2006_ex12"
    source := ⟨"chierchia-2006", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non leggerò qualunque libro"
    discourseSegments := []
    glossedTokens := []
    translation := "I will not read any book"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "universal"), ("environment", "negationBare"), ("force", "universal")]
    comment := "Only the rhetorical ¬∀ reading, not the ¬∃ reading of a negative-polarity item. Also numbered (73a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex73b : LinguisticExample :=
  { id := "chierchia2006_ex73b"
    source := ⟨"chierchia-2006", "(73b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non leggerò qualunque libro che mi consiglierà Gianni"
    discourseSegments := []
    glossedTokens := []
    translation := "I will not read any book that Gianni recommends to me"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fciType", "universal"), ("environment", "negationSubtrigged"), ("force", "ambiguous")]
    comment := "With a relative clause under negation the ∀¬ and ¬∃ readings become available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex10a, ex10b, ex10c, ex10d, ex11a, ex11b, ex11c, ex11d, ex12, ex73b]

end Chierchia2006.Examples
