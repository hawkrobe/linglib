import Linglib.Data.Examples.Schema

/-!
# `Fox2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Fox2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Fox2018.Examples`.
-/

namespace Fox2018.Examples

open Data.Examples

def ex16a : LinguisticExample :=
  { id := "fox2018_ex16a"
    source := ⟨"fox-2018", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tell me how fast you drove."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("family", "degree"), ("negation", "no"), ("modal", "no"), ("number", "na"), ("blocked", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16b : LinguisticExample :=
  { id := "fox2018_ex16b"
    source := ⟨"fox-hackl-2006", "negative islands"⟩
    reportedIn := some ⟨"fox-2018", "(16b)"⟩
    language := "stan1293"
    primaryText := "Tell me how fast you didn't drive."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("family", "degree"), ("negation", "yes"), ("modal", "no"), ("number", "na"), ("blocked", "yes")]
    comment := "No smallest degree above the actual speed: no maximally informative true member."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16c : LinguisticExample :=
  { id := "fox2018_ex16c"
    source := ⟨"fox-2018", "(16c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tell me how fast you are not allowed to drive."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("family", "degree"), ("negation", "yes"), ("modal", "yes"), ("number", "na"), ("blocked", "no")]
    comment := "The modal base can entail a least bound, so maximality can be met."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "fox2018_ex24"
    source := ⟨"fox-2018", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What are you required to read for this class? -- War and Peace or Brothers Karamazov."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .acceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "neutral"), ("blocked", "no")]
    comment := "Both scopes: the trace may range over individuals or over generalized quantifiers."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26 : LinguisticExample :=
  { id := "fox2018_ex26"
    source := ⟨"fox-2018", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you not read for this class? -- War and Peace or Brothers Karamazov."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not > or", .unacceptable), ("or > not", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "yes"), ("modal", "no"), ("number", "neutral"), ("blocked", "yes")]
    comment := "The higher-order denotation always contains the weak negated conjunction (28), which identifies no cell: Non-Vacuity fails."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27 : LinguisticExample :=
  { id := "fox2018_ex27"
    source := ⟨"fox-2018", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What are you not allowed to read for this class? -- War and Peace or Brothers Karamazov."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not > or", .acceptable), ("or > not", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "yes"), ("modal", "yes"), ("number", "neutral"), ("blocked", "no")]
    comment := "Marked ? for the narrow-scope reading; the necessity modal lets (29) be the strongest true member."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47a : LinguisticExample :=
  { id := "fox2018_ex47a"
    source := ⟨"fox-2018", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What are you required to read for this class? -- War and Peace or Brothers Karamazov."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .acceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "neutral"), ("blocked", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47b : LinguisticExample :=
  { id := "fox2018_ex47b"
    source := ⟨"fox-2018", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which books are you required to read for this class? -- The Russian books or the French books."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .acceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "plural"), ("blocked", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48 : LinguisticExample :=
  { id := "fox2018_ex48"
    source := ⟨"fox-2018", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which book are you required to read for this class? -- War and Peace or Brothers Karamazov."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > or", .unacceptable), ("or > required", .acceptable)]
    paperFeatures := [("family", "higherOrder"), ("negation", "no"), ("modal", "yes"), ("number", "singular"), ("blocked", "yes")]
    comment := "Singular wh-phrases cannot quantify over higher-type traces."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex16a, ex16b, ex16c, ex24, ex26, ex27, ex47a, ex47b, ex48]

end Fox2018.Examples
