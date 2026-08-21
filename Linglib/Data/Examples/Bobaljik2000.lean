import Linglib.Data.Examples.Schema

/-!
# `Bobaljik2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Bobaljik2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bobaljik2000.Examples`.
-/

namespace Bobaljik2000.Examples

open Data.Examples

def ex_9a : LinguisticExample :=
  { id := "bobaljik2000_9a"
    source := ⟨"bobaljik-2000", "(9a)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t’-kzu-s-cen"
    discourseSegments := []
    glossedTokens := [("t’-kzu-s-cen", "1S:SU-help-PRES-1>3P:OB")]
    translation := "I'm helping the mice"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "kzu"), ("rootClass", "I"), ("subj", "1sg"), ("obj", "3pl"), ("m1", "t"), ("m2", "kzu"), ("m3", "s"), ("m4", "cen")]
    comment := "Class I: no class marker."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9b : LinguisticExample :=
  { id := "bobaljik2000_9b"
    source := ⟨"bobaljik-2000", "(9b)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t-t-s-ki-cen"
    discourseSegments := []
    glossedTokens := [("t-t-s-ki-cen", "1S:SU-bring-PRES-II-1>3P:OB")]
    translation := "I'm bringing tasty rotten (mouse) heads"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "t"), ("rootClass", "II"), ("subj", "1sg"), ("obj", "3pl"), ("m1", "t"), ("m2", "t"), ("m3", "s"), ("m4", "ki"), ("m5", "cen")]
    comment := "Class II marker -ki- for a first-person subject acting on a third-person object (11)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a : LinguisticExample :=
  { id := "bobaljik2000_10a"
    source := ⟨"bobaljik-2000", "(10a)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "lcqu-z-in"
    discourseSegments := []
    glossedTokens := [("lcqu-z-in", "see-PRES-2S>3S:OB")]
    translation := "Do you see our house?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "lcqu"), ("rootClass", "I"), ("subj", "2sg"), ("obj", "3sg"), ("m1", "lcqu"), ("m2", "s"), ("m3", "in")]
    comment := "Present /s/ voiced intervocalically (note 4); second-singular realis subject prefix is null (7)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10b : LinguisticExample :=
  { id := "bobaljik2000_10b"
    source := ⟨"bobaljik-2000", "(10b)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t-s-c-in"
    discourseSegments := []
    glossedTokens := [("t-s-c-in", "bring-PRES-II-2S>3S:OB")]
    translation := "What are you bringing?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "t"), ("rootClass", "II"), ("subj", "2sg"), ("obj", "3sg"), ("m1", "t"), ("m2", "s"), ("m3", "c"), ("m4", "in")]
    comment := "Class II marker -c- for a second-singular realis subject acting on a third-person object (11)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_9a, ex_9b, ex_10a, ex_10b]

end Bobaljik2000.Examples
