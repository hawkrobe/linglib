import Linglib.Data.Examples.Schema

/-!
# `ImelGuoST2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ImelGuoST2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ImelGuoST2026.Examples`.
-/

namespace ImelGuoST2026.Examples

open Data.Examples

def s1a : LinguisticExample :=
  { id := "imelguost2026_s1a"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A friend walks in and shakes off a wet umbrella. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "strong"), ("flavor", "epistemic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s1b : LinguisticExample :=
  { id := "imelguost2026_s1b"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must upload your homework as a PDF."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are reading the specifications of a homework assignment. It partially reads:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "strong"), ("flavor", "deontic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s2a : LinguisticExample :=
  { id := "imelguost2026_s2a"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It may be raining."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A friend is leaving and grabs an umbrella on the way out, saying:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "weak"), ("flavor", "epistemic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s2b : LinguisticExample :=
  { id := "imelguost2026_s2b"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have a cookie."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A mother offers a treat to a child for finishing an assignment:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "weak"), ("flavor", "deontic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s3a : LinguisticExample :=
  { id := "imelguost2026_s3a"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(3a)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "nilh k'a lh(el)-(t)-en-s-wá(7)-(a) ptinus-em-sút"
    discourseSegments := []
    glossedTokens := [("nilh", "FOC"), ("k'a", "INFER"), ("lh(el)-(t)-en-s-wá(7)-(a)", "from-DET-1SG.POSS-NOM-IMPF-DET"), ("ptinus-em-sút", "think-MID-OOC")]
    translation := "It must be from my worrying."
    context := "You have a headache that won't go away, so you go to the doctor. All the tests show negative. There is nothing wrong, so it must just be tension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("source", "Rullmann et al. 2008:321, (5c)"), ("force", "strong"), ("flavor", "epistemic")]
    comment := "Variable-force k'a used with strong force."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s3b : LinguisticExample :=
  { id := "imelguost2026_s3b"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(3b)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "plan k'a qwatsáts"
    discourseSegments := []
    glossedTokens := [("plan", "already"), ("k'a", "INFER"), ("qwatsáts", "leave")]
    translation := "Maybe he's already gone."
    context := "His car isn't there."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("source", "Rullmann et al. 2008:321, (5e)"), ("force", "weak"), ("flavor", "epistemic")]
    comment := "Variable-force k'a used with weak force."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [s1a, s1b, s2a, s2b, s3a, s3b]

end ImelGuoST2026.Examples
