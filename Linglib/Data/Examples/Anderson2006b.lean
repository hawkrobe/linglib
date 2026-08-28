import Linglib.Data.Examples.Schema

/-!
# `Anderson2006b` — typed example data

Auto-generated from `Linglib/Data/Examples/Anderson2006b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anderson2006b.Examples`.
-/

namespace Anderson2006b.Examples

open Data.Examples

def ex_39a : LinguisticExample :=
  { id := "anderson2006b_39a"
    source := ⟨"anderson-2006b", "ch. 6 (39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill read the book"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill read the book"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "erg"), ("arg", "abs"), ("subject", "erg")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39b : LinguisticExample :=
  { id := "anderson2006b_39b"
    source := ⟨"anderson-2006b", "ch. 6 (39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill fell to the ground"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill fell to the ground"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "abs"), ("arg", "loc"), ("subject", "abs")]
    comment := "The locative carries the second-order feature {goal}; the subject is not inherently ergative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39c : LinguisticExample :=
  { id := "anderson2006b_39c"
    source := ⟨"anderson-2006b", "ch. 6 (39c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill flew to China"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill flew to China"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "abs,erg"), ("arg", "loc"), ("subject", "abs,erg")]
    comment := "The locative carries {goal}."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39h : LinguisticExample :=
  { id := "anderson2006b_39h"
    source := ⟨"anderson-2006b", "ch. 6 (39h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill knew the answer"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill knew the answer"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "erg,loc"), ("arg", "abs"), ("subject", "erg,loc")]
    comment := "E (Experiencer) = erg,loc."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39i : LinguisticExample :=
  { id := "anderson2006b_39i"
    source := ⟨"anderson-2006b", "ch. 6 (39i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill acquired a new shirt"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill acquired a new shirt"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "erg,loc"), ("arg", "abs"), ("subject", "erg,loc")]
    comment := "Experiencer with {goal} on its locative component: erg,loc{goal} + abs. Also 'a new outlook'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39j : LinguisticExample :=
  { id := "anderson2006b_39j"
    source := ⟨"anderson-2006b", "ch. 6 (39j)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill suffered from asthma"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill suffered from asthma"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "abs,erg,loc"), ("arg", "loc"), ("subject", "abs,erg,loc")]
    comment := "E + abl = abs,erg,loc{goal} + loc{src}. Also 'from delusions'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34 : LinguisticExample :=
  { id := "anderson2006b_34"
    source := ⟨"anderson-2006b", "ch. 6 (34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Phil suffered (from asthma)"
    discourseSegments := []
    glossedTokens := []
    translation := "Phil suffered (from asthma)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "abs,erg,loc"), ("arg", "loc"), ("subject", "abs,erg,loc")]
    comment := "A patient that is at once Experiencer and contactive: all three first-order features combine on one argument; the ablative is loc{src}."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_8a : LinguisticExample :=
  { id := "anderson2006b_4_8a"
    source := ⟨"anderson-2006b", "ch. 6 (4.8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sewage flooded into the tank"
    discourseSegments := []
    glossedTokens := []
    translation := "Sewage flooded into the tank"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "abs"), ("arg", "loc"), ("subject", "abs")]
    comment := "The simple absolutive is subject; the other argument does not combine locative with absolutive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_8b : LinguisticExample :=
  { id := "anderson2006b_4_8b"
    source := ⟨"anderson-2006b", "ch. 6 (4.8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tank flooded with sewage"
    discourseSegments := []
    glossedTokens := []
    translation := "The tank flooded with sewage"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "abs,loc"), ("arg", "abs"), ("subject", "abs,loc")]
    comment := "Under (38) with its optional comma the complex absolutive abs,loc takes precedence over the simple one; under (38)′ the with-phrase is an adjunct outside subject selection."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "anderson2006b_23a"
    source := ⟨"anderson-2006b", "ch. 6 (23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill reads lots of books"
    discourseSegments := []
    glossedTokens := []
    translation := "Bill reads lots of books"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("arg", "erg"), ("arg", "abs"), ("subject", "erg")]
    comment := "The object is absolutive but not contactive: no 'intimate contact'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_39a, ex_39b, ex_39c, ex_39h, ex_39i, ex_39j, ex_34, ex_4_8a, ex_4_8b, ex_23a]

end Anderson2006b.Examples
