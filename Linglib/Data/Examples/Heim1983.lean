import Linglib.Data.Examples.Schema

/-!
# `Heim1983` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1983.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1983.Examples`.
-/

namespace Heim1983.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "heim1983_ex1"
    source := ⟨"heim-1983", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king has a son."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "0"), ("presupposes", "there is a king")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2 : LinguisticExample :=
  { id := "heim1983_ex2"
    source := ⟨"heim-1983", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king's son is bald."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "0"), ("presupposes", "the king has a son")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3 : LinguisticExample :=
  { id := "heim1983_ex3"
    source := ⟨"heim-1983", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the king has a son, the king's son is bald."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "0"), ("presupposes", "there is a king"), ("filtered", "the king has a son")]
    comment := "Inherits the presupposition both constituents carry, not the one the consequent adds."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5 : LinguisticExample :=
  { id := "heim1983_ex5"
    source := ⟨"heim-1983", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John has children, then Mary will not like his twins."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("presupposes", "someone with children has twins"), ("gazdar", "nothing"), ("kp", "as reported")]
    comment := "Slightly strange out of context; Karttunen and Peters predict this, Gazdar the opposite."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6 : LinguisticExample :=
  { id := "heim1983_ex6"
    source := ⟨"heim-1983", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John has twins, then Mary will not like his children."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("presupposes", "nothing"), ("gazdar", "John has children"), ("kp", "nothing")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7 : LinguisticExample :=
  { id := "heim1983_ex7"
    source := ⟨"heim-1983", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every nation cherishes its king."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("presupposes", "every nation has a king"), ("kp", "every nation has a king")]
    comment := "Derived from (21) and (22) in §3.2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16 : LinguisticExample :=
  { id := "heim1983_ex16"
    source := ⟨"heim-1983", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king of France didn't come."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3"), ("global", "France has a king"), ("local", "either France has no king or he didn't come")]
    comment := "Global accommodation is preferred; the local option is taken when the speaker continues with 'because France doesn't have a king'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23 : LinguisticExample :=
  { id := "heim1983_ex23"
    source := ⟨"heim-1983", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who serves his king will be rewarded."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("presupposes", "everyone has a king"), ("kp", "nothing")]
    comment := "A presupposition in the restrictor; Heim's prediction differs from Karttunen and Peters's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "heim1983_ex24"
    source := ⟨"heim-1983", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No nation cherishes its king."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("cooper", "every nation has a king"), ("lernerZimmermann", "some nation has a king")]
    comment := "The paper sides with Cooper, barring local accommodation; the CCP of 'no' is not given."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25 : LinguisticExample :=
  { id := "heim1983_ex25"
    source := ⟨"heim-1983", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A fat man was pushing his bicycle."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("kp", "some fat man had a bicycle"), ("presupposes", "every fat man had a bicycle, unless accommodated")]
    comment := "The universal presupposition is avoided by accommodating that the fat man in question had a bicycle in the course of the update."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex5, ex6, ex7, ex16, ex23, ex24, ex25]

end Heim1983.Examples
