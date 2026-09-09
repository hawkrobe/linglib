import Linglib.Data.Examples.Schema

/-!
# `Francescotti1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Francescotti1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Francescotti1995.Examples`.
-/

namespace Francescotti1995.Examples

open Data.Examples

def ex5 : LinguisticExample :=
  { id := "francescotti1995_ex5"
    source := ⟨"francescotti-1995", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Albert passed the exam."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Albert, one of the best chemistry students in the school's history, passed; Marie, the very best, was even more likely to pass."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("surpassed", "1"), ("neighbors", "3"), ("felicitous", "no")]
    comment := "Albert's passing surpasses one neighbor, Marie's, in surprise, and no more: Bennett's condition wrongly licenses the sentence. The count of classmates is schematic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1 : LinguisticExample :=
  { id := "francescotti1995_ex1"
    source := ⟨"francescotti-1995", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Albert failed the exam."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Everyone in the class failed, Albert's failure being very surprising, and Marie's would be more so."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("surpassed", "2"), ("neighbors", "3"), ("felicitous", "yes")]
    comment := "Albert's failure surpasses every neighbor but Marie's: the universal condition wrongly blocks the sentence. The count of classmates is schematic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7 : LinguisticExample :=
  { id := "francescotti1995_ex7"
    source := ⟨"kay-1990", "lieutenant colonels"⟩
    reportedIn := some ⟨"francescotti-1995", "(7)"⟩
    language := "stan1293"
    primaryText := "The administration was so bewildered that they even had lieutenant colonels making policy decisions."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("surpassed", "2"), ("neighbors", "3"), ("felicitous", "yes")]
    comment := "Felicitous although majors, captains or sergeants making policy would be more extreme still. The counts are schematic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21far : LinguisticExample :=
  { id := "francescotti1995_ex21far"
    source := ⟨"francescotti-1995", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Andre cannot reach the top shelf."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Andre is by far the tallest person in the reference class."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("surpassed", "5"), ("neighbors", "5"), ("felicitous", "yes")]
    comment := "Surpasses every neighbor by a wide margin: very felicitous. The count of the reference class is schematic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21near : LinguisticExample :=
  { id := "francescotti1995_ex21near"
    source := ⟨"francescotti-1995", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Andre cannot reach the top shelf."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Andre is the tallest person in the reference class, but only by a small margin."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("surpassed", "5"), ("neighbors", "5"), ("felicitous", "yes")]
    comment := "Still felicitous, less so: the margin is the paper's first gradient of felicity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21half : LinguisticExample :=
  { id := "francescotti1995_ex21half"
    source := ⟨"francescotti-1995", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Andre cannot reach the top shelf."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Half of the group is over six foot five, the other half under five foot, and Andre is barely in the taller half."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("surpassed", "2"), ("neighbors", "4"), ("felicitous", "no")]
    comment := "Andre is not taller than the majority, though far taller than average: not felicitous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex5, ex1, ex7, ex21far, ex21near, ex21half]

end Francescotti1995.Examples
