import Linglib.Data.Examples.Schema

/-!
# `Kalin2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Kalin2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kalin2018.Examples`.
-/

namespace Kalin2018.Examples

open Data.Examples

def ex_8a : LinguisticExample :=
  { id := "kalin2018_8a"
    source := ⟨"kalin-2018", "(8a)"⟩
    reportedIn := none
    language := ""
    primaryText := "Xa ksuta lapl-a."
    discourseSegments := []
    glossedTokens := []
    translation := "A book is falling (e.g., but I don't know which)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "none"), ("subject_suffix", "S"), ("object_suffix", "none")]
    comment := "The subject is nonagentive, nonspecific, indefinite, inanimate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9a : LinguisticExample :=
  { id := "kalin2018_9a"
    source := ⟨"kalin-2018", "(9a)"⟩
    reportedIn := none
    language := ""
    primaryText := "Xa ksuta mpel-a."
    discourseSegments := []
    glossedTokens := []
    translation := "A book fell (e.g., but I don't know which)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "none"), ("subject_suffix", "L"), ("object_suffix", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9b : LinguisticExample :=
  { id := "kalin2018_9b"
    source := ⟨"kalin-2018", "(9b)"⟩
    reportedIn := none
    language := ""
    primaryText := "Ayet ksu-wa-lox."
    discourseSegments := []
    glossedTokens := []
    translation := "You wrote (a long time ago)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "none"), ("subject_suffix", "L"), ("object_suffix", "none")]
    comment := "The subject is agentive, specific, definite, animate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a : LinguisticExample :=
  { id := "kalin2018_10a"
    source := ⟨"kalin-2018", "(10a)"⟩
    reportedIn := none
    language := ""
    primaryText := "Ana (xa) ksuta xazy-an-a."
    discourseSegments := []
    glossedTokens := []
    translation := "I see a (specific) book (e.g., on the table)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10b : LinguisticExample :=
  { id := "kalin2018_10b"
    source := ⟨"kalin-2018", "(10b)"⟩
    reportedIn := none
    language := ""
    primaryText := "Ana o ksuta kasw-an-a."
    discourseSegments := []
    glossedTokens := []
    translation := "I (will) write that book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10c : LinguisticExample :=
  { id := "kalin2018_10c"
    source := ⟨"kalin-2018", "(10c)"⟩
    reportedIn := none
    language := ""
    primaryText := "Poles kod yoma baxt-e nasheq-∅-la."
    discourseSegments := []
    glossedTokens := []
    translation := "Paul kisses his wife every day."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11a : LinguisticExample :=
  { id := "kalin2018_11a"
    source := ⟨"kalin-2018", "(11a)"⟩
    reportedIn := none
    language := ""
    primaryText := "Ana (xa) ksuta kasw-an."
    discourseSegments := []
    glossedTokens := []
    translation := "I will write a book (e.g., someday, about something, I don't know what)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "nonspecific"), ("subject_suffix", "S"), ("object_suffix", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11b : LinguisticExample :=
  { id := "kalin2018_11b"
    source := ⟨"kalin-2018", "(11b)"⟩
    reportedIn := none
    language := ""
    primaryText := "Ana kod yoma yale xazy-an."
    discourseSegments := []
    glossedTokens := []
    translation := "I see some children every day (e.g., but it is not the same children every day)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "nonspecific"), ("subject_suffix", "S"), ("object_suffix", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12a : LinguisticExample :=
  { id := "kalin2018_12a"
    source := ⟨"kalin-2018", "(12a)"⟩
    reportedIn := none
    language := ""
    primaryText := "*Axnı o ksuta ksu-lan."
    discourseSegments := []
    glossedTokens := []
    translation := "Intended: We wrote that book."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "specific"), ("subject_suffix", "L"), ("object_suffix", "none")]
    comment := "A specific object is banned with the perfective base; (12b) shows no placement of object agreement rescues it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12c : LinguisticExample :=
  { id := "kalin2018_12c"
    source := ⟨"kalin-2018", "(12c)"⟩
    reportedIn := none
    language := ""
    primaryText := "Axnı xa ksuta ksu-lan."
    discourseSegments := []
    glossedTokens := []
    translation := "We wrote a book (e.g., we have written many; not referring to a specific one)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "nonspecific"), ("subject_suffix", "L"), ("object_suffix", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_38 : LinguisticExample :=
  { id := "kalin2018_38"
    source := ⟨"kalin-2018", "(38)"⟩
    reportedIn := none
    language := ""
    primaryText := "Axnı o ksuta kasw-ox-la."
    discourseSegments := []
    glossedTokens := []
    translation := "We (will) write that book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_8a, ex_9a, ex_9b, ex_10a, ex_10b, ex_10c, ex_11a, ex_11b, ex_12a, ex_12c, ex_38]

end Kalin2018.Examples
