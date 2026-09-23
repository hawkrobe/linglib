module

public import Linglib.Data.Examples.Schema

/-!
# `Sharvit2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Sharvit2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sharvit2003.Examples`.
-/

@[expose] public section

namespace Sharvit2003.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "sharvit2003_ex1"
    source := ⟨"sharvit-2003", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A week ago, John decided that in ten days, at breakfast, he would tell his mother that he missed her."
    discourseSegments := []
    glossedTokens := []
    translation := "A week ago, John decided that in ten days, at breakfast, he would tell his mother that he missed her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the telling overlaps the missing", .acceptable), ("anteriority: the missing precedes the telling", .acceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")]
    comment := "Inspired by an example of Abusch 1997. Past under past under past; the most deeply embedded past has a nonpast reading, John's 'Mother, I miss you', and an anteriority reading, 'Mother, I missed you'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2 : LinguisticExample :=
  { id := "sharvit2003_ex2"
    source := ⟨"sharvit-2003", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary was pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary was pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps John's now", .acceptable), ("anteriority: the pregnancy precedes John's now", .acceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")]
    comment := "Cited from Enç 1987. Past under past with both readings, the diagnostic of an SOT language."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3 : LinguisticExample :=
  { id := "sharvit2003_ex3"
    source := ⟨"sharvit-2003", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary is pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("double access: the pregnancy contains the believing time and the utterance time", .acceptable), ("nonpast: the pregnancy overlaps John's now only", .ungrammatical)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "no")]
    comment := "Present under past: only the double access reading; the English present is a matrix indexical."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex4a : LinguisticExample :=
  { id := "sharvit2003_ex4a"
    source := ⟨"sharvit-2003", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two years ago, Sally found out that Mary was pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "Two years ago, Sally found out that Mary was pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps the finding out", .acceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")]
    comment := "Acceptable through the nonpast reading: the pregnancy overlaps the finding out two years ago."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex4b : LinguisticExample :=
  { id := "sharvit2003_ex4b"
    source := ⟨"sharvit-2003", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two years ago, Sally found out that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "Two years ago, Sally found out that Mary is pregnant."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("double access: the pregnancy contains the finding out and the utterance time", .unacceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "no")]
    comment := "Marked # in the paper: the double access reading requires the pregnancy to contain both the finding out two years ago and the utterance time, which conflicts with the duration of pregnancies."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex5 : LinguisticExample :=
  { id := "sharvit2003_ex5"
    source := ⟨"sharvit-2003", "(5)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney šavua, Dan hexlit še be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo še hu mitga'agea ele-ha."
    discourseSegments := []
    glossedTokens := [("Lifney", "before"), ("šavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("še", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat", "meal-CST"), ("ha-boker", "the-morning"), ("hu", "he"), ("yomar", "will-tell"), ("le-imo", "to-his-mother"), ("še", "that"), ("hu", "he"), ("mitga'agea", "miss-PRES"), ("ele-ha", "to-her")]
    translation := "A week ago, Dan decided that in ten days, at breakfast, he would tell his mother that he misses her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the telling overlaps the missing", .acceptable)]
    paperFeatures := [("language", "hebrew"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "yes")]
    comment := "Hebrew present under past has the nonpast reading that English (1) gets from its deleted past: the Hebrew present is not a matrix indexical."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex6 : LinguisticExample :=
  { id := "sharvit2003_ex6"
    source := ⟨"sharvit-2003", "(6)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney šavua, Dan hexlit še be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo še hu hitga'agea ele-ha."
    discourseSegments := []
    glossedTokens := [("Lifney", "before"), ("šavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("še", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat", "meal-CST"), ("ha-boker", "the-morning"), ("hu", "he"), ("yomar", "will-tell"), ("le-imo", "to-his-mother"), ("še", "that"), ("hu", "he"), ("hitga'agea", "miss-PAST"), ("ele-ha", "to-her")]
    translation := "A week ago, Dan decided that in ten days, at breakfast, he would tell his mother that he missed her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("anteriority: the missing precedes the telling", .acceptable), ("nonpast: the telling overlaps the missing", .ungrammatical)]
    paperFeatures := [("language", "hebrew"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "no")]
    comment := "Minimal pair with (5): Hebrew has no SOT rule, so the embedded past is a real past and only the anteriority reading is available."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex12a : LinguisticExample :=
  { id := "sharvit2003_ex12a"
    source := ⟨"sharvit-2003", "(12a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria ine eggios."
    discourseSegments := []
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "told"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("ine", "is"), ("eggios", "pregnant")]
    translation := "In 1963 Kostas told us that Maria is pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps the telling", .acceptable)]
    paperFeatures := [("language", "greek"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "yes")]
    comment := "Modern Greek present under past with a nonpast reading, attributed to Schlenker 1999 and Iatridou p.c.: the Greek present is not a matrix indexical."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex12b : LinguisticExample :=
  { id := "sharvit2003_ex12b"
    source := ⟨"sharvit-2003", "(12b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria itan eggios."
    discourseSegments := []
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "told"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("itan", "was"), ("eggios", "pregnant")]
    translation := "In 1963 Kostas told us that Maria was pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps the telling", .acceptable)]
    paperFeatures := [("language", "greek"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")]
    comment := "Modern Greek past under past with a nonpast reading under a non-factive verb, unlike Hebrew and Japanese (fn. 3): Greek has the SOT rule."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex4a, ex4b, ex5, ex6, ex12a, ex12b]

end Sharvit2003.Examples
