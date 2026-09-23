module

public import Linglib.Data.Examples.Schema

/-!
# `Yan2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Yan2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yan2023.Examples`.
-/

@[expose] public section

namespace Yan2023.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "yan2023_1"
    source := ⟨"yan-2023", "Ch. 4 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas wants a free trip on the Concorde."
    discourseSegments := []
    glossedTokens := []
    translation := "Nicholas wants a free trip on the Concorde."
    context := "Nicholas is not willing to pay the 3,000 dollars he believes a trip would cost."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("role", "premise")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "yan2023_2"
    source := ⟨"yan-2023", "Ch. 4 (1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas wants a trip on the Concorde."
    discourseSegments := []
    glossedTokens := []
    translation := "Nicholas wants a trip on the Concorde."
    context := "As in (1b)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("role", "monotonic conclusion")]
    comment := "False in the scenario although a free trip is a trip."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "yan2023_3"
    source := ⟨"yan-2023", "Ch. 4 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want to teach on Tuesdays next semester."
    discourseSegments := []
    glossedTokens := []
    translation := "I want to teach on Tuesdays next semester."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Heim"), ("role", "premise")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "yan2023_4"
    source := ⟨"yan-2023", "Ch. 4 (2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want to teach next semester."
    discourseSegments := []
    glossedTokens := []
    translation := "I want to teach next semester."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Heim"), ("role", "monotonic conclusion")]
    comment := "Utterable in a situation where the speaker does not want to teach at all."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "yan2023_5"
    source := ⟨"yan-2023", "Ch. 4 (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to send the letter."
    discourseSegments := []
    glossedTokens := []
    translation := "John wants to send the letter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("role", "premise")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "yan2023_6"
    source := ⟨"yan-2023", "Ch. 4 (3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to send the letter or burn it."
    discourseSegments := []
    glossedTokens := []
    translation := "John wants to send the letter or burn it."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("role", "monotonic conclusion")]
    comment := "Suggests that John is okay with burning the letter."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "yan2023_7"
    source := ⟨"yan-2023", "Ch. 4 (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to buy a Ferrari or a Porsche."
    discourseSegments := []
    glossedTokens := []
    translation := "John wants to buy a Ferrari or a Porsche."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John is ok with a Ferrari and he is ok with a Porsche", .acceptable)]
    paperFeatures := [("inference", "box free choice")]
    comment := "The distributive inference does not rely on John not wanting a Ferrari and not wanting a Porsche."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "yan2023_8"
    source := ⟨"yan-2023", "Ch. 4 (26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for John to send the letter."
    discourseSegments := []
    glossedTokens := []
    translation := "It is ok for John to send the letter."
    context := "John wants to send the letter."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("formula", "◇SEND a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "yan2023_9"
    source := ⟨"yan-2023", "Ch. 4 (26d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for John to burn the letter."
    discourseSegments := []
    glossedTokens := []
    translation := "It is ok for John to burn the letter."
    context := "John wants to send the letter."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("formula", "◇BURN a")]
    comment := "Licensed only by the enriched disjunctive want, which the premise does not support."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "yan2023_10"
    source := ⟨"yan-2023", "Ch. 4 (27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for Nicholas to have a free trip."
    discourseSegments := []
    glossedTokens := []
    translation := "It is ok for Nicholas to have a free trip."
    context := "Nicholas wants a free trip on the Concorde."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("formula", "◇∃x FREE x")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "yan2023_11"
    source := ⟨"yan-2023", "Ch. 4 (27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for Nicholas to have a non-free trip."
    discourseSegments := []
    glossedTokens := []
    translation := "It is ok for Nicholas to have a non-free trip."
    context := "Nicholas wants a free trip on the Concorde."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("formula", "◇∃x ¬FREE x")]
    comment := "Licensed only by the enriched reinterpretation of TRIP, which the premise does not justify."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "yan2023_12"
    source := ⟨"yan-2023", "Ch. 4 (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't want to eat any fast food."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't want to eat any fast food."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidence", "monotonicity"), ("item", "NPI any")]
    comment := "The NPI is licensed under negated want, which requires want to be upward monotonic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "yan2023_13"
    source := ⟨"yan-2023", "Ch. 4 (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jones wants to buy a green sweater, but she doesn't want to buy a sweater."
    discourseSegments := []
    glossedTokens := []
    translation := "Jones wants to buy a green sweater, but she doesn't want to buy a sweater."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidence", "monotonicity"), ("role", "contradiction")]
    comment := "Infelicitous, as expected if want is upward monotonic; from Zimmermann 2006."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "yan2023_14"
    source := ⟨"yan-2023", "Ch. 4 (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for John to send the letter, and it is ok for him to burn it."
    discourseSegments := []
    glossedTokens := []
    translation := "It is ok for John to send the letter, and it is ok for him to burn it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("role", "free-choice inference")]
    comment := "The □-free-choice inference from the disjunctive want (8a), read with want scoping over the disjunction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "yan2023_15"
    source := ⟨"yan-2023", "Ch. 4 (16c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm ok to teach on the days that are not Tuesday next semester."
    discourseSegments := []
    glossedTokens := []
    translation := "I'm ok to teach on the days that are not Tuesday next semester."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Heim"), ("role", "unwarranted inference")]
    comment := "Drawn from the reinterpreted conclusion (16b) by free choice; not justified by the premise."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "yan2023_16"
    source := ⟨"yan-2023", "Ch. 4 (19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The school wants that students who struggle with math attend tutoring."
    discourseSegments := []
    glossedTokens := []
    translation := "The school wants that students who struggle with math attend tutoring."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Good Samaritan under desire"), ("role", "premise")]
    comment := "A Good Samaritan case under desire, with a wide- and a narrow-scope reading of the relative clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "yan2023_17"
    source := ⟨"yan-2023", "Ch. 4 (19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The school wants that students struggle with math."
    discourseSegments := []
    glossedTokens := []
    translation := "The school wants that students struggle with math."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Good Samaritan under desire"), ("role", "monotonic conclusion")]
    comment := "Follows from the wide-scope reading of (19a) by conjunction elimination; the paper leaves this case to a scope solution."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17]

end Yan2023.Examples
