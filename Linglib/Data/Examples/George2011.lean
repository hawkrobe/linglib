import Linglib.Data.Examples.Schema

/-!
# `George2011` — typed example data

Auto-generated from `Linglib/Data/Examples/George2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace George2011.Examples`.
-/

namespace George2011.Examples

open Data.Examples

def ex12 : LinguisticExample :=
  { id := "george2011_ex12"
    source := ⟨"george-2011", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maggie knows who was admitted to the program."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Three applicants, Riley, Adam and Robin; Riley and Adam were admitted and Robin rejected. Maggie, not on the admissions committee, was sent the complete list of admitted applicants and had never heard of any applicant before."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("sentence", "admittedKnown"), ("holds", "yes")]
    comment := "True on the strongly exhaustive reading: Maggie knows the admitted list is complete."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13 : LinguisticExample :=
  { id := "george2011_ex13"
    source := ⟨"george-2011", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maggie knows who wasn't admitted to the program."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Three applicants, Riley, Adam and Robin; Riley and Adam were admitted and Robin rejected. Maggie, not on the admissions committee, was sent the complete list of admitted applicants and had never heard of any applicant before."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("sentence", "notAdmittedKnown"), ("holds", "no")]
    comment := "False on every reading: nothing Maggie knows excludes Robin not having applied, or further applicants."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4 : LinguisticExample :=
  { id := "george2011_ex4"
    source := ⟨"george-2011", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maggie knows who was admitted to the program, but she doesn't know who wasn't admitted."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Three applicants, Riley, Adam and Robin; Riley and Adam were admitted and Robin rejected. Maggie, not on the admissions committee, was sent the complete list of admitted applicants and had never heard of any applicant before."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("sentence", "admittedButNot"), ("holds", "yes")]
    comment := "Adapted from Sharvit (2002); consistent, and true here on strongly exhaustive readings of both questions."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17 : LinguisticExample :=
  { id := "george2011_ex17"
    source := ⟨"george-2011", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rupert knows which of his four students were admitted, but he doesn't know which weren't."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Rupert's four students are Anne, Red, Alex and Jonathan; Anne and Red were admitted, Jonathan rejected, Alex neither. Rupert has the complete list of admitted students but does not know, for Jonathan and Alex, whether they were rejected or fall into another category."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("sentence", "fourStudents"), ("holds", "yes")]
    comment := "Adapted from Guerzoni and Sharvit (2007); true when 'weren't admitted' is understood as 'were rejected'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex33 : LinguisticExample :=
  { id := "george2011_ex33"
    source := ⟨"george-2011", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Janna knows where Rupert can buy a newspaper."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Rupert can buy a newspaper at PaperWorld and not at Newstopia. Janna and Red both know the former and know the same propositions; Red falsely believes Rupert can buy one at Newstopia, Janna has no opinion about Newstopia."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("sentence", "jannaNewspaper"), ("holds", "yes")]
    comment := "True on the mention-some reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34 : LinguisticExample :=
  { id := "george2011_ex34"
    source := ⟨"george-2011", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Red knows where Rupert can buy a newspaper."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Rupert can buy a newspaper at PaperWorld and not at Newstopia. Janna and Red both know the former and know the same propositions; Red falsely believes Rupert can buy one at Newstopia, Janna has no opinion about Newstopia."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("sentence", "redNewspaper"), ("holds", "no")]
    comment := "Untrue: Red's beliefs about where newspapers are available are at odds with the facts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex12, ex13, ex4, ex17, ex33, ex34]

end George2011.Examples
