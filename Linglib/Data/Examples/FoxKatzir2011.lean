import Linglib.Data.Examples.Schema

/-!
# `FoxKatzir2011` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxKatzir2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxKatzir2011.Examples`.
-/

namespace FoxKatzir2011.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "foxkatzir2011_ex1"
    source := ⟨"fox-katzir-2011", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John did all of the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2 : LinguisticExample :=
  { id := "foxkatzir2011_ex2"
    source := ⟨"fox-katzir-2011", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did the reading or the homework."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John did the reading and the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3 : LinguisticExample :=
  { id := "foxkatzir2011_ex3"
    source := ⟨"fox-katzir-2011", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has three children."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John has four children", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29 : LinguisticExample :=
  { id := "foxkatzir2011_ex29"
    source := ⟨"fox-katzir-2011", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only [read three books]F."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John read four books", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")]
    comment := "Context: What did John do? The symmetric 'read exactly three books' is not a formal alternative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex33 : LinguisticExample :=
  { id := "foxkatzir2011_ex33"
    source := ⟨"fox-katzir-2011", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only [read three books]F."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John read exactly three books", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")]
    comment := "Context: Mary read exactly three books. What did John do? Making the symmetric alternative salient does not let context keep it and prune 'four books'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38 : LinguisticExample :=
  { id := "foxkatzir2011_ex38"
    source := ⟨"sauerland-2004", "disjunction"⟩
    reportedIn := some ⟨"fox-katzir-2011", "(38)"⟩
    language := "stan1293"
    primaryText := "John did all of the homework or none of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John did all of the homework", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")]
    comment := "Neither disjunct's negation is an implicature; the disjuncts partition the assertion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40 : LinguisticExample :=
  { id := "foxkatzir2011_ex40"
    source := ⟨"fox-katzir-2011", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is determined to do all of the homework or none of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John is determined to do all of the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")]
    comment := "Both implicatures arise: the universal operator removes the symmetry."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41 : LinguisticExample :=
  { id := "foxkatzir2011_ex41"
    source := ⟨"fox-katzir-2011", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of my students did all of the homework or none of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: Each of my students did all of the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42a : LinguisticExample :=
  { id := "foxkatzir2011_ex42a"
    source := ⟨"katzir-2007", "Matsumoto examples"⟩
    reportedIn := some ⟨"fox-katzir-2011", "(42a)"⟩
    language := "stan1293"
    primaryText := "John did some of the homework yesterday, and he did just some of the homework today."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John did just some of the homework yesterday", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")]
    comment := "'Just some' is salient, so both it and 'all' are formal alternatives of 'some'; context cannot keep one and prune the other."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44 : LinguisticExample :=
  { id := "foxkatzir2011_ex44"
    source := ⟨"fox-katzir-2011", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was required to do some of the homework yesterday, and he was required to do just some of the homework today."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: John was required to do just some of the homework yesterday", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")]
    comment := "Also: not required to do all of it yesterday."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46 : LinguisticExample :=
  { id := "foxkatzir2011_ex46"
    source := ⟨"fox-katzir-2011", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every single student got some of the questions right last week; today every single student got just some of the questions right."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: Last week, every student got just some of the questions right", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47a : LinguisticExample :=
  { id := "foxkatzir2011_ex47a"
    source := ⟨"fox-katzir-2011", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In last week's robbery they only [stole the books]F. In today's robbery they [stole the books but not the jewelry]F."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: In last week's robbery they stole the books but not the jewelry", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49a : LinguisticExample :=
  { id := "foxkatzir2011_ex49a"
    source := ⟨"fox-katzir-2011", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Detective A only concluded that the robbers [stole the books]F. Detective B concluded that the robbers [stole the books but not the jewelry]F."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: Detective A concluded that the robbers stole the books but not the jewelry", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")]
    comment := "Also: not that they stole the books and the jewelry."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53 : LinguisticExample :=
  { id := "foxkatzir2011_ex53"
    source := ⟨"fox-katzir-2011", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John talked to Mary or Sue, and today, John talked to Mary."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not: Yesterday, John talked to Mary", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "no"), ("universal", "no"), ("compatible", "yes")]
    comment := "The disjuncts are compatible, so not symmetric; the pruned disjunct is exhaustively relevant given the restriction, which the allowable-restriction condition forbids."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex29, ex33, ex38, ex40, ex41, ex42a, ex44, ex46, ex47a, ex49a, ex53]

end FoxKatzir2011.Examples
