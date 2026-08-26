import Linglib.Data.Examples.Schema

/-!
# `Franke2011` — typed example data

Auto-generated from `Linglib/Data/Examples/Franke2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Franke2011.Examples`.
-/

namespace Franke2011.Examples

open Data.Examples

def ex4 : LinguisticExample :=
  { id := "franke2011_ex4"
    source := ⟨"franke-2011", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of Kiki's friends are metalheads."
    discourseSegments := []
    glossedTokens := []
    translation := "Some of Kiki's friends are metalheads."
    context := "Contrasted with 'All of Kiki's friends are metalheads' (5)."
    judgment := .acceptable
    alternatives := []
    readings := [("general epistemic: speaker does not believe all (6a)", .acceptable), ("strong epistemic: speaker believes not all (6b)", .acceptable), ("weak epistemic: speaker uncertain about all (6c)", .acceptable), ("base-level: not all (6d)", .acceptable)]
    paperFeatures := []
    comment := "The four epistemic varieties of a quantity implicature (§2); games SomeAll and SomeAllEpistemic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8 : LinguisticExample :=
  { id := "franke2011_ex8"
    source := ⟨"franke-2011", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha is in love with Alf or Bert."
    discourseSegments := []
    glossedTokens := []
    translation := "Martha is in love with Alf or Bert."
    context := "Alternatives (9): Alf; Bert; Alf and Bert."
    judgment := .acceptable
    alternatives := []
    readings := [("ignorance: speaker uncertain about each disjunct (10)", .acceptable), ("exclusivity: not both (11)", .acceptable)]
    paperFeatures := []
    comment := "Plain disjunction; games TwoDisjuncts, DisjunctionEpistemic, DisjunctionConj."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12a : LinguisticExample :=
  { id := "franke2011_ex12a"
    source := ⟨"franke-2011", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take an apple or a pear."
    discourseSegments := []
    glossedTokens := []
    translation := "You may take an apple or a pear."
    context := "Alternatives (17): may take an apple; may take a pear; may take both."
    judgment := .acceptable
    alternatives := []
    readings := [("free choice: may take an apple and may take a pear (12b)", .acceptable), ("exclusivity: may not take both (15d)", .acceptable)]
    paperFeatures := []
    comment := "Free choice permission; games TwoDisjuncts and FreeChoiceConj."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13 : LinguisticExample :=
  { id := "franke2011_ex13"
    source := ⟨"franke-2011", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take an apple or a pear, but I don't know which."
    discourseSegments := []
    glossedTokens := []
    translation := "You may take an apple or a pear, but I don't know which."
    context := "The speaker's authority over the permission is suspended."
    judgment := .acceptable
    alternatives := []
    readings := [("ignorance: speaker uncertain whether the hearer may take an apple (14a)", .acceptable)]
    paperFeatures := []
    comment := "Free choice gives way to ignorance implicatures in an epistemic game."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18 : LinguisticExample :=
  { id := "franke2011_ex18"
    source := ⟨"franke-2011", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you eat an apple or a pear, you will feel better."
    discourseSegments := []
    glossedTokens := []
    translation := "If you eat an apple or a pear, you will feel better."
    context := "Alternatives (19): if you eat an apple ...; if you eat a pear ..."
    judgment := .acceptable
    alternatives := []
    readings := [("simplification of disjunctive antecedents (19a) and (19b)", .acceptable)]
    paperFeatures := []
    comment := "SDA as a quantity implicature parallel to free choice; games TwoDisjuncts and SdaConj."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30 : LinguisticExample :=
  { id := "franke2011_ex30"
    source := ⟨"franke-2011", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John had taken an apple or a pear, he would have taken an apple."
    discourseSegments := []
    glossedTokens := []
    translation := "If John had taken an apple or a pear, he would have taken an apple."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simplification to (30b): if John had taken a pear, he would have taken an apple", .unacceptable)]
    paperFeatures := []
    comment := "Why SDA is not semantically valid (after McKay and van Inwagen)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex95a : LinguisticExample :=
  { id := "franke2011_ex95a"
    source := ⟨"franke-2011", "(95a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John or (John and Mary)."
    discourseSegments := []
    glossedTokens := []
    translation := "John or (John and Mary)."
    context := "Answer to 'Who (of John and Mary) came to the party?' (93)."
    judgment := .acceptable
    alternatives := []
    readings := [("speaker knows John came and considers it possible that Mary came (95b)", .acceptable)]
    paperFeatures := []
    comment := "Entailing disjuncts: truth-conditionally equivalent to 'John' (94a) but with a different implicature; game EntailingDisjuncts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex99 : LinguisticExample :=
  { id := "franke2011_ex99"
    source := ⟨"franke-2011", "(99)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody is allowed to take an apple or a pear."
    discourseSegments := []
    glossedTokens := []
    translation := "Everybody is allowed to take an apple or a pear."
    context := "Alternatives (100): everybody is allowed to take an apple; ... a pear."
    judgment := .acceptable
    alternatives := []
    readings := [("universal free choice: everybody may take an apple and everybody may take a pear", .acceptable)]
    paperFeatures := []
    comment := "Chemla's universal free choice, derived by pruning the mixed-group state; game GroupPermission."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex4, ex8, ex12a, ex13, ex18, ex30, ex95a, ex99]

end Franke2011.Examples
