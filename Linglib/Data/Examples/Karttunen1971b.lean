module

public import Linglib.Data.Examples.Schema

/-!
# `Karttunen1971b` — typed example data

Auto-generated from `Linglib/Data/Examples/Karttunen1971b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Karttunen1971b.Examples`.
-/

@[expose] public section

namespace Karttunen1971b.Examples

open Data.Examples

def ex_2a : LinguisticExample :=
  { id := "karttunen1971b_2a"
    source := ⟨"karttunen-1971b", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill regrets that Sheila is no longer young."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill regrets that Sheila is no longer young."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "atomic"), ("projective", "yes"), ("person", "3")]
    comment := "Presupposes (3), Sheila is no longer young."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2b : LinguisticExample :=
  { id := "karttunen1971b_2b"
    source := ⟨"karttunen-1971b", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill doesn't regret that Sheila is no longer young."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill doesn't regret that Sheila is no longer young."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2c : LinguisticExample :=
  { id := "karttunen1971b_2c"
    source := ⟨"karttunen-1971b", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does Bill regret that Sheila is no longer young?"
    discourseSegments := []
    glossedTokens := []
    translation := "Does Bill regret that Sheila is no longer young?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22a : LinguisticExample :=
  { id := "karttunen1971b_22a"
    source := ⟨"karttunen-1971b", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't regret that he had not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "John didn't regret that he had not told the truth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")]
    comment := "All of (22) presuppose that John had not told the truth."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22b : LinguisticExample :=
  { id := "karttunen1971b_22b"
    source := ⟨"karttunen-1971b", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't realize that he had not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "John didn't realize that he had not told the truth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")]
    comment := "All of (22) presuppose that John had not told the truth."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22c : LinguisticExample :=
  { id := "karttunen1971b_22c"
    source := ⟨"karttunen-1971b", "(22c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't discover that he had not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "John didn't discover that he had not told the truth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")]
    comment := "All of (22) presuppose that John had not told the truth."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "karttunen1971b_23"
    source := ⟨"karttunen-1971b", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John DIDN'T regret that he had not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "John DIDN'T regret that he had not told the truth."
    context := "An emphatic denial of somebody else's previous assertion; continued 'How could he have done that when he knew that what he had said was true?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "denial"), ("environment", "negation"), ("projective", "no"), ("person", "3")]
    comment := "The one circumstance in which (22) carries no commitment; footnote 7 analyzes it as 'it is not true that', the external negation of three-valued logic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24a : LinguisticExample :=
  { id := "karttunen1971b_24a"
    source := ⟨"karttunen-1971b", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you regret that you had not told the truth?"
    discourseSegments := []
    glossedTokens := []
    translation := "Did you regret that you had not told the truth?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "2")]
    comment := "Most informants agree the question commits the speaker to the view that the addressee has not told the truth."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24b : LinguisticExample :=
  { id := "karttunen1971b_24b"
    source := ⟨"karttunen-1971b", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you realize that you had not told the truth?"
    discourseSegments := []
    glossedTokens := []
    translation := "Did you realize that you had not told the truth?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "question"), ("person", "2")]
    comment := "'Possibly also with realize' the question commits the speaker; no judgment is recorded."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24c : LinguisticExample :=
  { id := "karttunen1971b_24c"
    source := ⟨"karttunen-1971b", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you discover that you had not told the truth?"
    discourseSegments := []
    glossedTokens := []
    translation := "Did you discover that you had not told the truth?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "no"), ("person", "2")]
    comment := "Can also be understood as a sincere request for information: both a factive and a non-factive interpretation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25a : LinguisticExample :=
  { id := "karttunen1971b_25a"
    source := ⟨"karttunen-1971b", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I regret later that I have not told the truth, I will confess it to everyone."
    discourseSegments := []
    glossedTokens := []
    translation := "If I regret later that I have not told the truth, I will confess it to everyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "yes"), ("person", "1")]
    comment := "The first clause contains an admission that the complement is true."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25b : LinguisticExample :=
  { id := "karttunen1971b_25b"
    source := ⟨"karttunen-1971b", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I realize later that I have not told the truth, I will confess it to everyone."
    discourseSegments := []
    glossedTokens := []
    translation := "If I realize later that I have not told the truth, I will confess it to everyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "no"), ("person", "1")]
    comment := "One only admits that there is a possibility that one has not told the truth."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25c : LinguisticExample :=
  { id := "karttunen1971b_25c"
    source := ⟨"karttunen-1971b", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I discover later that I have not told the truth, I will confess it to everyone."
    discourseSegments := []
    glossedTokens := []
    translation := "If I discover later that I have not told the truth, I will confess it to everyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "no"), ("person", "1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26a : LinguisticExample :=
  { id := "karttunen1971b_26a"
    source := ⟨"karttunen-1971b", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that I will regret later that I have not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "It is possible that I will regret later that I have not told the truth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("projective", "yes"), ("person", "1")]
    comment := "What (25a) conversationally implies; by the stronger postulates (11') one can infer the complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26b : LinguisticExample :=
  { id := "karttunen1971b_26b"
    source := ⟨"karttunen-1971b", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that I will realize later that I have not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "It is possible that I will realize later that I have not told the truth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("projective", "no"), ("person", "1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26c : LinguisticExample :=
  { id := "karttunen1971b_26c"
    source := ⟨"karttunen-1971b", "(26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that I will discover later that I have not told the truth."
    discourseSegments := []
    glossedTokens := []
    translation := "It is possible that I will discover later that I have not told the truth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("projective", "no"), ("person", "1")]
    comment := "From the fact that it is possible that I may discover something I cannot conclude that it is the case."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_2a, ex_2b, ex_2c, ex_22a, ex_22b, ex_22c, ex_23, ex_24a, ex_24b, ex_24c, ex_25a, ex_25b, ex_25c, ex_26a, ex_26b, ex_26c]

end Karttunen1971b.Examples
