import Linglib.Data.Examples.Schema

/-!
# `UegakiSudo2019` — typed example data

Auto-generated from `Linglib/Data/Examples/UegakiSudo2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace UegakiSudo2019.Examples`.
-/

namespace UegakiSudo2019.Examples

open Data.Examples

def ex_6a : LinguisticExample :=
  { id := "uegakisudo2019_6a"
    source := ⟨"uegaki-sudo-2019", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben hopes/wishes that Becky is invited to the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "non-veridical preferential"), ("complement", "declarative")]
    comment := "Non-veridical preferentials take declarative complements."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6c : LinguisticExample :=
  { id := "uegakisudo2019_6c"
    source := ⟨"uegaki-sudo-2019", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dorothy is surprised/annoyed/glad/happy that Daniel will give a presentation."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "declarative")]
    comment := "Veridical preferentials take declarative complements."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7b : LinguisticExample :=
  { id := "uegakisudo2019_7b"
    source := ⟨"uegaki-sudo-2019", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben is happy/glad ?(about) which students are invited to the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "wh-interrogative")]
    comment := "Veridical preferentials are responsive; the preposition improves some cases, an issue taken up in section 5."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7c : LinguisticExample :=
  { id := "uegakisudo2019_7c"
    source := ⟨"uegaki-sudo-2019", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris liked/hated which students were invited to the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "wh-interrogative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a : LinguisticExample :=
  { id := "uegakisudo2019_8a"
    source := ⟨"uegaki-sudo-2019", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben hopes/wishes which students will be invited to the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "non-veridical preferential"), ("complement", "wh-interrogative")]
    comment := "The hope-wh puzzle: non-veridical preferentials are anti-rogative; the which-NP clause has no free-relative reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8b : LinguisticExample :=
  { id := "uegakisudo2019_8b"
    source := ⟨"uegaki-sudo-2019", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris expects/fears how many students will be invited to the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "non-veridical preferential"), ("complement", "wh-interrogative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10b : LinguisticExample :=
  { id := "uegakisudo2019_10b"
    source := ⟨"uegaki-sudo-2019", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben is glad/happy (about) whether Becky is invited to the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "whether-interrogative")]
    comment := "Veridical preferentials reject whether-complements, a pattern the paper leaves to Romero's account."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_40a : LinguisticExample :=
  { id := "uegakisudo2019_40a"
    source := ⟨"uegaki-sudo-2019", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is happy that ALICE jumped."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John's preference for Alice's jumping is compared to alternatives false at the evaluation world", .acceptable)]
    paperFeatures := [("predicate", "veridical preferential"), ("focus", "subject")]
    comment := "Veridicality does not restrict the comparison class."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_40b : LinguisticExample :=
  { id := "uegakisudo2019_40b"
    source := ⟨"uegaki-sudo-2019", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hopes that ALICE jumped."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John's preference for Alice's jumping is compared only to alternatives he considers possible", .acceptable)]
    paperFeatures := [("predicate", "non-veridical preferential"), ("focus", "subject")]
    comment := "The doxastic condition of emotive doxastics restricts the comparison class as a whole, (39)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_41 : LinguisticExample :=
  { id := "uegakisudo2019_41"
    source := ⟨"uegaki-sudo-2019", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't happy about / doesn't like which student will sing."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "There is no particular student John wants to sing. John knows which student will sing."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "wh-interrogative"), ("evidence", "Threshold Significance")]
    comment := "Without Threshold Significance the sentence would be true in the context; instead it presupposes a student John preferred to sing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_42 : LinguisticExample :=
  { id := "uegakisudo2019_42"
    source := ⟨"uegaki-sudo-2019", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is indifferent about which student will sing."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "There is no particular student John wants to sing."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "be indifferent"), ("complement", "wh-interrogative")]
    comment := "Be indifferent compares questions rather than propositions, so Threshold Significance holds of a question, compatibly with the context of (41)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_43a : LinguisticExample :=
  { id := "uegakisudo2019_43a"
    source := ⟨"uegaki-sudo-2019", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is indifferent that Alice will sing."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "be indifferent"), ("complement", "declarative")]
    comment := "Marginal at best with a declarative: be indifferent concerns questions."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_6a, ex_6c, ex_7b, ex_7c, ex_8a, ex_8b, ex_10b, ex_40a, ex_40b, ex_41, ex_42, ex_43a]

end UegakiSudo2019.Examples
