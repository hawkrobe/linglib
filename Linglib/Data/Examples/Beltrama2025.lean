import Linglib.Data.Examples.Schema

/-!
# `Beltrama2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Beltrama2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beltrama2025.Examples`.
-/

namespace Beltrama2025.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "beltrama2025_1a"
    source := ⟨"beltrama-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is decent."
    discourseSegments := []
    glossedTokens := []
    translation := "This pizza is decent."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("middling: positive but only moderately so", .acceptable)]
    paperFeatures := [("class", "MPA"), ("inference", "middling")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3c : LinguisticExample :=
  { id := "beltrama2025_3c"
    source := ⟨"beltrama-2025", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Can you recommend a place making a decent pizza around here? B: Mario's! Their pizza is really good!"
    discourseSegments := []
    glossedTokens := []
    translation := "A: Can you recommend a place making a decent pizza around here? B: Mario's! Their pizza is really good!"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cancelability"), ("verdict", "middling inference is an implicature")]
    comment := "Contrast lukewarm (3b): elaborating with the stronger term contradicts lexicalized upper bounds."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4c : LinguisticExample :=
  { id := "beltrama2025_4c"
    source := ⟨"beltrama-2025", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is decent—but it's not great."
    discourseSegments := []
    glossedTokens := []
    translation := "This pizza is decent—but it's not great."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "reinforceability")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5c : LinguisticExample :=
  { id := "beltrama2025_5c"
    source := ⟨"beltrama-2025", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every customer who thinks their pizza was decent will get a refund."
    discourseSegments := []
    glossedTokens := []
    translation := "Every customer who thinks their pizza was decent will get a refund."
    context := "The refund is meant for unhappy customers."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "DE suspension"), ("verdict", "no upper-bounded reading in the restrictor")]
    comment := "The contradictory flavor shows the middling inference is suspended in downward-entailing contexts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a : LinguisticExample :=
  { id := "beltrama2025_8a"
    source := ⟨"beltrama-2025", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is decent for a US pizza; but for an Italian pizza, it wouldn't be."
    discourseSegments := []
    glossedTokens := []
    translation := "This pizza is decent for a US pizza; but for an Italian pizza, it wouldn't be."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "for-phrase"), ("property", "context-sensitivity")]
    comment := "MPAs are comparison-class sensitive, unlike absolute adjectives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11a : LinguisticExample :=
  { id := "beltrama2025_11a"
    source := ⟨"beltrama-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pizza is very/incredibly/super decent."
    discourseSegments := []
    glossedTokens := []
    translation := "The pizza is very/incredibly/super decent."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "strong intensifiers"), ("property", "restricted gradability")]
    comment := "Moderate modifiers (quite, pretty, somewhat) are fine; high and extreme ones degrade."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12a : LinguisticExample :=
  { id := "beltrama2025_12a"
    source := ⟨"beltrama-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pizza A is more decent than Pizza B."
    discourseSegments := []
    glossedTokens := []
    translation := "Pizza A is more decent than Pizza B."
    context := "Pizza A is exceptionally good."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "comparative"), ("property", "mildness retained in comparatives")]
    comment := "Better is fine in the same context: the MPA comparative keeps the middling flavor."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15a : LinguisticExample :=
  { id := "beltrama2025_15a"
    source := ⟨"beltrama-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is neither acceptable nor unacceptable."
    discourseSegments := []
    glossedTokens := []
    translation := "This pizza is neither acceptable nor unacceptable."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "zone of indifference"), ("verdict", "near-contradiction")]
    comment := "Good/bad leave a neutral gap (14a); MPAs do not — existential vs universal force clash."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "beltrama2025_21"
    source := ⟨"beltrama-2025", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is barely decent."
    discourseSegments := []
    glossedTokens := []
    translation := "This pizza is barely decent."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "barely"), ("property", "crisp boundary")]
    comment := "#barely good needs a special high-standard context; the necessity standard gives MPAs a crisp edge."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22a : LinguisticExample :=
  { id := "beltrama2025_22a"
    source := ⟨"beltrama-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ok, this pizza is acceptable. But a pizza any worse than this one—even by just a tiny bit—wouldn't be acceptable."
    discourseSegments := []
    glossedTokens := []
    translation := "Ok, this pizza is acceptable. But a pizza any worse than this one—even by just a tiny bit—wouldn't be acceptable."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "crisp judgment")]
    comment := "The same continuation with good is infelicitous — vague standards resist crisp cutoffs."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24a : LinguisticExample :=
  { id := "beltrama2025_24a"
    source := ⟨"beltrama-2025", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pizza scene in this town is truly desperate—you can't find even a decent one."
    discourseSegments := []
    glossedTokens := []
    translation := "The pizza scene in this town is truly desperate—you can't find even a decent one."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "emphasis in DE"), ("parallel", "minimizers")]
    comment := "With good or fantastic in place of decent the emphasis collapses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26a : LinguisticExample :=
  { id := "beltrama2025_26a"
    source := ⟨"beltrama-2025", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Joe is very low maintenance when it comes to pizza. It takes just a decent one to make him happy."
    discourseSegments := []
    glossedTokens := []
    translation := "Joe is very low maintenance when it comes to pizza. It takes just a decent one to make him happy."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "minimal sufficiency exclusive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_39 : LinguisticExample :=
  { id := "beltrama2025_39"
    source := ⟨"beltrama-2025", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pizza is slightly decent."
    discourseSegments := []
    glossedTokens := []
    translation := "The pizza is slightly decent."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "slightly"), ("verdict", "against the MinSAA analysis")]
    comment := "MinSAAs (slightly wet, slightly profitable) accept the modifier; MPAs reject it out of the blue."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51b : LinguisticExample :=
  { id := "beltrama2025_51b"
    source := ⟨"beltrama-2025", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pizza A is more decent than Pizza B, but neither is decent. In fact, they're both really bad."
    discourseSegments := []
    glossedTokens := []
    translation := "Pizza A is more decent than Pizza B, but neither is decent. In fact, they're both really bad."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "comparative entailment"), ("verdict", "positive form not entailed")]
    comment := "For MinSAAs the parallel construction contradicts — the MPA standard is more than nonzero value."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_70 : LinguisticExample :=
  { id := "beltrama2025_70"
    source := ⟨"beltrama-2025", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I heard that pizza sucks. B: Not at all. It's actually extremely decent!"
    discourseSegments := []
    glossedTokens := []
    translation := "A: I heard that pizza sucks. B: Not at all. It's actually extremely decent!"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "strong intensifier rescued"), ("condition", "significance excluded from the QUD")]
    comment := "When only the necessity standard is at issue, the intensifier clash with the middling flavor disappears."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_3c, ex_4c, ex_5c, ex_8a, ex_11a, ex_12a, ex_15a, ex_21, ex_22a, ex_24a, ex_26a, ex_39, ex_51b, ex_70]

end Beltrama2025.Examples
