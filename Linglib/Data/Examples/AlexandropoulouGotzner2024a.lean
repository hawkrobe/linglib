import Linglib.Data.Examples.Schema

/-!
# `AlexandropoulouGotzner2024a` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexandropoulouGotzner2024a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexandropoulouGotzner2024a.Examples`.
-/

namespace AlexandropoulouGotzner2024a.Examples

open Data.Examples

def ag2024a_t2_anna : LinguisticExample :=
  { id := "ag2024a_t2_anna"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna's room was not tiny."
    discourseSegments := []
    glossedTokens := []
    translation := "Anna's room was not tiny."
    context := "A group of friends goes on vacation. One friend named Tim writes a review for each person's room on booking.com. Please decide which rating the room receives in terms of its size based on Tim's statement. 1 = tiny; 5 = gigantic. Tim writes:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "gigantic"), ("adjectiveType", "relative"), ("adjective", "tiny"), ("strength", "strong"), ("polarity", "negative"), ("negation", "negated"), ("condition", "negated negative strong")]
    comment := "Three of the eight statements of the item; participants saw all eight concurrently and rated each room on the 1-5 scale. The same item appears in single-statement mode as Table 1 of Alexandropoulou and Gotzner (2024b)."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024a_t2_david : LinguisticExample :=
  { id := "ag2024a_t2_david"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David's room was small."
    discourseSegments := []
    glossedTokens := []
    translation := "David's room was small."
    context := "A group of friends goes on vacation. One friend named Tim writes a review for each person's room on booking.com. Please decide which rating the room receives in terms of its size based on Tim's statement. 1 = tiny; 5 = gigantic. Tim writes:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "gigantic"), ("adjectiveType", "relative"), ("adjective", "small"), ("strength", "weak"), ("polarity", "negative"), ("negation", "nonNegated"), ("condition", "non-negated negative weak")]
    comment := "Three of the eight statements of the item; participants saw all eight concurrently and rated each room on the 1-5 scale. The same item appears in single-statement mode as Table 1 of Alexandropoulou and Gotzner (2024b)."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024a_t2_brian : LinguisticExample :=
  { id := "ag2024a_t2_brian"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Brian's room was gigantic."
    discourseSegments := []
    glossedTokens := []
    translation := "Brian's room was gigantic."
    context := "A group of friends goes on vacation. One friend named Tim writes a review for each person's room on booking.com. Please decide which rating the room receives in terms of its size based on Tim's statement. 1 = tiny; 5 = gigantic. Tim writes:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "gigantic"), ("adjectiveType", "relative"), ("adjective", "gigantic"), ("strength", "strong"), ("polarity", "positive"), ("negation", "nonNegated"), ("condition", "non-negated positive strong")]
    comment := "Three of the eight statements of the item; participants saw all eight concurrently and rated each room on the 1-5 scale. The same item appears in single-statement mode as Table 1 of Alexandropoulou and Gotzner (2024b)."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024a_t3_anthony : LinguisticExample :=
  { id := "ag2024a_t3_anthony"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Saint Anthony's Hospital is not filthy."
    discourseSegments := []
    glossedTokens := []
    translation := "The Saint Anthony's Hospital is not filthy."
    context := "The government examines the hospitals of a big city for their hygiene standards. The examiner writes a review. Please decide which rating each hospital gets for its hygiene standards based on the examiner's statements. 1 = filthy; 5 = pristine. The examiner says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "pristine"), ("adjectiveType", "absolute"), ("adjective", "filthy"), ("strength", "strong"), ("polarity", "negative"), ("negation", "negated"), ("condition", "negated negative strong")]
    comment := "Three of the eight statements of the item; participants saw all eight concurrently and rated each hospital on the 1-5 scale. The same item appears in single-statement mode as Table 2 of Alexandropoulou and Gotzner (2024b)."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024a_t3_joseph : LinguisticExample :=
  { id := "ag2024a_t3_joseph"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Saint Joseph Hospital is not dirty."
    discourseSegments := []
    glossedTokens := []
    translation := "The Saint Joseph Hospital is not dirty."
    context := "The government examines the hospitals of a big city for their hygiene standards. The examiner writes a review. Please decide which rating each hospital gets for its hygiene standards based on the examiner's statements. 1 = filthy; 5 = pristine. The examiner says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "pristine"), ("adjectiveType", "absolute"), ("adjective", "dirty"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("condition", "negated negative weak")]
    comment := "Three of the eight statements of the item; participants saw all eight concurrently and rated each hospital on the 1-5 scale. The same item appears in single-statement mode as Table 2 of Alexandropoulou and Gotzner (2024b)."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024a_t3_mary : LinguisticExample :=
  { id := "ag2024a_t3_mary"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Saint's Mary's Hospital is pristine."
    discourseSegments := []
    glossedTokens := []
    translation := "The Saint's Mary's Hospital is pristine."
    context := "The government examines the hospitals of a big city for their hygiene standards. The examiner writes a review. Please decide which rating each hospital gets for its hygiene standards based on the examiner's statements. 1 = filthy; 5 = pristine. The examiner says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "pristine"), ("adjectiveType", "absolute"), ("adjective", "pristine"), ("strength", "strong"), ("polarity", "positive"), ("negation", "nonNegated"), ("condition", "non-negated positive strong")]
    comment := "Three of the eight statements of the item; participants saw all eight concurrently and rated each hospital on the 1-5 scale. The same item appears in single-statement mode as Table 2 of Alexandropoulou and Gotzner (2024b)."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def all : List LinguisticExample := [ag2024a_t2_anna, ag2024a_t2_david, ag2024a_t2_brian, ag2024a_t3_anthony, ag2024a_t3_joseph, ag2024a_t3_mary]

end AlexandropoulouGotzner2024a.Examples
