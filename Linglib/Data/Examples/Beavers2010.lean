import Linglib.Data.Examples.Schema

/-!
# `Beavers2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Beavers2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beavers2010.Examples`.
-/

namespace Beavers2010.Examples

open Data.Examples

def ex_9a : LinguisticExample :=
  { id := "beavers2010_9a"
    source := ⟨"beavers-2010", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John loaded the hay onto the wagon."
    discourseSegments := []
    glossedTokens := []
    translation := "John loaded the hay onto the wagon."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("direct", "theme")]
    comment := "Theme object: all the hay moved (quantized); the wagon at least partly filled (nonquantized)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9b : LinguisticExample :=
  { id := "beavers2010_9b"
    source := ⟨"beavers-2010", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John loaded the wagon with the hay."
    discourseSegments := []
    glossedTokens := []
    translation := "John loaded the wagon with the hay."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("direct", "location")]
    comment := "Location object: the wagon completely filled (quantized); the hay at least partly moved (nonquantized) — Anderson's holistic effect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a : LinguisticExample :=
  { id := "beavers2010_10a"
    source := ⟨"beavers-2010", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim loaded the hay onto the wagon, but still needed a truck for the rest."
    discourseSegments := []
    glossedTokens := []
    translation := "Kim loaded the hay onto the wagon, but still needed a truck for the rest."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("diagnostic", "holistic effect")]
    comment := "Infelicitous: the theme object entails total movement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18a : LinguisticExample :=
  { id := "beavers2010_18a"
    source := ⟨"beavers-2010", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cut the diamond on the glass."
    discourseSegments := []
    glossedTokens := []
    translation := "John cut the diamond on the glass."
    context := "John moves a sharp-edged diamond forcefully into contact with a piece of glass."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("verb class", "cut/slice")]
    comment := "Diamond affected: the object is damaged (nonquantized), the oblique only potentially (potential)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18b : LinguisticExample :=
  { id := "beavers2010_18b"
    source := ⟨"beavers-2010", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cut the glass with the diamond."
    discourseSegments := []
    glossedTokens := []
    translation := "John cut the glass with the diamond."
    context := "Same scenario; the glass is damaged rather than the diamond."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("verb class", "cut/slice")]
    comment := "No holistic effect, so locative alternations are not in general governed by aspect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20a : LinguisticExample :=
  { id := "beavers2010_20a"
    source := ⟨"beavers-2010", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie cut the rope."
    discourseSegments := []
    glossedTokens := []
    translation := "Marie cut the rope."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "cut")]
    comment := "The rope is cut, to no specific degree: nonquantized change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20b : LinguisticExample :=
  { id := "beavers2010_20b"
    source := ⟨"beavers-2010", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie cut at the rope."
    discourseSegments := []
    glossedTokens := []
    translation := "Marie cut at the rope."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "cut")]
    comment := "The rope may or may not be cut: potential for change only."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21a : LinguisticExample :=
  { id := "beavers2010_21a"
    source := ⟨"beavers-2010", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie ate her cake."
    discourseSegments := []
    glossedTokens := []
    translation := "Marie ate her cake."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "consumption")]
    comment := "All (or a contextually significant amount) of the cake consumed: quantized change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21b : LinguisticExample :=
  { id := "beavers2010_21b"
    source := ⟨"beavers-2010", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie ate at her cake."
    discourseSegments := []
    glossedTokens := []
    translation := "Marie ate at her cake."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "consumption")]
    comment := "At least some consumed, not necessarily all: nonquantized change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22a : LinguisticExample :=
  { id := "beavers2010_22a"
    source := ⟨"beavers-2010", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie hit Defarge."
    discourseSegments := []
    glossedTokens := []
    translation := "Marie hit Defarge."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "impact")]
    comment := "Defarge is hit but not necessarily affected: potential for change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22b : LinguisticExample :=
  { id := "beavers2010_22b"
    source := ⟨"beavers-2010", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marie hit at Defarge."
    discourseSegments := []
    glossedTokens := []
    translation := "Marie hit at Defarge."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "impact")]
    comment := "Defarge not necessarily even hit: unspecified for change (double modality)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24a : LinguisticExample :=
  { id := "beavers2010_24a"
    source := ⟨"beavers-2010", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hit the fence with the stick."
    discourseSegments := []
    glossedTokens := []
    translation := "John hit the fence with the stick."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("contrast", "none")]
    comment := "Alternates with 'John hit the stick against the fence' with no truth-conditional contrast — the equal-role case the MAP permits."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29 : LinguisticExample :=
  { id := "beavers2010_29"
    source := ⟨"beavers-2010", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tailor lengthened the jeans to 32ins."
    discourseSegments := []
    glossedTokens := []
    translation := "The tailor lengthened the jeans to 32ins."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("degree", "quantized"), ("diagnostic", "telicity")]
    comment := "Specific predicate-supplied result state: telic, quantized change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30 : LinguisticExample :=
  { id := "beavers2010_30"
    source := ⟨"beavers-2010", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tailor lengthened the jeans."
    discourseSegments := []
    glossedTokens := []
    translation := "The tailor lengthened the jeans."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("degree", "nonquantized"), ("diagnostic", "telicity")]
    comment := "Some result on the length scale, unspecified which: atelic, nonquantized change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_81a : LinguisticExample :=
  { id := "beavers2010_81a"
    source := ⟨"beavers-2010", "(81a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John climbed the stairs."
    discourseSegments := []
    glossedTokens := []
    translation := "John climbed the stairs."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "traversal"), ("degree", "totally traversed")]
    comment := "The stairs all traversed; the affected participant is John (quantized change of location)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_81b : LinguisticExample :=
  { id := "beavers2010_81b"
    source := ⟨"beavers-2010", "(81b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John climbed up the stairs."
    discourseSegments := []
    glossedTokens := []
    translation := "John climbed up the stairs."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "traversal"), ("degree", "traversed")]
    comment := "The stairs all or partly traversed: the oblique weakens total traversal to mere traversal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_88a : LinguisticExample :=
  { id := "beavers2010_88a"
    source := ⟨"beavers-2010", "(88a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim mailed London a ball."
    discourseSegments := []
    glossedTokens := []
    translation := "Kim mailed London a ball."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := [("London as an agency (Scotland Yard reading)", .acceptable)]
    paperFeatures := [("alternation", "dative"), ("direct", "recipient")]
    comment := "Indirect objects must be prospective possessors: the goal-only reading is out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_88b : LinguisticExample :=
  { id := "beavers2010_88b"
    source := ⟨"beavers-2010", "(88b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim mailed a ball to London."
    discourseSegments := []
    glossedTokens := []
    translation := "Kim mailed a ball to London."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "dative"), ("oblique", "goal")]
    comment := "The to-variant needs only a goal: the indirect object monotonically adds prospective possession (90)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_9a, ex_9b, ex_10a, ex_18a, ex_18b, ex_20a, ex_20b, ex_21a, ex_21b, ex_22a, ex_22b, ex_24a, ex_29, ex_30, ex_81a, ex_81b, ex_88a, ex_88b]

end Beavers2010.Examples
