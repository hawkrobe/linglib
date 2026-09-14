import Linglib.Data.Examples.Schema

/-!
# `Snyder2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Snyder2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Snyder2026.Examples`.
-/

namespace Snyder2026.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "snyder2026_1a"
    source := ⟨"snyder-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mars's moons are two (in number)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "predicative")]
    comment := "The predicative use of the number word."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "snyder2026_1b"
    source := ⟨"snyder-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Those are (Mars's) two moons."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "attributive")]
    comment := "The attributive use."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1c : LinguisticExample :=
  { id := "snyder2026_1c"
    source := ⟨"snyder-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mars has two moons."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "quantificational")]
    comment := "The quantificational use."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1d : LinguisticExample :=
  { id := "snyder2026_1d"
    source := ⟨"snyder-2026", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The number of Mars's moons is two."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "specificational")]
    comment := "The specificational use."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1e : LinguisticExample :=
  { id := "snyder2026_1e"
    source := ⟨"snyder-2026", "(1e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two is an even number."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "numeral")]
    comment := "The numeral use, a name."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1f : LinguisticExample :=
  { id := "snyder2026_1f"
    source := ⟨"snyder-2026", "(1f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The number two is even."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "closeAppositive")]
    comment := "The close appositive, a singular term coreferential with the numeral."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "snyder2026_4a"
    source := ⟨"snyder-2026", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each (kind of) two belongs to a different number system."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "On the board four number systems, the natural numbers, the integers, the rationals and the reals, are illustrated with examples of numbers belonging to them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "taxonomic")]
    comment := "A taxonomic use: the number word predicates a property of subkinds of TWO; repeated as (76j)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "snyder2026_4b"
    source := ⟨"snyder-2026", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two comes in several varieties: the natural number two, the rational number two, etc."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "On the board four number systems, the natural numbers, the integers, the rationals and the reals, are illustrated with examples of numbers belonging to them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "kindRef")]
    comment := "Reference to the superordinate kind TWO; repeated as (76i)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20a : LinguisticExample :=
  { id := "snyder2026_20a"
    source := ⟨"snyder-2026", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The von Neumann ordinal two is two-membered."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "closeAppositive")]
    comment := "True: the close appositive refers to the von Neumann ordinal {∅, {∅}}, a subkind of TWO."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20b : LinguisticExample :=
  { id := "snyder2026_20b"
    source := ⟨"snyder-2026", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Zermelo ordinal two is not two-membered."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "closeAppositive")]
    comment := "True: the close appositive refers to the Zermelo ordinal {{∅}}, a distinct subkind of TWO; on extant analyses the two close appositives are wrongly coreferential."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_76g : LinguisticExample :=
  { id := "snyder2026_76g"
    source := ⟨"snyder-2026", "(76g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two is next to a five on the board."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "tokenRef")]
    comment := "Reference to a numeral token by the numeral."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_76h : LinguisticExample :=
  { id := "snyder2026_76h"
    source := ⟨"snyder-2026", "(76h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That two is next to a five on the board."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "tokenPredicate")]
    comment := "The lexical predicate applied to a numeral token."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_83 : LinguisticExample :=
  { id := "snyder2026_83"
    source := ⟨"snyder-2026", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two is that set."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Mary is taking a set theory class where the natural numbers are modeled as finite von Neumann ordinals; John asks which of the sets on the board is the number two, and Mary points at {∅, {∅}}. In a second context the natural numbers are modeled as Zermelo ordinals and Mary points at {{∅}}."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "numeral")]
    comment := "Both utterances are true: the numeral refers to different subkinds of TWO in the two contexts, Benacerraf's Identification Problem dissolved."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_94a : LinguisticExample :=
  { id := "snyder2026_94a"
    source := ⟨"snyder-2026", "(94a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That (kind of) red is used to paint barns."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Mary is looking at three paint swatches, each displaying a different shade of red, and points at the first."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "taxonomic")]
    comment := "A colour word as a predicate of subkinds of RED."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_94b : LinguisticExample :=
  { id := "snyder2026_94b"
    source := ⟨"snyder-2026", "(94b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "{Red/The color red} comes in several varieties: crimson, maroon, ..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Mary is looking at three paint swatches, each displaying a different shade of red."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "kindRef")]
    comment := "Reference to the kind RED, of which crimson and maroon are subkinds."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_98 : LinguisticExample :=
  { id := "snyder2026_98"
    source := ⟨"snyder-2026", "(98)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(The color) red is {next to (the color) green/fading/barely visible}."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Mary is looking at a paint swatch exhibiting three colors of paint: a shade of red, a shade of green, and a shade of blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("function", "tokenRef")]
    comment := "Reference to a concrete colour token by the colour name or its close appositive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_1c, ex_1d, ex_1e, ex_1f, ex_4a, ex_4b, ex_20a, ex_20b, ex_76g, ex_76h, ex_83, ex_94a, ex_94b, ex_98]

end Snyder2026.Examples
