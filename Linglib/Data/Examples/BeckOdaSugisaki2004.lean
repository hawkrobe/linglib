import Linglib.Data.Examples.Schema

/-!
# `BeckOdaSugisaki2004` — typed example data

Auto-generated from `Linglib/Data/Examples/BeckOdaSugisaki2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeckOdaSugisaki2004.Examples`.
-/

namespace BeckOdaSugisaki2004.Examples

open Data.Examples

def amount_yori : LinguisticExample :=
  { id := "beckodasugisaki2004_amount_yori"
    source := ⟨"beck-oda-sugisaki-2004", "(3-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa [Hanako-ga katta yori (mo)] takusan(-no) kasa-o katta"
    discourseSegments := []
    glossedTokens := []
    translation := "Taroo bought more umbrellas than Hanako did"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "amount_comparative"), ("standard_requires_degree_abstraction", "false")]
    comment := "Amount yori-comparative; judgment from Ishii 1991. Gloss: Taroo-Top [Hanako-Nom bought YORI (mo)] many(-Gen) umbrella-Acc bought."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def degree_yori : LinguisticExample :=
  { id := "beckodasugisaki2004_degree_yori"
    source := ⟨"beck-oda-sugisaki-2004", "(4-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "?Taroo-wa [Hanako-ga katta yori (mo)] nagai kasa-o katta"
    discourseSegments := []
    glossedTokens := []
    translation := "Taroo bought a longer umbrella than Hanako did"
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degree_comparative"), ("standard_requires_degree_abstraction", "false")]
    comment := "Degree yori-comparative: Ishii 1991 reports ?*; the authors' consultants range from ? to ??. The variability itself is an explanandum for the contextual analysis."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def subcomp_ja : LinguisticExample :=
  { id := "beckodasugisaki2004_subcomp_ja"
    source := ⟨"beck-oda-sugisaki-2004", "(5-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "*Kono tana-wa [ano doa-ga hiroi yori (mo)] (motto) takai"
    discourseSegments := []
    glossedTokens := []
    translation := "This shelf is taller than that door is wide"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "subcomparative"), ("standard_requires_degree_abstraction", "true")]
    comment := "Japanese lacks subcomparatives (observed by Snyder, Wexler & Das 1995). Gloss: this shelf-Top [that door-Nom wide YORI (mo)] (more) tall."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def subcomp_en : LinguisticExample :=
  { id := "beckodasugisaki2004_subcomp_en"
    source := ⟨"beck-oda-sugisaki-2004", "(5-b), p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This shelf is taller than that door is wide"
    discourseSegments := []
    glossedTokens := []
    translation := "This shelf is taller than that door is wide"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "subcomparative"), ("standard_requires_degree_abstraction", "true")]
    comment := "English subcomparative control for (5-a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def negisland_ja : LinguisticExample :=
  { id := "beckodasugisaki2004_negisland_ja"
    source := ⟨"beck-oda-sugisaki-2004", "(6-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa [dare-mo kawa-naka-tta no yori] takai hon-o katta"
    discourseSegments := []
    glossedTokens := []
    translation := "John bought a book that is more expensive than the book that nobody bought"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative_island"), ("standard_requires_degree_abstraction", "false")]
    comment := "Well-formed, with the individual-comparing interpretation of the paper's (6'): the yori-clause denotes the (unique) book nobody bought, not a degree set. Gloss: John-Top [anyone buy-Neg-Past NO YORI] expensive book-Acc bought."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def negisland_en : LinguisticExample :=
  { id := "beckodasugisaki2004_negisland_en"
    source := ⟨"beck-oda-sugisaki-2004", "(6-b), p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*John bought a more expensive book than nobody did"
    discourseSegments := []
    glossedTokens := []
    translation := "*John bought a more expensive book than nobody did"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative_island"), ("standard_requires_degree_abstraction", "true")]
    comment := "English negative-island effect: no maximal degree such that nobody bought a that-expensive book (Rullmann 1995 undefinedness)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [amount_yori, degree_yori, subcomp_ja, subcomp_en, negisland_ja, negisland_en]

end BeckOdaSugisaki2004.Examples
