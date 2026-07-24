import Linglib.Data.Examples.Schema

/-!
# `Svenonius2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Svenonius2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Svenonius2004.Examples`.
-/

namespace Svenonius2004.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "svenonius2004_1a"
    source := ⟨"svenonius-2004", "(1a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Helder za-brosil mjač v vorota angličan."
    discourseSegments := []
    glossedTokens := [("Helder", "Helder"), ("za-brosil", "into-threw"), ("mjač", "ball"), ("v", "in"), ("vorota", "goal"), ("angličan", "English")]
    translation := "Helder kicked the ball into the English goal."
    context := "Spatial-resultative za-: the goal is the endpoint of the ball's path."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "First member of the (1a)/(1c) minimal pair on za-: transparently spatial (lexical) use."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_1b : LinguisticExample :=
  { id := "svenonius2004_1b"
    source := ⟨"svenonius-2004", "(1b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "David sovsem za-brosil futbol."
    discourseSegments := []
    glossedTokens := [("David", "David"), ("sovsem", "completely"), ("za-brosil", "into-threw"), ("futbol", "soccer")]
    translation := "David completely gave up soccer."
    context := "Idiomatic use of the same lexical za- as in the spatial (1a): idiosyncratic meaning is available to lexical prefixes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Lexical za- with idiomatic meaning 'give up' — lexical idiosyncrasy contrasts with the systematic meanings of superlexicals (his (56e))."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_1c : LinguisticExample :=
  { id := "svenonius2004_1c"
    source := ⟨"svenonius-2004", "(1c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ricardo nervno za-brosal mjač."
    discourseSegments := []
    glossedTokens := [("Ricardo", "Ricardo"), ("nervno", "nervously"), ("za-brosal", "incp-threw"), ("mjač", "ball")]
    translation := "Ricardo began to nervously throw the ball."
    context := "Inceptive (superlexical) za- on the imperfective stem brosat', versus the lexical za- of (1a)/(1b) on perfective brosit'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Second member of the (1a)/(1c) minimal pair: same prefix form, superlexical inceptive class."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_4a : LinguisticExample :=
  { id := "svenonius2004_4a"
    source := ⟨"svenonius-2004", "(4a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "po-vy-brasyvatj"
    discourseSegments := []
    glossedTokens := [("po-vy-brasyvatj", "dstr-out-throw")]
    translation := "throw out one by one"
    context := "Superlexical distributive po- stacked outside lexical vy- on the secondary-imperfective stem brasyvatj."
    judgment := .acceptable
    alternatives := [("vy-po-brasyvatj", .ungrammatical)]
    readings := []
    paperFeatures := []
    comment := "His (4a) with the reversed order (4b) *vy-po-brasyvatj: the superlexical prefix always appears outside the lexical prefix."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_4c : LinguisticExample :=
  { id := "svenonius2004_4c"
    source := ⟨"svenonius-2004", "(4c)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "po-w-chodzili"
    discourseSegments := []
    glossedTokens := [("po-w-chodzili", "dstr-in-walk")]
    translation := "walk in one by one"
    context := "Polish counterpart of (4a): superlexical distributive po- outside lexical w-."
    judgment := .acceptable
    alternatives := [("w-po-chodzili", .ungrammatical)]
    readings := []
    paperFeatures := []
    comment := "Attributed by Svenonius to Jabłońska 2004; not locatable as a numbered example in her paper. Reversed order (4d) *w-po-chodzili is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_3a : LinguisticExample :=
  { id := "svenonius2004_3a"
    source := ⟨"istratkova-2004", "§4 (kaža table)"⟩
    reportedIn := some ⟨"svenonius-2004", "(3a)"⟩
    language := "bulg1262"
    primaryText := "po-na-razkaža"
    discourseSegments := []
    glossedTokens := [("po-na-razkaža", "dlmt-cmlt-narrate")]
    translation := "tell a little of many"
    context := "Two superlexical prefixes stacked on the quantized perfective stem razkaža 'narrate'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Svenonius glosses the outer po- DLMT; on Istratkova's own taxonomy the po- that stacks over na- is her attenuative po- (her (23c)), her delimitative po- does not stack."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_3e : LinguisticExample :=
  { id := "svenonius2004_3e"
    source := ⟨"istratkova-2004", "§4 (kaža table)"⟩
    reportedIn := some ⟨"svenonius-2004", "(3e)"⟩
    language := "bulg1262"
    primaryText := "iz-po-na-pre-razkaža"
    discourseSegments := []
    glossedTokens := [("iz-po-na-pre-razkaža", "cmpl-dstr-cmlt-rpet-narrate")]
    translation := "renarrate completely one by one, of many"
    context := "Four superlexical prefixes stacked on the quantized perfective stem razkaža 'narrate'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "The deepest razkaža stack Svenonius cites from Istratkova's data; the po- after iz- is her distributive po-."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_58za : LinguisticExample :=
  { id := "svenonius2004_58za"
    source := ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "za-kuritj"
    discourseSegments := []
    glossedTokens := [("za-kuritj", "incp-smoke")]
    translation := "start smoking"
    context := "Inceptive za- almost never forms secondary imperfectives in Russian."
    judgment := .acceptable
    alternatives := [("za-kurivatj", .ungrammatical)]
    readings := []
    paperFeatures := []
    comment := "Datum for his (58a-i): inceptive za- blocks secondary imperfectivization, consistent with attachment above the SI position."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_58po : LinguisticExample :=
  { id := "svenonius2004_58po"
    source := ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "po-čitatj"
    discourseSegments := []
    glossedTokens := [("po-čitatj", "atten-read")]
    translation := "read for a little while"
    context := "Attenuative po- generally resists secondary imperfectivization but sometimes allows it."
    judgment := .acceptable
    alternatives := [("po-čityvatj", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Datum for his (58b): attenuative po- sometimes allows the secondary imperfective (po-čityvatj), unlike inceptive za-."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_1c, ex_4a, ex_4c, ex_3a, ex_3e, ex_58za, ex_58po]

end Svenonius2004.Examples
