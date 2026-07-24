import Linglib.Data.Examples.Schema

/-!
# `Istratkova2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Istratkova2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Istratkova2004.Examples`.
-/

namespace Istratkova2004.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "istratkova2004_1a"
    source := ⟨"istratkova-2004", "(1a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "za-piša"
    discourseSegments := []
    glossedTokens := []
    translation := "put down in writing"
    context := "Lexical za- on the simplex homogeneous verb piša 'write' (her (2f)); the derived verb is perfective, paired with secondary imperfective za-pis-va-m."
    judgment := .acceptable
    alternatives := [("za-pis-va-m", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Her (1) derivational-pattern table; citation forms are 1sg present (Bulgarian has no infinitive)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "istratkova2004_3a"
    source := ⟨"istratkova-2004", "(3a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "iz-misl'a"
    discourseSegments := []
    glossedTokens := []
    translation := "make up (a story)"
    context := "Lexical iz- with idiosyncratic meaning shift on the homogeneous simplex misl'a 'think' (her (2a)); paired with secondary imperfective iz-misl'-a-m."
    judgment := .acceptable
    alternatives := [("iz-misl'-a-m", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Her (3) pairs table: prefixation quantizes a homogeneous verb, which then comes in a perfective-imperfective pair."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "istratkova2004_3b"
    source := ⟨"istratkova-2004", "(3b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "za-običam"
    discourseSegments := []
    glossedTokens := []
    translation := "start to love"
    context := "Inceptive za- ('to begin' in her prefix taxonomy) on the homogeneous simplex običam 'love' (her (2b)); paired with za-obič-va-m."
    judgment := .acceptable
    alternatives := [("za-obič-va-m", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Compositional inceptive reading — a superlexical use of za-."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3c : LinguisticExample :=
  { id := "istratkova2004_3c"
    source := ⟨"istratkova-2004", "(3c)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "po-znam"
    discourseSegments := []
    glossedTokens := []
    translation := "guess"
    context := "po- on the homogeneous simplex znam 'know' (her (2c)) with fully idiosyncratic meaning; paired with po-zna-va-m."
    judgment := .acceptable
    alternatives := [("po-zna-va-m", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "The idiosyncratic meaning ('know' to 'guess') fits Svenonius's lexicality diagnostic (his (56e)); her table assigns no superlexical label."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3d : LinguisticExample :=
  { id := "istratkova2004_3d"
    source := ⟨"istratkova-2004", "(3d)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "za-blest'a"
    discourseSegments := []
    glossedTokens := []
    translation := "start to glitter"
    context := "Inceptive za- on the homogeneous simplex blest'a 'glitter' (her (2d)); paired with za-blet'-ava-m."
    judgment := .acceptable
    alternatives := [("za-blet'-ava-m", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Compositional inceptive reading — a superlexical use of za-."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3i : LinguisticExample :=
  { id := "istratkova2004_3i"
    source := ⟨"istratkova-2004", "(3i)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "pro-četa"
    discourseSegments := []
    glossedTokens := []
    translation := "read completely"
    context := "pro- on the homogeneous simplex četa 'read' (her (2h)), yielding the default perfectivization; paired with pro-čit-a-m."
    judgment := .acceptable
    alternatives := [("pro-čit-a-m", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "pro- is not in her superlexical prefix inventory — a lexical (quantizing) prefix."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22b : LinguisticExample :=
  { id := "istratkova2004_22b"
    source := ⟨"istratkova-2004", "(22b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "iz-po-na-pro-dam"
    discourseSegments := []
    glossedTokens := []
    translation := "completely sell (a lot) one by one"
    context := "Three superlexical prefixes (completive iz-, distributive po-, cumulative na-) stacked outside the lexical pro- on dam 'give' (pro-dam 'sell')."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "The po- here is her distributive po-, which only occurs after iz-."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23c : LinguisticExample :=
  { id := "istratkova2004_23c"
    source := ⟨"istratkova-2004", "(23c)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "po-na-pro-dam"
    discourseSegments := []
    glossedTokens := []
    translation := "sell a few things"
    context := "Attenuative po- over cumulative na- over lexical pro- on dam 'give': po- modifies the meaning of na- so that the verb means selling a few."
    judgment := .acceptable
    alternatives := [("na-pro-dam", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Her (23c) pair na-pro-dam 'sell a lot' vs po-na-prodam 'sell a few things': the stacking po- over na- is the attenuative po-."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_3a, ex_3b, ex_3c, ex_3d, ex_3i, ex_22b, ex_23c]

end Istratkova2004.Examples
