import Linglib.Data.Examples.Schema

/-!
# `GinzburgCooper2004` — typed example data

Auto-generated from `Linglib/Data/Examples/GinzburgCooper2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GinzburgCooper2004.Examples`.
-/

namespace GinzburgCooper2004.Examples

open Data.Examples

def ex_4a_bo : LinguisticExample :=
  { id := "ginzburgcooper2004_4a_bo"
    source := ⟨"ginzburg-cooper-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo finagle a raise? B: Bo?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "Bo"), ("antecedentCat", "NP"), ("fragment", "Bo"), ("fragmentCat", "NP"), ("access", "shared")]
    comment := "Clausal: are you asking if BO (of all people) finagled a raise? Constituent: who is Bo?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a_finagle : LinguisticExample :=
  { id := "ginzburgcooper2004_4a_finagle"
    source := ⟨"ginzburg-cooper-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo finagle a raise? B: Finagle?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "finagle"), ("antecedentCat", "V[bse]"), ("fragment", "Finagle"), ("fragmentCat", "V[bse]"), ("access", "shared")]
    comment := "Clausal: are you asking if Bo FINAGLED a raise (of all actions)? Constituent: what does it mean to finagle?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6a : LinguisticExample :=
  { id := "ginzburgcooper2004_6a"
    source := ⟨"ginzburg-cooper-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "George: you always had er er say every foot he had with a piece of spunyarn in the wire. Anon1: Spunyarn? George: Spunyarn, yes. Anon1: What's spunyarn? George: Well that's like er tarred rope."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "British National Corpus, file H5G, sentences 193–196."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "spunyarn"), ("antecedentCat", "N"), ("fragment", "Spunyarn"), ("fragmentCat", "N"), ("access", "shared")]
    comment := "George answers the clausal reading; Anon1 intended the constituent one and asks it non-elliptically."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a : LinguisticExample :=
  { id := "ginzburgcooper2004_8a"
    source := ⟨"ginzburg-cooper-2004", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: My cousin?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "Bo"), ("antecedentCat", "NP"), ("fragment", "My cousin"), ("fragmentCat", "NP"), ("access", "shared")]
    comment := "Clausal: are you asking if my cousin of all people left? Constituent: when you say Bo, are you referring to my cousin?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8b : LinguisticExample :=
  { id := "ginzburgcooper2004_8b"
    source := ⟨"ginzburg-cooper-2004", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did she annoy Bo? B: Sue?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "she"), ("antecedentCat", "NP"), ("fragment", "Sue"), ("fragmentCat", "NP"), ("access", "shared")]
    comment := "Clausal: are you asking if Sue of all people annoyed Bo? Constituent: when you say she, are you referring to Sue?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8c : LinguisticExample :=
  { id := "ginzburgcooper2004_8c"
    source := ⟨"ginzburg-cooper-2004", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did you bike to work yesterday? B: Cycle?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "bike"), ("antecedentCat", "V[bse]"), ("fragment", "Cycle"), ("fragmentCat", "V[bse]"), ("access", "shared")]
    comment := "Clausal: are you asking if I, of all things, cycled to work yesterday? Constituent: when you say bike, are you referring to the activity of cycling?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9a : LinguisticExample :=
  { id := "ginzburgcooper2004_9a"
    source := ⟨"ginzburg-cooper-2004", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: Who?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "Bo"), ("antecedentCat", "NP"), ("fragment", "Who"), ("fragmentCat", "NP"), ("access", "shared")]
    comment := "Clausal: who is it you are asking whether s/he left? Constituent: when you say Bo, who are you referring to?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a_him : LinguisticExample :=
  { id := "ginzburgcooper2004_10a_him"
    source := ⟨"ginzburg-cooper-2004", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I phoned him. B: Him?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "him"), ("antecedentCat", "NP[acc]"), ("fragment", "Him"), ("fragmentCat", "NP[acc]"), ("access", "shared")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a_he : LinguisticExample :=
  { id := "ginzburgcooper2004_10a_he"
    source := ⟨"ginzburg-cooper-2004", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I phoned him. B: He?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "him"), ("antecedentCat", "NP[acc]"), ("fragment", "He"), ("fragmentCat", "NP[nom]"), ("access", "shared")]
    comment := "Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10b_he : LinguisticExample :=
  { id := "ginzburgcooper2004_10b_he"
    source := ⟨"ginzburg-cooper-2004", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he phone you? B: He?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "he"), ("antecedentCat", "NP[nom]"), ("fragment", "He"), ("fragmentCat", "NP[nom]"), ("access", "shared")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10b_him : LinguisticExample :=
  { id := "ginzburgcooper2004_10b_him"
    source := ⟨"ginzburg-cooper-2004", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he phone you? B: Him?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "he"), ("antecedentCat", "NP[nom]"), ("fragment", "Him"), ("fragmentCat", "NP[acc]"), ("access", "shared")]
    comment := "Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10c_adore : LinguisticExample :=
  { id := "ginzburgcooper2004_10c_adore"
    source := ⟨"ginzburg-cooper-2004", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he adore the book? B: Adore?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "adore"), ("antecedentCat", "V[bse]"), ("fragment", "Adore"), ("fragmentCat", "V[bse]"), ("access", "shared")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10c_adored : LinguisticExample :=
  { id := "ginzburgcooper2004_10c_adored"
    source := ⟨"ginzburg-cooper-2004", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he adore the book? B: Adored?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "adore"), ("antecedentCat", "V[bse]"), ("fragment", "Adored"), ("fragmentCat", "V[fin]"), ("access", "shared")]
    comment := "Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10d_cycling : LinguisticExample :=
  { id := "ginzburgcooper2004_10d_cycling"
    source := ⟨"ginzburg-cooper-2004", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Were you cycling yesterday? B: Cycling?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "cycling"), ("antecedentCat", "V[prp]"), ("fragment", "Cycling"), ("fragmentCat", "V[prp]"), ("access", "shared")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10d_biking : LinguisticExample :=
  { id := "ginzburgcooper2004_10d_biking"
    source := ⟨"ginzburg-cooper-2004", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Were you cycling yesterday? B: Biking?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "cycling"), ("antecedentCat", "V[prp]"), ("fragment", "Biking"), ("fragmentCat", "V[prp]"), ("access", "shared")]
    comment := "A non-identical fragment of the same category."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10d_biked : LinguisticExample :=
  { id := "ginzburgcooper2004_10d_biked"
    source := ⟨"ginzburg-cooper-2004", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Were you cycling yesterday? B: Biked?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "cycling"), ("antecedentCat", "V[prp]"), ("fragment", "Biked"), ("fragmentCat", "V[psp]"), ("access", "shared")]
    comment := "Marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "ginzburgcooper2004_11"
    source := ⟨"ginzburg-cooper-2004", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Let's hold the conference here. B: Here?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A is located in Gothenburg, B in Hyderabad."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .unacceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "here"), ("antecedentCat", "AdvP"), ("fragment", "Here"), ("fragmentCat", "AdvP"), ("access", "distinct")]
    comment := "Only: what location are you talking about? Not: are you asking if we should hold the conference in Hyderabad of all places?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "ginzburgcooper2004_12"
    source := ⟨"ginzburg-cooper-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Let's hold the conference here. B: Here?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A and B are both located in Gothenburg."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "here"), ("antecedentCat", "AdvP"), ("fragment", "Here"), ("fragmentCat", "AdvP"), ("access", "shared")]
    comment := "Either: what location are you talking about? Or: are you asking if we should hold the conference in Gothenburg of all places?"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13a : LinguisticExample :=
  { id := "ginzburgcooper2004_13a"
    source := ⟨"ginzburg-cooper-2004", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Can I come in? B: I?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .unacceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "I"), ("antecedentCat", "NP[nom]"), ("fragment", "I"), ("fragmentCat", "NP[nom]"), ("access", "distinct")]
    comment := "Who is I, who are you? Cannot mean: am I asking if I of all people can come in."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_4a_bo, ex_4a_finagle, ex_6a, ex_8a, ex_8b, ex_8c, ex_9a, ex_10a_him, ex_10a_he, ex_10b_he, ex_10b_him, ex_10c_adore, ex_10c_adored, ex_10d_cycling, ex_10d_biking, ex_10d_biked, ex_11, ex_12, ex_13a]

end GinzburgCooper2004.Examples
