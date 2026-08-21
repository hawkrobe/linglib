import Linglib.Data.Examples.Schema

/-!
# `Myler2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Myler2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Myler2016.Examples`.
-/

namespace Myler2016.Examples

open Data.Examples

def concrete_hafa : LinguisticExample :=
  { id := "myler2016_concrete_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa stóra bók."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("stóra", "big"), ("bók", "book.ACC")]
    translation := "They have (own) a big book."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "clausal"), ("verb", "hafa")]
    comment := "Clausal possession, concrete relation, with hafa."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def concrete_eiga : LinguisticExample :=
  { id := "myler2016_concrete_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga stóra bók."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("stóra", "big"), ("bók", "book.ACC")]
    translation := "They have (own) a big book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "clausal"), ("verb", "eiga")]
    comment := "Clausal possession, concrete relation, with eiga."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def kinship_hafa : LinguisticExample :=
  { id := "myler2016_kinship_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa systur."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("systur", "sister.ACC")]
    translation := "They have a sister."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "clausal"), ("verb", "hafa")]
    comment := "Clausal possession, kinship relation, with hafa."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def kinship_eiga : LinguisticExample :=
  { id := "myler2016_kinship_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga systur."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("systur", "sister.ACC")]
    translation := "They have a sister."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "clausal"), ("verb", "eiga")]
    comment := "Clausal possession, kinship relation, with eiga."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def bodyPart_hafa : LinguisticExample :=
  { id := "myler2016_bodyPart_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa augu."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("augu", "eyes.ACC")]
    translation := "They have eyes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "clausal"), ("verb", "hafa")]
    comment := "Clausal possession, bodyPart relation, with hafa."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def bodyPart_eiga : LinguisticExample :=
  { id := "myler2016_bodyPart_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga augu."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("augu", "eyes.ACC")]
    translation := "They have eyes."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "clausal"), ("verb", "eiga")]
    comment := "Clausal possession, bodyPart relation, with eiga."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def abstract_hafa : LinguisticExample :=
  { id := "myler2016_abstract_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa ekki hugmynd."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("ekki", "not"), ("hugmynd", "idea.ACC")]
    translation := "They have no idea."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "clausal"), ("verb", "hafa")]
    comment := "Clausal possession, abstract relation, with hafa."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def abstract_eiga : LinguisticExample :=
  { id := "myler2016_abstract_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga ekki hugmynd."
    discourseSegments := []
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("ekki", "not"), ("hugmynd", "idea.ACC")]
    translation := "They have no idea."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "clausal"), ("verb", "eiga")]
    comment := "Clausal possession, abstract relation, with eiga."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def concrete_attrA : LinguisticExample :=
  { id := "myler2016_concrete_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "bók mín"
    discourseSegments := []
    glossedTokens := [("bók", "book"), ("mín", "my")]
    translation := "my book"
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "attributiveA")]
    comment := "Attributive possession, column A of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def concrete_attrB : LinguisticExample :=
  { id := "myler2016_concrete_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "bók-in mín"
    discourseSegments := []
    glossedTokens := [("bók-in", "book-DEF"), ("mín", "my")]
    translation := "my book"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "attributiveB")]
    comment := "Attributive possession, column B of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def concrete_attrC : LinguisticExample :=
  { id := "myler2016_concrete_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "bók-in hjá mér"
    discourseSegments := []
    glossedTokens := [("bók-in", "book-DEF"), ("hjá", "at"), ("mér", "me")]
    translation := "my book"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "attributiveC")]
    comment := "Attributive possession, column C of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def kinship_attrA : LinguisticExample :=
  { id := "myler2016_kinship_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "systir mín"
    discourseSegments := []
    glossedTokens := [("systir", "sister"), ("mín", "my")]
    translation := "my sister"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "attributiveA")]
    comment := "Attributive possession, column A of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def kinship_attrB : LinguisticExample :=
  { id := "myler2016_kinship_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "systir-in mín"
    discourseSegments := []
    glossedTokens := [("systir-in", "sister-DEF"), ("mín", "my")]
    translation := "my sister"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "attributiveB")]
    comment := "Attributive possession, column B of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def kinship_attrC : LinguisticExample :=
  { id := "myler2016_kinship_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "systir-in hjá mér"
    discourseSegments := []
    glossedTokens := [("systir-in", "sister-DEF"), ("hjá", "at"), ("mér", "me")]
    translation := "my sister"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "attributiveC")]
    comment := "Attributive possession, column C of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def bodyPart_attrA : LinguisticExample :=
  { id := "myler2016_bodyPart_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "augu mín"
    discourseSegments := []
    glossedTokens := [("augu", "eyes"), ("mín", "my")]
    translation := "my eyes"
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "attributiveA")]
    comment := "Attributive possession, column A of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def bodyPart_attrB : LinguisticExample :=
  { id := "myler2016_bodyPart_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "augu-n mín"
    discourseSegments := []
    glossedTokens := [("augu-n", "eyes-DEF"), ("mín", "my")]
    translation := "my eyes"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "attributiveB")]
    comment := "Attributive possession, column B of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def bodyPart_attrC : LinguisticExample :=
  { id := "myler2016_bodyPart_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "augu-n í mér"
    discourseSegments := []
    glossedTokens := [("augu-n", "eyes-DEF"), ("í", "in"), ("mér", "me")]
    translation := "my eyes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "attributiveC")]
    comment := "Attributive possession, column C of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def abstract_attrA : LinguisticExample :=
  { id := "myler2016_abstract_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hugmynd mín"
    discourseSegments := []
    glossedTokens := [("hugmynd", "idea"), ("mín", "my")]
    translation := "my idea"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveA")]
    comment := "Attributive possession, column A of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def abstract_attrB : LinguisticExample :=
  { id := "myler2016_abstract_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hugmynd-in mín"
    discourseSegments := []
    glossedTokens := [("hugmynd-in", "idea-DEF"), ("mín", "my")]
    translation := "my idea"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveB")]
    comment := "Attributive possession, column B of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def abstract_attrC : LinguisticExample :=
  { id := "myler2016_abstract_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hugmynd-in hjá mér"
    discourseSegments := []
    glossedTokens := [("hugmynd-in", "idea-DEF"), ("hjá", "at"), ("mér", "me")]
    translation := "my idea"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveC")]
    comment := "Attributive possession, column C of (92) (from Myler, Sigurðsson & Wood 2014); # is recorded as questionable, % as marginal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [concrete_hafa, concrete_eiga, kinship_hafa, kinship_eiga, bodyPart_hafa, bodyPart_eiga, abstract_hafa, abstract_eiga, concrete_attrA, concrete_attrB, concrete_attrC, kinship_attrA, kinship_attrB, kinship_attrC, bodyPart_attrA, bodyPart_attrB, bodyPart_attrC, abstract_attrA, abstract_attrB, abstract_attrC]

end Myler2016.Examples
