import Linglib.Data.Examples.Schema

/-!
# `Rett2020a` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2020a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2020a.Examples`.
-/

namespace Rett2020a.Examples

open Data.Examples

def ex_9 : LinguisticExample :=
  { id := "rett2020a_9"
    source := ⟨"rett-2020a", "(9)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Nakilala ni-Mary si-John bago siya um-akyat sa bundok."
    discourseSegments := []
    glossedTokens := [("Nakilala", "PFV.TV-meet"), ("ni-Mary", "GEN-Mary"), ("si-John", "SUBJ-John"), ("bago", "before"), ("siya", "SUBJ.3SG"), ("um-akyat", "PFV.AV-climb"), ("sa", "OBL"), ("bundok", "mountain")]
    translation := "Mary met John before he climbed to the top of the mountain."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-start", .acceptable), ("before-finish", .unacceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination")]
    comment := "Unambiguously read against the onset; Dutch, Hungarian and Italian consultants report the same."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_10 : LinguisticExample :=
  { id := "rett2020a_10"
    source := ⟨"rett-2020a", "(10)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mary hat John getroffen, nachdem er Single war."
    discourseSegments := []
    glossedTokens := [("Mary", "Mary"), ("hat", "had-3SG"), ("John", "John"), ("getroffen,", "met"), ("nachdem", "after"), ("er", "he"), ("Single", "single"), ("war.", "was-3SG")]
    translation := "Mary met John after he was single."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("after-finish", .acceptable), ("after-start", .unacceptable)]
    paperFeatures := [("construction", "after"), ("embedded", "process")]
    comment := "Unambiguously read against the end; Turkish consultants report the same."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_11a : LinguisticExample :=
  { id := "rett2020a_11a"
    source := ⟨"rett-2020a", "(11a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Mary je srela Johna pre nego što se peo na vrh planine."
    discourseSegments := []
    glossedTokens := [("Mary", "Mary-NOM"), ("je", "is-PRES-3FS"), ("srela", "met-PP-3FS"), ("Johna", "John-ACC"), ("pre", "before"), ("nego", "than"), ("što", "PTCL"), ("se", "REFL"), ("peo", "climb-IMP-3MS"), ("na", "on"), ("vrh", "top-ACC"), ("planine.", "mountain-GEN")]
    translation := "Mary met John before he climbed to the top of the mountain."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := [("before-start", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "imperfective")]
    comment := "Acceptable to the extent an imperfective is without an overt inchoative marker."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_11b : LinguisticExample :=
  { id := "rett2020a_11b"
    source := ⟨"rett-2020a", "(11b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Mary je srela Johna pre nego što se popeo na vrh planine."
    discourseSegments := []
    glossedTokens := [("Mary", "Mary-NOM"), ("je", "is-PRES-3FS"), ("srela", "met-PP-3FS"), ("Johna", "John-ACC"), ("pre", "before"), ("nego", "than"), ("što", "PTCL"), ("se", "REFL"), ("popeo", "climb-PP-3MS"), ("na", "on"), ("vrh", "top-ACC"), ("planine.", "mountain-GEN")]
    translation := "Mary met John before he climbed to the top of the mountain."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "perfective")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_12a : LinguisticExample :=
  { id := "rett2020a_12a"
    source := ⟨"rett-2020a", "(12a)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Um-alis siya bago niya w<in>alis-an ang-sahig."
    discourseSegments := []
    glossedTokens := [("Um-alis", "AV.PFV.NEUT-leave"), ("siya", "SUBJ.3SG"), ("bago", "before"), ("niya", "NON.SUBJ.3SG"), ("w<in>alis-an", "PFV.NEUT-sweep-LV"), ("ang-sahig.", "SUBJ-floor")]
    translation := "She left before he swept the floor."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-start", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "pfv.neut")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_12b : LinguisticExample :=
  { id := "rett2020a_12b"
    source := ⟨"rett-2020a", "(12b)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Um-alis siya bago niya na-walis-an ang-sahig."
    discourseSegments := []
    glossedTokens := [("Um-alis", "AV.PFV.NEUT-leave"), ("siya", "SUBJ.3SG"), ("bago", "before"), ("niya", "NON.SUBJ.3SG"), ("na-walis-an", "PFV.AIA-sweep-LV"), ("ang-sahig.", "SUBJ-floor")]
    translation := "She left before he swept the floor."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "aia")]
    comment := "The ability-and-involuntary-action perfective is the culminating one (Dell 1983)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_9, ex_10, ex_11a, ex_11b, ex_12a, ex_12b]

end Rett2020a.Examples
