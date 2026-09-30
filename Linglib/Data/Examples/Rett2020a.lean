module

public import Linglib.Data.Examples.Schema

/-!
# `Rett2020a` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2020a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2020a.Examples`.
-/

@[expose] public section

namespace Rett2020a.Examples

open Data.Examples

def ex_9 : Datum :=
  { id := "rett2020a_9"
    source := ⟨"rett-2020a", "(9)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Nakilala ni-Mary si-John bago siya um-akyat sa bundok."
    glossedTokens := [("Nakilala", "PFV.TV-meet"), ("ni-Mary", "GEN-Mary"), ("si-John", "SUBJ-John"), ("bago", "before"), ("siya", "SUBJ.3SG"), ("um-akyat", "PFV.AV-climb"), ("sa", "OBL"), ("bundok", "mountain")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-start", .acceptable), ("before-finish", .unacceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination")] }

def ex_10 : Datum :=
  { id := "rett2020a_10"
    source := ⟨"rett-2020a", "(10)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mary hat John getroffen, nachdem er Single war."
    glossedTokens := [("Mary", "Mary"), ("hat", "had-3SG"), ("John", "John"), ("getroffen,", "met"), ("nachdem", "after"), ("er", "he"), ("Single", "single"), ("war.", "was-3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("after-finish", .acceptable), ("after-start", .unacceptable)]
    paperFeatures := [("construction", "after"), ("embedded", "process")] }

def ex_11a : Datum :=
  { id := "rett2020a_11a"
    source := ⟨"rett-2020a", "(11a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Mary je srela Johna pre nego što se peo na vrh planine."
    glossedTokens := [("Mary", "Mary-NOM"), ("je", "is-PRES-3FS"), ("srela", "met-PP-3FS"), ("Johna", "John-ACC"), ("pre", "before"), ("nego", "than"), ("što", "PTCL"), ("se", "REFL"), ("peo", "climb-IMP-3MS"), ("na", "on"), ("vrh", "top-ACC"), ("planine.", "mountain-GEN")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := [("before-start", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "imperfective")] }

def ex_11b : Datum :=
  { id := "rett2020a_11b"
    source := ⟨"rett-2020a", "(11b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Mary je srela Johna pre nego što se popeo na vrh planine."
    glossedTokens := [("Mary", "Mary-NOM"), ("je", "is-PRES-3FS"), ("srela", "met-PP-3FS"), ("Johna", "John-ACC"), ("pre", "before"), ("nego", "than"), ("što", "PTCL"), ("se", "REFL"), ("popeo", "climb-PP-3MS"), ("na", "on"), ("vrh", "top-ACC"), ("planine.", "mountain-GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "perfective")] }

def ex_12a : Datum :=
  { id := "rett2020a_12a"
    source := ⟨"rett-2020a", "(12a)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Um-alis siya bago niya w<in>alis-an ang-sahig."
    glossedTokens := [("Um-alis", "AV.PFV.NEUT-leave"), ("siya", "SUBJ.3SG"), ("bago", "before"), ("niya", "NON.SUBJ.3SG"), ("w<in>alis-an", "PFV.NEUT-sweep-LV"), ("ang-sahig.", "SUBJ-floor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-start", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "pfv.neut")] }

def ex_12b : Datum :=
  { id := "rett2020a_12b"
    source := ⟨"rett-2020a", "(12b)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Um-alis siya bago niya na-walis-an ang-sahig."
    glossedTokens := [("Um-alis", "AV.PFV.NEUT-leave"), ("siya", "SUBJ.3SG"), ("bago", "before"), ("niya", "NON.SUBJ.3SG"), ("na-walis-an", "PFV.AIA-sweep-LV"), ("ang-sahig.", "SUBJ-floor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "aia")] }

def all : List Datum := [ex_9, ex_10, ex_11a, ex_11b, ex_12a, ex_12b]

end Rett2020a.Examples
