import Linglib.Data.Examples.Schema

/-!
# `Geurts2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Geurts2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Geurts2005.Examples`.
-/

namespace Geurts2005.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "geurts2005_1a"
    source := ⟨"geurts-2005", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may do this or (else) you may do that."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "may"), ("flavor", "deontic")]
    comment := "Both domains bound to the background; each alternative is possible."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "geurts2005_1b"
    source := ⟨"geurts-2005", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must do this or (else) you must do that."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "must"), ("flavor", "deontic")]
    comment := "The domains partition the background; neither disjunct follows on its own."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1c : LinguisticExample :=
  { id := "geurts2005_1c"
    source := ⟨"geurts-2005", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may do this or (else) you must do that."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "must"), ("flavor", "deontic")]
    comment := "The second, universal domain is the background minus the first disjunct's content."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1d : LinguisticExample :=
  { id := "geurts2005_1d"
    source := ⟨"geurts-2005", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?You must do this or (else) you may do that."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "may"), ("flavor", "deontic")]
    comment := "The first, universal domain is the background minus the second disjunct's content: a forward dependence, awkward like forward reference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a : LinguisticExample :=
  { id := "geurts2005_2a"
    source := ⟨"geurts-2005", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It may be here or (else) it may be there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "may"), ("flavor", "epistemic")]
    comment := "Both domains bound to the background; each alternative is possible."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2b : LinguisticExample :=
  { id := "geurts2005_2b"
    source := ⟨"geurts-2005", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be here or (else) it must be there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "must"), ("flavor", "epistemic")]
    comment := "The domains partition the background; neither disjunct follows on its own."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2c : LinguisticExample :=
  { id := "geurts2005_2c"
    source := ⟨"geurts-2005", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It may be here or (else) it must be there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "must"), ("flavor", "epistemic")]
    comment := "The second, universal domain is the background minus the first disjunct's content."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2d : LinguisticExample :=
  { id := "geurts2005_2d"
    source := ⟨"geurts-2005", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?It must be here or (else) it may be there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "may"), ("flavor", "epistemic")]
    comment := "The first, universal domain is the background minus the second disjunct's content: a forward dependence, awkward like forward reference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_1c, ex_1d, ex_2a, ex_2b, ex_2c, ex_2d]

end Geurts2005.Examples
