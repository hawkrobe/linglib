module

public import Linglib.Data.Examples.Schema

/-!
# `Scontras2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Scontras2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Scontras2014.Examples`.
-/

@[expose] public section

namespace Scontras2014.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "scontras2014_ex1"
    source := ⟨"scontras-2014", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Four grains of that water"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "selection")] }

def ex2a : LinguisticExample :=
  { id := "scontras2014_ex2a"
    source := ⟨"scontras-2014", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I bought every pound of rice from that store"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "pound"), ("nounClass", "measureTerm"), ("diagnostic", "quantifier")] }

def ex2b : LinguisticExample :=
  { id := "scontras2014_ex2b"
    source := ⟨"scontras-2014", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most liters of wine in this tank are polluted"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "quantifier")] }

def ex3 : LinguisticExample :=
  { id := "scontras2014_ex3"
    source := ⟨"scontras-2014", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I bought every grain of rice in that store"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "quantifier")] }

def ex4a : LinguisticExample :=
  { id := "scontras2014_ex4a"
    source := ⟨"scontras-2014", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I bought two beautiful slices of pizza"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "slice"), ("nounClass", "atomizer"), ("diagnostic", "modifier")] }

def ex4b : LinguisticExample :=
  { id := "scontras2014_ex4b"
    source := ⟨"scontras-2014", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I bought two beautiful pounds of pizza"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "pound"), ("nounClass", "measureTerm"), ("diagnostic", "modifier")] }

def ex10a : LinguisticExample :=
  { id := "scontras2014_ex10a"
    source := ⟨"scontras-2014", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three bucketfuls of mud were standing in a row against the wall"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bucket"), ("nounClass", "containerNoun"), ("diagnostic", "-ful"), ("reading", "container")] }

def ex10b : LinguisticExample :=
  { id := "scontras2014_ex10b"
    source := ⟨"scontras-2014", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We needed three bucketfuls of cement to build that wall"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bucket"), ("nounClass", "containerNoun"), ("diagnostic", "-ful"), ("reading", "measure")] }

def ex11a : LinguisticExample :=
  { id := "scontras2014_ex11a"
    source := ⟨"scontras-2014", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three literfuls of mud were standing in a row against the wall"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "-ful"), ("reading", "container")] }

def ex11b : LinguisticExample :=
  { id := "scontras2014_ex11b"
    source := ⟨"scontras-2014", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We needed three literfuls of cement to build that wall"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "-ful"), ("reading", "measure")] }

def ex12a : LinguisticExample :=
  { id := "scontras2014_ex12a"
    source := ⟨"scontras-2014", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three grainfuls of rice were standing in a row against the wall"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "-ful"), ("reading", "atomizing")] }

def ex12b : LinguisticExample :=
  { id := "scontras2014_ex12b"
    source := ⟨"scontras-2014", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We needed three grainfuls of rice to build that wall"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "-ful"), ("reading", "atomizing")] }

def ex13a : LinguisticExample :=
  { id := "scontras2014_ex13a"
    source := ⟨"scontras-2014", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two cups of wine on this tray. They are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "cup"), ("nounClass", "containerNoun"), ("diagnostic", "they"), ("reading", "container")] }

def ex13b : LinguisticExample :=
  { id := "scontras2014_ex13b"
    source := ⟨"scontras-2014", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two cups of wine in this soup. They are blue."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "cup"), ("nounClass", "containerNoun"), ("diagnostic", "they"), ("reading", "measure")] }

def ex14a : LinguisticExample :=
  { id := "scontras2014_ex14a"
    source := ⟨"scontras-2014", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two liters of wine on this tray. They are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "they"), ("reading", "container")] }

def ex14b : LinguisticExample :=
  { id := "scontras2014_ex14b"
    source := ⟨"scontras-2014", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two liters of wine in this soup. They are blue."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "they"), ("reading", "measure")] }

def ex15a : LinguisticExample :=
  { id := "scontras2014_ex15a"
    source := ⟨"scontras-2014", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two grains of rice on this tray. They are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "they"), ("reading", "atomizing")] }

def ex15b : LinguisticExample :=
  { id := "scontras2014_ex15b"
    source := ⟨"scontras-2014", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two grains of rice in this soup. They are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "they"), ("reading", "atomizing")] }

def ex16a : LinguisticExample :=
  { id := "scontras2014_ex16a"
    source := ⟨"scontras-2014", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is two cups of wine on this tray"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "cup"), ("nounClass", "containerNoun"), ("diagnostic", "singularAgreement"), ("reading", "container")] }

def ex16b : LinguisticExample :=
  { id := "scontras2014_ex16b"
    source := ⟨"scontras-2014", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is two cups of wine in this soup"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "cup"), ("nounClass", "containerNoun"), ("diagnostic", "singularAgreement"), ("reading", "measure")] }

def ex17a : LinguisticExample :=
  { id := "scontras2014_ex17a"
    source := ⟨"scontras-2014", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is two liters of wine on this tray"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "singularAgreement"), ("reading", "container")] }

def ex17b : LinguisticExample :=
  { id := "scontras2014_ex17b"
    source := ⟨"scontras-2014", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is two liters of wine in this soup"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "singularAgreement"), ("reading", "measure")] }

def ex18a : LinguisticExample :=
  { id := "scontras2014_ex18a"
    source := ⟨"scontras-2014", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is two grains of rice on this tray"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "singularAgreement"), ("reading", "atomizing")] }

def ex18b : LinguisticExample :=
  { id := "scontras2014_ex18b"
    source := ⟨"scontras-2014", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is two grains of rice in this soup"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "singularAgreement"), ("reading", "atomizing")] }

def ex19a : LinguisticExample :=
  { id := "scontras2014_ex19a"
    source := ⟨"scontras-2014", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The two cups of wine cost 2 euros each"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "cup"), ("nounClass", "containerNoun"), ("diagnostic", "each"), ("reading", "container")] }

def ex19b : LinguisticExample :=
  { id := "scontras2014_ex19b"
    source := ⟨"scontras-2014", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The two cups of wine in this soup cost 2 euros each"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "cup"), ("nounClass", "containerNoun"), ("diagnostic", "each"), ("reading", "measure")] }

def ex20a : LinguisticExample :=
  { id := "scontras2014_ex20a"
    source := ⟨"scontras-2014", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The two liters of wine cost 2 euros each"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "each"), ("reading", "container")] }

def ex20b : LinguisticExample :=
  { id := "scontras2014_ex20b"
    source := ⟨"scontras-2014", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The two liters of wine in this soup cost 2 euros each"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "liter"), ("nounClass", "measureTerm"), ("diagnostic", "each"), ("reading", "measure")] }

def ex21a : LinguisticExample :=
  { id := "scontras2014_ex21a"
    source := ⟨"scontras-2014", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The two grains of rice cost 2 euros each"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "each"), ("reading", "atomizing")] }

def ex21b : LinguisticExample :=
  { id := "scontras2014_ex21b"
    source := ⟨"scontras-2014", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The two grains of rice in this soup cost 2 euros each"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "each"), ("reading", "atomizing")] }

def ex62 : LinguisticExample :=
  { id := "scontras2014_ex62"
    source := ⟨"scontras-2014", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There were three grains on the floor"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grain"), ("nounClass", "atomizer"), ("diagnostic", "intransitive")] }

def ex80a : LinguisticExample :=
  { id := "scontras2014_ex80a"
    source := ⟨"scontras-2014", "(80a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alan found three quantities of rice on the floor"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "quantity"), ("nounClass", "atomizer"), ("diagnostic", "selection"), ("reading", "atomizing")] }

def ex80b : LinguisticExample :=
  { id := "scontras2014_ex80b"
    source := ⟨"scontras-2014", "(80b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill carried three quantities of water into the other room"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "quantity"), ("nounClass", "atomizer"), ("diagnostic", "selection"), ("reading", "atomizing")] }

def ex80c : LinguisticExample :=
  { id := "scontras2014_ex80c"
    source := ⟨"scontras-2014", "(80c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Charlie bought three quantities of apples from the farm stand"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "quantity"), ("nounClass", "atomizer"), ("diagnostic", "selection"), ("reading", "atomizing")] }

def all : List LinguisticExample := [ex1, ex2a, ex2b, ex3, ex4a, ex4b, ex10a, ex10b, ex11a, ex11b, ex12a, ex12b, ex13a, ex13b, ex14a, ex14b, ex15a, ex15b, ex16a, ex16b, ex17a, ex17b, ex18a, ex18b, ex19a, ex19b, ex20a, ex20b, ex21a, ex21b, ex62, ex80a, ex80b, ex80c]

end Scontras2014.Examples
