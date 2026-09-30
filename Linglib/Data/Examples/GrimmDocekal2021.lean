module

public import Linglib.Data.Examples.Schema

/-!
# `GrimmDocekal2021` — typed example data

Auto-generated from `Linglib/Data/Examples/GrimmDocekal2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GrimmDocekal2021.Examples`.
-/

@[expose] public section

namespace GrimmDocekal2021.Examples

open Data.Examples

def ex_9b : LinguisticExample :=
  { id := "grimmdocekal2021_9b"
    source := ⟨"grimm-docekal-2021", "(9b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "list-í-mi"
    glossedTokens := [("list-í-mi", "leaf-í-INST.PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "derivedAggregate"), ("numeral", "none"), ("operation", "pluralization")] }

def ex_10a : LinguisticExample :=
  { id := "grimmdocekal2021_10a"
    source := ⟨"grimm-docekal-2021", "(10a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dva list-y"
    glossedTokens := [("dva", "CARD.Masc"), ("list-y", "leaf-Masc.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "simple"), ("operation", "simpleCardinal")] }

def ex_10b : LinguisticExample :=
  { id := "grimmdocekal2021_10b"
    source := ⟨"grimm-docekal-2021", "(10b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dvě list-í"
    glossedTokens := [("dvě", "CARD.Neut"), ("list-í", "leaf-í.Neut")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "derivedAggregate"), ("numeral", "simple"), ("operation", "simpleCardinal")] }

def ex_11 : LinguisticExample :=
  { id := "grimmdocekal2021_11"
    source := ⟨"grimm-docekal-2021", "(11)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "mnohé list-í už spadl-y"
    glossedTokens := [("mnohé", "many"), ("list-í", "leaf-í"), ("už", "already"), ("spadl-y", "fell-PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "derivedAggregate"), ("numeral", "none"), ("operation", "vagueQuantifier")] }

def ex_12 : LinguisticExample :=
  { id := "grimmdocekal2021_12"
    source := ⟨"grimm-docekal-2021", "(12)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "břízy a smrky shodil-y mnohé list-í"
    glossedTokens := [("břízy", "birches"), ("a", "and"), ("smrky", "spruces"), ("shodil-y", "shed-PL"), ("mnohé", "many"), ("list-í", "leaf-í")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "derivedAggregate"), ("numeral", "none"), ("operation", "packaging")] }

def ex_13a : LinguisticExample :=
  { id := "grimmdocekal2021_13a"
    source := ⟨"grimm-docekal-2021", "(13a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "stol-í"
    glossedTokens := [("stol-í", "table-í")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "none"), ("operation", "derivation")] }

def ex_13b : LinguisticExample :=
  { id := "grimmdocekal2021_13b"
    source := ⟨"grimm-docekal-2021", "(13b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "kabát-í"
    glossedTokens := [("kabát-í", "jacket-í")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "none"), ("operation", "derivation")] }

def ex_13c : LinguisticExample :=
  { id := "grimmdocekal2021_13c"
    source := ⟨"grimm-docekal-2021", "(13c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "planet-í"
    glossedTokens := [("planet-í", "planet-í")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "none"), ("operation", "derivation")] }

def ex_15b : LinguisticExample :=
  { id := "grimmdocekal2021_15b"
    source := ⟨"grimm-docekal-2021", "(15b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "troj-ice námořník-ů"
    glossedTokens := [("troj-ice", "three-ICE"), ("námořník-ů", "sailor-GEN.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "animate"), ("numeral", "group"), ("operation", "none")] }

def ex_17 : LinguisticExample :=
  { id := "grimmdocekal2021_17"
    source := ⟨"grimm-docekal-2021", "(17)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dvě troj-ice námořník-ů"
    glossedTokens := [("dvě", "two"), ("troj-ice", "three-ICE"), ("námořník-ů", "sailor-GEN.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "animate"), ("numeral", "group"), ("operation", "outerCardinal")] }

def ex_18 : LinguisticExample :=
  { id := "grimmdocekal2021_18"
    source := ⟨"grimm-docekal-2021", "(18)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "mnohé troj-ice námořník-ů"
    glossedTokens := [("mnohé", "many"), ("troj-ice", "three-ICE"), ("námořník-ů", "sailor-GEN.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "animate"), ("numeral", "group"), ("operation", "vagueQuantifier")] }

def ex_19 : LinguisticExample :=
  { id := "grimmdocekal2021_19"
    source := ⟨"grimm-docekal-2021", "(19)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechna troj-ice námořník-ů"
    glossedTokens := [("všechna", "all"), ("troj-ice", "three-ICE"), ("námořník-ů", "sailor-GEN.PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "animate"), ("numeral", "group"), ("operation", "universal")] }

def ex_20a : LinguisticExample :=
  { id := "grimmdocekal2021_20a"
    source := ⟨"grimm-docekal-2021", "(20a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dv-oje-Ø kart-y ležel-y na stole."
    glossedTokens := [("Dv-oje-Ø", "two-OJE-NOM.PL"), ("kart-y", "card-NOM.PL"), ("ležel-y", "lie-3PL"), ("na", "on"), ("stole", "table")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_20b : LinguisticExample :=
  { id := "grimmdocekal2021_20b"
    source := ⟨"grimm-docekal-2021", "(20b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-oje klíč-e"
    glossedTokens := [("dv-oje", "two-OJE"), ("klíč-e", "key-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_20c : LinguisticExample :=
  { id := "grimmdocekal2021_20c"
    source := ⟨"grimm-docekal-2021", "(20c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-oje bot-y"
    glossedTokens := [("dv-oje", "two-OJE"), ("bot-y", "shoe-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_20d : LinguisticExample :=
  { id := "grimmdocekal2021_20d"
    source := ⟨"grimm-docekal-2021", "(20d)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-oje schod-y"
    glossedTokens := [("dv-oje", "two-OJE"), ("schod-y", "stair-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_24a : LinguisticExample :=
  { id := "grimmdocekal2021_24a"
    source := ⟨"grimm-docekal-2021", "(24a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dvě kuchyně, dva nákupy, dvě lednice, dv-oje nádobí"
    glossedTokens := [("Dvě", "two"), ("kuchyně", "kitchens"), ("dva", "two"), ("nákupy", "purchases"), ("dvě", "two"), ("lednice", "refrigerators"), ("dv-oje", "two-oje"), ("nádobí", "dishes")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "derivedAggregate"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_24b : LinguisticExample :=
  { id := "grimmdocekal2021_24b"
    source := ⟨"grimm-docekal-2021", "(24b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dvě kávy, dv-oje hranolky"
    glossedTokens := [("dvě", "two"), ("kávy", "coffees"), ("dv-oje", "two-oje"), ("hranolky", "French.fries")]
    context := "fast-food order"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "none"), ("context", "portion")] }

def ex_24b_simple : LinguisticExample :=
  { id := "grimmdocekal2021_24b_simple"
    source := ⟨"grimm-docekal-2021", "(24b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dvě kávy, dvě hranolky"
    glossedTokens := [("dvě", "two"), ("kávy", "coffees"), ("dvě", "two"), ("hranolky", "French.fries")]
    context := "fast-food order"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "simple"), ("operation", "simpleCardinal"), ("context", "portion")] }

def ex_25a : LinguisticExample :=
  { id := "grimmdocekal2021_25a"
    source := ⟨"grimm-docekal-2021", "(25a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-oje stol-y"
    glossedTokens := [("dv-oje", "two-OJE"), ("stol-y", "table-PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_25b : LinguisticExample :=
  { id := "grimmdocekal2021_25b"
    source := ⟨"grimm-docekal-2021", "(25b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-oje kabát-y"
    glossedTokens := [("dv-oje", "two-OJE"), ("kabát-y", "jacket-PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_25c : LinguisticExample :=
  { id := "grimmdocekal2021_25c"
    source := ⟨"grimm-docekal-2021", "(25c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "šest-ery aut-a"
    glossedTokens := [("šest-ery", "six-ERY"), ("aut-a", "car-PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_26a : LinguisticExample :=
  { id := "grimmdocekal2021_26a"
    source := ⟨"grimm-docekal-2021", "(26a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechny dv-oje housl-e"
    glossedTokens := [("všechny", "DET"), ("dv-oje", "two-OJE"), ("housl-e", "violin-PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "pluraleTantum"), ("numeral", "aggregate"), ("operation", "universal")] }

def ex_26b : LinguisticExample :=
  { id := "grimmdocekal2021_26b"
    source := ⟨"grimm-docekal-2021", "(26b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechny dv-oje klíč-e"
    glossedTokens := [("všechny", "DET"), ("dv-oje", "two-OJE"), ("klíč-e", "key-PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "universal")] }

def ex_26c : LinguisticExample :=
  { id := "grimmdocekal2021_26c"
    source := ⟨"grimm-docekal-2021", "(26c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechny sedm-ery schod-y"
    glossedTokens := [("všechny", "DET"), ("sedm-ery", "seven-ERY"), ("schod-y", "stair-PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "universal")] }

def ex_27a : LinguisticExample :=
  { id := "grimmdocekal2021_27a"
    source := ⟨"grimm-docekal-2021", "(27a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "tři dv-oje klíč-e"
    glossedTokens := [("tři", "three"), ("dv-oje", "two-OJE"), ("klíč-e", "key-PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "outerCardinal")] }

def ex_27b : LinguisticExample :=
  { id := "grimmdocekal2021_27b"
    source := ⟨"grimm-docekal-2021", "(27b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "tři dv-oje dveř-e"
    glossedTokens := [("tři", "three"), ("dv-oje", "two-OJE"), ("dveř-e", "door-PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "pluraleTantum"), ("numeral", "aggregate"), ("operation", "outerCardinal")] }

def ex_27c : LinguisticExample :=
  { id := "grimmdocekal2021_27c"
    source := ⟨"grimm-docekal-2021", "(27c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "tři sedm-ery schod-y"
    glossedTokens := [("tři", "three"), ("sedm-ery", "seven-ERY"), ("schod-y", "stair-PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "multiple"), ("numeral", "aggregate"), ("operation", "outerCardinal")] }

def ex_28a : LinguisticExample :=
  { id := "grimmdocekal2021_28a"
    source := ⟨"grimm-docekal-2021", "(28a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-ojí život"
    glossedTokens := [("dv-ojí", "two-OJI"), ("život", "life")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "abstract"), ("numeral", "taxonomic"), ("operation", "none")] }

def ex_28b : LinguisticExample :=
  { id := "grimmdocekal2021_28b"
    source := ⟨"grimm-docekal-2021", "(28b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-ojí sýry"
    glossedTokens := [("dv-ojí", "two-OJI"), ("sýry", "cheese")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "none")] }

def ex_28c : LinguisticExample :=
  { id := "grimmdocekal2021_28c"
    source := ⟨"grimm-docekal-2021", "(28c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-ojí tvář"
    glossedTokens := [("dv-ojí", "two-OJI"), ("tvář", "face")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "taxonomic"), ("operation", "none")] }

def ex_28d : LinguisticExample :=
  { id := "grimmdocekal2021_28d"
    source := ⟨"grimm-docekal-2021", "(28d)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "čtv-ero sýr-ů"
    glossedTokens := [("čtv-ero", "four-ERO"), ("sýr-ů", "cheese-GEN.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "none")] }

def ex_32a : LinguisticExample :=
  { id := "grimmdocekal2021_32a"
    source := ⟨"grimm-docekal-2021", "(32a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechny dv-ojí sýry"
    glossedTokens := [("všechny", "DET"), ("dv-ojí", "two-OJI"), ("sýry", "cheese")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "universal")] }

def ex_32b : LinguisticExample :=
  { id := "grimmdocekal2021_32b"
    source := ⟨"grimm-docekal-2021", "(32b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechen dv-ojí život"
    glossedTokens := [("všechen", "DET"), ("dv-ojí", "two-OJI"), ("život", "life")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "abstract"), ("numeral", "taxonomic"), ("operation", "universal")] }

def ex_32c : LinguisticExample :=
  { id := "grimmdocekal2021_32c"
    source := ⟨"grimm-docekal-2021", "(32c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "všechno čtv-ero sýr-ů"
    glossedTokens := [("všechno", "DET"), ("čtv-ero", "four-OJI"), ("sýr-ů", "cheese-GEN.PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "universal")] }

def ex_33a : LinguisticExample :=
  { id := "grimmdocekal2021_33a"
    source := ⟨"grimm-docekal-2021", "(33a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "tři dv-ojí sýry"
    glossedTokens := [("tři", "three"), ("dv-ojí", "two-OJI"), ("sýry", "life")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "outerCardinal")] }

def ex_33b : LinguisticExample :=
  { id := "grimmdocekal2021_33b"
    source := ⟨"grimm-docekal-2021", "(33b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "deset dv-ojí-ch životů"
    glossedTokens := [("deset", "ten"), ("dv-ojí-ch", "two-OJI-GEN.PL"), ("životů", "lives")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "abstract"), ("numeral", "taxonomic"), ("operation", "outerCardinal")] }

def ex_33c : LinguisticExample :=
  { id := "grimmdocekal2021_33c"
    source := ⟨"grimm-docekal-2021", "(33c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "devět čtv-ero sýr-ů"
    glossedTokens := [("devět", "nine"), ("čtv-ero", "four-ERO"), ("sýr-ů", "cheese-GEN.PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "outerCardinal")] }

def ex_34 : LinguisticExample :=
  { id := "grimmdocekal2021_34"
    source := ⟨"grimm-docekal-2021", "(34)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Po celé silnici byla kráva."
    glossedTokens := [("Po", "on"), ("celé", "whole"), ("silnici", "road"), ("byla", "was"), ("kráva", "cow")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "none"), ("operation", "grinding")] }

def ex_35 : LinguisticExample :=
  { id := "grimmdocekal2021_35"
    source := ⟨"grimm-docekal-2021", "(35)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "V salátu bylo prase."
    glossedTokens := [("V", "in"), ("salátu", "salad"), ("bylo", "was"), ("prase", "pig")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "none"), ("operation", "grinding")] }

def ex_36b : LinguisticExample :=
  { id := "grimmdocekal2021_36b"
    source := ⟨"grimm-docekal-2021", "(36b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "V salátu jsem použil dva oleje."
    glossedTokens := [("V", "to"), ("salátu", "salad"), ("jsem", "AUX.1SG"), ("použil", "used"), ("dva", "two"), ("oleje", "oils")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "simple"), ("operation", "simpleCardinal"), ("context", "episodic"), ("reading", "taxonomic")] }

def ex_37a : LinguisticExample :=
  { id := "grimmdocekal2021_37a"
    source := ⟨"grimm-docekal-2021", "(37a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Prodává-me vína lahvová i stáčená"
    glossedTokens := [("Prodává-me", "sell-1PL"), ("vína", "wine.PL"), ("lahvová", "in-bottles"), ("i", "and"), ("stáčená", "wine-on-tap")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "none"), ("operation", "pluralization"), ("context", "generic"), ("reading", "taxonomic")] }

def ex_37b : LinguisticExample :=
  { id := "grimmdocekal2021_37b"
    source := ⟨"grimm-docekal-2021", "(37b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Prodává-me oleje pro osobní, nákladní a užitková vozidla"
    glossedTokens := [("Prodává-me", "sell-1PL"), ("oleje", "oil.PL"), ("pro", "for"), ("osobní", "personal"), ("nákladní", "cargo"), ("a", "and"), ("užitková", "utility"), ("vozidla", "car.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "none"), ("operation", "pluralization"), ("context", "generic"), ("reading", "taxonomic")] }

def ex_38a : LinguisticExample :=
  { id := "grimmdocekal2021_38a"
    source := ⟨"grimm-docekal-2021", "(38a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "V Brně mají na čepu další tři piva"
    glossedTokens := [("V", "in"), ("Brně", "Brno"), ("mají", "have.3PL"), ("na", "on"), ("čepu", "tap"), ("další", "next"), ("tři", "three"), ("piva", "beer.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "simple"), ("operation", "simpleCardinal"), ("context", "generic"), ("reading", "taxonomic")] }

def ex_39 : LinguisticExample :=
  { id := "grimmdocekal2021_39"
    source := ⟨"grimm-docekal-2021", "(39)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Chováme psy (různých ras)"
    glossedTokens := [("Chováme", "breed.we.PL"), ("psy", "dog.PL"), ("(různých", "(different.GEN.PL"), ("ras)", "types.GEN.PL)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "none"), ("operation", "pluralization"), ("context", "generic"), ("reading", "taxonomic")] }

def ex_40a : LinguisticExample :=
  { id := "grimmdocekal2021_40a"
    source := ⟨"grimm-docekal-2021", "(40a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Naše benzínka prodává tři paliva."
    glossedTokens := [("Naše", "our"), ("benzínka", "gas-station"), ("prodává", "sells.IMPERF-HAB"), ("tři", "three"), ("paliva", "fuel.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "simple"), ("operation", "simpleCardinal"), ("context", "generic"), ("reading", "taxonomic")] }

def ex_40b : LinguisticExample :=
  { id := "grimmdocekal2021_40b"
    source := ⟨"grimm-docekal-2021", "(40b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Naše benzínka včera prodala tři paliva"
    glossedTokens := [("Naše", "our"), ("benzínka", "gas-station"), ("včera", "yesterday"), ("prodala", "sold.PERF"), ("tři", "three"), ("paliva", "fuel.PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "simple"), ("operation", "simpleCardinal"), ("context", "episodic"), ("reading", "taxonomic")] }

def ex_40c : LinguisticExample :=
  { id := "grimmdocekal2021_40c"
    source := ⟨"grimm-docekal-2021", "(40c)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Naše benzínka prodává trojí palivo."
    glossedTokens := [("Naše", "our"), ("benzínka", "gas-station"), ("prodává", "sells.IMPERF-HAB"), ("trojí", "three-kind"), ("palivo", "fuel.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "none"), ("context", "generic"), ("reading", "taxonomic")] }

def ex_40d : LinguisticExample :=
  { id := "grimmdocekal2021_40d"
    source := ⟨"grimm-docekal-2021", "(40d)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Naše benzínka včera prodala trojí palivo."
    glossedTokens := [("Naše", "our"), ("benzínka", "gas-station"), ("včera", "yesterday"), ("prodala", "sold.PERF"), ("trojí", "three-kind"), ("palivo", "fuel.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "taxonomic"), ("operation", "none"), ("context", "episodic"), ("reading", "taxonomic")] }

def ex_52a : LinguisticExample :=
  { id := "grimmdocekal2021_52a"
    source := ⟨"grimm-docekal-2021", "(52a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-ojí noha tohoto stolu"
    glossedTokens := [("dv-ojí", "two-OJI"), ("noha", "leg"), ("tohoto", "this"), ("stolu", "table")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "unique"), ("numeral", "taxonomic"), ("operation", "none")] }

def ex_52b : LinguisticExample :=
  { id := "grimmdocekal2021_52b"
    source := ⟨"grimm-docekal-2021", "(52b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-ojí Petr Novák"
    glossedTokens := [("dv-ojí", "two-OJI"), ("Petr", "Petr"), ("Novák", "Novák")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "proper"), ("numeral", "taxonomic"), ("operation", "none")] }

def ex_68 : LinguisticExample :=
  { id := "grimmdocekal2021_68"
    source := ⟨"grimm-docekal-2021", "(68)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr viděl na dvorku dv-oje psy."
    glossedTokens := [("Petr", "Petr"), ("viděl", "saw"), ("na", "on"), ("dvorku", "yard"), ("dv-oje", "two-OJE"), ("psy", "dogs")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ordinary"), ("numeral", "aggregate"), ("operation", "none")] }

def ex_69 : LinguisticExample :=
  { id := "grimmdocekal2021_69"
    source := ⟨"grimm-docekal-2021", "(69)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "dv-oje vody po šesti"
    glossedTokens := [("dv-oje", "two-OJE"), ("vody", "water"), ("po", "DIST"), ("šesti", "six")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "substance"), ("numeral", "aggregate"), ("operation", "packaging")] }

def all : List LinguisticExample := [ex_9b, ex_10a, ex_10b, ex_11, ex_12, ex_13a, ex_13b, ex_13c, ex_15b, ex_17, ex_18, ex_19, ex_20a, ex_20b, ex_20c, ex_20d, ex_24a, ex_24b, ex_24b_simple, ex_25a, ex_25b, ex_25c, ex_26a, ex_26b, ex_26c, ex_27a, ex_27b, ex_27c, ex_28a, ex_28b, ex_28c, ex_28d, ex_32a, ex_32b, ex_32c, ex_33a, ex_33b, ex_33c, ex_34, ex_35, ex_36b, ex_37a, ex_37b, ex_38a, ex_39, ex_40a, ex_40b, ex_40c, ex_40d, ex_52a, ex_52b, ex_68, ex_69]

end GrimmDocekal2021.Examples
