module

public import Linglib.Data.Examples.Schema

/-!
# `DeBelderVanCraenenbroeck2015` — typed example data

Auto-generated from `Linglib/Data/Examples/DeBelderVanCraenenbroeck2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DeBelderVanCraenenbroeck2015.Examples`.
-/

@[expose] public section

namespace DeBelderVanCraenenbroeck2015.Examples

def ex_2 : Datum :=
  { id := "debeldervancraenenbroeck2015_2"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(2)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb het waarom van de zaak nooit begrepen."
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("het", "the"), ("waarom", "why"), ("van", "of"), ("de", "the"), ("zaak", "case"), ("nooit", "never"), ("begrepen.", "understood")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "waarom"), ("class", "wh"), ("structure", "nominal")] }

def ex_3 : Datum :=
  { id := "debeldervancraenenbroeck2015_3"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(3)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "In een krantenartikel komt het wat/hoe/wie/waar altijd voor het waarom."
    glossedTokens := [("In", "in"), ("een", "a"), ("krantenartikel", "newspaper.article"), ("komt", "comes"), ("het", "the"), ("wat/hoe/wie/waar", "what/how/who/where"), ("altijd", "always"), ("voor", "before"), ("het", "the"), ("waarom.", "why")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "wat/hoe/wie/waar"), ("class", "wh"), ("structure", "nominal")] }

def ex_4 : Datum :=
  { id := "debeldervancraenenbroeck2015_4"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(4)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De studenten jij-en onderling."
    glossedTokens := [("De", "the"), ("studenten", "students"), ("jij-en", "you-INFINITIVE"), ("onderling.", "among.one.another")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "jij"), ("class", "pronoun"), ("structure", "verbal")] }

def ex_5 : Datum :=
  { id := "debeldervancraenenbroeck2015_5"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(5)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Martha is mijn tweede ik."
    glossedTokens := [("Martha", "Martha"), ("is", "is"), ("mijn", "my"), ("tweede", "second"), ("ik.", "I")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "ik"), ("class", "pronoun"), ("structure", "nominal")] }

def ex_6 : Datum :=
  { id := "debeldervancraenenbroeck2015_6"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(6)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niets te maar-en!"
    glossedTokens := [("Niets", "nothing"), ("te", "to"), ("maar-en!", "but-INFINITIVE")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "maar"), ("class", "conjunction"), ("structure", "verbal")] }

def ex_7 : Datum :=
  { id := "debeldervancraenenbroeck2015_7"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(7)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Paard is een het-woord."
    glossedTokens := [("Paard", "horse"), ("is", "is"), ("een", "a"), ("het-woord.", "the.NEUTER.DEFINITE-word")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "het"), ("class", "article"), ("structure", "compound")] }

def ex_8a : Datum :=
  { id := "debeldervancraenenbroeck2015_8a"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(8a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het getik van de klok"
    glossedTokens := [("het", "the"), ("getik", "GE-tick"), ("van", "of"), ("de", "the"), ("klok", "clock")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "tik"), ("class", "lexical"), ("structure", "geNominal")] }

def ex_8b : Datum :=
  { id := "debeldervancraenenbroeck2015_8b"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(8b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het gefluit van de vogels"
    glossedTokens := [("het", "the"), ("gefluit", "GE-whistle"), ("van", "of"), ("de", "the"), ("vogels", "birds")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "fluit"), ("class", "lexical"), ("structure", "geNominal")] }

def ex_9a : Datum :=
  { id := "debeldervancraenenbroeck2015_9a"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-maar niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-maar", "GE-but"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "maar"), ("class", "conjunction"), ("structure", "geNominal")] }

def ex_9b : Datum :=
  { id := "debeldervancraenenbroeck2015_9b"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-alhoewel niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-alhoewel", "GE-although"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "alhoewel"), ("class", "conjunction"), ("structure", "geNominal")] }

def ex_9c : Datum :=
  { id := "debeldervancraenenbroeck2015_9c"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-of niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-of", "GE-or"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "of"), ("class", "conjunction"), ("structure", "geNominal")] }

def ex_9d : Datum :=
  { id := "debeldervancraenenbroeck2015_9d"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-hé niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-hé", "GE-PARTICLE"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "hé"), ("class", "particle"), ("structure", "geNominal")] }

def ex_9e : Datum :=
  { id := "debeldervancraenenbroeck2015_9e"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9e)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-waarom niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-waarom", "GE-why"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "waarom"), ("class", "wh"), ("structure", "geNominal")] }

def ex_9f : Datum :=
  { id := "debeldervancraenenbroeck2015_9f"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9f)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-nooit niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-nooit", "GE-never"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "nooit"), ("class", "adverb"), ("structure", "geNominal")] }

def ex_9g : Datum :=
  { id := "debeldervancraenenbroeck2015_9g"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9g)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-ik niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-ik", "GE-I"), ("niet.", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "ik"), ("class", "pronoun"), ("structure", "geNominal")] }

def ex_10 : Datum :=
  { id := "debeldervancraenenbroeck2015_10"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(10)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Mijn tweede ik is ongelukkig."
    glossedTokens := [("Mijn", "my"), ("tweede", "second"), ("ik", "I"), ("is", "is"), ("ongelukkig.", "unhappy")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mijn tweede ik ben ongelukkig.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "agreement"), ("item", "ik"), ("class", "pronoun"), ("copula", "is")] }

def ex_11 : Datum :=
  { id := "debeldervancraenenbroeck2015_11"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(11)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niets te maar-en je hebt veel werk!"
    glossedTokens := [("Niets", "nothing"), ("te", "to"), ("maar-en", "but-INFINITIVE"), ("je", "you"), ("hebt", "have"), ("veel", "much"), ("werk!", "work")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "selection"), ("item", "maar"), ("class", "conjunction")] }

def all : List Datum := [ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9a, ex_9b, ex_9c, ex_9d, ex_9e, ex_9f, ex_9g, ex_10, ex_11]

end DeBelderVanCraenenbroeck2015.Examples
