module

public import Linglib.Data.Examples.Schema

/-!
# `Dolatian2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Dolatian2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dolatian2020.Examples`.
-/

@[expose] public section

namespace Dolatian2020.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "dolatian2020_1"
    source := ⟨"dolatian-2020", "(1)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "kórd͡z, kord͡z-avór, kord͡z-avor-nér, kord͡z-avor-nér-ə"
    glossedTokens := [("kórd͡z", "work"), ("kord͡z-avór", "work-er"), ("kord͡z-avor-nér", "work-er-PL"), ("kord͡z-avor-nér-ə", "work-er-PL-with")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("process", "stress")] }

def ex_2 : LinguisticExample :=
  { id := "dolatian2020_2"
    source := ⟨"dolatian-2020", "(2)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "hín, hən-utjún; teʁín, teʁn-orág"
    glossedTokens := [("hín", "old"), ("hən-utjún", "old-ness"), ("teʁín", "yellow"), ("teʁn-orág", "yellow-ish")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")] }

def ex_3b : LinguisticExample :=
  { id := "dolatian2020_3b"
    source := ⟨"dolatian-2020", "(3b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "had͡záχ, had͡zaχ-él; darpér, darper-él"
    glossedTokens := [("had͡záχ", "frequent"), ("had͡zaχ-él", "frequent-INF"), ("darpér", "different"), ("darper-él", "different-INF")]
    context := ""
    judgment := .acceptable
    alternatives := [("had͡zχ-él", .ungrammatical), ("darpr-él", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "none")] }

def ex_4 : LinguisticExample :=
  { id := "dolatian2020_4"
    source := ⟨"dolatian-2020", "(4)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún; irigún, irign-ajín"
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "husband-ness"), ("irigún", "evening"), ("irign-ajín", "evening-ADJ")]
    context := ""
    judgment := .acceptable
    alternatives := [("amsin-utjún", .ungrammatical), ("irgun-ajín", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "deletion")] }

def ex_5a : LinguisticExample :=
  { id := "dolatian2020_5a"
    source := ⟨"dolatian-2020", "(5a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "d͡zín, d͡zən-únt, d͡zən-ənt-agán"
    glossedTokens := [("d͡zín", "birth"), ("d͡zən-únt", "birth-NMLZ"), ("d͡zən-ənt-agán", "birth-NMLZ-ADJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "schwa")] }

def ex_5c : LinguisticExample :=
  { id := "dolatian2020_5c"
    source := ⟨"dolatian-2020", "(5c)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "kír, kər-ít͡ʃ, dúp, kər-t͡ʃ-a-dup"
    glossedTokens := [("kír", "handwriting"), ("kər-ít͡ʃ", "handwriting-AGT"), ("dúp", "box"), ("kər-t͡ʃ-a-dup", "handwriting-AGT-LV-box")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "compound"), ("reduction", "both")] }

def ex_7a : LinguisticExample :=
  { id := "dolatian2020_7a"
    source := ⟨"dolatian-2020", "(7a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún, amusin-óv"
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "husband-ness"), ("amusin-óv", "husband-INST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "vInflection"), ("reduction", "none")] }

def ex_7b : LinguisticExample :=
  { id := "dolatian2020_7b"
    source := ⟨"dolatian-2020", "(7b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "zərújt͡s, zərut͡s-él, zərujt͡s-óv"
    glossedTokens := [("zərújt͡s", "conversation"), ("zərut͡s-él", "conversation-INF"), ("zərujt͡s-óv", "conversation-INST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "vInflection"), ("reduction", "diphthong")] }

def ex_10c : LinguisticExample :=
  { id := "dolatian2020_10c"
    source := ⟨"dolatian-2020", "(10c)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "amusn-óv"
    glossedTokens := [("amusn-óv", "husband-INST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "deletion")] }

def ex_10e : LinguisticExample :=
  { id := "dolatian2020_10e"
    source := ⟨"dolatian-2020", "(10e)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "amusin-nér"
    glossedTokens := [("amusin-nér", "husband-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "cInflection"), ("reduction", "none")] }

def ex_12a : LinguisticExample :=
  { id := "dolatian2020_12a"
    source := ⟨"dolatian-2020", "(12a)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "zərújt͡sʰ, zərut͡sʰ-él, zərújt͡sʰ-óv"
    glossedTokens := [("zərújt͡sʰ", "conversation"), ("zərut͡sʰ-él", "conversation-INF"), ("zərújt͡sʰ-óv", "conversation-INST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "diphthong")] }

def ex_41 : LinguisticExample :=
  { id := "dolatian2020_41"
    source := ⟨"dolatian-2020", "(41)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "darí, darí-k; kaxtní, kaxtní-k; parí, parí-k"
    glossedTokens := [("darí", "year"), ("darí-k", "year-NMLZ"), ("kaxtní", "secret"), ("kaxtní-k", "secret-NMLZ"), ("parí", "good"), ("parí-k", "good-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "none")] }

def ex_42 : LinguisticExample :=
  { id := "dolatian2020_42"
    source := ⟨"dolatian-2020", "(42)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún; aznív, aznəv-utjún"
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "husband-ness"), ("aznív", "honest"), ("aznəv-utjún", "honest-ness")]
    context := ""
    judgment := .acceptable
    alternatives := [("amusən-utjún", .ungrammatical), ("aznv-utjún", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")] }

def ex_47a : LinguisticExample :=
  { id := "dolatian2020_47a"
    source := ⟨"dolatian-2020", "(47a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "hivánt, hivant-anál; hankíst, hankəst-anál; amusín, amusn-anál"
    glossedTokens := [("hivánt", "sick"), ("hivant-anál", "sick-INCH"), ("hankíst", "relaxed"), ("hankəst-anál", "relaxed-INCH"), ("amusín", "husband"), ("amusn-anál", "husband-INCH")]
    context := ""
    judgment := .acceptable
    alternatives := [("həvant-anál", .ungrammatical), ("hankist-anál", .ungrammatical), ("amsin-anál", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")] }

def ex_48a : LinguisticExample :=
  { id := "dolatian2020_48a"
    source := ⟨"dolatian-2020", "(48a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "ázk, azk-ajín, azk-ajn-agán"
    glossedTokens := [("ázk", "nation"), ("azk-ajín", "nation-ADJ"), ("azk-ajn-agán", "nation-ADJ-ADJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "deletion")] }

def ex_65 : LinguisticExample :=
  { id := "dolatian2020_65"
    source := ⟨"dolatian-2020", "(65)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "tʰúxtʰ, tʰəx.tʰ-í, tʰəx.tʰ-ít͡sʰ, tʰəx.tʰ-óv, tʰəx.tʰ-úm; amusín, amus.n-ú, amus.n-ít͡sʰ, amus.n-óv, amus.n-úm"
    glossedTokens := [("tʰúxtʰ", "paper"), ("tʰəx.tʰ-í", "paper-DAT"), ("tʰəx.tʰ-óv", "paper-INST"), ("amusín", "husband"), ("amus.n-ú", "husband-DAT"), ("amus.n-óv", "husband-INST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "both")] }

def ex_66 : LinguisticExample :=
  { id := "dolatian2020_66"
    source := ⟨"dolatian-2020", "(66)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "tʰəx.tʰ-ér, tʰəx.tʰ-er-óv; amusin.-nér, amusin.-ner-óv"
    glossedTokens := [("tʰəx.tʰ-ér", "paper-PL"), ("tʰəx.tʰ-er-óv", "paper-PL-INST"), ("amusin.-nér", "husband-PL"), ("amusin.-ner-óv", "husband-PL-INST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "plural"), ("reduction", "both")] }

def ex_72 : LinguisticExample :=
  { id := "dolatian2020_72"
    source := ⟨"dolatian-2020", "(72)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "manúk, mank-akán, mank-án, manuk-í; lúrd͡ʒ, lərd͡ʒ-anál, lurd͡ʒ-í; fílm, film-ajín, film-ér"
    glossedTokens := [("manúk", "child"), ("mank-akán", "child-ish"), ("mank-án", "child-GEN.irregular"), ("manuk-í", "child-GEN.regular"), ("lúrd͡ʒ", "serious"), ("lərd͡ʒ-anál", "serious-INCH"), ("lurd͡ʒ-í", "serious-GEN"), ("fílm", "film"), ("film-ajín", "film-ADJ"), ("film-ér", "film-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "none")] }

def all : List LinguisticExample := [ex_1, ex_2, ex_3b, ex_4, ex_5a, ex_5c, ex_7a, ex_7b, ex_10c, ex_10e, ex_12a, ex_41, ex_42, ex_47a, ex_48a, ex_65, ex_66, ex_72]

end Dolatian2020.Examples
