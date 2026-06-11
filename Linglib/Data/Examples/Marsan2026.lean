import Linglib.Data.Examples.Schema

/-!
# `Marsan2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Marsan2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Marsan2026.Examples`.
-/

namespace Marsan2026.Examples

open Data.Examples

def tr_001a : LinguisticExample :=
  { id := "tr_001a"
    source := ⟨"marsan-2026", "tr_001a"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Fatma ev-e gel-di."
    discourseSegments := []
    glossedTokens := [("Fatma", "Fatma"), ("ev-e", "home-DAT"), ("gel-di.", "come-DI")]
    translation := "Fatma came home"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI"), ("ET_ST", "ET < ST")]
    comment := "baseline DI"
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_001b : LinguisticExample :=
  { id := "tr_001b"
    source := ⟨"marsan-2026", "tr_001b"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Fatma ev-e gel-miş."
    discourseSegments := []
    glossedTokens := [("Fatma", "Fatma"), ("ev-e", "home-DAT"), ("gel-miş.", "come-MIS")]
    translation := "Fatma apparently came home"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET < EAT")]
    comment := "baseline MIS"
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_002 : LinguisticExample :=
  { id := "tr_002"
    source := ⟨"smirnova-2013", "tr_002"⟩
    reportedIn := some ⟨"marsan-2026", "tr_002"⟩
    language := "stan1290"
    primaryText := "Çok fena yağ-dı."
    discourseSegments := []
    glossedTokens := [("Çok", "very"), ("fena", "heavily"), ("yağ-dı.", "fall-DI")]
    translation := "It rained very heavily."
    context := "10 years ago the area where you live was devastated by a historic rainfall and the consequent
flood. You weren’t in your hometown then but you know that the aftermaths were catastrophic. Your
house was flooded, and the government announced the state of emergency in your area.
Now you say about that event:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET < EAT"), ("evidence_type", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_003 : LinguisticExample :=
  { id := "tr_003"
    source := ⟨"smirnova-2013", "tr_003"⟩
    reportedIn := some ⟨"marsan-2026", "tr_003"⟩
    language := "stan1290"
    primaryText := "Maria kitap yaz-ıyor-muş / yaz-acak-mış."
    discourseSegments := []
    glossedTokens := [("Maria", "Maria"), ("kitap", "book"), ("yaz-ıyor-muş", "write-IPFV-MIS"), ("/", "/"), ("yaz-acak-mış.", "write-PROSP-MIS")]
    translation := "Maria is writing a book, [I will hear]"
    context := "You suspect that Maria is writing a book, but you have no evidence. Next week you have
a meeting with Maria’s sister, a good friend of yours. You plan to ask her weather Maria is writing a
book. Today, when someone asks you what Maria does, you say:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("EAT_ET", "ET < EAT"), ("evidence_type", "indirect")]
    comment := "ST < EAT, Abusch upper limit constraint"
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_004a : LinguisticExample :=
  { id := "tr_004a"
    source := ⟨"marsan-2026", "tr_004a"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Maria iki gün sonra Sofya'ya gid-ecek-miş."
    discourseSegments := []
    glossedTokens := [("Maria", "Maria"), ("iki", "two"), ("gün", "day"), ("sonra", "later"), ("Sofya'ya", "Sofia-DAT"), ("gid-ecek-miş.", "go-PROSP-MIS")]
    translation := "Maria will go to Sofia two days from now [I heard]"
    context := "Ivan tells you today that Maria will travel to Sofia two days from now. You share this with
a friend of yours:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI"), ("ET_ST", "ST < ET"), ("EAT_ET", "EAT < ET"), ("evidence_type", "indirect"), ("evidential_context", "reportative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_004b : LinguisticExample :=
  { id := "tr_004b"
    source := ⟨"marsan-2026", "tr_004b"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Maria iki gün sonra Sofya'ya gid-ecek-miş."
    discourseSegments := []
    glossedTokens := [("Maria", "Maria"), ("iki", "two"), ("gün", "day"), ("sonra", "later"), ("Sofya'ya", "Sofia-DAT"), ("gid-ecek-miş.", "go-PROSP-MIS")]
    translation := "Maria will go to Sofia two days from now [I inferred]"
    context := "You see a ticket to Sofia for the day after tomorrow on Maria’s desk. You share this with a
friend:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ST < ET"), ("EAT_ET", "EAT < ET"), ("evidence_type", "indirect"), ("evidential_context", "inferential")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_005 : LinguisticExample :=
  { id := "tr_005"
    source := ⟨"smirnova-2012", "tr_005"⟩
    reportedIn := some ⟨"marsan-2026", "tr_005"⟩
    language := "stan1290"
    primaryText := "Yemek piş-miş."
    discourseSegments := []
    glossedTokens := [("Yemek", "dish"), ("piş-miş.", "cook-MIS")]
    translation := "The dish is/has been cooked."
    context := "You and your friends are cooking dinner together. According to the recipe, the dish should
cook for 20 more minutes. However, when you taste the dish, you realize that it is ready. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET < EAT"), ("evidence_type", "direct"), ("evidential_context", "inferential")]
    comment := "Smirnova takes this to be ET = EAT = ST"
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_006a : LinguisticExample :=
  { id := "tr_006a"
    source := ⟨"marsan-2026", "tr_006a"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Yemek piş-miş."
    discourseSegments := []
    glossedTokens := [("Yemek", "dish"), ("piş-miş.", "cook-MIS")]
    translation := "The dish is/has been cooked."
    context := "You and your friends are cooking dinner together. According to the recipe, the dish should
cook for 20 more minutes and is supposed to bubble when it is done. To your surprise, it starts bubbling
as you watch and stir it. You say:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ET = ST"), ("EAT_ET", "ET = EAT"), ("evidence_type", "direct")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_006b : LinguisticExample :=
  { id := "tr_006b"
    source := ⟨"marsan-2026", "tr_006b"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Yemek piş-miş."
    discourseSegments := []
    glossedTokens := [("Yemek", "dish"), ("piş-miş.", "cook-MIS")]
    translation := "The dish is/has been cooked."
    context := "You and your friends are cooking dinner together. According to the recipe, the dish should
cook for 20 more minutes and is supposed to bubble when it is done. You check it every five minutes.
The last time you checked, it was not done yet, but now, to your surprise, it is bubbling. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET < EAT"), ("evidence_type", "direct"), ("evidential_context", "inferential")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_007a : LinguisticExample :=
  { id := "tr_007a"
    source := ⟨"marsan-2026", "tr_007a"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Venüs balık ye-me-di."
    discourseSegments := []
    glossedTokens := [("Venüs", "Venus"), ("balık", "fish"), ("ye-me-di.", "eat-NEG-DI")]
    translation := "Venus didn't eat fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI"), ("ET_ST", "ET < ST")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_007b : LinguisticExample :=
  { id := "tr_007b"
    source := ⟨"marsan-2026", "tr_007b"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Venüs balık ye-di değil."
    discourseSegments := []
    glossedTokens := [("Venüs", "Venus"), ("balık", "fish"), ("ye-di", "eat-DI"), ("değil.", "NEG")]
    translation := "It is not the case that Venüs ate fish."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI"), ("ET_ST", "ET < ST")]
    comment := "Outer negation is not compatible with DI."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_008a : LinguisticExample :=
  { id := "tr_008a"
    source := ⟨"marsan-2026", "tr_008a"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "İlk set-i bizim takım önde bitir-di"
    discourseSegments := []
    glossedTokens := [("İlk", "first"), ("set-i", "set-ACC"), ("bizim", "our"), ("takım", "team"), ("önde", "ahead"), ("bitir-di", "end-DI")]
    translation := "Our team ended the first set ahead."
    context := "You follow a live volleyball game by listening to a radio commentator’s play-by-play
description. You have no direct visual or auditory access to the game itself. The next day, you report
on the match:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET = EAT"), ("evidence_type", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_008b : LinguisticExample :=
  { id := "tr_008b"
    source := ⟨"marsan-2026", "tr_008b"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "İlk set-i bizim takım önde bitir-miş"
    discourseSegments := []
    glossedTokens := [("İlk", "first"), ("set-i", "set-ACC"), ("bizim", "our"), ("takım", "team"), ("önde", "ahead"), ("bitir-miş", "end-MIS")]
    translation := "Our team ended the first set ahead."
    context := "You follow a live volleyball game by listening to a radio commentator’s play-by-play
description. You have no direct visual or auditory access to the game itself. The next day, you report
on the match:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET < EAT"), ("evidence_type", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_008c : LinguisticExample :=
  { id := "tr_008c"
    source := ⟨"marsan-2026", "tr_008c"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "İlk set-i bizim takım önde bitir-miş"
    discourseSegments := []
    glossedTokens := [("İlk", "first"), ("set-i", "set-ACC"), ("bizim", "our"), ("takım", "team"), ("önde", "ahead"), ("bitir-miş", "end-MIS")]
    translation := "Our team ended the first set ahead."
    context := "Following (tr_008a-b), due to a lost signal, you learn of the second set only from a summary during
a later break. The next day, you say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "MIS"), ("ET_ST", "ET < ST"), ("EAT_ET", "ET < EAT"), ("evidence_type", "indirect"), ("evidential_context", "reportative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_009a : LinguisticExample :=
  { id := "tr_009a"
    source := ⟨"marsan-2026", "tr_009a"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ivan spor salonu-na git-ti-miş"
    discourseSegments := []
    glossedTokens := [("Ivan", "Ivan"), ("spor", "sport"), ("salonu-na", "hall-DAT"), ("git-ti-miş", "go-DI-MIS")]
    translation := "Ivan went to the gym."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI, MIS")]
    comment := "DI + MIS is not a licensed form"
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def tr_009b : LinguisticExample :=
  { id := "tr_009b"
    source := ⟨"marsan-2026", "tr_009b"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ivan spor salonu-na git-miş-ti"
    discourseSegments := []
    glossedTokens := [("Ivan", "Ivan"), ("spor", "sport"), ("salonu-na", "hall-DAT"), ("git-miş-ti", "go-MIS-DI")]
    translation := "Ivan went to the gym."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tam", "DI, MIS")]
    comment := "MS + DI is licensed"
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [tr_001a, tr_001b, tr_002, tr_003, tr_004a, tr_004b, tr_005, tr_006a, tr_006b, tr_007a, tr_007b, tr_008a, tr_008b, tr_008c, tr_009a, tr_009b]

end Marsan2026.Examples
