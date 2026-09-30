module

public import Linglib.Data.Examples.Schema

/-!
# `AghaJeretic2026` — typed example data

Auto-generated from `Linglib/Data/Examples/AghaJeretic2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AghaJeretic2026.Examples`.
-/

@[expose] public section

namespace AghaJeretic2026.Examples

open Data.Examples

def ex_6a : LinguisticExample :=
  { id := "aghajeretic2026_6a"
    source := ⟨"agha-jeretic-2026", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must do the dishes, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "strong"), ("second", "strong")] }

def ex_6b : LinguisticExample :=
  { id := "aghajeretic2026_6b"
    source := ⟨"agha-jeretic-2026", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have to do the dishes, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "strong"), ("second", "strong")] }

def ex_6c : LinguisticExample :=
  { id := "aghajeretic2026_6c"
    source := ⟨"agha-jeretic-2026", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are required to do the dishes, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "strong"), ("second", "strong")] }

def ex_6d : LinguisticExample :=
  { id := "aghajeretic2026_6d"
    source := ⟨"agha-jeretic-2026", "(6d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have to do the dishes, but you are not required to."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "strong"), ("second", "strong")] }

def ex_8a : LinguisticExample :=
  { id := "aghajeretic2026_8a"
    source := ⟨"agha-jeretic-2026", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You ought to wash the dishes, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "weak"), ("second", "strong")] }

def ex_8b : LinguisticExample :=
  { id := "aghajeretic2026_8b"
    source := ⟨"agha-jeretic-2026", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should do the dishes, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "weak"), ("second", "strong")] }

def ex_8c : LinguisticExample :=
  { id := "aghajeretic2026_8c"
    source := ⟨"agha-jeretic-2026", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are supposed to do the dishes, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "contradiction"), ("first", "weak"), ("second", "strong")] }

def ex_11a : LinguisticExample :=
  { id := "aghajeretic2026_11a"
    source := ⟨"agha-jeretic-2026", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have to wash the dishes, and (in fact), you must."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "triviality"), ("first", "strong"), ("second", "strong")] }

def ex_11b : LinguisticExample :=
  { id := "aghajeretic2026_11b"
    source := ⟨"agha-jeretic-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must wash the dishes, and (in fact) you have to."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "triviality"), ("first", "strong"), ("second", "strong")] }

def ex_12a : LinguisticExample :=
  { id := "aghajeretic2026_12a"
    source := ⟨"agha-jeretic-2026", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should wash the dishes, and (in fact) you must."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "triviality"), ("first", "weak"), ("second", "strong")] }

def ex_12b : LinguisticExample :=
  { id := "aghajeretic2026_12b"
    source := ⟨"agha-jeretic-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You ought to wash the dishes, and in fact, you have to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "triviality"), ("first", "weak"), ("second", "strong")] }

def ex_15a : LinguisticExample :=
  { id := "aghajeretic2026_15a"
    source := ⟨"agha-jeretic-2026", "(15a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "prepi na plinis ta piata ala dhen ise ipexreomenos na to kanis"
    glossedTokens := [("prepi", "must"), ("na", "NA"), ("plinis", "wash"), ("ta", "the"), ("piata", "dishes"), ("ala", "but"), ("dhen", "NEG"), ("ise", "are"), ("ipexreomenos", "obliged"), ("na", "NA"), ("to", "it"), ("kanis", "do")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "prepi"), ("force", "strong"), ("test", "contradiction")] }

def ex_15b : LinguisticExample :=
  { id := "aghajeretic2026_15b"
    source := ⟨"agha-jeretic-2026", "(15b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "tha eprepe na plinis ta piata ala dhen ise ipexreomenos na to kanis"
    glossedTokens := [("tha", "FUT"), ("eprepe", "must.PST"), ("na", "NA"), ("plinis", "wash"), ("ta", "the"), ("piata", "dishes"), ("ala", "but"), ("dhen", "NEG"), ("ise", "are"), ("ipexreomenos", "obliged"), ("na", "NA"), ("to", "it"), ("kanis", "do")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "prepi+CF"), ("force", "weak"), ("derivation", "CF"), ("test", "contradiction")] }

def ex_16a : LinguisticExample :=
  { id := "aghajeretic2026_16a"
    source := ⟨"agha-jeretic-2026", "(16a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "tu dois faire la vaisselle, mais tu n'es pas obligé"
    glossedTokens := [("tu", "you"), ("dois", "must"), ("faire", "do"), ("la", "the"), ("vaisselle", "dishes"), ("mais", "but"), ("tu", "you"), ("n'es", "NEG.are"), ("pas", "NEG"), ("obligé", "obliged")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "devoir"), ("force", "strong"), ("test", "contradiction")] }

def ex_16b : LinguisticExample :=
  { id := "aghajeretic2026_16b"
    source := ⟨"agha-jeretic-2026", "(16b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "tu devrais faire la vaisselle, mais tu n'es pas obligé"
    glossedTokens := [("tu", "you"), ("devrais", "must.COND"), ("faire", "do"), ("la", "the"), ("vaisselle", "dishes"), ("mais", "but"), ("tu", "you"), ("n'es", "NEG.are"), ("pas", "NEG"), ("obligé", "obliged")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "devoir+CF"), ("force", "weak"), ("derivation", "CF"), ("test", "contradiction")] }

def ex_17 : LinguisticExample :=
  { id := "aghajeretic2026_17"
    source := ⟨"rubinstein-2014", "(21a)"⟩
    reportedIn := some ⟨"agha-jeretic-2026", "(17)"⟩
    language := "hebr1245"
    primaryText := "yoter/haxi tov še-hu yitpater, aval hu lo xayav lehitpater"
    glossedTokens := [("yoter/haxi", "more/most"), ("tov", "good"), ("še-hu", "that-he"), ("yitpater", "will.resign"), ("aval", "but"), ("hu", "he"), ("lo", "NEG"), ("xayav", "must"), ("lehitpater", "resign")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "yoter tov"), ("force", "weak"), ("derivation", "comparative"), ("test", "contradiction")] }

def ex_23 : LinguisticExample :=
  { id := "aghajeretic2026_23"
    source := ⟨"agha-jeretic-2026", "(23)"⟩
    reportedIn := none
    language := "java1254"
    primaryText := "wong wong jawa kudu-ne iso ngomong kromo, terus anak-e rojo yo kudu iso"
    glossedTokens := [("wong", "person"), ("wong", "person"), ("jawa", "java"), ("kudu-ne", "ROOT.NEC-NE"), ("iso", "CIRC.POS"), ("ngomong", "AV.talk"), ("kromo", "high.speech"), ("terus", "then"), ("anak-e", "child-DEF"), ("rojo", "king"), ("yo", "PRT.YES"), ("kudu", "ROOT.NEC"), ("iso", "CIRC.POS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "kudu+NE"), ("force", "weak"), ("derivation", "NE"), ("test", "triviality"), ("first", "weak"), ("second", "strong")] }

def ex_18a : LinguisticExample :=
  { id := "aghajeretic2026_18a"
    source := ⟨"agha-jeretic-2026", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He should not go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .unacceptable)]
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "clausemate")] }

def ex_18b : LinguisticExample :=
  { id := "aghajeretic2026_18b"
    source := ⟨"agha-jeretic-2026", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must not go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .unacceptable)]
    paperFeatures := [("modal", "must"), ("force", "strong"), ("negation", "clausemate")] }

def ex_18c : LinguisticExample :=
  { id := "aghajeretic2026_18c"
    source := ⟨"agha-jeretic-2026", "(18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He doesn't have to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .unacceptable), ("narrow", .acceptable)]
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("negation", "clausemate")] }

def ex_19a : LinguisticExample :=
  { id := "aghajeretic2026_19a"
    source := ⟨"agha-jeretic-2026", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann doesn't think Bill should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .unacceptable)]
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "higher")] }

def ex_19b : LinguisticExample :=
  { id := "aghajeretic2026_19b"
    source := ⟨"agha-jeretic-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann doesn't think Bill must go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .unacceptable), ("narrow", .acceptable)]
    paperFeatures := [("modal", "must"), ("force", "strong"), ("negation", "higher")] }

def ex_19c : LinguisticExample :=
  { id := "aghajeretic2026_19c"
    source := ⟨"agha-jeretic-2026", "(19c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann doesn't think Bill has to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .unacceptable), ("narrow", .acceptable)]
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("negation", "higher")] }

def ex_20a : LinguisticExample :=
  { id := "aghajeretic2026_20a"
    source := ⟨"agha-jeretic-2026", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that Bill should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .unacceptable)]
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "higher")] }

def ex_20b : LinguisticExample :=
  { id := "aghajeretic2026_20b"
    source := ⟨"agha-jeretic-2026", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case Bill must go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .unacceptable), ("narrow", .acceptable)]
    paperFeatures := [("modal", "must"), ("force", "strong"), ("negation", "higher")] }

def ex_20c : LinguisticExample :=
  { id := "aghajeretic2026_20c"
    source := ⟨"agha-jeretic-2026", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that Bill has to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .unacceptable), ("narrow", .acceptable)]
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("negation", "higher")] }

def ex_26a : LinguisticExample :=
  { id := "aghajeretic2026_26a"
    source := ⟨"agha-jeretic-2026", "(26a)"⟩
    reportedIn := none
    language := "afri1274"
    primaryText := "Ek moet nog na die partyjie toe gaan!"
    glossedTokens := [("Ek", "I"), ("moet", "NEC"), ("nog", "still"), ("na", "to"), ("die", "the"), ("partyjie", "party"), ("toe", "to"), ("gaan", "go")]
    context := "It's your last day at work before your leave, and there's a lot left to do. You catch sight of your calendar and realise the summer party is this afternoon. Talking to your colleague:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "moet"), ("force", "weak"), ("test", "contradiction")] }

def ex_28a : LinguisticExample :=
  { id := "aghajeretic2026_28a"
    source := ⟨"agha-jeretic-2026", "(28a)"⟩
    reportedIn := none
    language := "samo1305"
    primaryText := "E tatau ona ou alu i le pātī."
    glossedTokens := [("E", "TAM"), ("tatau", "NEC"), ("ona", "that"), ("ou", "I"), ("alu", "go"), ("i", "to"), ("le", "the"), ("pātī", "party")]
    context := "It's your last day at work before your leave, and there's a lot left to do. You catch sight of your calendar and realise the summer party is this afternoon. Talking to your colleague:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "tatau"), ("force", "weak"), ("test", "contradiction")] }

def ex_43 : LinguisticExample :=
  { id := "aghajeretic2026_43"
    source := ⟨"deal-2011", "(1)"⟩
    reportedIn := some ⟨"agha-jeretic-2026", "(43)"⟩
    language := "nezp1238"
    primaryText := "'inéhne-no'qa 'ee kii lepít cíickan"
    glossedTokens := [("'inéhne-no'qa", "take-MODAL"), ("'ee", "you"), ("kii", "DEM"), ("lepít", "two"), ("cíickan", "blanket")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded")] }

def ex_44 : LinguisticExample :=
  { id := "aghajeretic2026_44"
    source := ⟨"deal-2011", "(49)"⟩
    reportedIn := some ⟨"agha-jeretic-2026", "(44)"⟩
    language := "nezp1238"
    primaryText := "wéet'u 'ee kiy-ó'qa"
    glossedTokens := [("wéet'u", "not"), ("'ee", "you"), ("kiy-ó'qa", "go-MODAL")]
    context := "You are explaining to someone who thinks they have to leave that they are not in fact required to do so. It's not necessary for them to leave."
    judgment := .unacceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "clausemate negation")] }

def ex_45 : LinguisticExample :=
  { id := "aghajeretic2026_45"
    source := ⟨"deal-2011", "(60)"⟩
    reportedIn := some ⟨"agha-jeretic-2026", "(45)"⟩
    language := "nezp1238"
    primaryText := "c'alawi 'a-múu-no'qa saykiptaw'atóo-na, kaa 'e-múu-nu'"
    glossedTokens := [("c'alawi", "if"), ("'a-múu-no'qa", "3OBJ-call-MODAL"), ("saykiptaw'atóo-na", "doctor-OBJ"), ("kaa", "then"), ("'e-múu-nu'", "3OBJ-call-PR")]
    context := "Prompt: If I have to call the doctor, I will."
    judgment := .unacceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "other DE")] }

def ex_46 : LinguisticExample :=
  { id := "aghajeretic2026_46"
    source := ⟨"agha-jeretic-2026", "(46)"⟩
    reportedIn := none
    language := "sion1247"
    primaryText := "Tsiaya-jã'ã je'e-ñe ba-'i-ji."
    glossedTokens := [("Tsiaya-jã'ã", "river-PATH"), ("je'e-ñe", "cross-INF"), ("ba-'i-ji", "be-ASRT")]
    context := "San Pablo is on the other side of the river. A asks a stranger, B, how to get there. B answers:"
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "ba'iji"), ("environment", "unembedded")] }

def ex_48 : LinguisticExample :=
  { id := "aghajeretic2026_48"
    source := ⟨"agha-jeretic-2026", "(48)"⟩
    reportedIn := none
    language := "sion1247"
    primaryText := "Sai-ye beo-ji."
    glossedTokens := [("Sai-ye", "go-INF"), ("beo-ji", "NEG.be-3S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "ba'iji"), ("environment", "clausemate negation")] }

def ex_49 : LinguisticExample :=
  { id := "aghajeretic2026_49"
    source := ⟨"agha-jeretic-2026", "(49)"⟩
    reportedIn := none
    language := "sion1247"
    primaryText := "Sai-ye ba-'i-to, sa-si-'i."
    glossedTokens := [("Sai-ye", "go-INF"), ("ba-'i-to", "be-IPF-COND"), ("sa-si-'i", "go-FUT-OTH")]
    context := "I am waiting to see if there is going to be a spot for me in the boat. My friend asks me if I want to go."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "ba'iji"), ("environment", "other DE")] }

def ex_51 : LinguisticExample :=
  { id := "aghajeretic2026_51"
    source := ⟨"agha-jeretic-2026", "(51)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Alice får gå ut, men hon får också stanna."
    glossedTokens := [("Alice", "Alice"), ("får", "fa"), ("gå", "go"), ("ut", "out"), ("men", "but"), ("hon", "she"), ("får", "fa"), ("också", "also"), ("stanna", "stay")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "får"), ("environment", "unembedded")] }

def ex_52 : LinguisticExample :=
  { id := "aghajeretic2026_52"
    source := ⟨"agha-jeretic-2026", "(52)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Isac får betala en bot."
    glossedTokens := [("Isac", "Isac"), ("får", "MOD"), ("betala", "pay"), ("en", "a"), ("bot", "fine")]
    context := "I'm telling a story in which Isac illegally parked the car, and the police caught him."
    judgment := .acceptable
    alternatives := []
    readings := [("necessity", .acceptable)]
    paperFeatures := [("modal", "får"), ("environment", "unembedded")] }

def ex_53 : LinguisticExample :=
  { id := "aghajeretic2026_53"
    source := ⟨"agha-jeretic-2026", "(53)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Peter får inte lämna fängelset."
    glossedTokens := [("Peter", "Peter"), ("får", "MOD"), ("inte", "not"), ("lämna", "leave"), ("fängelset", "prison")]
    context := "Peter is a prisoner."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "får"), ("environment", "clausemate negation")] }

def ex_55 : LinguisticExample :=
  { id := "aghajeretic2026_55"
    source := ⟨"agha-jeretic-2026", "(55)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Om Lucas får äta glass blir han glad."
    glossedTokens := [("Om", "if"), ("Lucas", "Lucas"), ("får", "MOD"), ("äta", "eat"), ("glass", "ice.cream"), ("blir", "be.fut"), ("han", "he"), ("glad", "happy")]
    context := "Lucas loves ice cream, but only eats it when his mom gives him permission."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "får"), ("environment", "other DE")] }

def ex_56 : LinguisticExample :=
  { id := "aghajeretic2026_56"
    source := ⟨"agha-jeretic-2026", "(56)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Om Maria får betala en böter blir hon olycklig."
    glossedTokens := [("Om", "if"), ("Maria", "Maria"), ("får", "MOD"), ("betala", "pay"), ("en", "a"), ("böter", "fine"), ("blir", "be.fut"), ("hon", "she"), ("olycklig", "unhappy")]
    context := "Maria took the train without paying and is worried about getting caught."
    judgment := .acceptable
    alternatives := []
    readings := [("necessity", .acceptable)]
    paperFeatures := [("modal", "får"), ("environment", "other DE")] }

def ex_57 : LinguisticExample :=
  { id := "aghajeretic2026_57"
    source := ⟨"newkirk-2022a", ""⟩
    reportedIn := some ⟨"agha-jeretic-2026", "(57)"⟩
    language := "nand1264"
    primaryText := "Kabunga a-anga-na-sy-a oko kalhasi ko munabwire"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("weak necessity", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "anga"), ("environment", "unembedded")] }

def ex_58 : LinguisticExample :=
  { id := "aghajeretic2026_58"
    source := ⟨"newkirk-2022a", ""⟩
    reportedIn := some ⟨"agha-jeretic-2026", "(58)"⟩
    language := "nand1264"
    primaryText := "nga-oko reglema yi-ka-bug-a, si-u-anga-sat-a"
    glossedTokens := [("nga-oko", "COMP-COMP"), ("reglema", "c9.rules"), ("yi-ka-bug-a", "SM.c9-TM-say-FV"), ("si-u-anga-sat-a", "NEG-SM.2sg-MOD-dance-FV")]
    context := "A player has been hurt in a football match, and the ref is speaking to them, and saying:"
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("weak necessity", .unacceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "anga"), ("environment", "clausemate negation")] }

def table_oqa_unembedded : LinguisticExample :=
  { id := "aghajeretic2026_table_oqa_unembedded"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "o'qa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded"), ("table", "true")] }

def table_oqa_clausemate : LinguisticExample :=
  { id := "aghajeretic2026_table_oqa_clausemate"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "o'qa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "clausemate negation"), ("table", "true")] }

def table_oqa_other : LinguisticExample :=
  { id := "aghajeretic2026_table_oqa_other"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "o'qa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "other DE"), ("table", "true")] }

def table_baiji_unembedded : LinguisticExample :=
  { id := "aghajeretic2026_table_baiji_unembedded"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "sion1247"
    primaryText := "ba'iji"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("necessity", .acceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "ba'iji"), ("environment", "unembedded"), ("table", "true")] }

def table_baiji_clausemate : LinguisticExample :=
  { id := "aghajeretic2026_table_baiji_clausemate"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "sion1247"
    primaryText := "ba'iji"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "ba'iji"), ("environment", "clausemate negation"), ("table", "true")] }

def table_baiji_other : LinguisticExample :=
  { id := "aghajeretic2026_table_baiji_other"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "sion1247"
    primaryText := "ba'iji"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "ba'iji"), ("environment", "other DE"), ("table", "true")] }

def table_far_unembedded : LinguisticExample :=
  { id := "aghajeretic2026_table_far_unembedded"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "får"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "får"), ("environment", "unembedded"), ("table", "true")] }

def table_far_clausemate : LinguisticExample :=
  { id := "aghajeretic2026_table_far_clausemate"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "får"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "får"), ("environment", "clausemate negation"), ("table", "true")] }

def table_far_other : LinguisticExample :=
  { id := "aghajeretic2026_table_far_other"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "får"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "får"), ("environment", "other DE"), ("table", "true")] }

def table_anga_unembedded : LinguisticExample :=
  { id := "aghajeretic2026_table_anga_unembedded"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "nand1264"
    primaryText := "anga"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .acceptable)]
    paperFeatures := [("modal", "anga"), ("environment", "unembedded"), ("table", "true")] }

def table_anga_clausemate : LinguisticExample :=
  { id := "aghajeretic2026_table_anga_clausemate"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "nand1264"
    primaryText := "anga"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .unacceptable)]
    paperFeatures := [("modal", "anga"), ("environment", "clausemate negation"), ("table", "true")] }

def table_anga_other : LinguisticExample :=
  { id := "aghajeretic2026_table_anga_other"
    source := ⟨"agha-jeretic-2026", "§3.2 table"⟩
    reportedIn := none
    language := "nand1264"
    primaryText := "anga"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable), ("weak necessity", .acceptable)]
    paperFeatures := [("modal", "anga"), ("environment", "other DE"), ("table", "true")] }

def ex_79a : LinguisticExample :=
  { id := "aghajeretic2026_79a"
    source := ⟨"agha-jeretic-2026", "(79a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You don't succeed if you work hard."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .marginal)]
    paperFeatures := [("construction", "bare conditional"), ("negation", "clausemate")] }

def ex_85a : LinguisticExample :=
  { id := "aghajeretic2026_85a"
    source := ⟨"agha-jeretic-2026", "(85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Babies don't eat arugula."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .unacceptable)]
    paperFeatures := [("construction", "generic"), ("negation", "clausemate")] }

def ex_91a : LinguisticExample :=
  { id := "aghajeretic2026_91a"
    source := ⟨"agha-jeretic-2026", "(91a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man for John to play against is in the next room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("could", .acceptable), ("should", .acceptable)]
    paperFeatures := [("construction", "infinitival relative"), ("determiner", "weak")] }

def ex_91b : LinguisticExample :=
  { id := "aghajeretic2026_91b"
    source := ⟨"agha-jeretic-2026", "(91b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three men for John to play against are in the next room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("could", .acceptable), ("should", .acceptable)]
    paperFeatures := [("construction", "infinitival relative"), ("determiner", "weak")] }

def ex_92a : LinguisticExample :=
  { id := "aghajeretic2026_92a"
    source := ⟨"agha-jeretic-2026", "(92a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men for John to play against are in the next room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("could", .unacceptable), ("should", .acceptable)]
    paperFeatures := [("construction", "infinitival relative"), ("determiner", "strong")] }

def ex_92b : LinguisticExample :=
  { id := "aghajeretic2026_92b"
    source := ⟨"agha-jeretic-2026", "(92b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man for John to play against is in the next room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("could", .unacceptable), ("should", .acceptable)]
    paperFeatures := [("construction", "infinitival relative"), ("determiner", "strong")] }

def all : List LinguisticExample := [ex_6a, ex_6b, ex_6c, ex_6d, ex_8a, ex_8b, ex_8c, ex_11a, ex_11b, ex_12a, ex_12b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17, ex_23, ex_18a, ex_18b, ex_18c, ex_19a, ex_19b, ex_19c, ex_20a, ex_20b, ex_20c, ex_26a, ex_28a, ex_43, ex_44, ex_45, ex_46, ex_48, ex_49, ex_51, ex_52, ex_53, ex_55, ex_56, ex_57, ex_58, table_oqa_unembedded, table_oqa_clausemate, table_oqa_other, table_baiji_unembedded, table_baiji_clausemate, table_baiji_other, table_far_unembedded, table_far_clausemate, table_far_other, table_anga_unembedded, table_anga_clausemate, table_anga_other, ex_79a, ex_85a, ex_91a, ex_91b, ex_92a, ex_92b]

end AghaJeretic2026.Examples
