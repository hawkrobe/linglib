module

public import Linglib.Data.Examples.Schema

/-!
# `Baker1985` — typed example data

Auto-generated from `Linglib/Data/Examples/Baker1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Baker1985.Examples`.
-/

@[expose] public section

namespace Baker1985.Examples

open Data.Examples

def chamorro_15a : LinguisticExample :=
  { id := "baker1985_chamorro_15a"
    source := ⟨"gibson-1980", "(15a)"⟩
    reportedIn := some ⟨"baker-1985", "(15a)"⟩
    language := "cham1312"
    primaryText := "Man-dikiki'."
    glossedTokens := [("Man-dikiki'", "PL-small")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "small"), ("valence", "intransitive"), ("agreesWith", "surface subject"), ("m1", "PL"), ("f1", "man"), ("m2", "small"), ("f2", "dikiki'")] }

def chamorro_15b : LinguisticExample :=
  { id := "baker1985_chamorro_15b"
    source := ⟨"gibson-1980", "(15b)"⟩
    reportedIn := some ⟨"baker-1985", "(15b)"⟩
    language := "cham1312"
    primaryText := "Para#u#fan-s-in-aolak i famagu'un gi as tata-n-niha."
    glossedTokens := [("Para#u#fan-s-in-aolak", "IRR-3PL.SBJ-PL-PASS-spank"), ("i", "the"), ("famagu'un", "children"), ("gi as", "OBL"), ("tata-n-niha", "father-their")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "spank"), ("valence", "transitive"), ("agreesWith", "surface subject"), ("m1", "IRR"), ("f1", "para"), ("m2", "3PL.SBJ"), ("f2", "u"), ("m3", "PL"), ("f3", "fan"), ("m4", "PASS"), ("f4", "in"), ("m5", "spank"), ("f5", "saolak")] }

def chamorro_15c : LinguisticExample :=
  { id := "baker1985_chamorro_15c"
    source := ⟨"gibson-1980", "(15c)"⟩
    reportedIn := some ⟨"baker-1985", "(15c)"⟩
    language := "cham1312"
    primaryText := "Hu#na'-fan-otchu siha."
    glossedTokens := [("Hu#na'-fan-otchu", "1SG.SBJ-CAUS-PL-eat"), ("siha", "them")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "eat"), ("valence", "intransitive"), ("agreesWith", "semantic subject"), ("m1", "1SG.SBJ"), ("f1", "hu"), ("m2", "CAUS"), ("f2", "na'"), ("m3", "PL"), ("f3", "fan"), ("m4", "eat"), ("f4", "otchu")] }

def chamorro_25 : LinguisticExample :=
  { id := "baker1985_chamorro_25"
    source := ⟨"gibson-1980", "(25)"⟩
    reportedIn := some ⟨"baker-1985", "(25)"⟩
    language := "cham1312"
    primaryText := "Hu#na'-fan-s-in-aolak i famagu'un gi as tata-n-niha."
    glossedTokens := [("Hu#na'-fan-s-in-aolak", "1SG.SBJ-CAUS-PL-PASS-spank"), ("i famagu'un", "children"), ("gi as", "OBL"), ("tata-n-niha", "father-their")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "spank"), ("valence", "transitive"), ("agreesWith", "intermediate subject"), ("m1", "1SG.SBJ"), ("f1", "hu"), ("m2", "CAUS"), ("f2", "na'"), ("m3", "PL"), ("f3", "fan"), ("m4", "PASS"), ("f4", "in"), ("m5", "spank"), ("f5", "saolak")] }

def quechua_39a : LinguisticExample :=
  { id := "baker1985_quechua_39a"
    source := ⟨"muysken-1981", "(39a)"⟩
    reportedIn := some ⟨"baker-1985", "(39a)"⟩
    language := "quec1387"
    primaryText := "Maqa-naku-ya-chi-n."
    glossedTokens := [("Maqa-naku-ya-chi-n", "beat-RECP-DUR-CAUS-3SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "beat"), ("valence", "transitive"), ("links", "agent-patient"), ("m1", "beat"), ("f1", "maqa"), ("m2", "RECP"), ("f2", "naku"), ("m3", "DUR"), ("f3", "ya"), ("m4", "CAUS"), ("f4", "chi"), ("m5", "3SBJ"), ("f5", "n")] }

def quechua_39b : LinguisticExample :=
  { id := "baker1985_quechua_39b"
    source := ⟨"muysken-1981", "(39b)"⟩
    reportedIn := some ⟨"baker-1985", "(39b)"⟩
    language := "quec1387"
    primaryText := "Maqa-chi-naku-rka-n."
    glossedTokens := [("Maqa-chi-naku-rka-n", "beat-CAUS-RECP-PL-3SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "beat"), ("valence", "transitive"), ("links", "causer-patient"), ("m1", "beat"), ("f1", "maqa"), ("m2", "CAUS"), ("f2", "chi"), ("m3", "RECP"), ("f3", "naku"), ("m4", "PL"), ("f4", "rka"), ("m5", "3SBJ"), ("f5", "n")] }

def bemba_49a : LinguisticExample :=
  { id := "baker1985_bemba_49a"
    source := ⟨"givon-1976", "(49a)"⟩
    reportedIn := some ⟨"baker-1985", "(49a)"⟩
    language := "bemb1257"
    primaryText := "Naa-mon-an-ya Mwape na Mutumba."
    glossedTokens := [("Naa-mon-an-ya", "1SG.SBJ.PST-see-RECP-CAUS"), ("Mwape", "Mwape"), ("na", "and"), ("Mutumba", "Mutumba")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "see"), ("valence", "transitive"), ("links", "agent-patient"), ("m1", "1SG.SBJ.PST"), ("f1", "naa"), ("m2", "see"), ("f2", "mon"), ("m3", "RECP"), ("f3", "an"), ("m4", "CAUS"), ("f4", "ya")] }

def bemba_49b : LinguisticExample :=
  { id := "baker1985_bemba_49b"
    source := ⟨"givon-1976", "(49b)"⟩
    reportedIn := some ⟨"baker-1985", "(49b)"⟩
    language := "bemb1257"
    primaryText := "Mwape na Chilufya baa-mon-eshy-ana Mutumba."
    glossedTokens := [("Mwape", "Mwape"), ("na", "and"), ("Chilufya", "Chilufya"), ("baa-mon-eshy-ana", "3PL.SBJ-see-CAUS-RECP"), ("Mutumba", "Mutumba")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "see"), ("valence", "transitive"), ("links", "causer-agent"), ("m1", "3PL.SBJ"), ("f1", "baa"), ("m2", "see"), ("f2", "mon"), ("m3", "CAUS"), ("f3", "eshy"), ("m4", "RECP"), ("f4", "ana")] }

def huichol_55 : LinguisticExample :=
  { id := "baker1985_huichol_55"
    source := ⟨"comrie-1982", "(55)"⟩
    reportedIn := some ⟨"baker-1985", "(55)"⟩
    language := "huic1243"
    primaryText := "Tiiri yi-nauka-ti nawazi me-puutinanai-ri-yeri."
    glossedTokens := [("Tiiri", "children"), ("yi-nauka-ti", "four-SBJ"), ("nawazi", "knife"), ("me-puutinanai-ri-yeri", "3PL.SBJ-buy-BEN-PASS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "buy"), ("valence", "transitive"), ("surfaceSubject", "applied object"), ("m1", "3PL.SBJ"), ("f1", "me"), ("m2", "buy"), ("f2", "puutinanai"), ("m3", "BEN"), ("f3", "ri"), ("m4", "PASS"), ("f4", "yeri")] }

def chimwiini_56c : LinguisticExample :=
  { id := "baker1985_chimwiini_56c"
    source := ⟨"kisseberth-abasheikh-1977", "(56c)"⟩
    reportedIn := some ⟨"baker-1985", "(56c)"⟩
    language := "chim1312"
    primaryText := "Mwa:limu ∅-tet-el-el-a chibu:ku na Nu:ru."
    glossedTokens := [("Mwa:limu", "teacher"), ("∅-tet-el-el-a", "SP-bring-APPL-ASP-PASS"), ("chibu:ku", "book"), ("na", "by"), ("Nu:ru", "Nuru")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "bring"), ("valence", "transitive"), ("surfaceSubject", "applied object"), ("m1", "SP"), ("f1", "∅"), ("m2", "bring"), ("f2", "tet"), ("m3", "APPL"), ("f3", "el"), ("m4", "ASP"), ("f4", "el"), ("m5", "PASS"), ("f5", "a")] }

def chimwiini_56d : LinguisticExample :=
  { id := "baker1985_chimwiini_56d"
    source := ⟨"kisseberth-abasheikh-1977", "(56d)"⟩
    reportedIn := some ⟨"baker-1985", "(56d)"⟩
    language := "chim1312"
    primaryText := "Chibu:ku chi-tet-el-el-a mwa:limu na Nu:ru."
    glossedTokens := [("Chibu:ku", "book"), ("chi-tet-el-el-a", "SP-bring-APPL-ASP-PASS"), ("mwa:limu", "teacher"), ("na", "by"), ("Nu:ru", "Nuru")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "bring"), ("valence", "transitive"), ("surfaceSubject", "patient"), ("m1", "SP"), ("f1", "chi"), ("m2", "bring"), ("f2", "tet"), ("m3", "APPL"), ("f3", "el"), ("m4", "ASP"), ("f4", "el"), ("m5", "PASS"), ("f5", "a")] }

def kinyarwanda_57c : LinguisticExample :=
  { id := "baker1985_kinyarwanda_57c"
    source := ⟨"kimenyi-1980", "(57c)"⟩
    reportedIn := some ⟨"baker-1985", "(57c)"⟩
    language := "kiny1244"
    primaryText := "Ikaramu i-ra-andik-iish-w-a ibaruwa n'umugabo."
    glossedTokens := [("Ikaramu", "pen"), ("i-ra-andik-iish-w-a", "SP-PRS-write-INSTR-PASS-ASP"), ("ibaruwa", "letter"), ("n'umugabo", "by-man")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "write"), ("valence", "transitive"), ("surfaceSubject", "applied object"), ("m1", "SP"), ("f1", "i"), ("m2", "PRS"), ("f2", "ra"), ("m3", "write"), ("f3", "andik"), ("m4", "INSTR"), ("f4", "iish"), ("m5", "PASS"), ("f5", "w"), ("m6", "ASP"), ("f6", "a")] }

def kinyarwanda_57d : LinguisticExample :=
  { id := "baker1985_kinyarwanda_57d"
    source := ⟨"kimenyi-1980", "(57d)"⟩
    reportedIn := some ⟨"baker-1985", "(57d)"⟩
    language := "kiny1244"
    primaryText := "Ibaruwa i-ra-andik-iish-w-a ikaramu n'umugabo."
    glossedTokens := [("Ibaruwa", "letter"), ("i-ra-andik-iish-w-a", "SP-PRS-write-INSTR-PASS-ASP"), ("ikaramu", "pen"), ("n'umugabo", "by-man")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "write"), ("valence", "transitive"), ("surfaceSubject", "patient"), ("m1", "SP"), ("f1", "i"), ("m2", "PRS"), ("f2", "ra"), ("m3", "write"), ("f3", "andik"), ("m4", "INSTR"), ("f4", "iish"), ("m5", "PASS"), ("f5", "w"), ("m6", "ASP"), ("f6", "a")] }

def all : List LinguisticExample := [chamorro_15a, chamorro_15b, chamorro_15c, chamorro_25, quechua_39a, quechua_39b, bemba_49a, bemba_49b, huichol_55, chimwiini_56c, chimwiini_56d, kinyarwanda_57c, kinyarwanda_57d]

end Baker1985.Examples
