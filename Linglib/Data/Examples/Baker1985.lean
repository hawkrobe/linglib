import Linglib.Data.Examples.Schema

/-!
# `Baker1985` — typed example data

Auto-generated from `Linglib/Data/Examples/Baker1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Baker1985.Examples`.
-/

namespace Baker1985.Examples

open Data.Examples

def chamorro_15a : LinguisticExample :=
  { id := "baker1985_chamorro_15a"
    source := ⟨"gibson-1980", ""⟩
    reportedIn := some ⟨"baker-1985", "(15a)"⟩
    language := "cham1312"
    primaryText := "Man-dikiki'."
    discourseSegments := []
    glossedTokens := [("Man-dikiki'", "PL-small")]
    translation := "They are small."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Plural number agreement man- on an intransitive predicate; the singular form is null. Baker credits the Chamorro data to Gibson 1980."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def chamorro_15b : LinguisticExample :=
  { id := "baker1985_chamorro_15b"
    source := ⟨"gibson-1980", ""⟩
    reportedIn := some ⟨"baker-1985", "(15b)"⟩
    language := "cham1312"
    primaryText := "Para#u#fan-s-in-aolak i famagu'un gi as tata-n-niha."
    discourseSegments := []
    glossedTokens := [("Para#u#fan-s-in-aolak", "IRR-3PL.SBJ-PL-PASS-spank"), ("i", "the"), ("famagu'un", "children"), ("gi as", "OBL"), ("tata-n-niha", "father-their")]
    translation := "The children are going to be spanked by their father."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "fan- (outside passive -in-) registers the plurality of the surface subject; -in- is infixed after the stem-initial consonant (s-in-aolak)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def chamorro_15c : LinguisticExample :=
  { id := "baker1985_chamorro_15c"
    source := ⟨"gibson-1980", ""⟩
    reportedIn := some ⟨"baker-1985", "(15c)"⟩
    language := "cham1312"
    primaryText := "Hu#na'-fan-otchu siha."
    discourseSegments := []
    glossedTokens := [("Hu#na'-fan-otchu", "1SG.SBJ-CAUS-PL-eat"), ("siha", "them")]
    translation := "I made them eat."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "hu"), ("m2", "na'"), ("m3", "fan"), ("m4", "otchu")]
    comment := "fan- (inside causative na'-) registers the plurality of the semantic subject of 'eat', not the surface subject. Repeated as Baker's (30)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def chamorro_25 : LinguisticExample :=
  { id := "baker1985_chamorro_25"
    source := ⟨"gibson-1980", ""⟩
    reportedIn := some ⟨"baker-1985", "(25)"⟩
    language := "cham1312"
    primaryText := "Hu#na'-fan-s-in-aolak i famagu'un gi as tata-n-niha."
    discourseSegments := []
    glossedTokens := [("Hu#na'-fan-s-in-aolak", "1SG.SBJ-CAUS-PL-PASS-spank"), ("i famagu'un", "children"), ("gi as", "OBL"), ("tata-n-niha", "father-their")]
    translation := "I had the children spanked by their father."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "hu"), ("m2", "na'"), ("m3", "fan"), ("m4", "saolak"), ("m5", "in")]
    comment := "Causative of passive: fan- sits between -in- and na'- and registers the intermediate subject (post-passive, pre-causative) -- 'the children' is neither the semantic nor the surface subject."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def quechua_39a : LinguisticExample :=
  { id := "baker1985_quechua_39a"
    source := ⟨"muysken-1981", ""⟩
    reportedIn := some ⟨"baker-1985", "(39a)"⟩
    language := "quec1387"
    primaryText := "Maqa-naku-ya-chi-n."
    discourseSegments := []
    glossedTokens := [("Maqa-naku-ya-chi-n", "beat-RECP-DUR-CAUS-3SBJ")]
    translation := "He is causing them to beat each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "maqa"), ("m2", "naku"), ("m3", "ya"), ("m4", "chi"), ("m5", "n")]
    comment := "Baker's translation carries coreference indices ('He_j is causing them_i to beat each other_i'): the reciprocal binds within the caused event. Quechua variety unspecified; Baker credits Muysken 1981. Glottocode is the Quechuan family."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def quechua_39b : LinguisticExample :=
  { id := "baker1985_quechua_39b"
    source := ⟨"muysken-1981", ""⟩
    reportedIn := some ⟨"baker-1985", "(39b)"⟩
    language := "quec1387"
    primaryText := "Maqa-chi-naku-rka-n."
    discourseSegments := []
    glossedTokens := [("Maqa-chi-naku-rka-n", "beat-CAUS-RECP-PL-3SBJ")]
    translation := "They let someone beat each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "maqa"), ("m2", "chi"), ("m3", "naku"), ("m4", "rka"), ("m5", "n")]
    comment := "Baker's translation carries coreference indices ('They_j let someone_i beat each other_j'): the reciprocal binds the causers, applying after the causative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def bemba_49a : LinguisticExample :=
  { id := "baker1985_bemba_49a"
    source := ⟨"givon-1976", ""⟩
    reportedIn := some ⟨"baker-1985", "(49a)"⟩
    language := "bemb1257"
    primaryText := "Naa-mon-an-ya Mwape na Mutumba."
    discourseSegments := []
    glossedTokens := [("Naa-mon-an-ya", "1SG.SBJ.PST-see-RECP-CAUS"), ("Mwape", "Mwape"), ("na", "and"), ("Mutumba", "Mutumba")]
    translation := "I made Mwape and Mutumba see each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "naa"), ("m2", "mon"), ("m3", "an"), ("m4", "ya")]
    comment := "Reciprocal -an inside causative -ya: the same order and interpretation as Quechua (39a). Baker credits the Bemba data to Givon 1976."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def bemba_49b : LinguisticExample :=
  { id := "baker1985_bemba_49b"
    source := ⟨"givon-1976", ""⟩
    reportedIn := some ⟨"baker-1985", "(49b)"⟩
    language := "bemb1257"
    primaryText := "Mwape na Chilufya baa-mon-eshy-ana Mutumba."
    discourseSegments := []
    glossedTokens := [("Mwape", "Mwape"), ("na", "and"), ("Chilufya", "Chilufya"), ("baa-mon-eshy-ana", "3PL.SBJ-see-CAUS-RECP"), ("Mutumba", "Mutumba")]
    translation := "Mwape and Chilufya made each other see Mutumba."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "baa"), ("m2", "mon"), ("m3", "eshy"), ("m4", "ana")]
    comment := "Causative -eshy inside reciprocal -ana. Bemba's causative is Chamorro-type (Baker's (50)-(51)), so Reciprocal links causer and initial agent -- unlike Quechua (39b), where it links causer and initial patient."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def huichol_55 : LinguisticExample :=
  { id := "baker1985_huichol_55"
    source := ⟨"comrie-1982", ""⟩
    reportedIn := some ⟨"baker-1985", "(55)"⟩
    language := "huic1243"
    primaryText := "Tiiri yi-nauka-ti nawazi me-puutinanai-ri-yeri."
    discourseSegments := []
    glossedTokens := [("Tiiri", "children"), ("yi-nauka-ti", "four-SBJ"), ("nawazi", "knife"), ("me-puutinanai-ri-yeri", "3PL.SBJ-buy-BEN-PASS")]
    translation := "Four children were bought a knife."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "me"), ("m2", "puutinanai"), ("m3", "ri"), ("m4", "yeri")]
    comment := "Passive of the applicative (54b): the beneficiary has become subject (quantifier morphology, subject agreement), and benefactive -ri is closer to the verb than passive -yeri. Baker credits the Huichol data to Comrie 1982."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def chimwiini_56c : LinguisticExample :=
  { id := "baker1985_chimwiini_56c"
    source := ⟨"kisseberth-abasheikh-1977", ""⟩
    reportedIn := some ⟨"baker-1985", "(56c)"⟩
    language := "chim1312"
    primaryText := "Mwa:limu ∅-tet-el-el-a chibu:ku na Nu:ru."
    discourseSegments := []
    glossedTokens := [("Mwa:limu", "teacher"), ("∅-tet-el-el-a", "SP-bring-APPL-ASP-PASS"), ("chibu:ku", "book"), ("na", "by"), ("Nu:ru", "Nuru")]
    translation := "The teacher was brought the book by Nuru."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "tet"), ("m2", "el"), ("m3", "el"), ("m4", "a")]
    comment := "Passive of the applicative (56b): the goal 'the teacher' is surface subject; passive -a outside applied -el. SP = subject prefix (here null)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def chimwiini_56d : LinguisticExample :=
  { id := "baker1985_chimwiini_56d"
    source := ⟨"kisseberth-abasheikh-1977", ""⟩
    reportedIn := some ⟨"baker-1985", "(56d)"⟩
    language := "chim1312"
    primaryText := "Chibu:ku chi-tet-el-el-a mwa:limu na Nu:ru."
    discourseSegments := []
    glossedTokens := [("Chibu:ku", "book"), ("chi-tet-el-el-a", "SP-bring-APPL-ASP-PASS"), ("mwa:limu", "teacher"), ("na", "by"), ("Nu:ru", "Nuru")]
    translation := "The book was brought the teacher by Nuru."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Starred by the Mirror Principle: Applicative precedes Passive morphologically (its affix is closer to the root), but Passive would have to precede Applicative syntactically (the patient, not the goal, maps to subject)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def kinyarwanda_57c : LinguisticExample :=
  { id := "baker1985_kinyarwanda_57c"
    source := ⟨"kimenyi-1980", ""⟩
    reportedIn := some ⟨"baker-1985", "(57c)"⟩
    language := "kiny1244"
    primaryText := "Ikaramu i-ra-andik-iish-w-a ibaruwa n'umugabo."
    discourseSegments := []
    glossedTokens := [("Ikaramu", "pen"), ("i-ra-andik-iish-w-a", "SP-PRS-write-INSTR-PASS-ASP"), ("ibaruwa", "letter"), ("n'umugabo", "by-man")]
    translation := "The pen was written-with the letter by the man."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("m1", "i"), ("m2", "ra"), ("m3", "andik"), ("m4", "iish"), ("m5", "w"), ("m6", "a")]
    comment := "The instrument has become subject; passive -w outside applied -iish, as the Mirror Principle predicts. Baker credits the Kinyarwanda data to Kimenyi 1980."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def kinyarwanda_57d : LinguisticExample :=
  { id := "baker1985_kinyarwanda_57d"
    source := ⟨"kimenyi-1980", ""⟩
    reportedIn := some ⟨"baker-1985", "(57d)"⟩
    language := "kiny1244"
    primaryText := "Ibaruwa i-ra-andik-iish-w-a ikaramu n'umugabo."
    discourseSegments := []
    glossedTokens := [("Ibaruwa", "letter"), ("i-ra-andik-iish-w-a", "SP-PRS-write-INSTR-PASS-ASP"), ("ikaramu", "pen"), ("n'umugabo", "by-man")]
    translation := "The letter was written with the pen by the man."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Grammatical, unlike Chi-Mwi:ni (56d): Kinyarwanda passive independently promotes either postverbal NP of a double-object verb (Baker's (58)), so this is not a Mirror Principle counterexample."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [chamorro_15a, chamorro_15b, chamorro_15c, chamorro_25, quechua_39a, quechua_39b, bemba_49a, bemba_49b, huichol_55, chimwiini_56c, chimwiini_56d, kinyarwanda_57c, kinyarwanda_57d]

end Baker1985.Examples
