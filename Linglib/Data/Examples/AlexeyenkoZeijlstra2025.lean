module

public import Linglib.Data.Examples.Schema

/-!
# `AlexeyenkoZeijlstra2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexeyenkoZeijlstra2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexeyenkoZeijlstra2025.Examples`.
-/

@[expose] public section

namespace AlexeyenkoZeijlstra2025.Examples

open Data.Examples

def az2025_1a : Datum :=
  { id := "az2025_1a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is proud of her daughter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("dependent", "of")] }

def az2025_1b : Datum :=
  { id := "az2025_1b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud of her daughter mother"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("noun", "mother"), ("dependent", "of")] }

def az2025_2a : Datum :=
  { id := "az2025_2a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(2a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Ine perifanos gia to gio tu."
    glossedTokens := [("Ine", "is"), ("perifanos", "proud.M.SG"), ("gia", "for"), ("to", "the"), ("gio", "son.ACC"), ("tu", "his")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "perifanos"), ("dependent", "gia")] }

def az2025_2b : Datum :=
  { id := "az2025_2b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(2b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "o perifanos gia to gio tu pateras"
    glossedTokens := [("o", "the"), ("perifanos", "proud.M.SG"), ("gia", "for"), ("to", "the"), ("gio", "son.ACC"), ("tu", "his"), ("pateras", "father")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "perifanos"), ("noun", "pateras"), ("dependent", "gia")] }

def az2025_3a : Datum :=
  { id := "az2025_3a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(3a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Bere lanaz harro-a dago."
    glossedTokens := [("Bere", "her"), ("lanaz", "work.INS"), ("harro-a", "proud-DET"), ("dago", "is")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("dependent", "Bere")] }

def az2025_3b : Datum :=
  { id := "az2025_3b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(3b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "emakume bere lanaz harro-a"
    glossedTokens := [("emakume", "woman"), ("bere", "her"), ("lanaz", "work.INS"), ("harro-a", "proud-DET")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("noun", "emakume"), ("dependent", "bere")] }

def az2025_4a : Datum :=
  { id := "az2025_4a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(4a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Anha be farzand-an=e xod moftaxar-∅-and."
    glossedTokens := [("Anha", "they"), ("be", "in"), ("farzand-an=e", "child-PL=LNK"), ("xod", "own"), ("moftaxar-∅-and", "proud-COP.PRS-3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "moftaxar-∅-and"), ("dependent", "be")] }

def az2025_4b : Datum :=
  { id := "az2025_4b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(4b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "madar-an=e be farzand-an=e xod moftaxar"
    glossedTokens := [("madar-an=e", "mother-PL=LNK"), ("be", "in"), ("farzand-an=e", "child-PL=LNK"), ("xod", "own"), ("moftaxar", "proud")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "moftaxar"), ("attributivizer", "clitic"), ("noun", "madar-an=e"), ("dependent", "be")] }

def az2025_7a : Datum :=
  { id := "az2025_7a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a smoothly running meeting"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "running"), ("noun", "meeting"), ("dependent", "smoothly")] }

def az2025_7b : Datum :=
  { id := "az2025_7b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a running smoothly meeting"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "running"), ("noun", "meeting"), ("dependent", "smoothly")] }

def az2025_8 : Datum :=
  { id := "az2025_8"
    source := ⟨"alexeyenko-zeijlstra-2025", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the proud of his children man"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("noun", "man"), ("dependent", "of")] }

def az2025_9a : Datum :=
  { id := "az2025_9a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the proud that her daughter is a student woman"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("noun", "woman"), ("dependent", "that")] }

def az2025_9b : Datum :=
  { id := "az2025_9b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the wearing a coat person"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "wearing"), ("noun", "person"), ("dependent", "a")] }

def az2025_10a : Datum :=
  { id := "az2025_10a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the to Bill letter"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "to"), ("noun", "letter"), ("dependent", "Bill")] }

def az2025_10b : Datum :=
  { id := "az2025_10b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a which I published in 1991 book"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("noun", "book"), ("dependent", "I")] }

def az2025_15 : Datum :=
  { id := "az2025_15"
    source := ⟨"alexeyenko-zeijlstra-2025", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is a tall enough guy to play basketball."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "tall"), ("attributivizer", "null"), ("noun", "guy"), ("degree", "enough")] }

def az2025_16 : Datum :=
  { id := "az2025_16"
    source := ⟨"alexeyenko-zeijlstra-2025", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is a tall enough to play basketball guy."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "tall"), ("noun", "guy"), ("dependent", "to"), ("degree", "enough")] }

def az2025_17a : Datum :=
  { id := "az2025_17a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(17a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "es bič'-i aris damok'ideb-ul-i tavis deda-ze."
    glossedTokens := [("es", "this"), ("bič'-i", "boy-NOM"), ("aris", "is"), ("damok'ideb-ul-i", "depend-PTCP-NOM"), ("tavis", "his.DAT"), ("deda-ze", "mother-on")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "damok'ideb-ul-i"), ("dependent", "tavis")] }

def az2025_17b : Datum :=
  { id := "az2025_17b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "damok'ideb-ul-i tavis deda-ze bič'-i"
    glossedTokens := [("damok'ideb-ul-i", "depend-PTCP-NOM"), ("tavis", "his.DAT"), ("deda-ze", "mother-on"), ("bič'-i", "boy-NOM")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "damok'ideb-ul-i"), ("noun", "bič'-i"), ("dependent", "tavis")] }

def az2025_18a : Datum :=
  { id := "az2025_18a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(18a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "János független a szüle-i-től."
    glossedTokens := [("János", "János"), ("független", "independent"), ("a", "the"), ("szüle-i-től", "parents-POSS.3SG-from")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "független"), ("dependent", "a")] }

def az2025_18b : Datum :=
  { id := "az2025_18b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(18b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "egy független a szüle-i-től fiú"
    glossedTokens := [("egy", "a"), ("független", "independent"), ("a", "the"), ("szüle-i-től", "parents-POSS.3SG-from"), ("fiú", "boy")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "független"), ("noun", "fiú"), ("dependent", "a")] }

def az2025_19a : Datum :=
  { id := "az2025_19a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(19a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er stolt-ur af syni sínum."
    glossedTokens := [("Jón", "Jón"), ("er", "is"), ("stolt-ur", "proud-M.SG.NOM.STRONG"), ("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("dependent", "af")] }

def az2025_19b : Datum :=
  { id := "az2025_19b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(19b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-ur af syni sínum faðir"
    glossedTokens := [("stolt-ur", "proud-M.SG.NOM.STRONG"), ("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT"), ("faðir", "father")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("noun", "faðir"), ("dependent", "af")] }

def az2025_20a : Datum :=
  { id := "az2025_20a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(20a)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "Na hpart ē ir tłay-ov."
    glossedTokens := [("Na", "3SG"), ("hpart", "proud"), ("ē", "COP.3SG"), ("ir", "REFL.3SG.GEN"), ("tłay-ov", "boy-INS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "hpart"), ("dependent", "ir")] }

def az2025_20b : Datum :=
  { id := "az2025_20b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(20b)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "hpart ir tłay-ov hayr"
    glossedTokens := [("hpart", "proud"), ("ir", "REFL.3SG.GEN"), ("tłay-ov", "boy-INS"), ("hayr", "father")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "hpart"), ("noun", "hayr"), ("dependent", "ir")] }

def az2025_21a : Datum :=
  { id := "az2025_21a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(21a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "On je ponosan na svog sina."
    glossedTokens := [("On", "he"), ("je", "is"), ("ponosan", "proud.SHORT"), ("na", "on"), ("svog", "his"), ("sina", "son")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "ponosan"), ("dependent", "na")] }

def az2025_21b : Datum :=
  { id := "az2025_21b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(21b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ponosan na svog sina otac"
    glossedTokens := [("ponosan", "proud.SHORT"), ("na", "on"), ("svog", "his"), ("sina", "son"), ("otac", "father")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "ponosan"), ("noun", "otac"), ("dependent", "na")] }

def az2025_23b : Datum :=
  { id := "az2025_23b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(23b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I filikes pros tin Turkia xores apariθmunte os eksis"
    glossedTokens := [("I", "the"), ("filikes", "friendly"), ("pros", "toward"), ("tin", "the"), ("Turkia", "Turkey"), ("xores", "countries"), ("apariθmunte", "are.listed"), ("os", "as"), ("eksis", "following")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "filikes"), ("noun", "xores"), ("dependent", "pros")] }

def az2025_24c : Datum :=
  { id := "az2025_24c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(24c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Inogda on zažmurival ustavšyje ot plohogo osveščenija glaza"
    glossedTokens := [("Inogda", "sometimes"), ("on", "he"), ("zažmurival", "closed.tightly"), ("ustavšyje", "tired"), ("ot", "from"), ("plohogo", "bad"), ("osveščenija", "lighting"), ("glaza", "eyes")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "ustavšyje"), ("noun", "glaza"), ("dependent", "ot")] }

def az2025_26 : Datum :=
  { id := "az2025_26"
    source := ⟨"alexeyenko-zeijlstra-2025", "(26)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yí-ge dúlì yú fùmǔ de qīngshàonián"
    glossedTokens := [("yí-ge", "one-CLF"), ("dúlì", "independent"), ("yú", "from"), ("fùmǔ", "parents"), ("de", "LNK"), ("qīngshàonián", "teenager")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "dúlì"), ("attributivizer", "clitic"), ("noun", "qīngshàonián"), ("dependent", "yú")] }

def az2025_27 : Datum :=
  { id := "az2025_27"
    source := ⟨"alexeyenko-zeijlstra-2025", "(27)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Naghahanap ako ng bagay para sa bata=ng damit."
    glossedTokens := [("Naghahanap", "AV.PROG.search"), ("ako", "1SG.NOM"), ("ng", "GEN"), ("bagay", "suitable"), ("para", "for"), ("sa", "DAT"), ("bata=ng", "child=LNK"), ("damit", "dress")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "bagay"), ("attributivizer", "clitic"), ("noun", "damit"), ("dependent", "para")] }

def az2025_28b : Datum :=
  { id := "az2025_28b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(28b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "emakume harro-a"
    glossedTokens := [("emakume", "woman"), ("harro-a", "proud-DET")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("noun", "emakume")] }

def az2025_28d : Datum :=
  { id := "az2025_28d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(28d)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "bere lanaz harro-a dagoen emakume-a"
    glossedTokens := [("bere", "her"), ("lanaz", "work.INS"), ("harro-a", "proud-DET"), ("dagoen", "is.COMP"), ("emakume-a", "woman-DET")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("noun", "emakume-a"), ("dependent", "bere"), ("construction", "relative")] }

def az2025_29a : Datum :=
  { id := "az2025_29a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(29a)"⟩
    reportedIn := none
    language := "chac1251"
    primaryText := "naa motó tsi ʂo yói karetera ka=tí."
    glossedTokens := [("naa", "DEM"), ("motó", "motorcycle"), ("tsi", "PTCL"), ("ʂo", "DECL"), ("yói", "bad"), ("karetera", "highway"), ("ka=tí", "go=NMLZ:PURP")]
    context := ""
    judgment := .acceptable
    alternatives := [("naa motó tsi ʂo karetera ka=tí yói.", .acceptable)]
    readings := []
    paperFeatures := [("head", "yói"), ("dependent", "karetera")] }

def az2025_29b : Datum :=
  { id := "az2025_29b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(29b)"⟩
    reportedIn := none
    language := "chac1251"
    primaryText := "motó yói karetera ka=tí kopi=ki paí."
    glossedTokens := [("motó", "motorcycle"), ("yói", "bad"), ("karetera", "highway"), ("ka=tí", "go=NMLZ:PURP"), ("kopi=ki", "buy=DECL.NPST"), ("paí", "Paë")]
    context := ""
    judgment := .acceptable
    alternatives := [("motó karetera ka=tí yói kopi=ki paí.", .unacceptable)]
    readings := []
    paperFeatures := [("head", "yói"), ("noun", "motó"), ("dependent", "karetera")] }

def az2025_29c : Datum :=
  { id := "az2025_29c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(29c)"⟩
    reportedIn := none
    language := "chac1251"
    primaryText := "motó karetera ka=tí yói=ka kopi=ki paí."
    glossedTokens := [("motó", "motorcycle"), ("karetera", "highway"), ("ka=tí", "go=NMLZ:PURP"), ("yói=ka", "bad=REL"), ("kopi=ki", "buy=DECL.NPST"), ("paí", "Paë")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "yói=ka"), ("noun", "motó"), ("dependent", "karetera"), ("construction", "relative")] }

def az2025_30a : Datum :=
  { id := "az2025_30a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30a)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "nam-i-ce-∅-i kun dureys-umma=tti boon-aa-ɗa."
    glossedTokens := [("nam-i-ce-∅-i", "person-EP-SGV-NOM-EP"), ("kun", "this"), ("dureys-umma=tti", "rich-NMLZ=LOC"), ("boon-aa-ɗa", "proud-M-COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "boon-aa-ɗa"), ("dependent", "dureys-umma=tti")] }

def az2025_30b : Datum :=
  { id := "az2025_30b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30b)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "Muussa nama boon-aa-ɗa."
    glossedTokens := [("Muussa", "Muussa"), ("nama", "person"), ("boon-aa-ɗa", "proud-M-COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "boon-aa-ɗa"), ("noun", "nama")] }

def az2025_30c : Datum :=
  { id := "az2025_30c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30c)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "Muussa nama dureys-umma=tti boon-aa-ɗa."
    glossedTokens := [("Muussa", "Muussa"), ("nama", "person"), ("dureys-umma=tti", "rich-NMLZ=LOC"), ("boon-aa-ɗa", "proud-M-COP")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "boon-aa-ɗa"), ("noun", "nama"), ("dependent", "dureys-umma=tti")] }

def az2025_30d : Datum :=
  { id := "az2025_30d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30d)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "Muussa nama dureys-umma=tti boon-∅-u."
    glossedTokens := [("Muussa", "Muussa"), ("nama", "person"), ("dureys-umma=tti", "rich-NMLZ=LOC"), ("boon-∅-u", "proud-3SG.M-DPT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "boon-∅-u"), ("noun", "nama"), ("dependent", "dureys-umma=tti"), ("construction", "relative")] }

def az2025_31 : Datum :=
  { id := "az2025_31"
    source := ⟨"alexeyenko-zeijlstra-2025", "(31)"⟩
    reportedIn := none
    language := "kala1399"
    primaryText := "nukappiaqqa-p qimmi-mut kii-sit-tu-p uqaluttuar-aa."
    glossedTokens := [("nukappiaqqa-p", "boy-ERG.SG"), ("qimmi-mut", "dog-ALL.SG"), ("kii-sit-tu-p", "bite-CAUS-INTR.PTCP-ERG.SG"), ("uqaluttuar-aa", "tell.about-3SG>3SG.IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "kii-sit-tu-p"), ("noun", "nukappiaqqa-p"), ("dependent", "qimmi-mut")] }

def az2025_32 : Datum :=
  { id := "az2025_32"
    source := ⟨"alexeyenko-zeijlstra-2025", "(32)"⟩
    reportedIn := none
    language := "aton1241"
    primaryText := "naŋʔ=məŋ gore jal=na rak-khal =gaba =aw"
    glossedTokens := [("naŋʔ=məŋ", "2SG=GEN"), ("gore", "horse"), ("jal=na", "run=DAT"), ("rak-khal", "strong-CMPR/SPRL"), ("=gaba", "=ATTR"), ("=aw", "=REF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "rak-khal"), ("attributivizer", "clitic"), ("noun", "gore"), ("dependent", "jal=na")] }

def az2025_35 : Datum :=
  { id := "az2025_35"
    source := ⟨"alexeyenko-zeijlstra-2025", "(35)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "in praestantibus in re publica gubernanda viris"
    glossedTokens := [("in", "in"), ("praestantibus", "excellent.ABL.M.PL"), ("in", "in"), ("re", "thing"), ("publica", "public"), ("gubernanda", "to.be.governed"), ("viris", "man.ABL.M.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "praestantibus"), ("noun", "viris"), ("dependent", "re")] }

def az2025_36a : Datum :=
  { id := "az2025_36a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "nei bravi in matematica studenti"
    glossedTokens := [("nei", "in.the.M.PL"), ("bravi", "good.M.PL"), ("in", "in"), ("matematica", "math"), ("studenti", "student.M.PL")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti"), ("dependent", "in")] }

def az2025_36b : Datum :=
  { id := "az2025_36b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "negli studenti bravi in matematica"
    glossedTokens := [("negli", "in.the.M.PL"), ("studenti", "student.M.PL"), ("bravi", "good.M.PL"), ("in", "in"), ("matematica", "math")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti"), ("dependent", "in")] }

def az2025_36c : Datum :=
  { id := "az2025_36c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "nei bravi studenti"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti")] }

def az2025_36d : Datum :=
  { id := "az2025_36d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "negli studenti bravi"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti")] }

def az2025_37a : Datum :=
  { id := "az2025_37a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(37a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Aftos ine perifan-os."
    glossedTokens := [("Aftos", "he"), ("ine", "is"), ("perifan-os", "proud-M.SG.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := [("Aftos ine perifan.", .unacceptable)]
    readings := []
    paperFeatures := [("head", "perifan-os"), ("marker", "agreement")] }

def az2025_37b : Datum :=
  { id := "az2025_37b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(37b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "o perifan-os pateras"
    glossedTokens := [("o", "the"), ("perifan-os", "proud-M.SG.NOM"), ("pateras", "father")]
    context := ""
    judgment := .acceptable
    alternatives := [("o perifan pateras", .unacceptable)]
    readings := []
    paperFeatures := [("head", "perifan-os"), ("marker", "agreement"), ("noun", "pateras")] }

def az2025_38a : Datum :=
  { id := "az2025_38a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(38a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er ist stolz."
    glossedTokens := [("Er", "he"), ("ist", "is"), ("stolz", "proud")]
    context := ""
    judgment := .acceptable
    alternatives := [("Er ist stolz-er.", .unacceptable)]
    readings := []
    paperFeatures := [("head", "stolz"), ("marker", "bare")] }

def az2025_38b : Datum :=
  { id := "az2025_38b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(38b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "stolz-er Vater"
    glossedTokens := [("stolz-er", "proud-M.SG.NOM.STRONG"), ("Vater", "father")]
    context := ""
    judgment := .acceptable
    alternatives := [("stolz Vater", .unacceptable)]
    readings := []
    paperFeatures := [("head", "stolz-er"), ("marker", "agreement"), ("noun", "Vater")] }

def az2025_39a : Datum :=
  { id := "az2025_39a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(39a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ona umn-aja."
    glossedTokens := [("Ona", "she"), ("umn-aja", "smart-LONG.F.SG.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ona umn-a.", .acceptable)]
    readings := []
    paperFeatures := [("head", "umn-aja"), ("form", "long")] }

def az2025_39b : Datum :=
  { id := "az2025_39b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(39b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "umn-aja d'evočka"
    glossedTokens := [("umn-aja", "smart-LONG"), ("d'evočka", "girl")]
    context := ""
    judgment := .acceptable
    alternatives := [("umn-a d'evočka", .unacceptable)]
    readings := []
    paperFeatures := [("head", "umn-aja"), ("form", "long"), ("noun", "d'evočka")] }

def az2025_40b : Datum :=
  { id := "az2025_40b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(40b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er af syni sínum stolt-ur."
    glossedTokens := [("Jón", "Jón"), ("er", "is"), ("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT"), ("stolt-ur", "proud-M.SG.NOM.STRONG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("dependent", "af")] }

def az2025_41b : Datum :=
  { id := "az2025_41b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(41b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "af syni sínum stolt-ur faðir"
    glossedTokens := [("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT"), ("stolt-ur", "proud-M.SG.NOM.STRONG"), ("faðir", "father")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("noun", "faðir"), ("dependent", "af")] }

def az2025_42a : Datum :=
  { id := "az2025_42a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er stolt-ur."
    glossedTokens := [("Jón", "Jón"), ("er", "is"), ("stolt-ur", "proud-M.SG.NOM.STRONG")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jón er stolt-i.", .unacceptable)]
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("form", "strong")] }

def az2025_42b : Datum :=
  { id := "az2025_42b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-ur faðir"
    glossedTokens := [("stolt-ur", "proud-M.SG.NOM.STRONG"), ("faðir", "father")]
    context := ""
    judgment := .acceptable
    alternatives := [("stolt-i faðir", .unacceptable)]
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("form", "strong"), ("definiteness", "indefinite"), ("noun", "faðir")] }

def az2025_42c : Datum :=
  { id := "az2025_42c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-i faðir-inn"
    glossedTokens := [("stolt-i", "proud-M.SG.NOM.WEAK"), ("faðir-inn", "father-DEF.M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolt-i"), ("form", "weak"), ("definiteness", "definite"), ("noun", "faðir-inn")] }

def az2025_42d : Datum :=
  { id := "az2025_42d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-ur faðir-inn"
    glossedTokens := [("stolt-ur", "proud-M.SG.NOM.STRONG"), ("faðir-inn", "father-DEF.M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("form", "strong"), ("definiteness", "definite"), ("reading", "nonrestrictive"), ("noun", "faðir-inn")] }

def az2025_43a : Datum :=
  { id := "az2025_43a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(43a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Goran je lijep."
    glossedTokens := [("Goran", "Goran"), ("je", "is"), ("lijep", "nice.SHORT")]
    context := ""
    judgment := .acceptable
    alternatives := [("Goran je lijepi.", .unacceptable)]
    readings := []
    paperFeatures := [("head", "lijep"), ("form", "short")] }

def az2025_43b : Datum :=
  { id := "az2025_43b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(43b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "lijep momak"
    glossedTokens := [("lijep", "nice.SHORT"), ("momak", "young.man")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "lijep"), ("form", "short"), ("definiteness", "indefinite"), ("noun", "momak")] }

def az2025_43c : Datum :=
  { id := "az2025_43c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(43c)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "lijepi momak"
    glossedTokens := [("lijepi", "nice.LONG"), ("momak", "young.man")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "lijepi"), ("form", "long"), ("definiteness", "definite"), ("noun", "momak")] }

def az2025_62 : Datum :=
  { id := "az2025_62"
    source := ⟨"alexeyenko-zeijlstra-2025", "(62)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria ist stolz auf ihre Tochter."
    glossedTokens := [("Maria", "Maria"), ("ist", "is"), ("stolz", "proud"), ("auf", "on"), ("ihre", "her"), ("Tochter", "daughter")]
    context := ""
    judgment := .acceptable
    alternatives := [("Maria ist auf ihre Tochter stolz.", .acceptable)]
    readings := []
    paperFeatures := [("head", "stolz"), ("dependent", "auf")] }

def az2025_63a : Datum :=
  { id := "az2025_63a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(63a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "die stolz auf ihre Tochter-e Mutter"
    glossedTokens := [("die", "the"), ("stolz", "proud"), ("auf", "on"), ("ihre", "her"), ("Tochter-e", "daughter-ATTR.F.SG.NOM"), ("Mutter", "mother")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolz"), ("attributivizer", "affix"), ("noun", "Mutter"), ("dependent", "auf")] }

def az2025_63b : Datum :=
  { id := "az2025_63b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(63b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "die auf ihre Tochter stolz-e Mutter"
    glossedTokens := [("die", "the"), ("auf", "on"), ("ihre", "her"), ("Tochter", "daughter"), ("stolz-e", "proud-ATTR.F.SG.NOM"), ("Mutter", "mother")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "stolz-e"), ("attributivizer", "affix"), ("noun", "Mutter"), ("dependent", "auf")] }

def az2025_66a : Datum :=
  { id := "az2025_66a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(66a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een op haar moeder trots-e vrouw"
    glossedTokens := [("een", "a"), ("op", "of"), ("haar", "her"), ("moeder", "mother"), ("trots-e", "proud-ATTR"), ("vrouw", "woman")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "trots-e"), ("attributivizer", "affix"), ("noun", "vrouw"), ("dependent", "op")] }

def az2025_66b : Datum :=
  { id := "az2025_66b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(66b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots op haar moeder-e vrouw"
    glossedTokens := [("een", "a"), ("trots", "proud"), ("op", "of"), ("haar", "her"), ("moeder-e", "mother-ATTR"), ("vrouw", "woman")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "trots"), ("attributivizer", "affix"), ("noun", "vrouw"), ("dependent", "op")] }

def az2025_66c : Datum :=
  { id := "az2025_66c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(66c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots-e op haar moeder vrouw"
    glossedTokens := [("een", "a"), ("trots-e", "proud-ATTR"), ("op", "of"), ("haar", "her"), ("moeder", "mother"), ("vrouw", "woman")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "trots-e"), ("attributivizer", "affix"), ("noun", "vrouw"), ("dependent", "op")] }

def az2025_67a : Datum :=
  { id := "az2025_67a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(67a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een op haar vader trots-∅ kind"
    glossedTokens := [("een", "a"), ("op", "of"), ("haar", "her"), ("vader", "father"), ("trots-∅", "proud-ATTR"), ("kind", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "trots-∅"), ("attributivizer", "null"), ("noun", "kind"), ("dependent", "op")] }

def az2025_67b : Datum :=
  { id := "az2025_67b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(67b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots op haar vader-∅ kind"
    glossedTokens := [("een", "a"), ("trots", "proud"), ("op", "of"), ("haar", "her"), ("vader-∅", "father-ATTR"), ("kind", "child")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "trots"), ("attributivizer", "null"), ("noun", "kind"), ("dependent", "op")] }

def az2025_67c : Datum :=
  { id := "az2025_67c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(67c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots-∅ op haar vader kind"
    glossedTokens := [("een", "a"), ("trots-∅", "proud-ATTR"), ("op", "of"), ("haar", "her"), ("vader", "father"), ("kind", "child")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "trots-∅"), ("attributivizer", "null"), ("noun", "kind"), ("dependent", "op")] }

def az2025_68a : Datum :=
  { id := "az2025_68a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot genoeg-∅ kind"
    glossedTokens := [("een", "a"), ("groot", "big"), ("genoeg-∅", "enough-ATTR"), ("kind", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "groot"), ("attributivizer", "null"), ("noun", "kind"), ("degree", "genoeg-∅")] }

def az2025_68b : Datum :=
  { id := "az2025_68b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot genoeg-e vrouw"
    glossedTokens := [("een", "a"), ("groot", "big"), ("genoeg-e", "enough-ATTR"), ("vrouw", "woman")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "groot"), ("attributivizer", "affix"), ("noun", "vrouw"), ("degree", "genoeg-e")] }

def az2025_68c : Datum :=
  { id := "az2025_68c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot-e genoeg vrouw"
    glossedTokens := [("een", "a"), ("groot-e", "big-ATTR"), ("genoeg", "enough"), ("vrouw", "woman")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "groot-e"), ("noun", "vrouw"), ("degree", "genoeg")] }

def az2025_68d : Datum :=
  { id := "az2025_68d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot genoeg vrouw"
    glossedTokens := [("een", "a"), ("groot", "big"), ("genoeg", "enough"), ("vrouw", "woman")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "groot"), ("noun", "vrouw"), ("degree", "genoeg")] }

def az2025_71a : Datum :=
  { id := "az2025_71a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud child"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("attributivizer", "null"), ("noun", "child")] }

def az2025_71b : Datum :=
  { id := "az2025_71b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(71b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud of his mother child"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("attributivizer", "null"), ("noun", "child"), ("dependent", "of")] }

def az2025_71c : Datum :=
  { id := "az2025_71c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(71c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud enough child"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "proud"), ("attributivizer", "null"), ("noun", "child"), ("degree", "enough")] }

def all : List Datum := [az2025_1a, az2025_1b, az2025_2a, az2025_2b, az2025_3a, az2025_3b, az2025_4a, az2025_4b, az2025_7a, az2025_7b, az2025_8, az2025_9a, az2025_9b, az2025_10a, az2025_10b, az2025_15, az2025_16, az2025_17a, az2025_17b, az2025_18a, az2025_18b, az2025_19a, az2025_19b, az2025_20a, az2025_20b, az2025_21a, az2025_21b, az2025_23b, az2025_24c, az2025_26, az2025_27, az2025_28b, az2025_28d, az2025_29a, az2025_29b, az2025_29c, az2025_30a, az2025_30b, az2025_30c, az2025_30d, az2025_31, az2025_32, az2025_35, az2025_36a, az2025_36b, az2025_36c, az2025_36d, az2025_37a, az2025_37b, az2025_38a, az2025_38b, az2025_39a, az2025_39b, az2025_40b, az2025_41b, az2025_42a, az2025_42b, az2025_42c, az2025_42d, az2025_43a, az2025_43b, az2025_43c, az2025_62, az2025_63a, az2025_63b, az2025_66a, az2025_66b, az2025_66c, az2025_67a, az2025_67b, az2025_67c, az2025_68a, az2025_68b, az2025_68c, az2025_68d, az2025_71a, az2025_71b, az2025_71c]

end AlexeyenkoZeijlstra2025.Examples
