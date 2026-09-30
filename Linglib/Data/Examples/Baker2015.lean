module

public import Linglib.Data.Examples.Schema

/-!
# `Baker2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Baker2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Baker2015.Examples`.
-/

@[expose] public section

namespace Baker2015.Examples

def ex_1a : Datum :=
  { id := "baker2015_1a"
    source := ⟨"baker-2015", "ch. 1 (1a)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kellim."
    glossedTokens := [("Min", "I.NOM"), ("kel-li-m", "come-PST-1SG.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM")] }

def ex_1b : Datum :=
  { id := "baker2015_1b"
    source := ⟨"baker-2015", "ch. 1 (1b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min oloppohu aldjattym."
    glossedTokens := [("Min", "I.NOM"), ("oloppoh-u", "chair-ACC"), ("aldjat-ty-m", "break-PST-1SG.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "NOM"), ("objectCase", "ACC")] }

def ex_1c : Datum :=
  { id := "baker2015_1c"
    source := ⟨"baker-2015", "ch. 1 (1c)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Erel kinigeni atyylasta."
    glossedTokens := [("Erel", "Erel.NOM"), ("kinige-ni", "book-ACC"), ("atyylas-ta", "buy-PST.3SG.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "NOM"), ("objectCase", "ACC")] }

def ex_12a : Datum :=
  { id := "baker2015_12a"
    source := ⟨"baker-2015", "ch. 1 (12a)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Maria-nin-ra ochiti nokoke."
    glossedTokens := [("Maria-nin-ra", "Maria-ERG-PRT"), ("ochiti", "dog"), ("noko-ke", "find-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked")] }

def ex_12b : Datum :=
  { id := "baker2015_12b"
    source := ⟨"baker-2015", "ch. 1 (12b)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Maria-ra kake."
    glossedTokens := [("Maria-ra", "Maria-PRT"), ("ka-ke", "go-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "unmarked")] }

def ex_28a : Datum :=
  { id := "baker2015_28a"
    source := ⟨"baker-2015", "ch. 1 (28a)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Jose-kan ochiti benai."
    glossedTokens := [("Jose-kan", "Jose-ERG"), ("ochiti", "dog"), ("ben-ai", "seek-IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("genitiveForm", "Jose-kan")] }

def ex_28b : Datum :=
  { id := "baker2015_28b"
    source := ⟨"baker-2015", "ch. 1 (28b)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "E-n ochiti benai."
    glossedTokens := [("E-n", "I-ERG"), ("ochiti", "dog"), ("ben-ai", "seek-IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("genitiveForm", "nokon")] }

def ex_30a : Datum :=
  { id := "baker2015_30a"
    source := ⟨"baker-2015", "ch. 1 (30a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Hipáayna háama."
    glossedTokens := [("Hi-páay-na", "3SG.SBJ-arrive-ASP"), ("háama", "man.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM")] }

def ex_30b : Datum :=
  { id := "baker2015_30b"
    source := ⟨"baker-2015", "ch. 1 (30b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háamanm hinéec'wiye wewúkiyene."
    glossedTokens := [("Háama-nm", "man-ERG"), ("hi-néec-'wi-ye", "3SG.SBJ-PL.OBJ-shoot-ASP"), ("wewúkiye-ne", "elk-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ACC")] }

def ex_21a : Datum :=
  { id := "baker2015_21a"
    source := ⟨"baker-2015", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "Farid atanani?"
    glossedTokens := [("Farid", "Farid.ABS"), ("ata-na-ni", "come-AOR-Q")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "ABS")] }

def ex_21b : Datum :=
  { id := "baker2015_21b"
    source := ⟨"baker-2015", "ch. 2 (21b)"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "Sadiq'a jad qhwana."
    glossedTokens := [("Sadiq'-a", "Sadiq'-ERG"), ("jad", "water.ABS"), ("qhwa-na", "drink-AOR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ABS")] }

def ex_22a : Datum :=
  { id := "baker2015_22a"
    source := ⟨"baker-2015", "ch. 2 (22a)"⟩
    reportedIn := none
    language := "west2599"
    primaryText := "Ní adapara pírawa."
    glossedTokens := [("Ní", "I"), ("ada-para", "house-in"), ("píra-wa", "sit-1SG.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "unmarked"), ("subjectAgreement", "yes")] }

def ex_22b : Datum :=
  { id := "baker2015_22b"
    source := ⟨"baker-2015", "ch. 2 (22b)"⟩
    reportedIn := none
    language := "west2599"
    primaryText := "Némé irikai táwa."
    glossedTokens := [("Né-mé", "I-ERG"), ("irikai", "dog"), ("tá-wa", "hit-1SG.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("subjectAgreement", "yes")] }

def ex_23a : Datum :=
  { id := "baker2015_23a"
    source := ⟨"baker-2015", "ch. 2 (23a)"⟩
    reportedIn := none
    language := "buru1296"
    primaryText := "Dasín háe le hurútumo."
    glossedTokens := [("Dasín", "girl.ABS"), ("há-e", "house-OBL"), ("le", "in"), ("hurút-umo", "sit-PST.3SG.F.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "ABS"), ("subjectAgreement", "yes")] }

def ex_23b : Datum :=
  { id := "baker2015_23b"
    source := ⟨"baker-2015", "ch. 2 (23b)"⟩
    reportedIn := none
    language := "buru1296"
    primaryText := "Hilése dasin muyeétsimi."
    glossedTokens := [("Hilés-e", "boy-ERG"), ("dasin", "girl.ABS"), ("mu-yeéts-imi", "3SG.F.OBJ-see-PST.3SG.M.SBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ABS"), ("subjectAgreement", "yes"), ("objectAgreement", "yes")] }

def ex_25a : Datum :=
  { id := "baker2015_25a"
    source := ⟨"baker-2015", "ch. 2 (25a)"⟩
    reportedIn := none
    language := "urdu1245"
    primaryText := "Nadya nahayi."
    glossedTokens := [("Nadya", "Nadya.F.NOM"), ("naha-yi", "bathe-PRF.F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM"), ("subjectAgreement", "yes")] }

def ex_25b : Datum :=
  { id := "baker2015_25b"
    source := ⟨"baker-2015", "ch. 2 (25b)"⟩
    reportedIn := none
    language := "urdu1245"
    primaryText := "Ram=ne gaRi calayi hE."
    glossedTokens := [("Ram=ne", "Ram.M=ERG"), ("gaRi", "car.F.SG.NOM"), ("cala-yi", "drive-PRF.F.SG"), ("hE", "be.PRS.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "NOM"), ("subjectAgreement", "no"), ("objectAgreement", "yes")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_12a, ex_12b, ex_28a, ex_28b, ex_30a, ex_30b, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_25a, ex_25b]

end Baker2015.Examples
