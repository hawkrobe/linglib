import Linglib.Data.Examples.Schema

/-!
# `Baker2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Baker2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Baker2015.Examples`.
-/

namespace Baker2015.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "baker2015_1a"
    source := ⟨"baker-2015", "ch. 1 (1a)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kellim."
    discourseSegments := []
    glossedTokens := [("Min", "I.NOM"), ("kel-li-m", "come-PST-1SG.SBJ")]
    translation := "I came."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "baker2015_1b"
    source := ⟨"baker-2015", "ch. 1 (1b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min oloppohu aldjattym."
    discourseSegments := []
    glossedTokens := [("Min", "I.NOM"), ("oloppoh-u", "chair-ACC"), ("aldjat-ty-m", "break-PST-1SG.SBJ")]
    translation := "I broke the chair."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "NOM"), ("objectCase", "ACC")]
    comment := "From Vinokurova 2005."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1c : LinguisticExample :=
  { id := "baker2015_1c"
    source := ⟨"baker-2015", "ch. 1 (1c)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Erel kinigeni atyylasta."
    discourseSegments := []
    glossedTokens := [("Erel", "Erel.NOM"), ("kinige-ni", "book-ACC"), ("atyylas-ta", "buy-PST.3SG.SBJ")]
    translation := "Erel bought the book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "NOM"), ("objectCase", "ACC")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12a : LinguisticExample :=
  { id := "baker2015_12a"
    source := ⟨"baker-2015", "ch. 1 (12a)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Maria-nin-ra ochiti nokoke."
    discourseSegments := []
    glossedTokens := [("Maria-nin-ra", "Maria-ERG-PRT"), ("ochiti", "dog"), ("noko-ke", "find-PRF")]
    translation := "Maria found the dog."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12b : LinguisticExample :=
  { id := "baker2015_12b"
    source := ⟨"baker-2015", "ch. 1 (12b)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Maria-ra kake."
    discourseSegments := []
    glossedTokens := [("Maria-ra", "Maria-PRT"), ("ka-ke", "go-PRF")]
    translation := "Maria went."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "unmarked")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28a : LinguisticExample :=
  { id := "baker2015_28a"
    source := ⟨"baker-2015", "ch. 1 (28a)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Jose-kan ochiti benai."
    discourseSegments := []
    glossedTokens := [("Jose-kan", "Jose-ERG"), ("ochiti", "dog"), ("ben-ai", "seek-IPFV")]
    translation := "José is looking for a/the dog."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("genitiveForm", "Jose-kan")]
    comment := "The ergative suffix is also the genitive of the possessor in Jose-kan ochiti 'José's dog'; only the singular first and third person pronouns have distinct genitive forms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28b : LinguisticExample :=
  { id := "baker2015_28b"
    source := ⟨"baker-2015", "ch. 1 (28b)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "E-n ochiti benai."
    discourseSegments := []
    glossedTokens := [("E-n", "I-ERG"), ("ochiti", "dog"), ("ben-ai", "seek-IPFV")]
    translation := "I am looking for a/the dog."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("genitiveForm", "nokon")]
    comment := "The first-person possessor has the distinct genitive form nokon in nokon ochiti 'my dog'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30a : LinguisticExample :=
  { id := "baker2015_30a"
    source := ⟨"baker-2015", "ch. 1 (30a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Hipáayna háama."
    discourseSegments := []
    glossedTokens := [("Hi-páay-na", "3SG.SBJ-arrive-ASP"), ("háama", "man.NOM")]
    translation := "The man arrived."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM")]
    comment := "From Rude 1986."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30b : LinguisticExample :=
  { id := "baker2015_30b"
    source := ⟨"baker-2015", "ch. 1 (30b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háamanm hinéec'wiye wewúkiyene."
    discourseSegments := []
    glossedTokens := [("Háama-nm", "man-ERG"), ("hi-néec-'wi-ye", "3SG.SBJ-PL.OBJ-shoot-ASP"), ("wewúkiye-ne", "elk-ACC")]
    translation := "The man shot the elk(s)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ACC")]
    comment := "From Rude 1986."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21a : LinguisticExample :=
  { id := "baker2015_21a"
    source := ⟨"baker-2015", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "Farid atanani?"
    discourseSegments := []
    glossedTokens := [("Farid", "Farid.ABS"), ("ata-na-ni", "come-AOR-Q")]
    translation := "Has Farid come?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "ABS")]
    comment := "From Haspelmath 1993."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21b : LinguisticExample :=
  { id := "baker2015_21b"
    source := ⟨"baker-2015", "ch. 2 (21b)"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "Sadiq'a jad qhwana."
    discourseSegments := []
    glossedTokens := [("Sadiq'-a", "Sadiq'-ERG"), ("jad", "water.ABS"), ("qhwa-na", "drink-AOR")]
    translation := "Sadiq' drank water."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ABS")]
    comment := "From Haspelmath 1993."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22a : LinguisticExample :=
  { id := "baker2015_22a"
    source := ⟨"baker-2015", "ch. 2 (22a)"⟩
    reportedIn := none
    language := "west2599"
    primaryText := "Ní adapara pírawa."
    discourseSegments := []
    glossedTokens := [("Ní", "I"), ("ada-para", "house-in"), ("píra-wa", "sit-1SG.SBJ")]
    translation := "I sat in the house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "unmarked"), ("subjectAgreement", "yes")]
    comment := "From Franklin 1971; Kewa has subject agreement with ergative and absolutive subjects alike and no object agreement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22b : LinguisticExample :=
  { id := "baker2015_22b"
    source := ⟨"baker-2015", "ch. 2 (22b)"⟩
    reportedIn := none
    language := "west2599"
    primaryText := "Némé irikai táwa."
    discourseSegments := []
    glossedTokens := [("Né-mé", "I-ERG"), ("irikai", "dog"), ("tá-wa", "hit-1SG.SBJ")]
    translation := "I hit the dog."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("subjectAgreement", "yes")]
    comment := "From Franklin 1971."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "baker2015_23a"
    source := ⟨"baker-2015", "ch. 2 (23a)"⟩
    reportedIn := none
    language := "buru1296"
    primaryText := "Dasín háe le hurútumo."
    discourseSegments := []
    glossedTokens := [("Dasín", "girl.ABS"), ("há-e", "house-OBL"), ("le", "in"), ("hurút-umo", "sit-PST.3SG.F.SBJ")]
    translation := "The girl sat in the house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "ABS"), ("subjectAgreement", "yes")]
    comment := "From Willson 1996."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23b : LinguisticExample :=
  { id := "baker2015_23b"
    source := ⟨"baker-2015", "ch. 2 (23b)"⟩
    reportedIn := none
    language := "buru1296"
    primaryText := "Hilése dasin muyeétsimi."
    discourseSegments := []
    glossedTokens := [("Hilés-e", "boy-ERG"), ("dasin", "girl.ABS"), ("mu-yeéts-imi", "3SG.F.OBJ-see-PST.3SG.M.SBJ")]
    translation := "The boy saw the girl."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ABS"), ("subjectAgreement", "yes"), ("objectAgreement", "yes")]
    comment := "From Willson 1996; the tense suffix agrees with ergative and absolutive subjects alike, the prefix with the absolutive object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25a : LinguisticExample :=
  { id := "baker2015_25a"
    source := ⟨"baker-2015", "ch. 2 (25a)"⟩
    reportedIn := none
    language := "urdu1245"
    primaryText := "Nadya nahayi."
    discourseSegments := []
    glossedTokens := [("Nadya", "Nadya.F.NOM"), ("naha-yi", "bathe-PRF.F.SG")]
    translation := "Nadya bathed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM"), ("subjectAgreement", "yes")]
    comment := "From Butt and King 2003."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25b : LinguisticExample :=
  { id := "baker2015_25b"
    source := ⟨"baker-2015", "ch. 2 (25b)"⟩
    reportedIn := none
    language := "urdu1245"
    primaryText := "Ram=ne gaRi calayi hE."
    discourseSegments := []
    glossedTokens := [("Ram=ne", "Ram.M=ERG"), ("gaRi", "car.F.SG.NOM"), ("cala-yi", "drive-PRF.F.SG"), ("hE", "be.PRS.3SG")]
    translation := "Ram has driven a car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "NOM"), ("subjectAgreement", "no"), ("objectAgreement", "yes")]
    comment := "From Butt and King 2003; the finite verb agrees with a nominative subject but not with an ergative one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_1c, ex_12a, ex_12b, ex_28a, ex_28b, ex_30a, ex_30b, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_25a, ex_25b]

end Baker2015.Examples
