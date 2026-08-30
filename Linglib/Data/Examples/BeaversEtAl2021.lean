import Linglib.Data.Examples.Schema

/-!
# `BeaversEtAl2021` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaversEtAl2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaversEtAl2021.Examples`.
-/

namespace BeaversEtAl2021.Examples

open Data.Examples

def beavers_etal2021_1c : LinguisticExample :=
  { id := "beavers_etal2021_1c"
    source := ⟨"beavers-etal-2021", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase cracked."
    discourseSegments := []
    glossedTokens := []
    translation := "The vase cracked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "result"), ("form", "monomorphemic verb")]
    comment := "Change of state expressed by a basic verb, unlike 'became black' or 'flattened'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_7a : LinguisticExample :=
  { id := "beavers_etal2021_7a"
    source := ⟨"beavers-etal-2021", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Look at the bright picture on your left."
    discourseSegments := []
    glossedTokens := []
    translation := "Look at the bright picture on your left."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "property concept"), ("form", "basic stative")]
    comment := "PC roots show both a simple adjective and a deverbal one ('brightened', (7b))."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_10a : LinguisticExample :=
  { id := "beavers_etal2021_10a"
    source := ⟨"beavers-etal-2021", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bright photo has never brightened."
    discourseSegments := []
    glossedTokens := []
    translation := "The bright photo has never brightened."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "property concept")]
    comment := "Simple PC adjectives survive change denial; deverbal '#brightened photo' does not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_11c : LinguisticExample :=
  { id := "beavers_etal2021_11c"
    source := ⟨"beavers-etal-2021", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The shattered vase has never shattered."
    discourseSegments := []
    glossedTokens := []
    translation := "The shattered vase has never shattered."
    context := "An artist makes ceramic pieces that, properly assembled, would form a vase."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")]
    comment := "Contradictory even in a prototypical-result context: the adjective entails prior change."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_13 : LinguisticExample :=
  { id := "beavers_etal2021_13"
    source := ⟨"beavers-etal-2021", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The window is broken but it never broke. It was manufactured that way."
    discourseSegments := []
    glossedTokens := []
    translation := "The window is broken but it never broke. It was manufactured that way."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")]
    comment := "Acceptable for some speakers: lexical drift toward a 'not functioning' sense, expected variation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_15a : LinguisticExample :=
  { id := "beavers_etal2021_15a"
    source := ⟨"beavers-etal-2021", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    discourseSegments := []
    glossedTokens := []
    translation := "John sharpened the knife again."
    context := "John buys a knife forged already sharp, uses it until it becomes blunt, and sharpens it with a whetting stone."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive: could be just one sharpening", .acceptable)]
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "property concept")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_16a : LinguisticExample :=
  { id := "beavers_etal2021_16a"
    source := ⟨"beavers-etal-2021", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris thawed the meat again."
    discourseSegments := []
    glossedTokens := []
    translation := "Chris thawed the meat again."
    context := "Chris kills a rabbit, butchers it, freezes the fresh meat for a week, then puts it out to thaw."
    judgment := .unacceptable
    alternatives := []
    readings := [("repetitive: necessarily two defrostings", .acceptable)]
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")]
    comment := "Result roots lack the restitutive reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_25a : LinguisticExample :=
  { id := "beavers_etal2021_25a"
    source := ⟨"beavers-etal-2021", "(25a)"⟩
    reportedIn := none
    language := "cash1251"
    primaryText := "madin papanka ëdkitëkënia."
    discourseSegments := []
    glossedTokens := [("madi=n", "sand=POSS"), ("papa=n=ka=a", "father=A/S=VAL=3A/S"), ("ëd-ki-tëkën-i-a", "dry-INTR-again-IPFV-NPROX")]
    translation := "The desert is getting dry again."
    context := "The desert starts off dry. Then it is made nondry. Then it turns dry again."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "property concept")]
    comment := "Kakataibo PC roots generally allow restitutive -tëkën; this token was rejected in the given context."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_26 : LinguisticExample :=
  { id := "beavers_etal2021_26"
    source := ⟨"beavers-etal-2021", "(26)"⟩
    reportedIn := none
    language := "cash1251"
    primaryText := "maxákana rë(të)tëkëa."
    discourseSegments := []
    glossedTokens := [("maxat=ka=na", "stone=VAL=1A/S"), ("rëtë-tëkën-a", "kill-again-PFV")]
    translation := "I killed the stone again."
    context := "The stone was always dead. Then it was brought to life. Then I kill it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")]
    comment := "Unlike English 'kill': rëtë means 'not alive', applicable to never-alive inanimates — expected lexicalization variation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_28a : LinguisticExample :=
  { id := "beavers_etal2021_28a"
    source := ⟨"beavers-etal-2021", "(28a)"⟩
    reportedIn := none
    language := "kiny1244"
    primaryText := "Icy-uma gi-hor-a gi-tyay-e."
    discourseSegments := []
    glossedTokens := [("Icy-uma", "7-knife"), ("gi-hor-a", "7S-always-FV"), ("gi-tyay-e", "7S-sharp-PFV")]
    translation := "The knife has always been sharp."
    context := "Habimana buys a knife that is manufactured very sharp."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "property concept")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_28b : LinguisticExample :=
  { id := "beavers_etal2021_28b"
    source := ⟨"beavers-etal-2021", "(28b)"⟩
    reportedIn := none
    language := "kiny1244"
    primaryText := "Umu-keri u-hor-a u-tek-ets-e."
    discourseSegments := []
    glossedTokens := [("Umu-keri", "3-fruit"), ("u-hor-a", "3S-always-FV"), ("u-tek-ets-e", "3S-cook-STV-PFV")]
    translation := "The fruit has always been cooked."
    context := "A hypothetical fruit that is always soft and ripe since it first grows and can be eaten any time."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_29b : LinguisticExample :=
  { id := "beavers_etal2021_29b"
    source := ⟨"beavers-etal-2021", "(29b)"⟩
    reportedIn := none
    language := "kiny1244"
    primaryText := "Karemera y-ongey-e ku-men-a iki-rahure."
    discourseSegments := []
    glossedTokens := [("Karemera", "Karemera"), ("y-ongey-e", "1S-again-PFV"), ("ku-men-a", "INF-break-FV"), ("iki-rahure", "7-glass")]
    translation := "Karemera broke the glass again."
    context := "Small pieces of glass, manufactured in that size, are assembled into a single pane, which Karemera then breaks."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_31 : LinguisticExample :=
  { id := "beavers_etal2021_31"
    source := ⟨"beavers-etal-2021", "(31)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ha-gesher 'arox 'aval 'afpa'am lo hu'arax."
    discourseSegments := []
    glossedTokens := [("ha-gesher", "the-bridge"), ("'arox", "long"), ("'aval", "but"), ("'afpa'am", "never"), ("lo", "NEG"), ("hu'arax", "lengthened.PASS")]
    translation := "The bridge is long but was never lengthened."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "property concept")]
    comment := "With deverbal mu'arax 'lengthened' in place of 'arox the sentence is contradictory."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_32 : LinguisticExample :=
  { id := "beavers_etal2021_32"
    source := ⟨"beavers-etal-2021", "(32)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ha-zxuxit menupecet, 'aval hi 'afpa'am lo hitnapca."
    discourseSegments := []
    glossedTokens := [("ha-zxuxit", "the-glass"), ("menupecet", "shattered"), ("'aval", "but"), ("hi", "it"), ("'afpa'am", "never"), ("lo", "NEG"), ("hitnapca", "shattered.REFL")]
    translation := "The glass is shattered, but it never shattered."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_33b : LinguisticExample :=
  { id := "beavers_etal2021_33b"
    source := ⟨"beavers-etal-2021", "(33b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Kim nipca šuv/mexadaš 'et ha-zxuxit."
    discourseSegments := []
    glossedTokens := [("Kim", "Kim"), ("nipca", "shattered"), ("šuv/mexadaš", "again/anew"), ("'et", "ACC"), ("ha-zxuxit", "the-glass")]
    translation := "Kim shattered the glass again."
    context := "Small pieces of glass, manufactured in that size, are assembled into a single pane, which Kim then shatters."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")]
    comment := "mexadaš 'anew' generates only restitutive readings, similar to English re- prefixation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_35b : LinguisticExample :=
  { id := "beavers_etal2021_35b"
    source := ⟨"beavers-etal-2021", "(35b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "kāc phoɖ-leli āhe pəɳ ti kədhi phuʈ-leli nāhi."
    discourseSegments := []
    glossedTokens := [("kāc", "glass.NOM.F.SG"), ("phoɖ-leli", "shatter.TR-PART.F.SG"), ("āhe", "be.PRS.3SG"), ("pəɳ", "but"), ("ti", "DEM.F.SG"), ("kədhi", "ever"), ("phuʈ-leli", "shatter.INTR-PART.F.SG"), ("nāhi", "NEG")]
    translation := "The glass is shattered, but it never shattered."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_36b : LinguisticExample :=
  { id := "beavers_etal2021_36b"
    source := ⟨"beavers-etal-2021", "(36b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "Kim-ne parat kach phoɖ-li."
    discourseSegments := []
    glossedTokens := [("Kim-ne", "Kim-ERG"), ("parat", "again"), ("kach", "glass.F.SG.NOM"), ("phoɖ-li", "break-PFV.F.SG")]
    translation := "Kim broke the glass again."
    context := "Small pieces of glass, manufactured in that size, are assembled into a single pane, which Kim then shatters."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beavers_etal2021_38b : LinguisticExample :=
  { id := "beavers_etal2021_38b"
    source := ⟨"beavers-etal-2021", "(38b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Maria eftiakse ke tin tileorasi."
    discourseSegments := []
    glossedTokens := [("I", "the"), ("Maria", "Mary"), ("eftiakse", "fixed"), ("ke", "also"), ("tin", "the"), ("tileorasi", "television")]
    translation := "Mary fixed the television too."
    context := "Mary bought a new TV and a new laptop. The laptop was working fine, but the TV was not. Mary brought her tools."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "additive restitutive"), ("root class", "result")]
    comment := "Spathas's additive test: ftiahno 'fix' rejects the restitutive-like additive reading, patterning with result roots."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [beavers_etal2021_1c, beavers_etal2021_7a, beavers_etal2021_10a, beavers_etal2021_11c, beavers_etal2021_13, beavers_etal2021_15a, beavers_etal2021_16a, beavers_etal2021_25a, beavers_etal2021_26, beavers_etal2021_28a, beavers_etal2021_28b, beavers_etal2021_29b, beavers_etal2021_31, beavers_etal2021_32, beavers_etal2021_33b, beavers_etal2021_35b, beavers_etal2021_36b, beavers_etal2021_38b]

end BeaversEtAl2021.Examples
