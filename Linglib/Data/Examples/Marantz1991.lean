import Linglib.Data.Examples.Schema

/-!
# `Marantz1991` — typed example data

Auto-generated from `Linglib/Data/Examples/Marantz1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Marantz1991.Examples`.
-/

namespace Marantz1991.Examples

open Data.Examples

def m1991_1a : LinguisticExample :=
  { id := "m1991_1a"
    source := ⟨"marantz-1991", "(1a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vano pikr-ob-s marikaze."
    discourseSegments := []
    glossedTokens := [("vano", "Vano.NOM"), ("pikr-ob-s", "think-INFL.I"), ("marikaze", "Marika.on")]
    translation := "Vano is thinking about Marika."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "I"), ("subject", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_1b : LinguisticExample :=
  { id := "m1991_1b"
    source := ⟨"marantz-1991", "(1b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vano-m i-pikr-a marikaze."
    discourseSegments := []
    glossedTokens := [("vano-m", "Vano-ERG"), ("i-pikr-a", "think-INFL.II"), ("marikaze", "Marika.on")]
    translation := "Vano thought about Marika."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "II"), ("subject", "ERG")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_1c : LinguisticExample :=
  { id := "m1991_1c"
    source := ⟨"marantz-1991", "(1c)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "nino gia-s surateb-s a-čven-eb-s."
    discourseSegments := []
    glossedTokens := [("nino", "Nino.NOM"), ("gia-s", "Gia-DAT"), ("surateb-s", "pictures-DAT"), ("a-čven-eb-s", "show-INFL.I")]
    translation := "Nino is showing pictures to Gia."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("inflection", "I"), ("subject", "NOM"), ("object", "DAT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_1d : LinguisticExample :=
  { id := "m1991_1d"
    source := ⟨"marantz-1991", "(1d)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "nino-m gia-s surateb-i a-čven-a"
    discourseSegments := []
    glossedTokens := [("nino-m", "Nino-ERG"), ("gia-s", "Gia-DAT"), ("surateb-i", "pictures-NOM"), ("a-čven-a", "show-INFL.II")]
    translation := "Nino showed the pictures to Gia."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("inflection", "II"), ("subject", "ERG"), ("object", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_2a : LinguisticExample :=
  { id := "m1991_2a"
    source := ⟨"marantz-1991", "(2a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "es saxl-i ivane-s a=u-šendeb-a."
    discourseSegments := []
    glossedTokens := [("es", "this"), ("saxl-i", "house-NOM"), ("ivane-s", "Ivan-DAT"), ("a=u-šendeb-a", "PreV=built-INFL.I.3SG")]
    translation := "This house will be built for Ivan."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "I"), ("subject", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_2b : LinguisticExample :=
  { id := "m1991_2b"
    source := ⟨"marantz-1991", "(2b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "es saxl-i ivane-s a=u-šend-a."
    discourseSegments := []
    glossedTokens := [("es", "this"), ("saxl-i", "house-NOM"), ("ivane-s", "Ivan-DAT"), ("a=u-šend-a", "PreV=built-INFL.II.3SG")]
    translation := "This house was built for Ivan."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "II"), ("subject", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_3a : LinguisticExample :=
  { id := "m1991_3a"
    source := ⟨"marantz-1991", "(3a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "šen pelamuš-i g-i-qvar-s."
    discourseSegments := []
    glossedTokens := [("šen", "you.DAT"), ("pelamuš-i", "pelamusi-NOM"), ("g-i-qvar-s", "AGR-like-INFL.I")]
    translation := "You like pelamusi."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "psych"), ("inflection", "I"), ("subject", "DAT"), ("object", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_3b : LinguisticExample :=
  { id := "m1991_3b"
    source := ⟨"marantz-1991", "(3b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "šen pelamuš-i g-e-qvar-e."
    discourseSegments := []
    glossedTokens := [("šen", "you.DAT"), ("pelamuš-i", "pelamusi-NOM"), ("g-e-qvar-e", "AGR-like-INFL.II")]
    translation := "You liked pelamusi."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "psych"), ("inflection", "II"), ("subject", "DAT"), ("object", "NOM")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_4a : LinguisticExample :=
  { id := "m1991_4a"
    source := ⟨"marantz-1991", "(4a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "siita aayii."
    discourseSegments := []
    glossedTokens := [("siita", "Sita.FEM"), ("aayii", "arrived/came-FEM")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "perfect"), ("subject", "NOM")]
    comment := "The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_4a_erg : LinguisticExample :=
  { id := "m1991_4a_erg"
    source := ⟨"marantz-1991", "(4a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "siita ne aayii."
    discourseSegments := []
    glossedTokens := [("siita", "Sita.FEM"), ("ne", "ERG"), ("aayii", "arrived/came-FEM")]
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "perfect"), ("subject", "ERG")]
    comment := "The paper gives the ergative marker as excluded, *siita (*ne) aayii*. The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_4b : LinguisticExample :=
  { id := "m1991_4b"
    source := ⟨"marantz-1991", "(4b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kutte bhoNke."
    discourseSegments := []
    glossedTokens := [("kutte", "dogs.MASC.PL"), ("bhoNke", "barked.MASC.PL")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "perfect"), ("subject", "NOM")]
    comment := "The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_4c : LinguisticExample :=
  { id := "m1991_4c"
    source := ⟨"marantz-1991", "(4c)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kuttoN ne bhoNkaa."
    discourseSegments := []
    glossedTokens := [("kuttoN", "dogs.PL"), ("ne", "ERG"), ("bhoNkaa", "barked.MASC.SG")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "perfect"), ("subject", "ERG")]
    comment := "The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_4d : LinguisticExample :=
  { id := "m1991_4d"
    source := ⟨"marantz-1991", "(4d)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "raam ne roTii khaayii thii."
    discourseSegments := []
    glossedTokens := [("raam", "Ram.MASC"), ("ne", "ERG"), ("roTii", "bread.FEM"), ("khaayii", "eat.FEM"), ("thii", "be.PAST.FEM")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("inflection", "perfect"), ("subject", "ERG"), ("object", "NOM")]
    comment := "The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_5a : LinguisticExample :=
  { id := "m1991_5a"
    source := ⟨"marantz-1991", "(5a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Ni etorri naiz."
    discourseSegments := []
    glossedTokens := [("Ni", "I.ABS"), ("etorri", "come"), ("naiz", "1SG.be")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("subject", "ABS")]
    comment := "The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_5b : LinguisticExample :=
  { id := "m1991_5b"
    source := ⟨"marantz-1991", "(5b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik lan egin dut."
    discourseSegments := []
    glossedTokens := [("Nik", "I.ERG"), ("lan", "work"), ("egin", "do"), ("dut", "have.1SG")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("subject", "ERG")]
    comment := "The paper gives no free translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def m1991_5c : LinguisticExample :=
  { id := "m1991_5c"
    source := ⟨"marantz-1991", "(5c)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik libura ekarri dut."
    discourseSegments := []
    glossedTokens := [("Nik", "I.ERG"), ("libura", "book.ABS"), ("ekarri", "bought"), ("dut", "have.1SG")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("subject", "ERG"), ("object", "ABS")]
    comment := "The paper gives no free translation and glosses *ekarri* as 'bought'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [m1991_1a, m1991_1b, m1991_1c, m1991_1d, m1991_2a, m1991_2b, m1991_3a, m1991_3b, m1991_4a, m1991_4a_erg, m1991_4b, m1991_4c, m1991_4d, m1991_5a, m1991_5b, m1991_5c]

end Marantz1991.Examples
