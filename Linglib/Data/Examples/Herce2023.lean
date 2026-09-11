import Linglib.Data.Examples.Schema

/-!
# `Herce2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Herce2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Herce2023.Examples`.
-/

namespace Herce2023.Examples

open Data.Examples

def venir_1sg_ind : LinguisticExample :=
  { id := "herce2023_venir_1sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "veng-o"
    discourseSegments := []
    glossedTokens := [("veng-o", "come-1SG.PRS.IND")]
    translation := "I come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.IND"), ("lexeme", "venir"), ("stem", "veng")]
    comment := "The velar stem of the L-morphome."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def venir_2sg_ind : LinguisticExample :=
  { id := "herce2023_venir_2sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "vien-es"
    discourseSegments := []
    glossedTokens := [("vien-es", "come-2SG.PRS.IND")]
    translation := "you come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "2SG.PRS.IND"), ("lexeme", "venir"), ("stem", "vien")]
    comment := "The diphthongized stem outside the L-morphome."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def venir_1pl_ind : LinguisticExample :=
  { id := "herce2023_venir_1pl_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "ven-imos"
    discourseSegments := []
    glossedTokens := [("ven-imos", "come-1PL.PRS.IND")]
    translation := "we come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "1PL.PRS.IND"), ("lexeme", "venir"), ("stem", "ven")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def venir_1sg_sbjv : LinguisticExample :=
  { id := "herce2023_venir_1sg_sbjv"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "veng-a"
    discourseSegments := []
    glossedTokens := [("veng-a", "come-1SG.PRS.SBJV")]
    translation := "(that) I come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.SBJV"), ("lexeme", "venir"), ("stem", "veng")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nacer_1sg_ind : LinguisticExample :=
  { id := "herce2023_nacer_1sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "naθk-o"
    discourseSegments := []
    glossedTokens := [("naθk-o", "be.born-1SG.PRS.IND")]
    translation := "I am born"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.IND"), ("lexeme", "nacer"), ("stem", "naθk")]
    comment := "The velar stem of the L-morphome under a different exponent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nacer_1pl_ind : LinguisticExample :=
  { id := "herce2023_nacer_1pl_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "naθ-emos"
    discourseSegments := []
    glossedTokens := [("naθ-emos", "be.born-1PL.PRS.IND")]
    translation := "we are born"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "1PL.PRS.IND"), ("lexeme", "nacer"), ("stem", "naθ")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def caber_1sg_ind : LinguisticExample :=
  { id := "herce2023_caber_1sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "kep-o"
    discourseSegments := []
    glossedTokens := [("kep-o", "fit-1SG.PRS.IND")]
    translation := "I fit"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "1SG.PRS.IND"), ("lexeme", "caber"), ("stem", "kep")]
    comment := "The weakly suppletive stem of the L-morphome."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def caber_2sg_ind : LinguisticExample :=
  { id := "herce2023_caber_2sg_ind"
    source := ⟨"herce-2023", "Table 1.2"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "kab-es"
    discourseSegments := []
    glossedTokens := [("kab-es", "fit-2SG.PRS.IND")]
    translation := "you fit"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "2SG.PRS.IND"), ("lexeme", "caber"), ("stem", "kab")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ra_npst_1sg : LinguisticExample :=
  { id := "herce2023_ra_npst_1sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-hi"
    discourseSegments := []
    glossedTokens := [("ra-hi", "come-NPST.1SG")]
    translation := "I come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "NPST.1SG"), ("lexeme", "ra")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ra_npst_2sg : LinguisticExample :=
  { id := "herce2023_ra_npst_2sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-he-n"
    discourseSegments := []
    glossedTokens := [("ra-he-n", "come-NPST-1PL/2")]
    translation := "you come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "NPST.2SG"), ("lexeme", "ra")]
    comment := "The suffix shared by the first person plural and the second person; the second person plural adds an optional -i."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ra_npst_3sg : LinguisticExample :=
  { id := "herce2023_ra_npst_3sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-ni"
    discourseSegments := []
    glossedTokens := [("ra-ni", "come-NPST.3")]
    translation := "he/she comes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "NPST.3SG"), ("lexeme", "ra")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ra_pst_2sg : LinguisticExample :=
  { id := "herce2023_ra_pst_2sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-n-su"
    discourseSegments := []
    glossedTokens := [("ra-n-su", "come-1PL/2-PST")]
    translation := "you came"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "PST.2SG"), ("lexeme", "ra")]
    comment := "The same cells share a different suffix in the past: the syncretism recurs across tenses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ra_pst_1sg : LinguisticExample :=
  { id := "herce2023_ra_pst_1sg"
    source := ⟨"herce-2023", "Table 4.32"⟩
    reportedIn := none
    language := "darm1243"
    primaryText := "ra-ju"
    discourseSegments := []
    glossedTokens := [("ra-ju", "come-PST")]
    translation := "I came"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cell", "PST.1SG"), ("lexeme", "ra")]
    comment := "The past form of the first person singular and the third person."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [venir_1sg_ind, venir_2sg_ind, venir_1pl_ind, venir_1sg_sbjv, nacer_1sg_ind, nacer_1pl_ind, caber_1sg_ind, caber_2sg_ind, ra_npst_1sg, ra_npst_2sg, ra_npst_3sg, ra_pst_2sg, ra_pst_1sg]

end Herce2023.Examples
