import Linglib.Data.Examples.Schema

/-!
# `Landau2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Landau2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Landau2026.Examples`.
-/

namespace Landau2026.Examples

open Data.Examples

def hebrewEN : LinguisticExample :=
  { id := "landau2026_hebrewEN"
    source := ⟨"landau-2026", "(18a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš la'hakot še-ahavti et ha-šeni."
    discourseSegments := []
    glossedTokens := []
    translation := "(There are bands that I liked the second one.)"
    context := "Empty noun (EN), deep anaphor: a bare n head hosting a resumptive bound by an Ā-operator."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "nP"), ("depth", "deep"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")]
    comment := "Landau 2026, §2.2 (18a). EN fails EIR: no internal structure to host the resumptive, so the Ā-operator violates the BVQ. NP-ellipsis previously established; EIR gives additional confirmation via the EN/ENP contrast."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hebrewENP : LinguisticExample :=
  { id := "landau2026_hebrewENP"
    source := ⟨"landau-2026", "(19a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš la'hakot še-ahavti et ha-albom ha-rišon šela'hen, ve-yeš la'hakot še-ahavti et ha-šeni."
    discourseSegments := []
    glossedTokens := []
    translation := "There are bands that I liked their first album, and there are bands that I liked their second one."
    context := "Elided noun phrase (ENP), surface anaphor: full nP structure deleted under identity, licensed by [E] on Num."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("domain", "nP"), ("depth", "surface"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, maximizing relative")]
    comment := "Landau 2026, §2.2 (19a). ENP passes EIR: the resumptive inside the elided nP supplies the variable the operator binds."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hebrewNCA_DP : LinguisticExample :=
  { id := "landau2026_hebrewNCA_DP"
    source := ⟨"landau-2026", "(31a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš li xaver exad še-maxarti."
    discourseSegments := []
    glossedTokens := []
    translation := "(I have one friend that I sold.)"
    context := "Null complement anaphora (NCA) / pro, deep anaphor in the DP domain."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "DP"), ("depth", "deep"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")]
    comment := "Landau 2026, §3.2 (31a). NCA/pro fails EIR: no internal structure. The existence of AE in Hebrew was debated; EIR provides a novel argument."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hebrewAE : LinguisticExample :=
  { id := "landau2026_hebrewAE"
    source := ⟨"landau-2026", "(32a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš li xaver še-kaniti et ha-oto šelo, ve-yeš li xaver axer še-maxarti."
    discourseSegments := []
    glossedTokens := []
    translation := "I have one friend whose car I bought and I have another one whose car I sold."
    context := "Argument ellipsis (AE) / DP-ellipsis, surface anaphor: full DP structure deleted under identity."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("domain", "DP"), ("depth", "surface"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")]
    comment := "Landau 2026, §3.2 (32a). AE passes EIR: a resumptive inside the elided DP supplies the variable. Novel argument for AE in Hebrew."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hebrewNCA_PP : LinguisticExample :=
  { id := "landau2026_hebrewNCA_PP"
    source := ⟨"landau-2026", "(37a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš irgunim še-ani lo xotemet."
    discourseSegments := []
    glossedTokens := []
    translation := "(There are organizations that I don't sign.)"
    context := "Null PP via NCA, deep anaphor: PP argument omitted, content recovered pragmatically."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "PP"), ("depth", "deep"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")]
    comment := "Landau 2026, §4.2 (37a). Null PP via NCA fails EIR: no internal structure."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hebrewPPE : LinguisticExample :=
  { id := "landau2026_hebrewPPE"
    source := ⟨"landau-2026", "(38a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš irgunim še-ani xotemet al ha-acumot šelahem, ve-yeš irgunim še-ani lo xotemet."
    discourseSegments := []
    glossedTokens := []
    translation := "There are organizations that I sign their petitions and there are organizations that I don't."
    context := "PP-ellipsis (PPE), surface anaphor: full PP structure deleted under identity. Data are Landau's own (first documented in Vardi 2022)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("domain", "PP"), ("depth", "surface"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")]
    comment := "Landau 2026, §4.2 (38a). PPE passes EIR: first robust evidence for PP-ellipsis; the paper argues this holds cross-linguistically, not only in Hebrew."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def englishVPE : LinguisticExample :=
  { id := "landau2026_englishVPE"
    source := ⟨"landau-2026", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Deep Purple, I never bought their records. Led Zeppelin, I did."
    discourseSegments := ["Deep Purple, I never bought their records.", "Led Zeppelin, I did."]
    glossedTokens := []
    translation := "Deep Purple, I never bought their records. Led Zeppelin, I did."
    context := "VP-ellipsis, surface anaphor: left-dislocated constituent binds a resumptive possessive inside the elided VP. Contrastive baseline for do so."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "surface"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")]
    comment := "Landau 2026, §5 (44a). VP-ellipsis passes EIR."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def englishDoSo : LinguisticExample :=
  { id := "landau2026_englishDoSo"
    source := ⟨"landau-2026", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Deep Purple, I never bought their records. Led Zeppelin, I did so."
    discourseSegments := ["Deep Purple, I never bought their records.", "Led Zeppelin, I did so."]
    glossedTokens := []
    translation := "Deep Purple, I never bought their records. Led Zeppelin, I did so."
    context := "do so, deep VP anaphor: left-dislocation with resumptive binding into do so is ungrammatical."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")]
    comment := "Landau 2026, §5 (44c). do so fails EIR; Ā-extraction is also impossible, but that is ambiguous between deep anaphor and derivational bleeding. EIR resolves the ambiguity: do so is deep [bruening-2019]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def dutchDatDoen : LinguisticExample :=
  { id := "landau2026_dutchDatDoen"
    source := ⟨"landau-2026", "(45a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan, ik heb zijn muffins al eens geproefd; maar Wim, ik heb dat nog niet gedaan."
    discourseSegments := []
    glossedTokens := []
    translation := "Jan, I have already tasted his muffins once, but Wim, I haven't done that."
    context := "dat doen 'do that', deep VP anaphor: blocks most Ā-extractions and fails EIR."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")]
    comment := "Landau 2026, §5 (45a). dat doen fails EIR (Marcel den Dikken, p.c.)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def danishDet : LinguisticExample :=
  { id := "landau2026_danishDet"
    source := ⟨"landau-2026", "(46b)"⟩
    reportedIn := none
    language := "dani1285"
    primaryText := "Den gamle bager, jeg har smagt hans rugbrød, men den nye bager, jeg har det ikke."
    discourseSegments := []
    glossedTokens := []
    translation := "The old baker, I have tasted his rye bread, but the new baker, I haven't."
    context := "det 'it', deep VP anaphor: allows A-dependencies but not Ā-dependencies, so it fails EIR."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")]
    comment := "Landau 2026, §5 (46b). det fails EIR (Line Mikkelsen, p.c.). The grammatical baseline is (46a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def koreanNullObj : LinguisticExample :=
  { id := "landau2026_koreanNullObj"
    source := ⟨"landau-2026", "(47b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Na-uy i chinkwu, nay-ka ku-uy cha-lul sasse. Nay-uy ce chinkwu, nay-ka phallasse."
    discourseSegments := ["Na-uy i chinkwu, nay-ka ku-uy cha-lul sasse.", "Nay-uy ce chinkwu, nay-ka phallasse."]
    glossedTokens := []
    translation := "This friend of mine, I bought his car. THAT friend of mine, I sold his car."
    context := "Korean null object, deep anaphor (pro): left-dislocation mandates a resumptive, but the null object fails to host one."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("domain", "DP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")]
    comment := "Landau 2026, §5 (47b). Korean null object fails EIR (Heejeong Ko, p.c.), supporting the pro analysis over AE. The grammatical baseline is (47a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [hebrewEN, hebrewENP, hebrewNCA_DP, hebrewAE, hebrewNCA_PP, hebrewPPE, englishVPE, englishDoSo, dutchDatDoen, danishDet, koreanNullObj]

end Landau2026.Examples
