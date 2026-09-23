module

public import Linglib.Data.Examples.Schema

/-!
# `Sassoon2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Sassoon2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sassoon2013.Examples`.
-/

@[expose] public section

namespace Sassoon2013.Examples

open Data.Examples

def healthy : LinguisticExample :=
  { id := "sassoon2013_healthy"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "healthy"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "54"), ("disj", "11"), ("polarity", "660"), ("positive", "true"), ("totality", "87"), ("standard", "total"), ("antonym", "sick")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def normal : LinguisticExample :=
  { id := "sassoon2013_normal"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "normal"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "69"), ("disj", "10"), ("polarity", "565"), ("positive", "true"), ("totality", "98"), ("standard", "total"), ("antonym", "abnormal")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def typical : LinguisticExample :=
  { id := "sassoon2013_typical"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "typical"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "54"), ("disj", "9"), ("polarity", "420"), ("positive", "true"), ("totality", "92"), ("standard", "total"), ("antonym", "atypical")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def similar : LinguisticExample :=
  { id := "sassoon2013_similar"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "similar"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "80"), ("disj", "67"), ("polarity", "450"), ("positive", "true"), ("totality", "50"), ("standard", "partial"), ("antonym", "dissimilar")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def identical : LinguisticExample :=
  { id := "sassoon2013_identical"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "identical"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "86"), ("disj", "49"), ("polarity", "415"), ("positive", "true"), ("totality", "89"), ("standard", "total"), ("antonym", "different")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def good : LinguisticExample :=
  { id := "sassoon2013_good"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "good"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "24"), ("disj", "21"), ("polarity", "645"), ("positive", "true"), ("totality", "90"), ("standard", "total"), ("antonym", "bad")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def familiar : LinguisticExample :=
  { id := "sassoon2013_familiar"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "familiar"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "45"), ("disj", "9"), ("polarity", "580"), ("positive", "true"), ("totality", "68"), ("standard", "partial"), ("antonym", "unfamiliar")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def intelligent : LinguisticExample :=
  { id := "sassoon2013_intelligent"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "intelligent"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "37"), ("disj", "41"), ("polarity", "670"), ("positive", "true"), ("totality", "71"), ("standard", "relative")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def healthier : LinguisticExample :=
  { id := "sassoon2013_healthier"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "healthier"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "35"), ("disj", "9"), ("polarity", "605"), ("positive", "true"), ("totality", "3"), ("standard", "partial"), ("base", "healthy")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def better : LinguisticExample :=
  { id := "sassoon2013_better"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "better"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "25"), ("disj", "25"), ("polarity", "630"), ("positive", "true"), ("totality", "3"), ("standard", "partial"), ("antonym", "worse"), ("base", "good")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sick : LinguisticExample :=
  { id := "sassoon2013_sick"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "sick"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "2"), ("disj", "26"), ("polarity", "150"), ("positive", "false"), ("totality", "49"), ("standard", "partial")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def abnormal : LinguisticExample :=
  { id := "sassoon2013_abnormal"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "abnormal"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "6"), ("disj", "20"), ("polarity", "180"), ("positive", "false"), ("totality", "35"), ("standard", "partial")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def atypical : LinguisticExample :=
  { id := "sassoon2013_atypical"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "atypical"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "19"), ("disj", "68"), ("polarity", "320"), ("positive", "false"), ("totality", "19"), ("standard", "partial")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def dissimilar : LinguisticExample :=
  { id := "sassoon2013_dissimilar"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dissimilar"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "58"), ("disj", "83"), ("polarity", "280"), ("positive", "false"), ("totality", "89"), ("standard", "total")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def different : LinguisticExample :=
  { id := "sassoon2013_different"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "different"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "13"), ("disj", "40"), ("polarity", "340"), ("positive", "false"), ("totality", "38"), ("standard", "partial")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bad : LinguisticExample :=
  { id := "sassoon2013_bad"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "bad"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "3"), ("disj", "55"), ("polarity", "110"), ("positive", "false"), ("totality", "73"), ("standard", "partial")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unfamiliar : LinguisticExample :=
  { id := "sassoon2013_unfamiliar"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "unfamiliar"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "15"), ("disj", "27"), ("polarity", "260"), ("positive", "false"), ("totality", "85"), ("standard", "total")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def worse : LinguisticExample :=
  { id := "sassoon2013_worse"
    source := ⟨"sassoon-2013", "Tables 2–4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "worse"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conj", "20"), ("disj", "32"), ("polarity", "140"), ("positive", "false"), ("totality", "2"), ("standard", "partial"), ("base", "bad")]
    comment := "conj and disj are the percentages of dimensional uses among exception phrases in positive and negated contexts; polarity is the mean judgment on the 1–7 scale in hundredths; totality is the normalized totality index; standard is the inference-test classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [healthy, normal, typical, similar, identical, good, familiar, intelligent, healthier, better, sick, abnormal, atypical, dissimilar, different, bad, unfamiliar, worse]

end Sassoon2013.Examples
