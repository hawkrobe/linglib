module

public import Linglib.Data.Examples.Schema

/-!
# `Alderete2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Alderete2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Alderete2001.Examples`.
-/

@[expose] public section

namespace Alderete2001.Examples

open Data.Examples

def ex_6a_bat : Datum :=
  { id := "alderete2001_6a_bat"
    source := ⟨"alderete-2001", "(6a)"⟩
    reportedIn := none
    language := "luok1236"
    primaryText := "bed-e"
    glossedTokens := [("bed-e", "arm-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "bat"), ("derivative", "bed-e"), ("change", "voicing")] }

def ex_6a_luth : Datum :=
  { id := "alderete2001_6a_luth"
    source := ⟨"alderete-2001", "(6a)"⟩
    reportedIn := none
    language := "luok1236"
    primaryText := "luð-e"
    glossedTokens := [("luð-e", "walking_stick-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "luθ"), ("derivative", "luð-e"), ("change", "voicing")] }

def ex_6b_cogo : Datum :=
  { id := "alderete2001_6b_cogo"
    source := ⟨"alderete-2001", "(6b)"⟩
    reportedIn := none
    language := "luok1236"
    primaryText := "ʧok-e"
    glossedTokens := [("ʧok-e", "bone-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "ʧogo"), ("derivative", "ʧok-e"), ("change", "devoicing")] }

def ex_6b_owadu : Datum :=
  { id := "alderete2001_6b_owadu"
    source := ⟨"alderete-2001", "(6b)"⟩
    reportedIn := none
    language := "luok1236"
    primaryText := "owet-e"
    glossedTokens := [("owet-e", "brother-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "owadu"), ("derivative", "owet-e"), ("change", "devoicing")] }

def ex_1_yon : Datum :=
  { id := "alderete2001_1_yon"
    source := ⟨"alderete-2001", "(1)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "yón-dara"
    glossedTokens := [("yón-dara", "read-if")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "yón"), ("derivative", "yón-dara"), ("affix", "-tára"), ("affixClass", "recessive"), ("baseAccented", "true")] }

def ex_1_yon2 : Datum :=
  { id := "alderete2001_1_yon2"
    source := ⟨"alderete-2001", "(1)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "yon-dára"
    glossedTokens := [("yon-dára", "call-if")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "yon"), ("derivative", "yon-dára"), ("affix", "-tára"), ("affixClass", "recessive"), ("baseAccented", "false")] }

def ex_17_abura : Datum :=
  { id := "alderete2001_17_abura"
    source := ⟨"alderete-2001", "(17a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "abura-ppó-i"
    glossedTokens := [("abura-ppó-i", "oily")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "abura"), ("derivative", "abura-ppó-i"), ("affix", "-ppó"), ("affixClass", "dominant"), ("affixAccented", "true"), ("baseAccented", "false")] }

def ex_17_kaze : Datum :=
  { id := "alderete2001_17_kaze"
    source := ⟨"alderete-2001", "(17a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kaze-ppó-i"
    glossedTokens := [("kaze-ppó-i", "sniffily")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "kaze"), ("derivative", "kaze-ppó-i"), ("affix", "-ppó"), ("affixClass", "dominant"), ("affixAccented", "true"), ("baseAccented", "false")] }

def ex_17_kodomo : Datum :=
  { id := "alderete2001_17_kodomo"
    source := ⟨"alderete-2001", "(17a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kodomo-ppó-i"
    glossedTokens := [("kodomo-ppó-i", "childish")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "kodomo"), ("derivative", "kodomo-ppó-i"), ("affix", "-ppó"), ("affixClass", "dominant"), ("affixAccented", "true"), ("baseAccented", "false")] }

def ex_17_ada : Datum :=
  { id := "alderete2001_17_ada"
    source := ⟨"alderete-2001", "(17b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ada-ppó-i"
    glossedTokens := [("ada-ppó-i", "coquettish")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "adá"), ("derivative", "ada-ppó-i"), ("affix", "-ppó"), ("affixClass", "dominant"), ("affixAccented", "true"), ("baseAccented", "true")] }

def ex_17_netu : Datum :=
  { id := "alderete2001_17_netu"
    source := ⟨"alderete-2001", "(17b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "netu-ppó-i"
    glossedTokens := [("netu-ppó-i", "zealous")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "netú"), ("derivative", "netu-ppó-i"), ("affix", "-ppó"), ("affixClass", "dominant"), ("affixAccented", "true"), ("baseAccented", "true")] }

def ex_17_kiza : Datum :=
  { id := "alderete2001_17_kiza"
    source := ⟨"alderete-2001", "(17b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kiza-ppó-i"
    glossedTokens := [("kiza-ppó-i", "affected")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "kíza"), ("derivative", "kiza-ppó-i"), ("affix", "-ppó"), ("affixClass", "dominant"), ("affixAccented", "true"), ("baseAccented", "true")] }

def ex_18_edo : Datum :=
  { id := "alderete2001_18_edo"
    source := ⟨"alderete-2001", "(18a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "edo-kko"
    glossedTokens := [("edo-kko", "native_of_Tokyo")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "edo"), ("derivative", "edo-kko"), ("affix", "-kko"), ("affixClass", "dominant"), ("affixAccented", "false"), ("baseAccented", "false")] }

def ex_18_niigata : Datum :=
  { id := "alderete2001_18_niigata"
    source := ⟨"alderete-2001", "(18a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "niigata-kko"
    glossedTokens := [("niigata-kko", "native_of_Niigata")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "niigata"), ("derivative", "niigata-kko"), ("affix", "-kko"), ("affixClass", "dominant"), ("affixAccented", "false"), ("baseAccented", "false")] }

def ex_18_oosaka : Datum :=
  { id := "alderete2001_18_oosaka"
    source := ⟨"alderete-2001", "(18a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "oosaka-kko"
    glossedTokens := [("oosaka-kko", "native_of_Osaka")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "oosaka"), ("derivative", "oosaka-kko"), ("affix", "-kko"), ("affixClass", "dominant"), ("affixAccented", "false"), ("baseAccented", "false")] }

def ex_18_koobe : Datum :=
  { id := "alderete2001_18_koobe"
    source := ⟨"alderete-2001", "(18b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "koobe-kko"
    glossedTokens := [("koobe-kko", "native_of_Kobe")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "kóobe"), ("derivative", "koobe-kko"), ("affix", "-kko"), ("affixClass", "dominant"), ("affixAccented", "false"), ("baseAccented", "true")] }

def ex_18_nagoya : Datum :=
  { id := "alderete2001_18_nagoya"
    source := ⟨"alderete-2001", "(18b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "nagoya-kko"
    glossedTokens := [("nagoya-kko", "native_of_Nagoya")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "nágoya"), ("derivative", "nagoya-kko"), ("affix", "-kko"), ("affixClass", "dominant"), ("affixAccented", "false"), ("baseAccented", "true")] }

def ex_18_nyuuyooku : Datum :=
  { id := "alderete2001_18_nyuuyooku"
    source := ⟨"alderete-2001", "(18b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "nyuuyooku-kko"
    glossedTokens := [("nyuuyooku-kko", "native_of_New_York")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "nyuuyóoku"), ("derivative", "nyuuyooku-kko"), ("affix", "-kko"), ("affixClass", "dominant"), ("affixAccented", "false"), ("baseAccented", "true")] }

def ex_42_wise_masculine : Datum :=
  { id := "alderete2001_42_wise_masculine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "wíiz-ə"
    glossedTokens := [("wíiz-ə", "wise-M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "wíís"), ("derivative", "wíiz-ə"), ("suffix", "masculine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_wise_feminine : Datum :=
  { id := "alderete2001_42_wise_feminine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "wíis"
    glossedTokens := [("wíis", "wise-F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "wíís"), ("derivative", "wíis"), ("suffix", "feminine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_wise_comparative : Datum :=
  { id := "alderete2001_42_wise_comparative"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "wíiz-ər"
    glossedTokens := [("wíiz-ər", "wise-COMP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "wíís"), ("derivative", "wíiz-ər"), ("suffix", "comparative"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_stiff_masculine : Datum :=
  { id := "alderete2001_42_stiff_masculine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "stíiv-ə"
    glossedTokens := [("stíiv-ə", "stiff-M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "stííf"), ("derivative", "stíiv-ə"), ("suffix", "masculine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_stiff_feminine : Datum :=
  { id := "alderete2001_42_stiff_feminine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "stíif"
    glossedTokens := [("stíif", "stiff-F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "stííf"), ("derivative", "stíif"), ("suffix", "feminine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_stiff_comparative : Datum :=
  { id := "alderete2001_42_stiff_comparative"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "stíiv-ər"
    glossedTokens := [("stíiv-ər", "stiff-COMP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "stííf"), ("derivative", "stíiv-ər"), ("suffix", "comparative"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_bald_masculine : Datum :=
  { id := "alderete2001_42_bald_masculine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "káal-ə"
    glossedTokens := [("káal-ə", "bald-M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "káál"), ("derivative", "káal-ə"), ("suffix", "masculine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_bald_feminine : Datum :=
  { id := "alderete2001_42_bald_feminine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "káal"
    glossedTokens := [("káal", "bald-F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "káál"), ("derivative", "káal"), ("suffix", "feminine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_bald_comparative : Datum :=
  { id := "alderete2001_42_bald_comparative"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "káal-ər"
    glossedTokens := [("káal-ər", "bald-COMP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "káál"), ("derivative", "káal-ər"), ("suffix", "comparative"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_paralysed_masculine : Datum :=
  { id := "alderete2001_42_paralysed_masculine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "láam-ə"
    glossedTokens := [("láam-ə", "paralysed-M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "láám"), ("derivative", "láam-ə"), ("suffix", "masculine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_paralysed_feminine : Datum :=
  { id := "alderete2001_42_paralysed_feminine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "láam"
    glossedTokens := [("láam", "paralysed-F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "láám"), ("derivative", "láam"), ("suffix", "feminine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_paralysed_comparative : Datum :=
  { id := "alderete2001_42_paralysed_comparative"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "láam-ər"
    glossedTokens := [("láam-ər", "paralysed-COMP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "láám"), ("derivative", "láam-ər"), ("suffix", "comparative"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_refined_masculine : Datum :=
  { id := "alderete2001_42_refined_masculine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "fíin-ə"
    glossedTokens := [("fíin-ə", "refined-M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "fíín"), ("derivative", "fíin-ə"), ("suffix", "masculine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_refined_feminine : Datum :=
  { id := "alderete2001_42_refined_feminine"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "fíin"
    glossedTokens := [("fíin", "refined-F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "fíín"), ("derivative", "fíin"), ("suffix", "feminine"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def ex_42_refined_comparative : Datum :=
  { id := "alderete2001_42_refined_comparative"
    source := ⟨"alderete-2001", "(42)"⟩
    reportedIn := none
    language := "limb1263"
    primaryText := "fíin-ər"
    glossedTokens := [("fíin-ər", "refined-COMP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("base", "fíín"), ("derivative", "fíin-ər"), ("suffix", "comparative"), ("baseTone", "dragging"), ("derivativeTone", "falling")] }

def all : List Datum := [ex_6a_bat, ex_6a_luth, ex_6b_cogo, ex_6b_owadu, ex_1_yon, ex_1_yon2, ex_17_abura, ex_17_kaze, ex_17_kodomo, ex_17_ada, ex_17_netu, ex_17_kiza, ex_18_edo, ex_18_niigata, ex_18_oosaka, ex_18_koobe, ex_18_nagoya, ex_18_nyuuyooku, ex_42_wise_masculine, ex_42_wise_feminine, ex_42_wise_comparative, ex_42_stiff_masculine, ex_42_stiff_feminine, ex_42_stiff_comparative, ex_42_bald_masculine, ex_42_bald_feminine, ex_42_bald_comparative, ex_42_paralysed_masculine, ex_42_paralysed_feminine, ex_42_paralysed_comparative, ex_42_refined_masculine, ex_42_refined_feminine, ex_42_refined_comparative]

end Alderete2001.Examples
