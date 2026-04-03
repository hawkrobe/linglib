import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144U: Double negation in verb-initial languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144U`.

Chapter 144, 17 languages.
-/

namespace Core.WALS.F144U

/-- WALS 144U values. -/
inductive DoubleNegationInVerbInitialLanguages where
  | negvnegso  -- NegVNegSO (1 languages)
  | negvnegos  -- NegVNegOS (1 languages)
  | negvsoneg  -- NegVSONeg (1 languages)
  | negnegvso  -- NegNegVSO (1 languages)
  | vnegsoneg  -- VNegSONeg (1 languages)
  | vsVoNegVNeg  -- VS & VO & [Neg-V-Neg] (1 languages)
  | negvosnegVnegosnegSnegvonegSvnegoneg  -- NegVOSNeg/VNegOSNeg/SNegVONeg/SVNegONeg (1 languages)
  | vsoneg  -- V(Neg)SONeg (1 languages)
  | negvso  -- Neg(Neg)VSO (1 languages)
  | negvsoNegVNegSo  -- NegVSO/[Neg-V-Neg]SO (1 languages)
  | negvsoOptstemchange  -- NegVSO&OptStemChange (1 languages)
  | svoVsoButNegVSo  -- SVO/VSO but [Neg-V]SO(Neg) (1 languages)
  | vsVoNegV  -- VS&VO&Neg[(Neg-)V] (2 languages)
  | vsVoNegvVNeg  -- VS&VO&NegV/[(Neg-)V-Neg] (1 languages)
  | vosNegvneg  -- VOS & NegVNeg (1 languages)
  | vsoSvoV  -- VSO/SVO & (Neg)V(Neg) (1 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 144U dataset (17 languages). -/
def allData : List (Datapoint DoubleNegationInVerbInitialLanguages) :=
  [ { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .vsVoNegV }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .vsVoNegVNeg }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .svoVsoButNegVSo }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .negvnegos }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .vosNegvneg }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .vsVoNegvVNeg }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vnegsoneg }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .negvnegso }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .negvsoneg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vsoneg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .negvosnegVnegosnegSnegvonegSvnegoneg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .vsVoNegV }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .negvsoNegVNegSo }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .negvso }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .vsoSvoV }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .negvsoOptstemchange }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .negnegvso }
  ]

-- Count verification
theorem total_count : allData.length = 17 := by native_decide

theorem count_negvnegso :
    (allData.filter (·.value == .negvnegso)).length = 1 := by native_decide
theorem count_negvnegos :
    (allData.filter (·.value == .negvnegos)).length = 1 := by native_decide
theorem count_negvsoneg :
    (allData.filter (·.value == .negvsoneg)).length = 1 := by native_decide
theorem count_negnegvso :
    (allData.filter (·.value == .negnegvso)).length = 1 := by native_decide
theorem count_vnegsoneg :
    (allData.filter (·.value == .vnegsoneg)).length = 1 := by native_decide
theorem count_vsVoNegVNeg :
    (allData.filter (·.value == .vsVoNegVNeg)).length = 1 := by native_decide
theorem count_negvosnegVnegosnegSnegvonegSvnegoneg :
    (allData.filter (·.value == .negvosnegVnegosnegSnegvonegSvnegoneg)).length = 1 := by native_decide
theorem count_vsoneg :
    (allData.filter (·.value == .vsoneg)).length = 1 := by native_decide
theorem count_negvso :
    (allData.filter (·.value == .negvso)).length = 1 := by native_decide
theorem count_negvsoNegVNegSo :
    (allData.filter (·.value == .negvsoNegVNegSo)).length = 1 := by native_decide
theorem count_negvsoOptstemchange :
    (allData.filter (·.value == .negvsoOptstemchange)).length = 1 := by native_decide
theorem count_svoVsoButNegVSo :
    (allData.filter (·.value == .svoVsoButNegVSo)).length = 1 := by native_decide
theorem count_vsVoNegV :
    (allData.filter (·.value == .vsVoNegV)).length = 2 := by native_decide
theorem count_vsVoNegvVNeg :
    (allData.filter (·.value == .vsVoNegvVNeg)).length = 1 := by native_decide
theorem count_vosNegvneg :
    (allData.filter (·.value == .vosNegvneg)).length = 1 := by native_decide
theorem count_vsoSvoV :
    (allData.filter (·.value == .vsoSvoV)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144U
