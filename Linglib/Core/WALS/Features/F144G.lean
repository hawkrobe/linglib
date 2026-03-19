/-!
# WALS Feature 144G: Optional Double Negation in SVO languages
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144G`.

Chapter 144, 35 languages.
-/

namespace Core.WALS.F144G

/-- WALS 144G values. -/
inductive OptionalDoubleNegationInSvoLanguages where
  | snegvo  -- SNegVO(Neg) (6 languages)
  | svoneg  -- S(Neg)VONeg (8 languages)
  | svnego  -- S(Neg)VNegO (3 languages)
  | snegvo_4  -- SNegV(Neg)O (1 languages)
  | svoneg_5  -- (Neg)SVONeg (2 languages)
  | svnego_6  -- SVNegO(Neg) (1 languages)
  | negsVO  -- NegS[V(-Neg)]O (1 languages)
  | sVNego  -- S[(Neg-)V]NegO (1 languages)
  | sNegVO  -- S[Neg-V]O(Neg) (2 languages)
  | snegvoSvnegoNegtone  -- SNegVO/SVNegO&NegTone (1 languages)
  | sVO  -- S(Neg)[V(-Neg)]O (1 languages)
  | sNegVO_12  -- S[Neg-V(-Neg)]O (2 languages)
  | svonegSvoneg  -- (Neg)SVONeg/S(Neg)VONeg (1 languages)
  | sNegVONegsvnego  -- S[Neg-V]O/NegSVNegO (1 languages)
  | snegVNegOSNegVNegO  -- SNeg[V-Neg]O/S[Neg-V-Neg]O (1 languages)
  | sVONegv  -- S[V(-Neg)]O & NegV (1 languages)
  | svoSovVNeg  -- SVO/SOV & (Neg)[V-Neg] (1 languages)
  | svoVsoNegvVnegNegvneg  -- SVO/VSO & NegV/VNeg/NegVNeg (1 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144G datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : OptionalDoubleNegationInSvoLanguages
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144G dataset (35 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "adz", language := "Adzera", iso := "adz", value := .sNegVO }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .snegVNegOSNegVNegO }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .snegvo }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .snegvo }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .sNegVO }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .svoneg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .snegvo_4 }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .snegvo }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .sNegVONegsvnego }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .svnego }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .snegvoSvnegoNegtone }
  , { walsCode := "fre", language := "French", iso := "fra", value := .svnego }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .svoneg_5 }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .svoneg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .snegvo }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .sVNego }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .svoSovVNeg }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .svonegSvoneg }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .svnego_6 }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .svnego }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .svoneg }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .svoneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .svoneg_5 }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .sVO }
  , { walsCode := "one", language := "One", iso := "aun", value := .svoneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .svoneg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .snegvo }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .svoVsoNegvVnegNegvneg }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .negsVO }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .svoneg }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .svoneg }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .snegvo }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .sNegVO_12 }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .sVONegv }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .sNegVO_12 }
  ]

-- Count verification
theorem total_count : allData.length = 35 := by native_decide

theorem count_snegvo :
    (allData.filter (·.value == .snegvo)).length = 6 := by native_decide
theorem count_svoneg :
    (allData.filter (·.value == .svoneg)).length = 8 := by native_decide
theorem count_svnego :
    (allData.filter (·.value == .svnego)).length = 3 := by native_decide
theorem count_snegvo_4 :
    (allData.filter (·.value == .snegvo_4)).length = 1 := by native_decide
theorem count_svoneg_5 :
    (allData.filter (·.value == .svoneg_5)).length = 2 := by native_decide
theorem count_svnego_6 :
    (allData.filter (·.value == .svnego_6)).length = 1 := by native_decide
theorem count_negsVO :
    (allData.filter (·.value == .negsVO)).length = 1 := by native_decide
theorem count_sVNego :
    (allData.filter (·.value == .sVNego)).length = 1 := by native_decide
theorem count_sNegVO :
    (allData.filter (·.value == .sNegVO)).length = 2 := by native_decide
theorem count_snegvoSvnegoNegtone :
    (allData.filter (·.value == .snegvoSvnegoNegtone)).length = 1 := by native_decide
theorem count_sVO :
    (allData.filter (·.value == .sVO)).length = 1 := by native_decide
theorem count_sNegVO_12 :
    (allData.filter (·.value == .sNegVO_12)).length = 2 := by native_decide
theorem count_svonegSvoneg :
    (allData.filter (·.value == .svonegSvoneg)).length = 1 := by native_decide
theorem count_sNegVONegsvnego :
    (allData.filter (·.value == .sNegVONegsvnego)).length = 1 := by native_decide
theorem count_snegVNegOSNegVNegO :
    (allData.filter (·.value == .snegVNegOSNegVNegO)).length = 1 := by native_decide
theorem count_sVONegv :
    (allData.filter (·.value == .sVONegv)).length = 1 := by native_decide
theorem count_svoSovVNeg :
    (allData.filter (·.value == .svoSovVNeg)).length = 1 := by native_decide
theorem count_svoVsoNegvVnegNegvneg :
    (allData.filter (·.value == .svoVsoNegvVnegNegvneg)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144G
