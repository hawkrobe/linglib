/-!
# WALS Feature 144O: Optional Double Negation in SOV languages
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144O`.

Chapter 144, 31 languages.
-/

namespace Core.WALS.F144O

/-- WALS 144O values. -/
inductive OptionalDoubleNegationInSovLanguages where
  | negsov  -- NegSOV(Neg) (1 languages)
  | sovneg  -- S(Neg)OVNeg (3 languages)
  | snegov  -- SNegOV(Neg) (1 languages)
  | snegoV  -- SNegO[V(-Neg)] (1 languages)
  | soVNeg  -- SO[(Neg-)V]Neg (1 languages)
  | soNegV  -- SO[Neg-V(-Neg)] (2 languages)
  | soVNeg_7  -- SO[(Neg-)V-Neg] (3 languages)
  | soVNeg_8  -- SO[V-Neg](Neg) (2 languages)
  | sovnegSoNegVNeg  -- SOVNeg/SO[Neg-V-Neg] (1 languages)
  | snegoV_10  -- SNegO[V(-Neg)](Neg) (1 languages)
  | sovButSNegVNegOSoVNeg  -- SOV but S[Neg-V-Neg]O/SO[V-Neg] (1 languages)
  | soNegVSovneg  -- SO[Neg-V-(Neg)]/SOVNeg (1 languages)
  | sovnegSovnegSovneg  -- (Neg)SOVNeg/S(Neg)OVNeg/SO(Neg)VNeg (3 languages)
  | soVSoV  -- S(Neg)O[V(-Neg)]/SO(Neg)[V(-Neg)] (1 languages)
  | sovVNeg  -- SOV & (Neg)[V-Neg] (2 languages)
  | sovV  -- SOV & (Neg)[V(-Neg)] (1 languages)
  | sovSvoNegV  -- SOV/SVO & Neg[V-(Neg)] (1 languages)
  | svOvV  -- SV & OV & (Neg)V(Neg) (1 languages)
  | svOvVNeg  -- SV & OV &  (Neg)[V-Neg] (1 languages)
  | svOvNegV  -- SV & OV &  [Neg-V(-Neg)] (1 languages)
  | svOvVNeg_21  -- SV & OV &  [(Neg-)V-Neg] (2 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144O datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : OptionalDoubleNegationInSovLanguages
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144O dataset (31 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "adg", language := "Adang", iso := "adn", value := .sovneg }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .soVSoV }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .soNegV }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .svOvVNeg_21 }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .soVNeg }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .sovneg }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .svOvVNeg_21 }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .sovnegSoNegVNeg }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .sovV }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .sovnegSovnegSovneg }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .sovSvoNegV }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .soVNeg_7 }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .sovButSNegVNegOSoVNeg }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .soNegV }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .sovnegSovnegSovneg }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .soVNeg_7 }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .sovVNeg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .snegoV_10 }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .soVNeg_8 }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .negsov }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .snegov }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .svOvNegV }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .soVNeg_8 }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .sovVNeg }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .sovneg }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .svOvV }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .soVNeg_7 }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .sovnegSovnegSovneg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .soNegVSovneg }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .snegoV }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .svOvVNeg }
  ]

-- Count verification
theorem total_count : allData.length = 31 := by native_decide

theorem count_negsov :
    (allData.filter (·.value == .negsov)).length = 1 := by native_decide
theorem count_sovneg :
    (allData.filter (·.value == .sovneg)).length = 3 := by native_decide
theorem count_snegov :
    (allData.filter (·.value == .snegov)).length = 1 := by native_decide
theorem count_snegoV :
    (allData.filter (·.value == .snegoV)).length = 1 := by native_decide
theorem count_soVNeg :
    (allData.filter (·.value == .soVNeg)).length = 1 := by native_decide
theorem count_soNegV :
    (allData.filter (·.value == .soNegV)).length = 2 := by native_decide
theorem count_soVNeg_7 :
    (allData.filter (·.value == .soVNeg_7)).length = 3 := by native_decide
theorem count_soVNeg_8 :
    (allData.filter (·.value == .soVNeg_8)).length = 2 := by native_decide
theorem count_sovnegSoNegVNeg :
    (allData.filter (·.value == .sovnegSoNegVNeg)).length = 1 := by native_decide
theorem count_snegoV_10 :
    (allData.filter (·.value == .snegoV_10)).length = 1 := by native_decide
theorem count_sovButSNegVNegOSoVNeg :
    (allData.filter (·.value == .sovButSNegVNegOSoVNeg)).length = 1 := by native_decide
theorem count_soNegVSovneg :
    (allData.filter (·.value == .soNegVSovneg)).length = 1 := by native_decide
theorem count_sovnegSovnegSovneg :
    (allData.filter (·.value == .sovnegSovnegSovneg)).length = 3 := by native_decide
theorem count_soVSoV :
    (allData.filter (·.value == .soVSoV)).length = 1 := by native_decide
theorem count_sovVNeg :
    (allData.filter (·.value == .sovVNeg)).length = 2 := by native_decide
theorem count_sovV :
    (allData.filter (·.value == .sovV)).length = 1 := by native_decide
theorem count_sovSvoNegV :
    (allData.filter (·.value == .sovSvoNegV)).length = 1 := by native_decide
theorem count_svOvV :
    (allData.filter (·.value == .svOvV)).length = 1 := by native_decide
theorem count_svOvVNeg :
    (allData.filter (·.value == .svOvVNeg)).length = 1 := by native_decide
theorem count_svOvNegV :
    (allData.filter (·.value == .svOvNegV)).length = 1 := by native_decide
theorem count_svOvVNeg_21 :
    (allData.filter (·.value == .svOvVNeg_21)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144O
