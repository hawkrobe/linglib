/-!
# WALS Feature 143C: Optional Double Negation
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143C`.

Chapter 143, 81 languages.
-/

namespace Core.WALS.F143C

/-- WALS 143C values. -/
inductive OptionalDoubleNegation where
  | negv  -- NegV(Neg) (11 languages)
  | vneg  -- (Neg)VNeg (20 languages)
  | negV  -- Neg[V(-Neg)] (5 languages)
  | vNeg  -- (Neg)[V-Neg] (5 languages)
  | negV_5  -- [Neg-V](Neg) (3 languages)
  | vNeg_6  -- [(Neg-)V]Neg (2 languages)
  | negV_7  -- [Neg-V(-Neg)] (5 languages)
  | vNeg_8  -- [(Neg-)V-Neg] (6 languages)
  | vneg_9  -- V(Neg)Neg (2 languages)
  | vNeg_10  -- [V-Neg](Neg) (2 languages)
  | negv_11  -- Neg(Neg)V (1 languages)
  | negV_12  -- Neg[(Neg-)]V (3 languages)
  | negvOptchangeverbstem  -- NegV&OptChangeVerbStem (1 languages)
  | negvNegVNeg  -- NegV/[Neg-V-Neg] (2 languages)
  | vnegNegVNeg  -- VNeg/[Neg-V-Neg] (1 languages)
  | negVNegvneg  -- [Neg-V]/NegVNeg (1 languages)
  | negvOrNegativetoneVneg  -- NegV or NegativeTone&VNeg (1 languages)
  | negvVNegNegVNeg  -- NegV/[V-Neg]/Neg[V-Neg] (4 languages)
  | negvVnegNegvneg  -- NegV/VNeg/NegVNeg (2 languages)
  | negvVNegNegVNeg_20  -- NegV/[V-Neg]/[Neg-V-Neg] (1 languages)
  | negVVnegNegVNeg  -- [Neg-V]/VNeg/[Neg-V-Neg] (1 languages)
  | negvNegVNegNegV  -- NegV/[Neg-V]/Neg[Neg-V] (1 languages)
  | optdoublenegOpttripleneg  -- OptDoubleNeg&OptTripleNeg (1 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 143C datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : OptionalDoubleNegation
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 143C dataset (81 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "adg", language := "Adang", iso := "adn", value := .vneg }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .negV_5 }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .negvVNegNegVNeg }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .negV_12 }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .negV_7 }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .negvNegVNeg }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .negv }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .negV_5 }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .vNeg_8 }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .vNeg_6 }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .negv }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .vneg }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .negV_5 }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .vneg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .negv }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .vNeg }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .vNeg_8 }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .negv }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .negv }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .negVNegvneg }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .negvVNegNegVNeg_20 }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .vneg }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .vnegNegVNeg }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .negvOrNegativetoneVneg }
  , { walsCode := "fre", language := "French", iso := "fra", value := .vneg }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .vneg }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .vneg }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .negvVNegNegVNeg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .negv }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .vneg }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .vNeg_6 }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .vNeg }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .vNeg_8 }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .vNeg_8 }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .negV_7 }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .vneg }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .vNeg_8 }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .vneg }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .vNeg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .optdoublenegOpttripleneg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vneg_9 }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .vneg_9 }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .vNeg_10 }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .negv }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .negv }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .vneg }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .negv }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .negvNegVNegNegV }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .negV_12 }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .vneg }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .vneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .vneg }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .negV_7 }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .vNeg_10 }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .negvVNegNegVNeg }
  , { walsCode := "one", language := "One", iso := "aun", value := .vneg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .negV_12 }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .vneg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .negv }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .negvNegVNeg }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .negv_11 }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .negvVnegNegvneg }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .vNeg }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .negV }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .vneg }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .negvVnegNegvneg }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .negvOptchangeverbstem }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .vNeg_8 }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .negV }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .vneg }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .vneg }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .vneg }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .negvVNegNegVNeg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .negVVnegNegVNeg }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .negV }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .negv }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .negV_7 }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .negV }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .vNeg }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .negV }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .negV_7 }
  ]

-- Count verification
theorem total_count : allData.length = 81 := by native_decide

theorem count_negv :
    (allData.filter (·.value == .negv)).length = 11 := by native_decide
theorem count_vneg :
    (allData.filter (·.value == .vneg)).length = 20 := by native_decide
theorem count_negV :
    (allData.filter (·.value == .negV)).length = 5 := by native_decide
theorem count_vNeg :
    (allData.filter (·.value == .vNeg)).length = 5 := by native_decide
theorem count_negV_5 :
    (allData.filter (·.value == .negV_5)).length = 3 := by native_decide
theorem count_vNeg_6 :
    (allData.filter (·.value == .vNeg_6)).length = 2 := by native_decide
theorem count_negV_7 :
    (allData.filter (·.value == .negV_7)).length = 5 := by native_decide
theorem count_vNeg_8 :
    (allData.filter (·.value == .vNeg_8)).length = 6 := by native_decide
theorem count_vneg_9 :
    (allData.filter (·.value == .vneg_9)).length = 2 := by native_decide
theorem count_vNeg_10 :
    (allData.filter (·.value == .vNeg_10)).length = 2 := by native_decide
theorem count_negv_11 :
    (allData.filter (·.value == .negv_11)).length = 1 := by native_decide
theorem count_negV_12 :
    (allData.filter (·.value == .negV_12)).length = 3 := by native_decide
theorem count_negvOptchangeverbstem :
    (allData.filter (·.value == .negvOptchangeverbstem)).length = 1 := by native_decide
theorem count_negvNegVNeg :
    (allData.filter (·.value == .negvNegVNeg)).length = 2 := by native_decide
theorem count_vnegNegVNeg :
    (allData.filter (·.value == .vnegNegVNeg)).length = 1 := by native_decide
theorem count_negVNegvneg :
    (allData.filter (·.value == .negVNegvneg)).length = 1 := by native_decide
theorem count_negvOrNegativetoneVneg :
    (allData.filter (·.value == .negvOrNegativetoneVneg)).length = 1 := by native_decide
theorem count_negvVNegNegVNeg :
    (allData.filter (·.value == .negvVNegNegVNeg)).length = 4 := by native_decide
theorem count_negvVnegNegvneg :
    (allData.filter (·.value == .negvVnegNegvneg)).length = 2 := by native_decide
theorem count_negvVNegNegVNeg_20 :
    (allData.filter (·.value == .negvVNegNegVNeg_20)).length = 1 := by native_decide
theorem count_negVVnegNegVNeg :
    (allData.filter (·.value == .negVVnegNegVNeg)).length = 1 := by native_decide
theorem count_negvNegVNegNegV :
    (allData.filter (·.value == .negvNegVNegNegV)).length = 1 := by native_decide
theorem count_optdoublenegOpttripleneg :
    (allData.filter (·.value == .optdoublenegOpttripleneg)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F143C
