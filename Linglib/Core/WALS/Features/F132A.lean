/-!
# WALS Feature 132A: Number of Non-Derived Basic Colour Categories
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 132A`.

Chapter 132, 119 languages.
-/

namespace Core.WALS.F132A

/-- WALS 132A values. -/
inductive NumberOfNonDerivedBasicColourCategories where
  | v3  -- 3 (10 languages)
  | v35  -- 3.5 (3 languages)
  | v4  -- 4 (9 languages)
  | v45  -- 4.5 (1 languages)
  | v5  -- 5 (56 languages)
  | v55  -- 5.5 (11 languages)
  | v6  -- 6 (29 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 132A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NumberOfNonDerivedBasicColourCategories
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 132A dataset (119 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abd", language := "Abidji", iso := "abi", value := .v35 }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .v5 }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .v5 }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .v5 }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .v55 }
  , { walsCode := "ape", language := "Ampeeli", iso := "apz", value := .v5 }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .v6 }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .v5 }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .v5 }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .v5 }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .v6 }
  , { walsCode := "bhn", language := "Bahinemo", iso := "bjh", value := .v5 }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .v5 }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .v5 }
  , { walsCode := "bhi", language := "Bhili", iso := "bhb", value := .v5 }
  , { walsCode := "bgl", language := "Buglere", iso := "sab", value := .v6 }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .v3 }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .v6 }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .v3 }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .v6 }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .v55 }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .v5 }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .v5 }
  , { walsCode := "cvc", language := "Chavacano", iso := "cbk", value := .v6 }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .v5 }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .v5 }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .v6 }
  , { walsCode := "cum", language := "Chumburung", iso := "ncu", value := .v55 }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .v4 }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .v5 }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .v5 }
  , { walsCode := "cul", language := "Culina", iso := "cul", value := .v4 }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .v3 }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .v5 }
  , { walsCode := "dym", language := "Dyimini", iso := "dyi", value := .v6 }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .v3 }
  , { walsCode := "eng", language := "English", iso := "eng", value := .v6 }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .v5 }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .v45 }
  , { walsCode := "fre", language := "French", iso := "fra", value := .v6 }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .v6 }
  , { walsCode := "ger", language := "German", iso := "deu", value := .v6 }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .v5 }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .v55 }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .v5 }
  , { walsCode := "gun", language := "Gunu", iso := "yas", value := .v35 }
  , { walsCode := "hlb", language := "Halbi", iso := "hlb", value := .v5 }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .v5 }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .v6 }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .v5 }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .v5 }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .v5 }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .v6 }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .v6 }
  , { walsCode := "kak", language := "Kamano-Kafe", iso := "kbq", value := .v6 }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .v4 }
  , { walsCode := "kmt", language := "Kemtuik", iso := "kmt", value := .v5 }
  , { walsCode := "kkz", language := "Kokni", iso := "kex", value := .v6 }
  , { walsCode := "kkb", language := "Konkomba", iso := "xon", value := .v35 }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .v6 }
  , { walsCode := "knq", language := "Kriol (Ngukurr)", iso := "rop", value := .v6 }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .v3 }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .v5 }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .v3 }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .v4 }
  , { walsCode := "mmp", language := "Mampruli", iso := "maw", value := .v55 }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .v6 }
  , { walsCode := "mav", language := "Maring", iso := "mbw", value := .v55 }
  , { walsCode := "mwa", language := "Martu Wangka", iso := "mpj", value := .v5 }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .v4 }
  , { walsCode := "mwc", language := "Mawchi", iso := "mke", value := .v5 }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .v6 }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .v55 }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .v5 }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .v6 }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .v5 }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .v5 }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .v5 }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .v3 }
  , { walsCode := "mdu", language := "Mündü", iso := "muh", value := .v3 }
  , { walsCode := "naf", language := "Nafaanra", iso := "nfr", value := .v3 }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .v6 }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .v6 }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .v6 }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .v5 }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .v5 }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .v55 }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .v5 }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .v4 }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .v6 }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .v55 }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .v5 }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .v5 }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .v5 }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .v6 }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .v6 }
  , { walsCode := "sur", language := "Sursurunga", iso := "sgz", value := .v5 }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .v5 }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .v55 }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .v5 }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .v5 }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .v5 }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .v55 }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .v5 }
  , { walsCode := "tif", language := "Tifal", iso := "tif", value := .v4 }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .v5 }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .v5 }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .v5 }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .v5 }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .v4 }
  , { walsCode := "vas", language := "Vasavi", iso := "vas", value := .v5 }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .v4 }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .v5 }
  , { walsCode := "wob", language := "Wobe", iso := "wob", value := .v3 }
  , { walsCode := "ykn", language := "Yakan", iso := "yka", value := .v6 }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .v5 }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .v5 }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .v5 }
  , { walsCode := "zte", language := "Zapotec (Texmelucan)", iso := "zpz", value := .v5 }
  ]

-- Count verification
theorem total_count : allData.length = 119 := by native_decide

theorem count_v3 :
    (allData.filter (·.value == .v3)).length = 10 := by native_decide
theorem count_v35 :
    (allData.filter (·.value == .v35)).length = 3 := by native_decide
theorem count_v4 :
    (allData.filter (·.value == .v4)).length = 9 := by native_decide
theorem count_v45 :
    (allData.filter (·.value == .v45)).length = 1 := by native_decide
theorem count_v5 :
    (allData.filter (·.value == .v5)).length = 56 := by native_decide
theorem count_v55 :
    (allData.filter (·.value == .v55)).length = 11 := by native_decide
theorem count_v6 :
    (allData.filter (·.value == .v6)).length = 29 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F132A
