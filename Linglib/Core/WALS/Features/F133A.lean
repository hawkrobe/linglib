import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 133A: Number of Basic Colour Categories
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 133A`.

Chapter 133, 119 languages.
-/

namespace Core.WALS.F133A

/-- WALS 133A values. -/
inductive NumberOfBasicColourCategories where
  | v34  -- 3-4 (20 languages)
  | v4555  -- 4.5-5.5 (26 languages)
  | v665  -- 6-6.5 (34 languages)
  | v775  -- 7-7.5 (14 languages)
  | v885  -- 8-8.5 (6 languages)
  | v910  -- 9-10 (8 languages)
  | v11  -- 11 (11 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 133A dataset (119 languages). -/
def allData : List (Datapoint NumberOfBasicColourCategories) :=
  [ { walsCode := "abd", language := "Abidji", iso := "abi", value := .v4555 }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .v4555 }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .v665 }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .v775 }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .v665 }
  , { walsCode := "ape", language := "Ampeeli", iso := "apz", value := .v4555 }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .v885 }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .v775 }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .v4555 }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .v4555 }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .v11 }
  , { walsCode := "bhn", language := "Bahinemo", iso := "bjh", value := .v665 }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .v4555 }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .v4555 }
  , { walsCode := "bhi", language := "Bhili", iso := "bhb", value := .v775 }
  , { walsCode := "bgl", language := "Buglere", iso := "sab", value := .v665 }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .v34 }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .v11 }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .v34 }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .v910 }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .v4555 }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .v665 }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .v4555 }
  , { walsCode := "cvc", language := "Chavacano", iso := "cbk", value := .v910 }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .v665 }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .v775 }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .v910 }
  , { walsCode := "cum", language := "Chumburung", iso := "ncu", value := .v775 }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .v34 }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .v665 }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .v4555 }
  , { walsCode := "cul", language := "Culina", iso := "cul", value := .v34 }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .v34 }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .v775 }
  , { walsCode := "dym", language := "Dyimini", iso := "dyi", value := .v665 }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .v34 }
  , { walsCode := "eng", language := "English", iso := "eng", value := .v11 }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .v775 }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .v4555 }
  , { walsCode := "fre", language := "French", iso := "fra", value := .v11 }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .v910 }
  , { walsCode := "ger", language := "German", iso := "deu", value := .v11 }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .v665 }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .v665 }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .v665 }
  , { walsCode := "gun", language := "Gunu", iso := "yas", value := .v34 }
  , { walsCode := "hlb", language := "Halbi", iso := "hlb", value := .v4555 }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .v665 }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .v910 }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .v4555 }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .v4555 }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .v4555 }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .v11 }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .v665 }
  , { walsCode := "kak", language := "Kamano-Kafe", iso := "kbq", value := .v665 }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .v4555 }
  , { walsCode := "kmt", language := "Kemtuik", iso := "kmt", value := .v4555 }
  , { walsCode := "kkz", language := "Kokni", iso := "kex", value := .v775 }
  , { walsCode := "kkb", language := "Konkomba", iso := "xon", value := .v34 }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .v11 }
  , { walsCode := "knq", language := "Kriol (Ngukurr)", iso := "rop", value := .v11 }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .v34 }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .v775 }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .v34 }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .v34 }
  , { walsCode := "mmp", language := "Mampruli", iso := "maw", value := .v665 }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .v885 }
  , { walsCode := "mav", language := "Maring", iso := "mbw", value := .v4555 }
  , { walsCode := "mwa", language := "Martu Wangka", iso := "mpj", value := .v4555 }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .v34 }
  , { walsCode := "mwc", language := "Mawchi", iso := "mke", value := .v775 }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .v910 }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .v910 }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .v665 }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .v665 }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .v885 }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .v775 }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .v665 }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .v34 }
  , { walsCode := "mdu", language := "Mündü", iso := "muh", value := .v34 }
  , { walsCode := "naf", language := "Nafaanra", iso := "nfr", value := .v34 }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .v885 }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .v665 }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .v775 }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .v885 }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .v665 }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .v665 }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .v4555 }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .v34 }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .v11 }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .v910 }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .v665 }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .v665 }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .v4555 }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .v775 }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .v11 }
  , { walsCode := "sur", language := "Sursurunga", iso := "sgz", value := .v665 }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .v665 }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .v665 }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .v4555 }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .v665 }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .v665 }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .v775 }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .v665 }
  , { walsCode := "tif", language := "Tifal", iso := "tif", value := .v34 }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .v885 }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .v4555 }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .v4555 }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .v4555 }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .v34 }
  , { walsCode := "vas", language := "Vasavi", iso := "vas", value := .v665 }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .v34 }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .v665 }
  , { walsCode := "wob", language := "Wobe", iso := "wob", value := .v34 }
  , { walsCode := "ykn", language := "Yakan", iso := "yka", value := .v11 }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .v4555 }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .v665 }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .v665 }
  , { walsCode := "zte", language := "Zapotec (Texmelucan)", iso := "zpz", value := .v665 }
  ]

-- Count verification
theorem total_count : allData.length = 119 := by native_decide

theorem count_v34 :
    (allData.filter (·.value == .v34)).length = 20 := by native_decide
theorem count_v4555 :
    (allData.filter (·.value == .v4555)).length = 26 := by native_decide
theorem count_v665 :
    (allData.filter (·.value == .v665)).length = 34 := by native_decide
theorem count_v775 :
    (allData.filter (·.value == .v775)).length = 14 := by native_decide
theorem count_v885 :
    (allData.filter (·.value == .v885)).length = 6 := by native_decide
theorem count_v910 :
    (allData.filter (·.value == .v910)).length = 8 := by native_decide
theorem count_v11 :
    (allData.filter (·.value == .v11)).length = 11 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F133A
