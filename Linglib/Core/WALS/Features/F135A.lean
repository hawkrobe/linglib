import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 135A: Red and Yellow
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 135A`.

Chapter 135, 120 languages.
-/

namespace Core.WALS.F135A

/-- WALS 135A values. -/
inductive RedAndYellow where
  | redVsYellow  -- Red vs. yellow (98 languages)
  | redYellow  -- Red/yellow (15 languages)
  | yellowGreenBlueVsRed  -- Yellow/green/blue vs. red (3 languages)
  | yellowGreenVsRed  -- Yellow/green vs. red (1 languages)
  | none  -- None (3 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 135A dataset (120 languages). -/
def allData : List (Datapoint RedAndYellow) :=
  [ { walsCode := "abd", language := "Abidji", iso := "abi", value := .redYellow }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .redVsYellow }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .redVsYellow }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .redVsYellow }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .redVsYellow }
  , { walsCode := "ape", language := "Ampeeli", iso := "apz", value := .redVsYellow }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .redVsYellow }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .redVsYellow }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .redVsYellow }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .redVsYellow }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .redVsYellow }
  , { walsCode := "bhn", language := "Bahinemo", iso := "bjh", value := .redVsYellow }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .redVsYellow }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .redVsYellow }
  , { walsCode := "bhi", language := "Bhili", iso := "bhb", value := .redVsYellow }
  , { walsCode := "bgl", language := "Buglere", iso := "sab", value := .redVsYellow }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .redYellow }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .redVsYellow }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .redVsYellow }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .redYellow }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .redVsYellow }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .redVsYellow }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .redVsYellow }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .redVsYellow }
  , { walsCode := "cvc", language := "Chavacano", iso := "cbk", value := .redVsYellow }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .redVsYellow }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .redVsYellow }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .redVsYellow }
  , { walsCode := "cum", language := "Chumburung", iso := "ncu", value := .redVsYellow }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .redYellow }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .redVsYellow }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .yellowGreenVsRed }
  , { walsCode := "cul", language := "Culina", iso := "cul", value := .yellowGreenBlueVsRed }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .redYellow }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .redVsYellow }
  , { walsCode := "dym", language := "Dyimini", iso := "dyi", value := .redVsYellow }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .redYellow }
  , { walsCode := "eng", language := "English", iso := "eng", value := .redVsYellow }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .redVsYellow }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .redVsYellow }
  , { walsCode := "fre", language := "French", iso := "fra", value := .redVsYellow }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .redVsYellow }
  , { walsCode := "ger", language := "German", iso := "deu", value := .redVsYellow }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .redVsYellow }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .redVsYellow }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .redVsYellow }
  , { walsCode := "gun", language := "Gunu", iso := "yas", value := .redYellow }
  , { walsCode := "hlb", language := "Halbi", iso := "hlb", value := .redVsYellow }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .redVsYellow }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .redVsYellow }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .redVsYellow }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .redVsYellow }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .redVsYellow }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .redVsYellow }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .redVsYellow }
  , { walsCode := "kak", language := "Kamano-Kafe", iso := "kbq", value := .redVsYellow }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .yellowGreenBlueVsRed }
  , { walsCode := "kmt", language := "Kemtuik", iso := "kmt", value := .redVsYellow }
  , { walsCode := "kkz", language := "Kokni", iso := "kex", value := .redVsYellow }
  , { walsCode := "kkb", language := "Konkomba", iso := "xon", value := .redYellow }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .redVsYellow }
  , { walsCode := "knq", language := "Kriol (Ngukurr)", iso := "rop", value := .redVsYellow }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .none }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .redVsYellow }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .redVsYellow }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .yellowGreenBlueVsRed }
  , { walsCode := "mmp", language := "Mampruli", iso := "maw", value := .redVsYellow }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .redVsYellow }
  , { walsCode := "mav", language := "Maring", iso := "mbw", value := .redVsYellow }
  , { walsCode := "mwa", language := "Martu Wangka", iso := "mpj", value := .redVsYellow }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .redVsYellow }
  , { walsCode := "mwc", language := "Mawchi", iso := "mke", value := .redVsYellow }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .redVsYellow }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .redVsYellow }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .redVsYellow }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .redVsYellow }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .redVsYellow }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .redVsYellow }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .redVsYellow }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .none }
  , { walsCode := "mdu", language := "Mündü", iso := "muh", value := .redYellow }
  , { walsCode := "naf", language := "Nafaanra", iso := "nfr", value := .redYellow }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .redVsYellow }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .redVsYellow }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .redVsYellow }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .redVsYellow }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .redVsYellow }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .redVsYellow }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .redVsYellow }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .redYellow }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .redVsYellow }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .redVsYellow }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .redVsYellow }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .redVsYellow }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .redVsYellow }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .redVsYellow }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .redVsYellow }
  , { walsCode := "sur", language := "Sursurunga", iso := "sgz", value := .redVsYellow }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .redVsYellow }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .redYellow }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .redYellow }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .redVsYellow }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .redVsYellow }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .redVsYellow }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .redVsYellow }
  , { walsCode := "tif", language := "Tifal", iso := "tif", value := .redVsYellow }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .redVsYellow }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .redVsYellow }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .redVsYellow }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .redYellow }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .redVsYellow }
  , { walsCode := "vas", language := "Vasavi", iso := "vas", value := .redVsYellow }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .none }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .redVsYellow }
  , { walsCode := "wob", language := "Wobe", iso := "wob", value := .redYellow }
  , { walsCode := "ykn", language := "Yakan", iso := "yka", value := .redVsYellow }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .redVsYellow }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .redVsYellow }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .redVsYellow }
  , { walsCode := "zte", language := "Zapotec (Texmelucan)", iso := "zpz", value := .redVsYellow }
  ]

-- Count verification
theorem total_count : allData.length = 120 := by native_decide

theorem count_redVsYellow :
    (allData.filter (·.value == .redVsYellow)).length = 98 := by native_decide
theorem count_redYellow :
    (allData.filter (·.value == .redYellow)).length = 15 := by native_decide
theorem count_yellowGreenBlueVsRed :
    (allData.filter (·.value == .yellowGreenBlueVsRed)).length = 3 := by native_decide
theorem count_yellowGreenVsRed :
    (allData.filter (·.value == .yellowGreenVsRed)).length = 1 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 3 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F135A
