import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 134A: Green and Blue
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 134A`.

Chapter 134, 120 languages.
-/

namespace Core.WALS.F134A

/-- WALS 134A values. -/
inductive GreenAndBlue where
  | greenVsBlue  -- Green vs. blue (30 languages)
  | greenBlue  -- Green/blue (68 languages)
  | blackGreenBlue  -- Black/green/blue (15 languages)
  | blackBlueVsGreen  -- Black/blue vs. green (2 languages)
  | yellowGreenBlue  -- Yellow/green/blue (2 languages)
  | yellowGreenVsBlue  -- Yellow/green vs. blue (1 languages)
  | none  -- None (2 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 134A dataset (120 languages). -/
def allData : List (Datapoint GreenAndBlue) :=
  [ { walsCode := "abd", language := "Abidji", iso := "abi", value := .greenBlue }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .greenBlue }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .greenBlue }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .greenBlue }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .greenBlue }
  , { walsCode := "ape", language := "Ampeeli", iso := "apz", value := .greenBlue }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .greenVsBlue }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .greenVsBlue }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .greenBlue }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .greenBlue }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .greenVsBlue }
  , { walsCode := "bhn", language := "Bahinemo", iso := "bjh", value := .greenBlue }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .greenBlue }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .greenBlue }
  , { walsCode := "bhi", language := "Bhili", iso := "bhb", value := .greenBlue }
  , { walsCode := "bgl", language := "Buglere", iso := "sab", value := .greenVsBlue }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .blackGreenBlue }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .greenBlue }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .greenVsBlue }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .blackGreenBlue }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .greenVsBlue }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .greenVsBlue }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .greenBlue }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .greenBlue }
  , { walsCode := "cvc", language := "Chavacano", iso := "cbk", value := .greenVsBlue }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .greenBlue }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .greenBlue }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .greenVsBlue }
  , { walsCode := "cum", language := "Chumburung", iso := "ncu", value := .greenVsBlue }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .greenBlue }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .greenBlue }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .yellowGreenVsBlue }
  , { walsCode := "cul", language := "Culina", iso := "cul", value := .blackGreenBlue }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .blackGreenBlue }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .greenBlue }
  , { walsCode := "dym", language := "Dyimini", iso := "dyi", value := .greenVsBlue }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .blackGreenBlue }
  , { walsCode := "eng", language := "English", iso := "eng", value := .greenVsBlue }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .greenBlue }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .blackGreenBlue }
  , { walsCode := "fre", language := "French", iso := "fra", value := .greenVsBlue }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .greenVsBlue }
  , { walsCode := "ger", language := "German", iso := "deu", value := .greenVsBlue }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .greenBlue }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .greenBlue }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .greenBlue }
  , { walsCode := "gun", language := "Gunu", iso := "yas", value := .blackGreenBlue }
  , { walsCode := "hlb", language := "Halbi", iso := "hlb", value := .greenBlue }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .greenBlue }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .greenVsBlue }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .greenBlue }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .blackBlueVsGreen }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .greenBlue }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .greenVsBlue }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .greenBlue }
  , { walsCode := "kak", language := "Kamano-Kafe", iso := "kbq", value := .greenBlue }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .yellowGreenBlue }
  , { walsCode := "kmt", language := "Kemtuik", iso := "kmt", value := .greenBlue }
  , { walsCode := "kkz", language := "Kokni", iso := "kex", value := .greenVsBlue }
  , { walsCode := "kkb", language := "Konkomba", iso := "xon", value := .blackGreenBlue }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .greenVsBlue }
  , { walsCode := "knq", language := "Kriol (Ngukurr)", iso := "rop", value := .greenVsBlue }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .none }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .greenBlue }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .blackGreenBlue }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .yellowGreenBlue }
  , { walsCode := "mmp", language := "Mampruli", iso := "maw", value := .blackGreenBlue }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .greenVsBlue }
  , { walsCode := "mav", language := "Maring", iso := "mbw", value := .greenBlue }
  , { walsCode := "mwa", language := "Martu Wangka", iso := "mpj", value := .blackBlueVsGreen }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .greenBlue }
  , { walsCode := "mwc", language := "Mawchi", iso := "mke", value := .greenBlue }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .greenVsBlue }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .greenBlue }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .greenBlue }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .greenVsBlue }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .greenBlue }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .greenBlue }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .greenBlue }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .none }
  , { walsCode := "mdu", language := "Mündü", iso := "muh", value := .blackGreenBlue }
  , { walsCode := "naf", language := "Nafaanra", iso := "nfr", value := .blackGreenBlue }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .greenVsBlue }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .greenVsBlue }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .greenVsBlue }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .greenBlue }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .greenBlue }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .greenBlue }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .greenBlue }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .greenBlue }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .greenVsBlue }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .greenBlue }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .greenBlue }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .greenBlue }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .greenBlue }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .greenVsBlue }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .greenVsBlue }
  , { walsCode := "sur", language := "Sursurunga", iso := "sgz", value := .greenBlue }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .greenBlue }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .greenBlue }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .greenBlue }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .greenBlue }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .greenBlue }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .greenBlue }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .greenBlue }
  , { walsCode := "tif", language := "Tifal", iso := "tif", value := .blackGreenBlue }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .greenBlue }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .greenBlue }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .greenBlue }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .greenBlue }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .blackGreenBlue }
  , { walsCode := "vas", language := "Vasavi", iso := "vas", value := .greenBlue }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .greenBlue }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .greenBlue }
  , { walsCode := "wob", language := "Wobe", iso := "wob", value := .blackGreenBlue }
  , { walsCode := "ykn", language := "Yakan", iso := "yka", value := .greenVsBlue }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .greenBlue }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .greenBlue }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .greenBlue }
  , { walsCode := "zte", language := "Zapotec (Texmelucan)", iso := "zpz", value := .greenBlue }
  ]

-- Count verification
theorem total_count : allData.length = 120 := by native_decide

theorem count_greenVsBlue :
    (allData.filter (·.value == .greenVsBlue)).length = 30 := by native_decide
theorem count_greenBlue :
    (allData.filter (·.value == .greenBlue)).length = 68 := by native_decide
theorem count_blackGreenBlue :
    (allData.filter (·.value == .blackGreenBlue)).length = 15 := by native_decide
theorem count_blackBlueVsGreen :
    (allData.filter (·.value == .blackBlueVsGreen)).length = 2 := by native_decide
theorem count_yellowGreenBlue :
    (allData.filter (·.value == .yellowGreenBlue)).length = 2 := by native_decide
theorem count_yellowGreenVsBlue :
    (allData.filter (·.value == .yellowGreenVsBlue)).length = 1 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F134A
