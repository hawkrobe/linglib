import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 130B: Cultural Categories of Languages with Identity of 'Finger' and 'Hand'
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 130B`.

Chapter 130, 72 languages.
-/

namespace Core.WALS.F130B

/-- WALS 130B values. -/
inductive CulturalCategoriesOfLanguagesWithIdentityOfFingerAndHand where
  | hunterGatherers  -- Hunter-gatherers (46 languages)
  | farmerForagers  -- Farmer-foragers (18 languages)
  | fullFledgedFarmers  -- Full-fledged farmers (8 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 130B dataset (72 languages). -/
def allData : List (Datapoint CulturalCategoriesOfLanguagesWithIdentityOfFingerAndHand) :=
  [ { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .hunterGatherers }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .farmerForagers }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .farmerForagers }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .hunterGatherers }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .hunterGatherers }
  , { walsCode := "ati", language := "Atikamekw", iso := "atj", value := .hunterGatherers }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .hunterGatherers }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .hunterGatherers }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .hunterGatherers }
  , { walsCode := "beo", language := "Beothuk", iso := "bue", value := .hunterGatherers }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .hunterGatherers }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .hunterGatherers }
  , { walsCode := "crj", language := "Carijona", iso := "cbd", value := .farmerForagers }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .farmerForagers }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .farmerForagers }
  , { walsCode := "cmc", language := "Comecrudo", iso := "xcm", value := .hunterGatherers }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .hunterGatherers }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .hunterGatherers }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .hunterGatherers }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .farmerForagers }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .fullFledgedFarmers }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .hunterGatherers }
  , { walsCode := "inu", language := "Iñupiaq", iso := "esi", value := .hunterGatherers }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .farmerForagers }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .hunterGatherers }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .farmerForagers }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .hunterGatherers }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .hunterGatherers }
  , { walsCode := "kaq", language := "Kaurna", iso := "zku", value := .hunterGatherers }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .fullFledgedFarmers }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .hunterGatherers }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .hunterGatherers }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .hunterGatherers }
  , { walsCode := "mwp", language := "Miwok (Plains)", iso := "pmw", value := .hunterGatherers }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .farmerForagers }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .farmerForagers }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .hunterGatherers }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .farmerForagers }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .fullFledgedFarmers }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .hunterGatherers }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .hunterGatherers }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .hunterGatherers }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .hunterGatherers }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .fullFledgedFarmers }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .hunterGatherers }
  , { walsCode := "ojm", language := "Ojibwe (Minnesota)", iso := "ciw", value := .hunterGatherers }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .farmerForagers }
  , { walsCode := "onn", language := "Onondaga", iso := "ono", value := .farmerForagers }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .hunterGatherers }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .fullFledgedFarmers }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .hunterGatherers }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .hunterGatherers }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .hunterGatherers }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .farmerForagers }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .hunterGatherers }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .hunterGatherers }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .fullFledgedFarmers }
  , { walsCode := "tsm", language := "Tasmanian", iso := "", value := .hunterGatherers }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .hunterGatherers }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .fullFledgedFarmers }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .farmerForagers }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .farmerForagers }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .hunterGatherers }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .hunterGatherers }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .farmerForagers }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .hunterGatherers }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .hunterGatherers }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .fullFledgedFarmers }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .hunterGatherers }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .hunterGatherers }
  , { walsCode := "ykp", language := "Yukpa", iso := "yup", value := .farmerForagers }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .hunterGatherers }
  ]

-- Count verification
theorem total_count : allData.length = 72 := by native_decide

theorem count_hunterGatherers :
    (allData.filter (·.value == .hunterGatherers)).length = 46 := by native_decide
theorem count_farmerForagers :
    (allData.filter (·.value == .farmerForagers)).length = 18 := by native_decide
theorem count_fullFledgedFarmers :
    (allData.filter (·.value == .fullFledgedFarmers)).length = 8 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F130B
