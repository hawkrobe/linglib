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
  /-- Hunter-gatherers (46 languages). -/
  | hunterGatherers
  /-- Farmer-foragers (18 languages). -/
  | farmerForagers
  /-- Full-fledged farmers (8 languages). -/
  | fullFledgedFarmers
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 130B dataset (72 languages). -/
def allData : List (Datapoint CulturalCategoriesOfLanguagesWithIdentityOfFingerAndHand) :=
  [ { walsCode := "aly", iso := "aly", value := .hunterGatherers }
  , { walsCode := "amc", iso := "amc", value := .farmerForagers }
  , { walsCode := "apw", iso := "apw", value := .farmerForagers }
  , { walsCode := "amp", iso := "aer", value := .hunterGatherers }
  , { walsCode := "atk", iso := "aqp", value := .hunterGatherers }
  , { walsCode := "ati", iso := "atj", value := .hunterGatherers }
  , { walsCode := "bnj", iso := "bdy", value := .hunterGatherers }
  , { walsCode := "bwa", iso := "bdy", value := .hunterGatherers }
  , { walsCode := "byu", iso := "bdy", value := .hunterGatherers }
  , { walsCode := "beo", iso := "bue", value := .hunterGatherers }
  , { walsCode := "bnb", iso := "bck", value := .hunterGatherers }
  , { walsCode := "cah", iso := "chl", value := .hunterGatherers }
  , { walsCode := "crj", iso := "cbd", value := .farmerForagers }
  , { walsCode := "chy", iso := "cbt", value := .farmerForagers }
  , { walsCode := "ccp", iso := "coc", value := .farmerForagers }
  , { walsCode := "cmc", iso := "xcm", value := .hunterGatherers }
  , { walsCode := "die", iso := "dih", value := .hunterGatherers }
  , { walsCode := "dja", iso := "dyy", value := .hunterGatherers }
  , { walsCode := "dji", iso := "jig", value := .hunterGatherers }
  , { walsCode := "eud", iso := "", value := .farmerForagers }
  , { walsCode := "haw", iso := "haw", value := .fullFledgedFarmers }
  , { walsCode := "hup", iso := "hup", value := .hunterGatherers }
  , { walsCode := "inu", iso := "esi", value := .hunterGatherers }
  , { walsCode := "jiv", iso := "jiv", value := .farmerForagers }
  , { walsCode := "kls", iso := "fla", value := .hunterGatherers }
  , { walsCode := "jva", iso := "kpj", value := .farmerForagers }
  , { walsCode := "kkw", iso := "zkk", value := .hunterGatherers }
  , { walsCode := "krk", iso := "kyh", value := .hunterGatherers }
  , { walsCode := "kaq", iso := "zku", value := .hunterGatherers }
  , { walsCode := "ksa", iso := "kee", value := .fullFledgedFarmers }
  , { walsCode := "kxo", iso := "xuu", value := .hunterGatherers }
  , { walsCode := "mku", iso := "zmr", value := .hunterGatherers }
  , { walsCode := "mwn", iso := "nsq", value := .hunterGatherers }
  , { walsCode := "mwp", iso := "pmw", value := .hunterGatherers }
  , { walsCode := "moh", iso := "moh", value := .farmerForagers }
  , { walsCode := "muu", iso := "myu", value := .farmerForagers }
  , { walsCode := "mpa", iso := "mwf", value := .hunterGatherers }
  , { walsCode := "nat", iso := "ncz", value := .farmerForagers }
  , { walsCode := "nav", iso := "nav", value := .fullFledgedFarmers }
  , { walsCode := "ndj", iso := "djj", value := .hunterGatherers }
  , { walsCode := "nez", iso := "nez", value := .hunterGatherers }
  , { walsCode := "ngj", iso := "nju", value := .hunterGatherers }
  , { walsCode := "ngi", iso := "wyb", value := .hunterGatherers }
  , { walsCode := "ngz", iso := "ngi", value := .fullFledgedFarmers }
  , { walsCode := "nug", iso := "nuy", value := .hunterGatherers }
  , { walsCode := "ojm", iso := "ciw", value := .hunterGatherers }
  , { walsCode := "ond", iso := "one", value := .farmerForagers }
  , { walsCode := "onn", iso := "ono", value := .farmerForagers }
  , { walsCode := "pkn", iso := "drl", value := .hunterGatherers }
  , { walsCode := "pac", iso := "pac", value := .fullFledgedFarmers }
  , { walsCode := "pin", iso := "piu", value := .hunterGatherers }
  , { walsCode := "pit", iso := "pjt", value := .hunterGatherers }
  , { walsCode := "qui", iso := "qui", value := .hunterGatherers }
  , { walsCode := "snc", iso := "see", value := .farmerForagers }
  , { walsCode := "ser", iso := "sei", value := .hunterGatherers }
  , { walsCode := "shs", iso := "sht", value := .hunterGatherers }
  , { walsCode := "tah", iso := "tah", value := .fullFledgedFarmers }
  , { walsCode := "tsm", iso := "", value := .hunterGatherers }
  , { walsCode := "tho", iso := "thp", value := .hunterGatherers }
  , { walsCode := "tua", iso := "pmt", value := .fullFledgedFarmers }
  , { walsCode := "tun", iso := "tun", value := .farmerForagers }
  , { walsCode := "urk", iso := "urb", value := .farmerForagers }
  , { walsCode := "wam", iso := "wmb", value := .hunterGatherers }
  , { walsCode := "wrl", iso := "wbp", value := .hunterGatherers }
  , { walsCode := "wnb", iso := "win", value := .farmerForagers }
  , { walsCode := "win", iso := "wnw", value := .hunterGatherers }
  , { walsCode := "xok", iso := "xok", value := .hunterGatherers }
  , { walsCode := "ygr", iso := "ygr", value := .fullFledgedFarmers }
  , { walsCode := "yan", iso := "ynn", value := .hunterGatherers }
  , { walsCode := "yir", iso := "yyr", value := .hunterGatherers }
  , { walsCode := "ykp", iso := "yup", value := .farmerForagers }
  , { walsCode := "yuk", iso := "gcd", value := .hunterGatherers }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F130B
