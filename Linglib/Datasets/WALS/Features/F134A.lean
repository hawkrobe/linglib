import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 134A: Green and Blue
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 134A`.

Chapter 134, 120 languages.
-/

namespace Datasets.WALS.F134A

/-- WALS 134A values. -/
inductive GreenAndBlue where
  /-- Green vs. blue (30 languages). -/
  | greenVsBlue
  /-- Green/blue (68 languages). -/
  | greenBlue
  /-- Black/green/blue (15 languages). -/
  | blackGreenBlue
  /-- Black/blue vs. green (2 languages). -/
  | blackBlueVsGreen
  /-- Yellow/green/blue (2 languages). -/
  | yellowGreenBlue
  /-- Yellow/green vs. blue (1 languages). -/
  | yellowGreenVsBlue
  /-- None (2 languages). -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 134A dataset (120 languages). -/
def allData : List (Datapoint GreenAndBlue) :=
  [ { walsCode := "abd", iso := "abi", value := .greenBlue }
  , { walsCode := "aga", iso := "agd", value := .greenBlue }
  , { walsCode := "agc", iso := "agt", value := .greenBlue }
  , { walsCode := "agu", iso := "agu", value := .greenBlue }
  , { walsCode := "amk", iso := "amr", value := .greenBlue }
  , { walsCode := "ape", iso := "apz", value := .greenBlue }
  , { walsCode := "amz", iso := "amu", value := .greenVsBlue }
  , { walsCode := "ant", iso := "agm", value := .greenVsBlue }
  , { walsCode := "api", iso := "apn", value := .greenBlue }
  , { walsCode := "arb", iso := "arl", value := .greenBlue }
  , { walsCode := "arl", iso := "apc", value := .greenVsBlue }
  , { walsCode := "bhn", iso := "bjh", value := .greenBlue }
  , { walsCode := "bzi", iso := "bvz", value := .greenBlue }
  , { walsCode := "brk", iso := "bkl", value := .greenBlue }
  , { walsCode := "bhi", iso := "bhb", value := .greenBlue }
  , { walsCode := "bgl", iso := "sab", value := .greenVsBlue }
  , { walsCode := "bet", iso := "bev", value := .blackGreenBlue }
  , { walsCode := "cah", iso := "chl", value := .greenBlue }
  , { walsCode := "cak", iso := "cak", value := .greenVsBlue }
  , { walsCode := "cax", iso := "", value := .blackGreenBlue }
  , { walsCode := "cam", iso := "kbh", value := .greenVsBlue }
  , { walsCode := "can", iso := "cbu", value := .greenVsBlue }
  , { walsCode := "cav", iso := "cav", value := .greenBlue }
  , { walsCode := "cay", iso := "cbi", value := .greenBlue }
  , { walsCode := "cvc", iso := "cbk", value := .greenVsBlue }
  , { walsCode := "chy", iso := "cbt", value := .greenBlue }
  , { walsCode := "cle", iso := "cle", value := .greenBlue }
  , { walsCode := "cqt", iso := "cax", value := .greenVsBlue }
  , { walsCode := "cum", iso := "ncu", value := .greenVsBlue }
  , { walsCode := "cbo", iso := "cao", value := .greenBlue }
  , { walsCode := "cof", iso := "con", value := .greenBlue }
  , { walsCode := "cea", iso := "csw", value := .yellowGreenVsBlue }
  , { walsCode := "cul", iso := "cul", value := .blackGreenBlue }
  , { walsCode := "dan", iso := "dnj", value := .blackGreenBlue }
  , { walsCode := "did", iso := "did", value := .greenBlue }
  , { walsCode := "dym", iso := "dyi", value := .greenVsBlue }
  , { walsCode := "eja", iso := "etu", value := .blackGreenBlue }
  , { walsCode := "eng", iso := "eng", value := .greenVsBlue }
  , { walsCode := "ese", iso := "ese", value := .greenBlue }
  , { walsCode := "pdp", iso := "ppo", value := .blackGreenBlue }
  , { walsCode := "fre", iso := "fra", value := .greenVsBlue }
  , { walsCode := "grf", iso := "cab", value := .greenVsBlue }
  , { walsCode := "ger", iso := "deu", value := .greenVsBlue }
  , { walsCode := "ghb", iso := "guh", value := .greenBlue }
  , { walsCode := "gmb", iso := "gum", value := .greenBlue }
  , { walsCode := "grj", iso := "var", value := .greenBlue }
  , { walsCode := "gun", iso := "yas", value := .blackGreenBlue }
  , { walsCode := "hlb", iso := "hlb", value := .greenBlue }
  , { walsCode := "htc", iso := "hus", value := .greenBlue }
  , { walsCode := "hve", iso := "huv", value := .greenVsBlue }
  , { walsCode := "idn", iso := "viv", value := .greenBlue }
  , { walsCode := "ifu", iso := "ifb", value := .blackBlueVsGreen }
  , { walsCode := "iwm", iso := "iwm", value := .greenBlue }
  , { walsCode := "jpn", iso := "jpn", value := .greenVsBlue }
  , { walsCode := "klq", iso := "kmh", value := .greenBlue }
  , { walsCode := "kak", iso := "kbq", value := .greenBlue }
  , { walsCode := "jva", iso := "kpj", value := .yellowGreenBlue }
  , { walsCode := "kmt", iso := "kmt", value := .greenBlue }
  , { walsCode := "kkz", iso := "kex", value := .greenVsBlue }
  , { walsCode := "kkb", iso := "xon", value := .blackGreenBlue }
  , { walsCode := "kor", iso := "kor", value := .greenVsBlue }
  , { walsCode := "knq", iso := "rop", value := .greenVsBlue }
  , { walsCode := "kya", iso := "gvn", value := .none }
  , { walsCode := "kun", iso := "kvn", value := .greenBlue }
  , { walsCode := "kwb", iso := "kwe", value := .blackGreenBlue }
  , { walsCode := "lel", iso := "lln", value := .yellowGreenBlue }
  , { walsCode := "mmp", iso := "maw", value := .blackGreenBlue }
  , { walsCode := "mnd", iso := "cmn", value := .greenVsBlue }
  , { walsCode := "mav", iso := "mbw", value := .greenBlue }
  , { walsCode := "mwa", iso := "mpj", value := .blackBlueVsGreen }
  , { walsCode := "myr", iso := "mcf", value := .greenBlue }
  , { walsCode := "mwc", iso := "mke", value := .greenBlue }
  , { walsCode := "maz", iso := "maz", value := .greenVsBlue }
  , { walsCode := "mzc", iso := "maq", value := .greenBlue }
  , { walsCode := "mey", iso := "mcr", value := .greenBlue }
  , { walsCode := "mic", iso := "mic", value := .greenVsBlue }
  , { walsCode := "mki", iso := "mik", value := .greenBlue }
  , { walsCode := "mxp", iso := "mil", value := .greenBlue }
  , { walsCode := "mrl", iso := "mur", value := .greenBlue }
  , { walsCode := "mpa", iso := "mwf", value := .none }
  , { walsCode := "mdu", iso := "muh", value := .blackGreenBlue }
  , { walsCode := "naf", iso := "nfr", value := .blackGreenBlue }
  , { walsCode := "nhn", iso := "ncj", value := .greenVsBlue }
  , { walsCode := "ndy", iso := "djk", value := .greenVsBlue }
  , { walsCode := "nbr", iso := "gym", value := .greenVsBlue }
  , { walsCode := "ood", iso := "ood", value := .greenBlue }
  , { walsCode := "oca", iso := "oca", value := .greenBlue }
  , { walsCode := "pat", iso := "ptp", value := .greenBlue }
  , { walsCode := "pec", iso := "pay", value := .greenBlue }
  , { walsCode := "prh", iso := "myp", value := .greenBlue }
  , { walsCode := "rus", iso := "rus", value := .greenVsBlue }
  , { walsCode := "srm", iso := "srm", value := .greenBlue }
  , { walsCode := "ser", iso := "sei", value := .greenBlue }
  , { walsCode := "shk", iso := "shp", value := .greenBlue }
  , { walsCode := "srn", iso := "srq", value := .greenBlue }
  , { walsCode := "sla", iso := "den", value := .greenVsBlue }
  , { walsCode := "spa", iso := "spa", value := .greenVsBlue }
  , { walsCode := "sur", iso := "sgz", value := .greenBlue }
  , { walsCode := "tbl", iso := "tnm", value := .greenBlue }
  , { walsCode := "tac", iso := "tna", value := .greenBlue }
  , { walsCode := "tce", iso := "tar", value := .greenBlue }
  , { walsCode := "twe", iso := "tac", value := .greenBlue }
  , { walsCode := "tbo", iso := "tbl", value := .greenBlue }
  , { walsCode := "trb", iso := "tfr", value := .greenBlue }
  , { walsCode := "tic", iso := "tca", value := .greenBlue }
  , { walsCode := "tif", iso := "tif", value := .blackGreenBlue }
  , { walsCode := "tlp", iso := "tcf", value := .greenBlue }
  , { walsCode := "tol", iso := "jic", value := .greenBlue }
  , { walsCode := "tsf", iso := "cof", value := .greenBlue }
  , { walsCode := "tuc", iso := "tuo", value := .greenBlue }
  , { walsCode := "vag", iso := "vag", value := .blackGreenBlue }
  , { walsCode := "vas", iso := "vas", value := .greenBlue }
  , { walsCode := "wao", iso := "auc", value := .greenBlue }
  , { walsCode := "wrl", iso := "wbp", value := .greenBlue }
  , { walsCode := "wob", iso := "wob", value := .blackGreenBlue }
  , { walsCode := "ykn", iso := "yka", value := .greenVsBlue }
  , { walsCode := "yam", iso := "yaa", value := .greenBlue }
  , { walsCode := "ycn", iso := "ycn", value := .greenBlue }
  , { walsCode := "yus", iso := "ess", value := .greenBlue }
  , { walsCode := "zte", iso := "zpz", value := .greenBlue }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F134A
