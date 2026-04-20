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
  /-- Red vs. yellow (98 languages). -/
  | redVsYellow
  /-- Red/yellow (15 languages). -/
  | redYellow
  /-- Yellow/green/blue vs. red (3 languages). -/
  | yellowGreenBlueVsRed
  /-- Yellow/green vs. red (1 languages). -/
  | yellowGreenVsRed
  /-- None (3 languages). -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 135A dataset (120 languages). -/
def allData : List (Datapoint RedAndYellow) :=
  [ { walsCode := "abd", iso := "abi", value := .redYellow }
  , { walsCode := "aga", iso := "agd", value := .redVsYellow }
  , { walsCode := "agc", iso := "agt", value := .redVsYellow }
  , { walsCode := "agu", iso := "agu", value := .redVsYellow }
  , { walsCode := "amk", iso := "amr", value := .redVsYellow }
  , { walsCode := "ape", iso := "apz", value := .redVsYellow }
  , { walsCode := "amz", iso := "amu", value := .redVsYellow }
  , { walsCode := "ant", iso := "agm", value := .redVsYellow }
  , { walsCode := "api", iso := "apn", value := .redVsYellow }
  , { walsCode := "arb", iso := "arl", value := .redVsYellow }
  , { walsCode := "arl", iso := "apc", value := .redVsYellow }
  , { walsCode := "bhn", iso := "bjh", value := .redVsYellow }
  , { walsCode := "bzi", iso := "bvz", value := .redVsYellow }
  , { walsCode := "brk", iso := "bkl", value := .redVsYellow }
  , { walsCode := "bhi", iso := "bhb", value := .redVsYellow }
  , { walsCode := "bgl", iso := "sab", value := .redVsYellow }
  , { walsCode := "bet", iso := "bev", value := .redYellow }
  , { walsCode := "cah", iso := "chl", value := .redVsYellow }
  , { walsCode := "cak", iso := "cak", value := .redVsYellow }
  , { walsCode := "cax", iso := "", value := .redYellow }
  , { walsCode := "cam", iso := "kbh", value := .redVsYellow }
  , { walsCode := "can", iso := "cbu", value := .redVsYellow }
  , { walsCode := "cav", iso := "cav", value := .redVsYellow }
  , { walsCode := "cay", iso := "cbi", value := .redVsYellow }
  , { walsCode := "cvc", iso := "cbk", value := .redVsYellow }
  , { walsCode := "chy", iso := "cbt", value := .redVsYellow }
  , { walsCode := "cle", iso := "cle", value := .redVsYellow }
  , { walsCode := "cqt", iso := "cax", value := .redVsYellow }
  , { walsCode := "cum", iso := "ncu", value := .redVsYellow }
  , { walsCode := "cbo", iso := "cao", value := .redYellow }
  , { walsCode := "cof", iso := "con", value := .redVsYellow }
  , { walsCode := "cea", iso := "csw", value := .yellowGreenVsRed }
  , { walsCode := "cul", iso := "cul", value := .yellowGreenBlueVsRed }
  , { walsCode := "dan", iso := "dnj", value := .redYellow }
  , { walsCode := "did", iso := "did", value := .redVsYellow }
  , { walsCode := "dym", iso := "dyi", value := .redVsYellow }
  , { walsCode := "eja", iso := "etu", value := .redYellow }
  , { walsCode := "eng", iso := "eng", value := .redVsYellow }
  , { walsCode := "ese", iso := "ese", value := .redVsYellow }
  , { walsCode := "pdp", iso := "ppo", value := .redVsYellow }
  , { walsCode := "fre", iso := "fra", value := .redVsYellow }
  , { walsCode := "grf", iso := "cab", value := .redVsYellow }
  , { walsCode := "ger", iso := "deu", value := .redVsYellow }
  , { walsCode := "ghb", iso := "guh", value := .redVsYellow }
  , { walsCode := "gmb", iso := "gum", value := .redVsYellow }
  , { walsCode := "grj", iso := "var", value := .redVsYellow }
  , { walsCode := "gun", iso := "yas", value := .redYellow }
  , { walsCode := "hlb", iso := "hlb", value := .redVsYellow }
  , { walsCode := "htc", iso := "hus", value := .redVsYellow }
  , { walsCode := "hve", iso := "huv", value := .redVsYellow }
  , { walsCode := "idn", iso := "viv", value := .redVsYellow }
  , { walsCode := "ifu", iso := "ifb", value := .redVsYellow }
  , { walsCode := "iwm", iso := "iwm", value := .redVsYellow }
  , { walsCode := "jpn", iso := "jpn", value := .redVsYellow }
  , { walsCode := "klq", iso := "kmh", value := .redVsYellow }
  , { walsCode := "kak", iso := "kbq", value := .redVsYellow }
  , { walsCode := "jva", iso := "kpj", value := .yellowGreenBlueVsRed }
  , { walsCode := "kmt", iso := "kmt", value := .redVsYellow }
  , { walsCode := "kkz", iso := "kex", value := .redVsYellow }
  , { walsCode := "kkb", iso := "xon", value := .redYellow }
  , { walsCode := "kor", iso := "kor", value := .redVsYellow }
  , { walsCode := "knq", iso := "rop", value := .redVsYellow }
  , { walsCode := "kya", iso := "gvn", value := .none }
  , { walsCode := "kun", iso := "kvn", value := .redVsYellow }
  , { walsCode := "kwb", iso := "kwe", value := .redVsYellow }
  , { walsCode := "lel", iso := "lln", value := .yellowGreenBlueVsRed }
  , { walsCode := "mmp", iso := "maw", value := .redVsYellow }
  , { walsCode := "mnd", iso := "cmn", value := .redVsYellow }
  , { walsCode := "mav", iso := "mbw", value := .redVsYellow }
  , { walsCode := "mwa", iso := "mpj", value := .redVsYellow }
  , { walsCode := "myr", iso := "mcf", value := .redVsYellow }
  , { walsCode := "mwc", iso := "mke", value := .redVsYellow }
  , { walsCode := "maz", iso := "maz", value := .redVsYellow }
  , { walsCode := "mzc", iso := "maq", value := .redVsYellow }
  , { walsCode := "mey", iso := "mcr", value := .redVsYellow }
  , { walsCode := "mic", iso := "mic", value := .redVsYellow }
  , { walsCode := "mki", iso := "mik", value := .redVsYellow }
  , { walsCode := "mxp", iso := "mil", value := .redVsYellow }
  , { walsCode := "mrl", iso := "mur", value := .redVsYellow }
  , { walsCode := "mpa", iso := "mwf", value := .none }
  , { walsCode := "mdu", iso := "muh", value := .redYellow }
  , { walsCode := "naf", iso := "nfr", value := .redYellow }
  , { walsCode := "nhn", iso := "ncj", value := .redVsYellow }
  , { walsCode := "ndy", iso := "djk", value := .redVsYellow }
  , { walsCode := "nbr", iso := "gym", value := .redVsYellow }
  , { walsCode := "ood", iso := "ood", value := .redVsYellow }
  , { walsCode := "oca", iso := "oca", value := .redVsYellow }
  , { walsCode := "pat", iso := "ptp", value := .redVsYellow }
  , { walsCode := "pec", iso := "pay", value := .redVsYellow }
  , { walsCode := "prh", iso := "myp", value := .redYellow }
  , { walsCode := "rus", iso := "rus", value := .redVsYellow }
  , { walsCode := "srm", iso := "srm", value := .redVsYellow }
  , { walsCode := "ser", iso := "sei", value := .redVsYellow }
  , { walsCode := "shk", iso := "shp", value := .redVsYellow }
  , { walsCode := "srn", iso := "srq", value := .redVsYellow }
  , { walsCode := "sla", iso := "den", value := .redVsYellow }
  , { walsCode := "spa", iso := "spa", value := .redVsYellow }
  , { walsCode := "sur", iso := "sgz", value := .redVsYellow }
  , { walsCode := "tbl", iso := "tnm", value := .redVsYellow }
  , { walsCode := "tac", iso := "tna", value := .redYellow }
  , { walsCode := "tce", iso := "tar", value := .redYellow }
  , { walsCode := "twe", iso := "tac", value := .redVsYellow }
  , { walsCode := "tbo", iso := "tbl", value := .redVsYellow }
  , { walsCode := "trb", iso := "tfr", value := .redVsYellow }
  , { walsCode := "tic", iso := "tca", value := .redVsYellow }
  , { walsCode := "tif", iso := "tif", value := .redVsYellow }
  , { walsCode := "tlp", iso := "tcf", value := .redVsYellow }
  , { walsCode := "tol", iso := "jic", value := .redVsYellow }
  , { walsCode := "tsf", iso := "cof", value := .redVsYellow }
  , { walsCode := "tuc", iso := "tuo", value := .redYellow }
  , { walsCode := "vag", iso := "vag", value := .redVsYellow }
  , { walsCode := "vas", iso := "vas", value := .redVsYellow }
  , { walsCode := "wao", iso := "auc", value := .none }
  , { walsCode := "wrl", iso := "wbp", value := .redVsYellow }
  , { walsCode := "wob", iso := "wob", value := .redYellow }
  , { walsCode := "ykn", iso := "yka", value := .redVsYellow }
  , { walsCode := "yam", iso := "yaa", value := .redVsYellow }
  , { walsCode := "ycn", iso := "ycn", value := .redVsYellow }
  , { walsCode := "yus", iso := "ess", value := .redVsYellow }
  , { walsCode := "zte", iso := "zpz", value := .redVsYellow }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F135A
