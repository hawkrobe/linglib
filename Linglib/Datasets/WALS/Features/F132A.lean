import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 132A: Number of Non-Derived Basic Colour Categories
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 132A`.

Chapter 132, 119 languages.
-/

namespace Datasets.WALS.F132A

/-- WALS 132A values. -/
inductive NumberOfNonDerivedBasicColourCategories where
  /-- 3 (10 languages). -/
  | v3
  /-- 3.5 (3 languages). -/
  | v35
  /-- 4 (9 languages). -/
  | v4
  /-- 4.5 (1 languages). -/
  | v45
  /-- 5 (56 languages). -/
  | v5
  /-- 5.5 (11 languages). -/
  | v55
  /-- 6 (29 languages). -/
  | v6
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 132A dataset (119 languages). -/
def allData : List (Datapoint NumberOfNonDerivedBasicColourCategories) :=
  [ { walsCode := "abd", iso := "abi", value := .v35 }
  , { walsCode := "aga", iso := "agd", value := .v5 }
  , { walsCode := "agc", iso := "agt", value := .v5 }
  , { walsCode := "agu", iso := "agu", value := .v5 }
  , { walsCode := "amk", iso := "amr", value := .v55 }
  , { walsCode := "ape", iso := "apz", value := .v5 }
  , { walsCode := "amz", iso := "amu", value := .v6 }
  , { walsCode := "ant", iso := "agm", value := .v5 }
  , { walsCode := "api", iso := "apn", value := .v5 }
  , { walsCode := "arb", iso := "arl", value := .v5 }
  , { walsCode := "arl", iso := "apc", value := .v6 }
  , { walsCode := "bhn", iso := "bjh", value := .v5 }
  , { walsCode := "bzi", iso := "bvz", value := .v5 }
  , { walsCode := "brk", iso := "bkl", value := .v5 }
  , { walsCode := "bhi", iso := "bhb", value := .v5 }
  , { walsCode := "bgl", iso := "sab", value := .v6 }
  , { walsCode := "bet", iso := "bev", value := .v3 }
  , { walsCode := "cak", iso := "cak", value := .v6 }
  , { walsCode := "cax", iso := "", value := .v3 }
  , { walsCode := "cam", iso := "kbh", value := .v6 }
  , { walsCode := "can", iso := "cbu", value := .v55 }
  , { walsCode := "cav", iso := "cav", value := .v5 }
  , { walsCode := "cay", iso := "cbi", value := .v5 }
  , { walsCode := "cvc", iso := "cbk", value := .v6 }
  , { walsCode := "chy", iso := "cbt", value := .v5 }
  , { walsCode := "cle", iso := "cle", value := .v5 }
  , { walsCode := "cqt", iso := "cax", value := .v6 }
  , { walsCode := "cum", iso := "ncu", value := .v55 }
  , { walsCode := "cbo", iso := "cao", value := .v4 }
  , { walsCode := "cof", iso := "con", value := .v5 }
  , { walsCode := "cea", iso := "csw", value := .v5 }
  , { walsCode := "cul", iso := "cul", value := .v4 }
  , { walsCode := "dan", iso := "dnj", value := .v3 }
  , { walsCode := "did", iso := "did", value := .v5 }
  , { walsCode := "dym", iso := "dyi", value := .v6 }
  , { walsCode := "eja", iso := "etu", value := .v3 }
  , { walsCode := "eng", iso := "eng", value := .v6 }
  , { walsCode := "ese", iso := "ese", value := .v5 }
  , { walsCode := "pdp", iso := "ppo", value := .v45 }
  , { walsCode := "fre", iso := "fra", value := .v6 }
  , { walsCode := "grf", iso := "cab", value := .v6 }
  , { walsCode := "ger", iso := "deu", value := .v6 }
  , { walsCode := "ghb", iso := "guh", value := .v5 }
  , { walsCode := "gmb", iso := "gum", value := .v55 }
  , { walsCode := "grj", iso := "var", value := .v5 }
  , { walsCode := "gun", iso := "yas", value := .v35 }
  , { walsCode := "hlb", iso := "hlb", value := .v5 }
  , { walsCode := "htc", iso := "hus", value := .v5 }
  , { walsCode := "hve", iso := "huv", value := .v6 }
  , { walsCode := "idn", iso := "viv", value := .v5 }
  , { walsCode := "ifu", iso := "ifb", value := .v5 }
  , { walsCode := "iwm", iso := "iwm", value := .v5 }
  , { walsCode := "jpn", iso := "jpn", value := .v6 }
  , { walsCode := "klq", iso := "kmh", value := .v6 }
  , { walsCode := "kak", iso := "kbq", value := .v6 }
  , { walsCode := "jva", iso := "kpj", value := .v4 }
  , { walsCode := "kmt", iso := "kmt", value := .v5 }
  , { walsCode := "kkz", iso := "kex", value := .v6 }
  , { walsCode := "kkb", iso := "xon", value := .v35 }
  , { walsCode := "kor", iso := "kor", value := .v6 }
  , { walsCode := "knq", iso := "rop", value := .v6 }
  , { walsCode := "kya", iso := "gvn", value := .v3 }
  , { walsCode := "kun", iso := "kvn", value := .v5 }
  , { walsCode := "kwb", iso := "kwe", value := .v3 }
  , { walsCode := "lel", iso := "lln", value := .v4 }
  , { walsCode := "mmp", iso := "maw", value := .v55 }
  , { walsCode := "mnd", iso := "cmn", value := .v6 }
  , { walsCode := "mav", iso := "mbw", value := .v55 }
  , { walsCode := "mwa", iso := "mpj", value := .v5 }
  , { walsCode := "myr", iso := "mcf", value := .v4 }
  , { walsCode := "mwc", iso := "mke", value := .v5 }
  , { walsCode := "maz", iso := "maz", value := .v6 }
  , { walsCode := "mzc", iso := "maq", value := .v55 }
  , { walsCode := "mey", iso := "mcr", value := .v5 }
  , { walsCode := "mic", iso := "mic", value := .v6 }
  , { walsCode := "mki", iso := "mik", value := .v5 }
  , { walsCode := "mxp", iso := "mil", value := .v5 }
  , { walsCode := "mrl", iso := "mur", value := .v5 }
  , { walsCode := "mpa", iso := "mwf", value := .v3 }
  , { walsCode := "mdu", iso := "muh", value := .v3 }
  , { walsCode := "naf", iso := "nfr", value := .v3 }
  , { walsCode := "nhn", iso := "ncj", value := .v6 }
  , { walsCode := "ndy", iso := "djk", value := .v6 }
  , { walsCode := "nbr", iso := "gym", value := .v6 }
  , { walsCode := "ood", iso := "ood", value := .v5 }
  , { walsCode := "oca", iso := "oca", value := .v5 }
  , { walsCode := "pat", iso := "ptp", value := .v55 }
  , { walsCode := "pec", iso := "pay", value := .v5 }
  , { walsCode := "prh", iso := "myp", value := .v4 }
  , { walsCode := "rus", iso := "rus", value := .v6 }
  , { walsCode := "srm", iso := "srm", value := .v55 }
  , { walsCode := "ser", iso := "sei", value := .v5 }
  , { walsCode := "shk", iso := "shp", value := .v5 }
  , { walsCode := "srn", iso := "srq", value := .v5 }
  , { walsCode := "sla", iso := "den", value := .v6 }
  , { walsCode := "spa", iso := "spa", value := .v6 }
  , { walsCode := "sur", iso := "sgz", value := .v5 }
  , { walsCode := "tbl", iso := "tnm", value := .v5 }
  , { walsCode := "tac", iso := "tna", value := .v55 }
  , { walsCode := "tce", iso := "tar", value := .v5 }
  , { walsCode := "twe", iso := "tac", value := .v5 }
  , { walsCode := "tbo", iso := "tbl", value := .v5 }
  , { walsCode := "trb", iso := "tfr", value := .v55 }
  , { walsCode := "tic", iso := "tca", value := .v5 }
  , { walsCode := "tif", iso := "tif", value := .v4 }
  , { walsCode := "tlp", iso := "tcf", value := .v5 }
  , { walsCode := "tol", iso := "jic", value := .v5 }
  , { walsCode := "tsf", iso := "cof", value := .v5 }
  , { walsCode := "tuc", iso := "tuo", value := .v5 }
  , { walsCode := "vag", iso := "vag", value := .v4 }
  , { walsCode := "vas", iso := "vas", value := .v5 }
  , { walsCode := "wao", iso := "auc", value := .v4 }
  , { walsCode := "wrl", iso := "wbp", value := .v5 }
  , { walsCode := "wob", iso := "wob", value := .v3 }
  , { walsCode := "ykn", iso := "yka", value := .v6 }
  , { walsCode := "yam", iso := "yaa", value := .v5 }
  , { walsCode := "ycn", iso := "ycn", value := .v5 }
  , { walsCode := "yus", iso := "ess", value := .v5 }
  , { walsCode := "zte", iso := "zpz", value := .v5 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F132A
