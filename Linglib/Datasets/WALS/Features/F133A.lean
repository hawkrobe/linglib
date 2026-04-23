import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 133A: Number of Basic Colour Categories
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 133A`.

Chapter 133, 119 languages.
-/

namespace Datasets.WALS.F133A

/-- WALS 133A values. -/
inductive NumberOfBasicColourCategories where
  /-- 3-4 (20 languages). -/
  | v34
  /-- 4.5-5.5 (26 languages). -/
  | v4555
  /-- 6-6.5 (34 languages). -/
  | v665
  /-- 7-7.5 (14 languages). -/
  | v775
  /-- 8-8.5 (6 languages). -/
  | v885
  /-- 9-10 (8 languages). -/
  | v910
  /-- 11 (11 languages). -/
  | v11
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 133A dataset (119 languages). -/
def allData : List (Datapoint NumberOfBasicColourCategories) :=
  [ { walsCode := "abd", iso := "abi", value := .v4555 }
  , { walsCode := "aga", iso := "agd", value := .v4555 }
  , { walsCode := "agc", iso := "agt", value := .v665 }
  , { walsCode := "agu", iso := "agu", value := .v775 }
  , { walsCode := "amk", iso := "amr", value := .v665 }
  , { walsCode := "ape", iso := "apz", value := .v4555 }
  , { walsCode := "amz", iso := "amu", value := .v885 }
  , { walsCode := "ant", iso := "agm", value := .v775 }
  , { walsCode := "api", iso := "apn", value := .v4555 }
  , { walsCode := "arb", iso := "arl", value := .v4555 }
  , { walsCode := "arl", iso := "apc", value := .v11 }
  , { walsCode := "bhn", iso := "bjh", value := .v665 }
  , { walsCode := "bzi", iso := "bvz", value := .v4555 }
  , { walsCode := "brk", iso := "bkl", value := .v4555 }
  , { walsCode := "bhi", iso := "bhb", value := .v775 }
  , { walsCode := "bgl", iso := "sab", value := .v665 }
  , { walsCode := "bet", iso := "bev", value := .v34 }
  , { walsCode := "cak", iso := "cak", value := .v11 }
  , { walsCode := "cax", iso := "", value := .v34 }
  , { walsCode := "cam", iso := "kbh", value := .v910 }
  , { walsCode := "can", iso := "cbu", value := .v4555 }
  , { walsCode := "cav", iso := "cav", value := .v665 }
  , { walsCode := "cay", iso := "cbi", value := .v4555 }
  , { walsCode := "cvc", iso := "cbk", value := .v910 }
  , { walsCode := "chy", iso := "cbt", value := .v665 }
  , { walsCode := "cle", iso := "cle", value := .v775 }
  , { walsCode := "cqt", iso := "cax", value := .v910 }
  , { walsCode := "cum", iso := "ncu", value := .v775 }
  , { walsCode := "cbo", iso := "cao", value := .v34 }
  , { walsCode := "cof", iso := "con", value := .v665 }
  , { walsCode := "cea", iso := "csw", value := .v4555 }
  , { walsCode := "cul", iso := "cul", value := .v34 }
  , { walsCode := "dan", iso := "dnj", value := .v34 }
  , { walsCode := "did", iso := "did", value := .v775 }
  , { walsCode := "dym", iso := "dyi", value := .v665 }
  , { walsCode := "eja", iso := "etu", value := .v34 }
  , { walsCode := "eng", iso := "eng", value := .v11 }
  , { walsCode := "ese", iso := "ese", value := .v775 }
  , { walsCode := "pdp", iso := "ppo", value := .v4555 }
  , { walsCode := "fre", iso := "fra", value := .v11 }
  , { walsCode := "grf", iso := "cab", value := .v910 }
  , { walsCode := "ger", iso := "deu", value := .v11 }
  , { walsCode := "ghb", iso := "guh", value := .v665 }
  , { walsCode := "gmb", iso := "gum", value := .v665 }
  , { walsCode := "grj", iso := "var", value := .v665 }
  , { walsCode := "gun", iso := "yas", value := .v34 }
  , { walsCode := "hlb", iso := "hlb", value := .v4555 }
  , { walsCode := "htc", iso := "hus", value := .v665 }
  , { walsCode := "hve", iso := "huv", value := .v910 }
  , { walsCode := "idn", iso := "viv", value := .v4555 }
  , { walsCode := "ifu", iso := "ifb", value := .v4555 }
  , { walsCode := "iwm", iso := "iwm", value := .v4555 }
  , { walsCode := "jpn", iso := "jpn", value := .v11 }
  , { walsCode := "klq", iso := "kmh", value := .v665 }
  , { walsCode := "kak", iso := "kbq", value := .v665 }
  , { walsCode := "jva", iso := "kpj", value := .v4555 }
  , { walsCode := "kmt", iso := "kmt", value := .v4555 }
  , { walsCode := "kkz", iso := "kex", value := .v775 }
  , { walsCode := "kkb", iso := "xon", value := .v34 }
  , { walsCode := "kor", iso := "kor", value := .v11 }
  , { walsCode := "knq", iso := "rop", value := .v11 }
  , { walsCode := "kya", iso := "gvn", value := .v34 }
  , { walsCode := "kun", iso := "kvn", value := .v775 }
  , { walsCode := "kwb", iso := "kwe", value := .v34 }
  , { walsCode := "lel", iso := "lln", value := .v34 }
  , { walsCode := "mmp", iso := "maw", value := .v665 }
  , { walsCode := "mnd", iso := "cmn", value := .v885 }
  , { walsCode := "mav", iso := "mbw", value := .v4555 }
  , { walsCode := "mwa", iso := "mpj", value := .v4555 }
  , { walsCode := "myr", iso := "mcf", value := .v34 }
  , { walsCode := "mwc", iso := "mke", value := .v775 }
  , { walsCode := "maz", iso := "maz", value := .v910 }
  , { walsCode := "mzc", iso := "maq", value := .v910 }
  , { walsCode := "mey", iso := "mcr", value := .v665 }
  , { walsCode := "mic", iso := "mic", value := .v665 }
  , { walsCode := "mki", iso := "mik", value := .v885 }
  , { walsCode := "mxp", iso := "mil", value := .v775 }
  , { walsCode := "mrl", iso := "mur", value := .v665 }
  , { walsCode := "mpa", iso := "mwf", value := .v34 }
  , { walsCode := "mdu", iso := "muh", value := .v34 }
  , { walsCode := "naf", iso := "nfr", value := .v34 }
  , { walsCode := "nhn", iso := "ncj", value := .v885 }
  , { walsCode := "ndy", iso := "djk", value := .v665 }
  , { walsCode := "nbr", iso := "gym", value := .v775 }
  , { walsCode := "ood", iso := "ood", value := .v885 }
  , { walsCode := "oca", iso := "oca", value := .v665 }
  , { walsCode := "pat", iso := "ptp", value := .v665 }
  , { walsCode := "pec", iso := "pay", value := .v4555 }
  , { walsCode := "prh", iso := "myp", value := .v34 }
  , { walsCode := "rus", iso := "rus", value := .v11 }
  , { walsCode := "srm", iso := "srm", value := .v910 }
  , { walsCode := "ser", iso := "sei", value := .v665 }
  , { walsCode := "shk", iso := "shp", value := .v665 }
  , { walsCode := "srn", iso := "srq", value := .v4555 }
  , { walsCode := "sla", iso := "den", value := .v775 }
  , { walsCode := "spa", iso := "spa", value := .v11 }
  , { walsCode := "sur", iso := "sgz", value := .v665 }
  , { walsCode := "tbl", iso := "tnm", value := .v665 }
  , { walsCode := "tac", iso := "tna", value := .v665 }
  , { walsCode := "tce", iso := "tar", value := .v4555 }
  , { walsCode := "twe", iso := "tac", value := .v665 }
  , { walsCode := "tbo", iso := "tbl", value := .v665 }
  , { walsCode := "trb", iso := "tfr", value := .v775 }
  , { walsCode := "tic", iso := "tca", value := .v665 }
  , { walsCode := "tif", iso := "tif", value := .v34 }
  , { walsCode := "tlp", iso := "tcf", value := .v885 }
  , { walsCode := "tol", iso := "jic", value := .v4555 }
  , { walsCode := "tsf", iso := "cof", value := .v4555 }
  , { walsCode := "tuc", iso := "tuo", value := .v4555 }
  , { walsCode := "vag", iso := "vag", value := .v34 }
  , { walsCode := "vas", iso := "vas", value := .v665 }
  , { walsCode := "wao", iso := "auc", value := .v34 }
  , { walsCode := "wrl", iso := "wbp", value := .v665 }
  , { walsCode := "wob", iso := "wob", value := .v34 }
  , { walsCode := "ykn", iso := "yka", value := .v11 }
  , { walsCode := "yam", iso := "yaa", value := .v4555 }
  , { walsCode := "ycn", iso := "ycn", value := .v665 }
  , { walsCode := "yus", iso := "ess", value := .v665 }
  , { walsCode := "zte", iso := "zpz", value := .v665 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F133A
