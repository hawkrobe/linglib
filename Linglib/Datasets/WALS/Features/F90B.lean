import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 90B: Prenominal relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90B`.

Chapter 90, 191 languages.
-/

namespace Datasets.WALS.F90B

/-- WALS 90B values. -/
inductive PrenominalRelativeClauses where
  /-- Relative clause-Noun (RelN) dominant (141 languages). -/
  | relativeClauseNounDominant
  /-- RelN or NRel (29 languages). -/
  | relnOrNrel
  /-- RelN or internally-headed (15 languages). -/
  | relnOrInternallyHeaded
  /-- RelN or correlative (5 languages). -/
  | relnOrCorrelative
  /-- RelN or double-headed (1 languages). -/
  | relnOrDoubleHeaded
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90B dataset (191 languages). -/
def allData : List (Datapoint PrenominalRelativeClauses) :=
  [ { walsCode := "abk", iso := "abk", value := .relativeClauseNounDominant }
  , { walsCode := "acn", iso := "acn", value := .relativeClauseNounDominant }
  , { walsCode := "ain", iso := "ain", value := .relativeClauseNounDominant }
  , { walsCode := "akh", iso := "ahk", value := .relativeClauseNounDominant }
  , { walsCode := "ala", iso := "amp", value := .relativeClauseNounDominant }
  , { walsCode := "amb", iso := "abt", value := .relativeClauseNounDominant }
  , { walsCode := "amt", iso := "adx", value := .relnOrInternallyHeaded }
  , { walsCode := "amh", iso := "amh", value := .relativeClauseNounDominant }
  , { walsCode := "ami", iso := "ami", value := .relativeClauseNounDominant }
  , { walsCode := "ao", iso := "njo", value := .relnOrInternallyHeaded }
  , { walsCode := "apt", iso := "apt", value := .relativeClauseNounDominant }
  , { walsCode := "arm", iso := "hye", value := .relnOrNrel }
  , { walsCode := "asm", iso := "cns", value := .relativeClauseNounDominant }
  , { walsCode := "ath", iso := "aph", value := .relativeClauseNounDominant }
  , { walsCode := "awa", iso := "awb", value := .relativeClauseNounDominant }
  , { walsCode := "awt", iso := "kmn", value := .relativeClauseNounDominant }
  , { walsCode := "azi", iso := "azb", value := .relnOrNrel }
  , { walsCode := "bai", iso := "bca", value := .relativeClauseNounDominant }
  , { walsCode := "blt", iso := "bft", value := .relativeClauseNounDominant }
  , { walsCode := "brl", iso := "loy", value := .relativeClauseNounDominant }
  , { walsCode := "bsk", iso := "bak", value := .relativeClauseNounDominant }
  , { walsCode := "bsq", iso := "eus", value := .relativeClauseNounDominant }
  , { walsCode := "baw", iso := "bgr", value := .relnOrInternallyHeaded }
  , { walsCode := "bel", iso := "byw", value := .relativeClauseNounDominant }
  , { walsCode := "bil", iso := "blb", value := .relnOrNrel }
  , { walsCode := "bla", iso := "bla", value := .relnOrNrel }
  , { walsCode := "bod", iso := "brx", value := .relativeClauseNounDominant }
  , { walsCode := "brm", iso := "mya", value := .relativeClauseNounDominant }
  , { walsCode := "bur", iso := "bsk", value := .relativeClauseNounDominant }
  , { walsCode := "bya", iso := "bee", value := .relnOrInternallyHeaded }
  , { walsCode := "cml", iso := "rab", value := .relativeClauseNounDominant }
  , { walsCode := "cnt", iso := "yue", value := .relativeClauseNounDominant }
  , { walsCode := "chh", iso := "sgw", value := .relativeClauseNounDominant }
  , { walsCode := "chg", iso := "nbc", value := .relnOrInternallyHeaded }
  , { walsCode := "chn", iso := "chx", value := .relativeClauseNounDominant }
  , { walsCode := "chc", iso := "che", value := .relativeClauseNounDominant }
  , { walsCode := "cpn", iso := "cdm", value := .relativeClauseNounDominant }
  , { walsCode := "che", iso := "chr", value := .relativeClauseNounDominant }
  , { walsCode := "chs", iso := "csy", value := .relativeClauseNounDominant }
  , { walsCode := "cpy", iso := "cap", value := .relativeClauseNounDominant }
  , { walsCode := "chk", iso := "ckt", value := .relnOrNrel }
  , { walsCode := "chv", iso := "chv", value := .relativeClauseNounDominant }
  , { walsCode := "dgr", iso := "dta", value := .relativeClauseNounDominant }
  , { walsCode := "drg", iso := "dar", value := .relativeClauseNounDominant }
  , { walsCode := "drm", iso := "drd", value := .relnOrCorrelative }
  , { walsCode := "dhm", iso := "dhi", value := .relativeClauseNounDominant }
  , { walsCode := "dhi", iso := "div", value := .relativeClauseNounDominant }
  , { walsCode := "dig", iso := "mhu", value := .relativeClauseNounDominant }
  , { walsCode := "dms", iso := "dis", value := .relativeClauseNounDominant }
  , { walsCode := "dlm", iso := "kbv", value := .relnOrInternallyHeaded }
  , { walsCode := "eip", iso := "eip", value := .relativeClauseNounDominant }
  , { walsCode := "evn", iso := "eve", value := .relativeClauseNounDominant }
  , { walsCode := "eve", iso := "evn", value := .relativeClauseNounDominant }
  , { walsCode := "gah", iso := "gah", value := .relnOrNrel }
  , { walsCode := "gal", iso := "adl", value := .relativeClauseNounDominant }
  , { walsCode := "gam", iso := "gmv", value := .relativeClauseNounDominant }
  , { walsCode := "gar", iso := "grt", value := .relativeClauseNounDominant }
  , { walsCode := "gim", iso := "bcq", value := .relnOrNrel }
  , { walsCode := "god", iso := "gdo", value := .relnOrNrel }
  , { walsCode := "gur", iso := "", value := .relativeClauseNounDominant }
  , { walsCode := "gyc", iso := "jya", value := .relativeClauseNounDominant }
  , { walsCode := "hak", iso := "hak", value := .relativeClauseNounDominant }
  , { walsCode := "hhu", iso := "wos", value := .relativeClauseNounDominant }
  , { walsCode := "han", iso := "hni", value := .relativeClauseNounDominant }
  , { walsCode := "har", iso := "tmd", value := .relnOrInternallyHeaded }
  , { walsCode := "hay", iso := "vay", value := .relativeClauseNounDominant }
  , { walsCode := "ho", iso := "hoc", value := .relativeClauseNounDominant }
  , { walsCode := "hua", iso := "ygr", value := .relativeClauseNounDominant }
  , { walsCode := "hum", iso := "huu", value := .relativeClauseNounDominant }
  , { walsCode := "hun", iso := "hun", value := .relnOrNrel }
  , { walsCode := "hzb", iso := "huz", value := .relativeClauseNounDominant }
  , { walsCode := "hpd", iso := "jup", value := .relativeClauseNounDominant }
  , { walsCode := "ijo", iso := "ijc", value := .relativeClauseNounDominant }
  , { walsCode := "imo", iso := "imn", value := .relnOrInternallyHeaded }
  , { walsCode := "ing", iso := "inh", value := .relativeClauseNounDominant }
  , { walsCode := "jpn", iso := "jpn", value := .relativeClauseNounDominant }
  , { walsCode := "jng", iso := "kac", value := .relativeClauseNounDominant }
  , { walsCode := "kab", iso := "kbd", value := .relativeClauseNounDominant }
  , { walsCode := "kmk", iso := "xal", value := .relativeClauseNounDominant }
  , { walsCode := "kmz", iso := "kms", value := .relnOrNrel }
  , { walsCode := "knd", iso := "kan", value := .relnOrCorrelative }
  , { walsCode := "krc", iso := "krc", value := .relativeClauseNounDominant }
  , { walsCode := "kkp", iso := "kaa", value := .relativeClauseNounDominant }
  , { walsCode := "kem", iso := "ahg", value := .relativeClauseNounDominant }
  , { walsCode := "kew", iso := "kew", value := .relnOrInternallyHeaded }
  , { walsCode := "khg", iso := "klr", value := .relativeClauseNounDominant }
  , { walsCode := "kha", iso := "khk", value := .relativeClauseNounDominant }
  , { walsCode := "kmh", iso := "kjl", value := .relativeClauseNounDominant }
  , { walsCode := "khd", iso := "khg", value := .relativeClauseNounDominant }
  , { walsCode := "kty", iso := "kca", value := .relativeClauseNounDominant }
  , { walsCode := "khr", iso := "khr", value := .relnOrCorrelative }
  , { walsCode := "khw", iso := "khw", value := .relativeClauseNounDominant }
  , { walsCode := "koa", iso := "cku", value := .relnOrInternallyHeaded }
  , { walsCode := "kob", iso := "kpw", value := .relnOrDoubleHeaded }
  , { walsCode := "kol", iso := "kfb", value := .relativeClauseNounDominant }
  , { walsCode := "krn", iso := "kqz", value := .relnOrNrel }
  , { walsCode := "kor", iso := "kor", value := .relativeClauseNounDominant }
  , { walsCode := "kku", iso := "kfq", value := .relativeClauseNounDominant }
  , { walsCode := "krw", iso := "khe", value := .relnOrNrel }
  , { walsCode := "koy", iso := "kff", value := .relativeClauseNounDominant }
  , { walsCode := "klg", iso := "kle", value := .relnOrNrel }
  , { walsCode := "kuv", iso := "kxv", value := .relativeClauseNounDominant }
  , { walsCode := "kwo", iso := "kmo", value := .relativeClauseNounDominant }
  , { walsCode := "kwt", iso := "kwo", value := .relativeClauseNounDominant }
  , { walsCode := "kgy", iso := "kgy", value := .relativeClauseNounDominant }
  , { walsCode := "lah", iso := "lhu", value := .relativeClauseNounDominant }
  , { walsCode := "lai", iso := "cnh", value := .relnOrInternallyHeaded }
  , { walsCode := "lal", iso := "ywt", value := .relnOrNrel }
  , { walsCode := "lmn", iso := "lmn", value := .relativeClauseNounDominant }
  , { walsCode := "ldu", iso := "led", value := .relnOrNrel }
  , { walsCode := "lez", iso := "lez", value := .relativeClauseNounDominant }
  , { walsCode := "lim", iso := "lif", value := .relativeClauseNounDominant }
  , { walsCode := "lis", iso := "lis", value := .relativeClauseNounDominant }
  , { walsCode := "ara", iso := "arw", value := .relnOrNrel }
  , { walsCode := "mac", iso := "mbc", value := .relnOrNrel }
  , { walsCode := "mne", iso := "nmu", value := .relativeClauseNounDominant }
  , { walsCode := "mak", iso := "myh", value := .relnOrNrel }
  , { walsCode := "mym", iso := "mal", value := .relativeClauseNounDominant }
  , { walsCode := "nmm", iso := "nmm", value := .relativeClauseNounDominant }
  , { walsCode := "mnd", iso := "cmn", value := .relativeClauseNounDominant }
  , { walsCode := "mgg", iso := "mjg", value := .relativeClauseNounDominant }
  , { walsCode := "mns", iso := "mns", value := .relativeClauseNounDominant }
  , { walsCode := "mhi", iso := "mar", value := .relativeClauseNounDominant }
  , { walsCode := "mru", iso := "mhx", value := .relativeClauseNounDominant }
  , { walsCode := "mei", iso := "mni", value := .relativeClauseNounDominant }
  , { walsCode := "msg", iso := "mrg", value := .relativeClauseNounDominant }
  , { walsCode := "mun", iso := "unr", value := .relativeClauseNounDominant }
  , { walsCode := "nma", iso := "nbi", value := .relativeClauseNounDominant }
  , { walsCode := "ngt", iso := "nmf", value := .relativeClauseNounDominant }
  , { walsCode := "nhn", iso := "ncj", value := .relnOrNrel }
  , { walsCode := "kho", iso := "naq", value := .relativeClauseNounDominant }
  , { walsCode := "nam", iso := "nnm", value := .relnOrNrel }
  , { walsCode := "nph", iso := "npa", value := .relativeClauseNounDominant }
  , { walsCode := "nwd", iso := "new", value := .relativeClauseNounDominant }
  , { walsCode := "new", iso := "new", value := .relativeClauseNounDominant }
  , { walsCode := "niv", iso := "niv", value := .relativeClauseNounDominant }
  , { walsCode := "noc", iso := "njb", value := .relativeClauseNounDominant }
  , { walsCode := "pan", iso := "pan", value := .relnOrInternallyHeaded }
  , { walsCode := "pum", iso := "pmi", value := .relativeClauseNounDominant }
  , { walsCode := "prk", iso := "prx", value := .relativeClauseNounDominant }
  , { walsCode := "qaf", iso := "aar", value := .relativeClauseNounDominant }
  , { walsCode := "qia", iso := "", value := .relativeClauseNounDominant }
  , { walsCode := "qhu", iso := "qub", value := .relativeClauseNounDominant }
  , { walsCode := "qim", iso := "qvi", value := .relativeClauseNounDominant }
  , { walsCode := "raw", iso := "raw", value := .relativeClauseNounDominant }
  , { walsCode := "ruk", iso := "dru", value := .relnOrNrel }
  , { walsCode := "rum", iso := "klq", value := .relativeClauseNounDominant }
  , { walsCode := "stl", iso := "sat", value := .relnOrCorrelative }
  , { walsCode := "sar", iso := "dju", value := .relativeClauseNounDominant }
  , { walsCode := "svs", iso := "svs", value := .relativeClauseNounDominant }
  , { walsCode := "skw", iso := "swv", value := .relnOrCorrelative }
  , { walsCode := "sid", iso := "sid", value := .relativeClauseNounDominant }
  , { walsCode := "skk", iso := "sip", value := .relativeClauseNounDominant }
  , { walsCode := "sng", iso := "snc", value := .relativeClauseNounDominant }
  , { walsCode := "squ", iso := "squ", value := .relnOrNrel }
  , { walsCode := "tam", iso := "taj", value := .relativeClauseNounDominant }
  , { walsCode := "tml", iso := "tam", value := .relativeClauseNounDominant }
  , { walsCode := "twe", iso := "tac", value := .relnOrNrel }
  , { walsCode := "tvo", iso := "tat", value := .relativeClauseNounDominant }
  , { walsCode := "tau", iso := "tya", value := .relnOrNrel }
  , { walsCode := "tel", iso := "tel", value := .relativeClauseNounDominant }
  , { walsCode := "thu", iso := "tdh", value := .relativeClauseNounDominant }
  , { walsCode := "tdr", iso := "bod", value := .relnOrNrel }
  , { walsCode := "tmo", iso := "bod", value := .relativeClauseNounDominant }
  , { walsCode := "tis", iso := "bod", value := .relnOrInternallyHeaded }
  , { walsCode := "tib", iso := "bod", value := .relativeClauseNounDominant }
  , { walsCode := "tgr", iso := "tig", value := .relativeClauseNounDominant }
  , { walsCode := "tli", iso := "tli", value := .relativeClauseNounDominant }
  , { walsCode := "tsf", iso := "cof", value := .relativeClauseNounDominant }
  , { walsCode := "tgl", iso := "tsj", value := .relativeClauseNounDominant }
  , { walsCode := "ttu", iso := "bbl", value := .relativeClauseNounDominant }
  , { walsCode := "tuc", iso := "tuo", value := .relativeClauseNounDominant }
  , { walsCode := "tur", iso := "tur", value := .relativeClauseNounDominant }
  , { walsCode := "tkm", iso := "tuk", value := .relativeClauseNounDominant }
  , { walsCode := "tsh", iso := "par", value := .relnOrNrel }
  , { walsCode := "uby", iso := "uby", value := .relativeClauseNounDominant }
  , { walsCode := "udh", iso := "ude", value := .relnOrInternallyHeaded }
  , { walsCode := "una", iso := "mtg", value := .relativeClauseNounDominant }
  , { walsCode := "urn", iso := "ura", value := .relativeClauseNounDominant }
  , { walsCode := "uyg", iso := "uig", value := .relativeClauseNounDominant }
  , { walsCode := "uzb", iso := "", value := .relativeClauseNounDominant }
  , { walsCode := "wbn", iso := "wms", value := .relnOrInternallyHeaded }
  , { walsCode := "wao", iso := "auc", value := .relnOrNrel }
  , { walsCode := "wrg", iso := "wgy", value := .relnOrNrel }
  , { walsCode := "ygr", iso := "ygr", value := .relativeClauseNounDominant }
  , { walsCode := "ykt", iso := "sah", value := .relativeClauseNounDominant }
  , { walsCode := "yal", iso := "kkl", value := .relativeClauseNounDominant }
  , { walsCode := "yar", iso := "yrb", value := .relativeClauseNounDominant }
  , { walsCode := "yko", iso := "yux", value := .relativeClauseNounDominant }
  , { walsCode := "yur", iso := "yur", value := .relnOrNrel }
  , { walsCode := "zay", iso := "zay", value := .relativeClauseNounDominant }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F90B
