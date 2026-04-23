import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 137A: N-M Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 137A`.

Chapter 137, 230 languages.
-/

namespace Datasets.WALS.F137A

/-- WALS 137A values. -/
inductive NMPronouns where
  /-- No N-M pronouns (194 languages). -/
  | noNMPronouns
  /-- N-M pronouns, paradigmatic (25 languages). -/
  | nMPronounsParadigmatic
  /-- N-M pronouns, non-paradigmatic (11 languages). -/
  | nMPronounsNonParadigmatic
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 137A dataset (230 languages). -/
def allData : List (Datapoint NMPronouns) :=
  [ { walsCode := "abk", iso := "abk", value := .noNMPronouns }
  , { walsCode := "ace", iso := "ace", value := .noNMPronouns }
  , { walsCode := "aco", iso := "kjq", value := .noNMPronouns }
  , { walsCode := "ain", iso := "ain", value := .noNMPronouns }
  , { walsCode := "ala", iso := "amp", value := .noNMPronouns }
  , { walsCode := "ame", iso := "aey", value := .noNMPronouns }
  , { walsCode := "amh", iso := "amh", value := .noNMPronouns }
  , { walsCode := "ane", iso := "anz", value := .noNMPronouns }
  , { walsCode := "apu", iso := "apu", value := .noNMPronouns }
  , { walsCode := "aeg", iso := "arz", value := .noNMPronouns }
  , { walsCode := "arp", iso := "ape", value := .noNMPronouns }
  , { walsCode := "amp", iso := "aer", value := .noNMPronouns }
  , { walsCode := "asm", iso := "cns", value := .nMPronounsNonParadigmatic }
  , { walsCode := "atk", iso := "aqp", value := .noNMPronouns }
  , { walsCode := "awp", iso := "kwi", value := .noNMPronouns }
  , { walsCode := "awt", iso := "kmn", value := .noNMPronouns }
  , { walsCode := "ayw", iso := "nfl", value := .noNMPronouns }
  , { walsCode := "bag", iso := "bmi", value := .noNMPronouns }
  , { walsCode := "brs", iso := "bsn", value := .noNMPronouns }
  , { walsCode := "bsq", iso := "eus", value := .noNMPronouns }
  , { walsCode := "bej", iso := "bej", value := .noNMPronouns }
  , { walsCode := "bel", iso := "byw", value := .noNMPronouns }
  , { walsCode := "bma", iso := "tzm", value := .nMPronounsNonParadigmatic }
  , { walsCode := "brk", iso := "bkl", value := .noNMPronouns }
  , { walsCode := "brr", iso := "bor", value := .noNMPronouns }
  , { walsCode := "brm", iso := "mya", value := .noNMPronouns }
  , { walsCode := "bur", iso := "bsk", value := .noNMPronouns }
  , { walsCode := "cax", iso := "", value := .nMPronounsParadigmatic }
  , { walsCode := "cnl", iso := "ram", value := .noNMPronouns }
  , { walsCode := "csh", iso := "cbs", value := .nMPronounsParadigmatic }
  , { walsCode := "cyv", iso := "cyb", value := .noNMPronouns }
  , { walsCode := "cha", iso := "cha", value := .noNMPronouns }
  , { walsCode := "cjo", iso := "pei", value := .noNMPronouns }
  , { walsCode := "chi", iso := "cid", value := .nMPronounsParadigmatic }
  , { walsCode := "cku", iso := "wac", value := .nMPronounsParadigmatic }
  , { walsCode := "ctm", iso := "ctm", value := .noNMPronouns }
  , { walsCode := "cho", iso := "chd", value := .nMPronounsParadigmatic }
  , { walsCode := "chk", iso := "ckt", value := .noNMPronouns }
  , { walsCode := "cin", iso := "inz", value := .noNMPronouns }
  , { walsCode := "chv", iso := "chv", value := .noNMPronouns }
  , { walsCode := "coo", iso := "csz", value := .noNMPronouns }
  , { walsCode := "cre", iso := "crk", value := .noNMPronouns }
  , { walsCode := "dag", iso := "dgz", value := .noNMPronouns }
  , { walsCode := "dni", iso := "dni", value := .noNMPronouns }
  , { walsCode := "die", iso := "dih", value := .nMPronounsParadigmatic }
  , { walsCode := "diy", iso := "dif", value := .noNMPronouns }
  , { walsCode := "diz", iso := "mdx", value := .noNMPronouns }
  , { walsCode := "djp", iso := "dwu", value := .noNMPronouns }
  , { walsCode := "dji", iso := "jig", value := .noNMPronouns }
  , { walsCode := "dum", iso := "vam", value := .nMPronounsParadigmatic }
  , { walsCode := "dyi", iso := "dbl", value := .noNMPronouns }
  , { walsCode := "eng", iso := "eng", value := .noNMPronouns }
  , { walsCode := "fij", iso := "fij", value := .noNMPronouns }
  , { walsCode := "fin", iso := "fin", value := .noNMPronouns }
  , { walsCode := "fre", iso := "fra", value := .noNMPronouns }
  , { walsCode := "fua", iso := "fub", value := .noNMPronouns }
  , { walsCode := "fur", iso := "fvr", value := .noNMPronouns }
  , { walsCode := "gbb", iso := "gbp", value := .noNMPronouns }
  , { walsCode := "geo", iso := "kat", value := .noNMPronouns }
  , { walsCode := "ger", iso := "deu", value := .noNMPronouns }
  , { walsCode := "git", iso := "git", value := .nMPronounsNonParadigmatic }
  , { walsCode := "goo", iso := "gni", value := .noNMPronouns }
  , { walsCode := "grb", iso := "grj", value := .nMPronounsNonParadigmatic }
  , { walsCode := "grk", iso := "ell", value := .noNMPronouns }
  , { walsCode := "grw", iso := "kal", value := .noNMPronouns }
  , { walsCode := "gua", iso := "gug", value := .noNMPronouns }
  , { walsCode := "gku", iso := "pue", value := .nMPronounsNonParadigmatic }
  , { walsCode := "hai", iso := "hai", value := .noNMPronouns }
  , { walsCode := "hat", iso := "had", value := .noNMPronouns }
  , { walsCode := "hau", iso := "hau", value := .noNMPronouns }
  , { walsCode := "heb", iso := "heb", value := .noNMPronouns }
  , { walsCode := "hin", iso := "hin", value := .noNMPronouns }
  , { walsCode := "hix", iso := "hix", value := .noNMPronouns }
  , { walsCode := "hmo", iso := "hnj", value := .noNMPronouns }
  , { walsCode := "hua", iso := "ygr", value := .noNMPronouns }
  , { walsCode := "hve", iso := "huv", value := .noNMPronouns }
  , { walsCode := "hun", iso := "hun", value := .noNMPronouns }
  , { walsCode := "iau", iso := "tmu", value := .noNMPronouns }
  , { walsCode := "imo", iso := "imn", value := .noNMPronouns }
  , { walsCode := "ind", iso := "ind", value := .noNMPronouns }
  , { walsCode := "ing", iso := "inh", value := .noNMPronouns }
  , { walsCode := "ite", iso := "itl", value := .noNMPronouns }
  , { walsCode := "jak", iso := "jac", value := .noNMPronouns }
  , { walsCode := "jpn", iso := "jpn", value := .noNMPronouns }
  , { walsCode := "jaq", iso := "jqr", value := .nMPronounsNonParadigmatic }
  , { walsCode := "jiv", iso := "jiv", value := .noNMPronouns }
  , { walsCode := "juh", iso := "ktz", value := .noNMPronouns }
  , { walsCode := "knd", iso := "kan", value := .noNMPronouns }
  , { walsCode := "knr", iso := "knc", value := .nMPronounsNonParadigmatic }
  , { walsCode := "krk", iso := "kyh", value := .nMPronounsParadigmatic }
  , { walsCode := "kay", iso := "gyd", value := .noNMPronouns }
  , { walsCode := "ket", iso := "ket", value := .noNMPronouns }
  , { walsCode := "kew", iso := "kew", value := .noNMPronouns }
  , { walsCode := "kha", iso := "khk", value := .noNMPronouns }
  , { walsCode := "kio", iso := "kio", value := .nMPronounsParadigmatic }
  , { walsCode := "kri", iso := "kzw", value := .noNMPronouns }
  , { walsCode := "kiw", iso := "kjd", value := .noNMPronouns }
  , { walsCode := "shp", iso := "yak", value := .nMPronounsParadigmatic }
  , { walsCode := "koa", iso := "cku", value := .noNMPronouns }
  , { walsCode := "kob", iso := "kpw", value := .noNMPronouns }
  , { walsCode := "kmb", iso := "", value := .noNMPronouns }
  , { walsCode := "kor", iso := "kor", value := .noNMPronouns }
  , { walsCode := "kot", iso := "kfe", value := .noNMPronouns }
  , { walsCode := "kse", iso := "ses", value := .noNMPronouns }
  , { walsCode := "kro", iso := "kgo", value := .noNMPronouns }
  , { walsCode := "kut", iso := "kut", value := .noNMPronouns }
  , { walsCode := "kat", iso := "kmg", value := .nMPronounsNonParadigmatic }
  , { walsCode := "lkt", iso := "lkt", value := .noNMPronouns }
  , { walsCode := "lan", iso := "laj", value := .noNMPronouns }
  , { walsCode := "lav", iso := "lvk", value := .noNMPronouns }
  , { walsCode := "lez", iso := "lez", value := .noNMPronouns }
  , { walsCode := "lda", iso := "lug", value := .noNMPronouns }
  , { walsCode := "lug", iso := "lgg", value := .noNMPronouns }
  , { walsCode := "lui", iso := "lui", value := .nMPronounsParadigmatic }
  , { walsCode := "luv", iso := "lue", value := .noNMPronouns }
  , { walsCode := "maa", iso := "mas", value := .noNMPronouns }
  , { walsCode := "mne", iso := "nmu", value := .nMPronounsParadigmatic }
  , { walsCode := "mal", iso := "plt", value := .noNMPronouns }
  , { walsCode := "mlk", iso := "mpb", value := .noNMPronouns }
  , { walsCode := "mnd", iso := "cmn", value := .noNMPronouns }
  , { walsCode := "mdk", iso := "mnk", value := .noNMPronouns }
  , { walsCode := "myi", iso := "mpc", value := .noNMPronouns }
  , { walsCode := "map", iso := "arn", value := .nMPronounsParadigmatic }
  , { walsCode := "mar", iso := "mrc", value := .noNMPronouns }
  , { walsCode := "mrt", iso := "vma", value := .noNMPronouns }
  , { walsCode := "mau", iso := "mph", value := .noNMPronouns }
  , { walsCode := "may", iso := "ayz", value := .noNMPronouns }
  , { walsCode := "mei", iso := "mni", value := .noNMPronouns }
  , { walsCode := "mis", iso := "miq", value := .nMPronounsParadigmatic }
  , { walsCode := "mss", iso := "skd", value := .nMPronounsNonParadigmatic }
  , { walsCode := "mco", iso := "mco", value := .nMPronounsParadigmatic }
  , { walsCode := "mxc", iso := "mig", value := .noNMPronouns }
  , { walsCode := "mot", iso := "siw", value := .noNMPronouns }
  , { walsCode := "mun", iso := "unr", value := .noNMPronouns }
  , { walsCode := "nah", iso := "nll", value := .noNMPronouns }
  , { walsCode := "kho", iso := "naq", value := .noNMPronouns }
  , { walsCode := "nmb", iso := "nab", value := .noNMPronouns }
  , { walsCode := "nai", iso := "gld", value := .noNMPronouns }
  , { walsCode := "nar", iso := "nrb", value := .noNMPronouns }
  , { walsCode := "nat", iso := "ncz", value := .noNMPronouns }
  , { walsCode := "ntu", iso := "yrk", value := .noNMPronouns }
  , { walsCode := "ntj", iso := "ntj", value := .noNMPronouns }
  , { walsCode := "ngl", iso := "nig", value := .noNMPronouns }
  , { walsCode := "ngi", iso := "wyb", value := .noNMPronouns }
  , { walsCode := "nbr", iso := "gym", value := .noNMPronouns }
  , { walsCode := "nca", iso := "caq", value := .noNMPronouns }
  , { walsCode := "niv", iso := "niv", value := .noNMPronouns }
  , { walsCode := "nug", iso := "nuy", value := .noNMPronouns }
  , { walsCode := "nuu", iso := "nuk", value := .noNMPronouns }
  , { walsCode := "ood", iso := "ood", value := .nMPronounsParadigmatic }
  , { walsCode := "ond", iso := "one", value := .noNMPronouns }
  , { walsCode := "ori", iso := "tag", value := .noNMPronouns }
  , { walsCode := "orh", iso := "hae", value := .noNMPronouns }
  , { walsCode := "oss", iso := "oss", value := .noNMPronouns }
  , { walsCode := "otm", iso := "ote", value := .noNMPronouns }
  , { walsCode := "pai", iso := "pwn", value := .noNMPronouns }
  , { walsCode := "pau", iso := "pad", value := .noNMPronouns }
  , { walsCode := "prs", iso := "pes", value := .noNMPronouns }
  , { walsCode := "pip", iso := "ppl", value := .nMPronounsParadigmatic }
  , { walsCode := "prh", iso := "myp", value := .noNMPronouns }
  , { walsCode := "pme", iso := "peb", value := .noNMPronouns }
  , { walsCode := "pur", iso := "tsz", value := .noNMPronouns }
  , { walsCode := "qim", iso := "qvi", value := .noNMPronouns }
  , { walsCode := "qui", iso := "qui", value := .noNMPronouns }
  , { walsCode := "ram", iso := "rma", value := .nMPronounsParadigmatic }
  , { walsCode := "rap", iso := "rap", value := .noNMPronouns }
  , { walsCode := "rus", iso := "rus", value := .noNMPronouns }
  , { walsCode := "sah", iso := "saj", value := .noNMPronouns }
  , { walsCode := "sal", iso := "sln", value := .noNMPronouns }
  , { walsCode := "syu", iso := "sll", value := .noNMPronouns }
  , { walsCode := "san", iso := "sag", value := .noNMPronouns }
  , { walsCode := "snm", iso := "xsu", value := .noNMPronouns }
  , { walsCode := "snc", iso := "see", value := .noNMPronouns }
  , { walsCode := "snt", iso := "set", value := .noNMPronouns }
  , { walsCode := "shs", iso := "sht", value := .noNMPronouns }
  , { walsCode := "sla", iso := "den", value := .noNMPronouns }
  , { walsCode := "spa", iso := "spa", value := .noNMPronouns }
  , { walsCode := "squ", iso := "squ", value := .noNMPronouns }
  , { walsCode := "sul", iso := "sua", value := .noNMPronouns }
  , { walsCode := "sup", iso := "spp", value := .nMPronounsParadigmatic }
  , { walsCode := "swa", iso := "swh", value := .noNMPronouns }
  , { walsCode := "tag", iso := "tgl", value := .noNMPronouns }
  , { walsCode := "tkl", iso := "tkm", value := .noNMPronouns }
  , { walsCode := "tau", iso := "tya", value := .noNMPronouns }
  , { walsCode := "tlf", iso := "tlf", value := .noNMPronouns }
  , { walsCode := "tmr", iso := "tea", value := .noNMPronouns }
  , { walsCode := "tib", iso := "bod", value := .noNMPronouns }
  , { walsCode := "tmc", iso := "tjm", value := .noNMPronouns }
  , { walsCode := "tiw", iso := "tiw", value := .noNMPronouns }
  , { walsCode := "tli", iso := "tli", value := .noNMPronouns }
  , { walsCode := "ton", iso := "tqw", value := .noNMPronouns }
  , { walsCode := "tpa", iso := "top", value := .noNMPronouns }
  , { walsCode := "tru", iso := "tpy", value := .noNMPronouns }
  , { walsCode := "tuk", iso := "", value := .noNMPronouns }
  , { walsCode := "tun", iso := "tun", value := .nMPronounsNonParadigmatic }
  , { walsCode := "tur", iso := "tur", value := .noNMPronouns }
  , { walsCode := "tuv", iso := "tyv", value := .noNMPronouns }
  , { walsCode := "tzu", iso := "tzj", value := .noNMPronouns }
  , { walsCode := "ung", iso := "ung", value := .noNMPronouns }
  , { walsCode := "uhi", iso := "urf", value := .noNMPronouns }
  , { walsCode := "usa", iso := "wnu", value := .noNMPronouns }
  , { walsCode := "vie", iso := "vie", value := .noNMPronouns }
  , { walsCode := "wgl", iso := "wbk", value := .noNMPronouns }
  , { walsCode := "wao", iso := "auc", value := .noNMPronouns }
  , { walsCode := "wap", iso := "wao", value := .noNMPronouns }
  , { walsCode := "wra", iso := "wba", value := .noNMPronouns }
  , { walsCode := "wrd", iso := "wrr", value := .noNMPronouns }
  , { walsCode := "war", iso := "pav", value := .nMPronounsParadigmatic }
  , { walsCode := "wrn", iso := "wnd", value := .noNMPronouns }
  , { walsCode := "was", iso := "was", value := .noNMPronouns }
  , { walsCode := "wsk", iso := "wsk", value := .noNMPronouns }
  , { walsCode := "wem", iso := "xww", value := .noNMPronouns }
  , { walsCode := "wic", iso := "wic", value := .noNMPronouns }
  , { walsCode := "wch", iso := "mzh", value := .nMPronounsParadigmatic }
  , { walsCode := "win", iso := "wnw", value := .nMPronounsParadigmatic }
  , { walsCode := "wiy", iso := "wiy", value := .noNMPronouns }
  , { walsCode := "xok", iso := "xok", value := .nMPronounsParadigmatic }
  , { walsCode := "yag", iso := "yad", value := .noNMPronouns }
  , { walsCode := "yaq", iso := "yaq", value := .nMPronounsParadigmatic }
  , { walsCode := "ywl", iso := "yok", value := .nMPronounsParadigmatic }
  , { walsCode := "yim", iso := "yee", value := .noNMPronouns }
  , { walsCode := "yor", iso := "yor", value := .noNMPronouns }
  , { walsCode := "yuc", iso := "yuc", value := .noNMPronouns }
  , { walsCode := "yko", iso := "yux", value := .noNMPronouns }
  , { walsCode := "yuk", iso := "gcd", value := .noNMPronouns }
  , { walsCode := "yna", iso := "ynk", value := .noNMPronouns }
  , { walsCode := "yur", iso := "yur", value := .nMPronounsNonParadigmatic }
  , { walsCode := "zqc", iso := "zoc", value := .noNMPronouns }
  , { walsCode := "zul", iso := "zul", value := .noNMPronouns }
  , { walsCode := "zun", iso := "zun", value := .noNMPronouns }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F137A
