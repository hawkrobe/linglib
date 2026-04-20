import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 136B: M in First Person Singular
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 136B`.

Chapter 136, 230 languages.
-/

namespace Core.WALS.F136B

/-- WALS 136B values. -/
inductive MInFirstPersonSingular where
  /-- No m in first person singular (177 languages). -/
  | noMInFirstPersonSingular
  /-- m in first person singular (53 languages). -/
  | mInFirstPersonSingular
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 136B dataset (230 languages). -/
def allData : List (Datapoint MInFirstPersonSingular) :=
  [ { walsCode := "abk", iso := "abk", value := .noMInFirstPersonSingular }
  , { walsCode := "ace", iso := "ace", value := .noMInFirstPersonSingular }
  , { walsCode := "aco", iso := "kjq", value := .noMInFirstPersonSingular }
  , { walsCode := "ain", iso := "ain", value := .noMInFirstPersonSingular }
  , { walsCode := "ala", iso := "amp", value := .noMInFirstPersonSingular }
  , { walsCode := "ame", iso := "aey", value := .noMInFirstPersonSingular }
  , { walsCode := "amh", iso := "amh", value := .noMInFirstPersonSingular }
  , { walsCode := "ane", iso := "anz", value := .noMInFirstPersonSingular }
  , { walsCode := "apu", iso := "apu", value := .noMInFirstPersonSingular }
  , { walsCode := "aeg", iso := "arz", value := .noMInFirstPersonSingular }
  , { walsCode := "arp", iso := "ape", value := .noMInFirstPersonSingular }
  , { walsCode := "amp", iso := "aer", value := .noMInFirstPersonSingular }
  , { walsCode := "asm", iso := "cns", value := .noMInFirstPersonSingular }
  , { walsCode := "atk", iso := "aqp", value := .noMInFirstPersonSingular }
  , { walsCode := "awp", iso := "kwi", value := .noMInFirstPersonSingular }
  , { walsCode := "awt", iso := "kmn", value := .noMInFirstPersonSingular }
  , { walsCode := "ayw", iso := "nfl", value := .noMInFirstPersonSingular }
  , { walsCode := "bag", iso := "bmi", value := .mInFirstPersonSingular }
  , { walsCode := "brs", iso := "bsn", value := .noMInFirstPersonSingular }
  , { walsCode := "bsq", iso := "eus", value := .noMInFirstPersonSingular }
  , { walsCode := "bej", iso := "bej", value := .noMInFirstPersonSingular }
  , { walsCode := "bel", iso := "byw", value := .noMInFirstPersonSingular }
  , { walsCode := "bma", iso := "tzm", value := .noMInFirstPersonSingular }
  , { walsCode := "brk", iso := "bkl", value := .noMInFirstPersonSingular }
  , { walsCode := "brr", iso := "bor", value := .mInFirstPersonSingular }
  , { walsCode := "brm", iso := "mya", value := .noMInFirstPersonSingular }
  , { walsCode := "bur", iso := "bsk", value := .noMInFirstPersonSingular }
  , { walsCode := "cax", iso := "", value := .noMInFirstPersonSingular }
  , { walsCode := "cnl", iso := "ram", value := .mInFirstPersonSingular }
  , { walsCode := "csh", iso := "cbs", value := .noMInFirstPersonSingular }
  , { walsCode := "cyv", iso := "cyb", value := .noMInFirstPersonSingular }
  , { walsCode := "cha", iso := "cha", value := .noMInFirstPersonSingular }
  , { walsCode := "cjo", iso := "pei", value := .noMInFirstPersonSingular }
  , { walsCode := "chi", iso := "cid", value := .noMInFirstPersonSingular }
  , { walsCode := "cku", iso := "wac", value := .noMInFirstPersonSingular }
  , { walsCode := "ctm", iso := "ctm", value := .noMInFirstPersonSingular }
  , { walsCode := "cho", iso := "chd", value := .noMInFirstPersonSingular }
  , { walsCode := "chk", iso := "ckt", value := .mInFirstPersonSingular }
  , { walsCode := "cin", iso := "inz", value := .noMInFirstPersonSingular }
  , { walsCode := "chv", iso := "chv", value := .mInFirstPersonSingular }
  , { walsCode := "coo", iso := "csz", value := .noMInFirstPersonSingular }
  , { walsCode := "cre", iso := "crk", value := .noMInFirstPersonSingular }
  , { walsCode := "dag", iso := "dgz", value := .noMInFirstPersonSingular }
  , { walsCode := "dni", iso := "dni", value := .noMInFirstPersonSingular }
  , { walsCode := "diy", iso := "dif", value := .noMInFirstPersonSingular }
  , { walsCode := "diz", iso := "mdx", value := .noMInFirstPersonSingular }
  , { walsCode := "djp", iso := "dwu", value := .noMInFirstPersonSingular }
  , { walsCode := "dji", iso := "jig", value := .noMInFirstPersonSingular }
  , { walsCode := "dum", iso := "vam", value := .noMInFirstPersonSingular }
  , { walsCode := "dyi", iso := "dbl", value := .noMInFirstPersonSingular }
  , { walsCode := "eng", iso := "eng", value := .mInFirstPersonSingular }
  , { walsCode := "fij", iso := "fij", value := .noMInFirstPersonSingular }
  , { walsCode := "fin", iso := "fin", value := .mInFirstPersonSingular }
  , { walsCode := "fre", iso := "fra", value := .mInFirstPersonSingular }
  , { walsCode := "fua", iso := "fub", value := .mInFirstPersonSingular }
  , { walsCode := "fur", iso := "fvr", value := .noMInFirstPersonSingular }
  , { walsCode := "gbb", iso := "gbp", value := .mInFirstPersonSingular }
  , { walsCode := "geo", iso := "kat", value := .mInFirstPersonSingular }
  , { walsCode := "ger", iso := "deu", value := .mInFirstPersonSingular }
  , { walsCode := "git", iso := "git", value := .noMInFirstPersonSingular }
  , { walsCode := "goo", iso := "gni", value := .noMInFirstPersonSingular }
  , { walsCode := "grb", iso := "grj", value := .mInFirstPersonSingular }
  , { walsCode := "grk", iso := "ell", value := .mInFirstPersonSingular }
  , { walsCode := "grw", iso := "kal", value := .mInFirstPersonSingular }
  , { walsCode := "gua", iso := "gug", value := .noMInFirstPersonSingular }
  , { walsCode := "gku", iso := "pue", value := .noMInFirstPersonSingular }
  , { walsCode := "hai", iso := "hai", value := .noMInFirstPersonSingular }
  , { walsCode := "hat", iso := "had", value := .noMInFirstPersonSingular }
  , { walsCode := "hau", iso := "hau", value := .noMInFirstPersonSingular }
  , { walsCode := "heb", iso := "heb", value := .noMInFirstPersonSingular }
  , { walsCode := "hin", iso := "hin", value := .mInFirstPersonSingular }
  , { walsCode := "hix", iso := "hix", value := .noMInFirstPersonSingular }
  , { walsCode := "hmo", iso := "hnj", value := .noMInFirstPersonSingular }
  , { walsCode := "hua", iso := "ygr", value := .noMInFirstPersonSingular }
  , { walsCode := "hve", iso := "huv", value := .noMInFirstPersonSingular }
  , { walsCode := "hun", iso := "hun", value := .mInFirstPersonSingular }
  , { walsCode := "iau", iso := "tmu", value := .mInFirstPersonSingular }
  , { walsCode := "imo", iso := "imn", value := .noMInFirstPersonSingular }
  , { walsCode := "ind", iso := "ind", value := .noMInFirstPersonSingular }
  , { walsCode := "ing", iso := "inh", value := .noMInFirstPersonSingular }
  , { walsCode := "ite", iso := "itl", value := .mInFirstPersonSingular }
  , { walsCode := "jak", iso := "jac", value := .noMInFirstPersonSingular }
  , { walsCode := "jpn", iso := "jpn", value := .noMInFirstPersonSingular }
  , { walsCode := "jaq", iso := "jqr", value := .noMInFirstPersonSingular }
  , { walsCode := "jiv", iso := "jiv", value := .noMInFirstPersonSingular }
  , { walsCode := "juh", iso := "ktz", value := .mInFirstPersonSingular }
  , { walsCode := "knd", iso := "kan", value := .noMInFirstPersonSingular }
  , { walsCode := "knr", iso := "knc", value := .noMInFirstPersonSingular }
  , { walsCode := "krk", iso := "kyh", value := .noMInFirstPersonSingular }
  , { walsCode := "kay", iso := "gyd", value := .noMInFirstPersonSingular }
  , { walsCode := "ket", iso := "ket", value := .mInFirstPersonSingular }
  , { walsCode := "kew", iso := "kew", value := .noMInFirstPersonSingular }
  , { walsCode := "kha", iso := "khk", value := .mInFirstPersonSingular }
  , { walsCode := "kio", iso := "kio", value := .noMInFirstPersonSingular }
  , { walsCode := "kri", iso := "kzw", value := .noMInFirstPersonSingular }
  , { walsCode := "kiw", iso := "kjd", value := .mInFirstPersonSingular }
  , { walsCode := "koa", iso := "cku", value := .noMInFirstPersonSingular }
  , { walsCode := "kob", iso := "kpw", value := .noMInFirstPersonSingular }
  , { walsCode := "kmb", iso := "", value := .mInFirstPersonSingular }
  , { walsCode := "kor", iso := "kor", value := .noMInFirstPersonSingular }
  , { walsCode := "kot", iso := "kfe", value := .noMInFirstPersonSingular }
  , { walsCode := "kse", iso := "ses", value := .noMInFirstPersonSingular }
  , { walsCode := "kro", iso := "kgo", value := .noMInFirstPersonSingular }
  , { walsCode := "kut", iso := "kut", value := .noMInFirstPersonSingular }
  , { walsCode := "kyq", iso := "nuk", value := .noMInFirstPersonSingular }
  , { walsCode := "kat", iso := "kmg", value := .mInFirstPersonSingular }
  , { walsCode := "lkt", iso := "lkt", value := .mInFirstPersonSingular }
  , { walsCode := "lan", iso := "laj", value := .noMInFirstPersonSingular }
  , { walsCode := "lav", iso := "lvk", value := .noMInFirstPersonSingular }
  , { walsCode := "lez", iso := "lez", value := .noMInFirstPersonSingular }
  , { walsCode := "lda", iso := "lug", value := .noMInFirstPersonSingular }
  , { walsCode := "lug", iso := "lgg", value := .mInFirstPersonSingular }
  , { walsCode := "lui", iso := "lui", value := .noMInFirstPersonSingular }
  , { walsCode := "luv", iso := "lue", value := .mInFirstPersonSingular }
  , { walsCode := "maa", iso := "mas", value := .noMInFirstPersonSingular }
  , { walsCode := "mne", iso := "nmu", value := .noMInFirstPersonSingular }
  , { walsCode := "mal", iso := "plt", value := .noMInFirstPersonSingular }
  , { walsCode := "mlk", iso := "mpb", value := .noMInFirstPersonSingular }
  , { walsCode := "mnd", iso := "cmn", value := .noMInFirstPersonSingular }
  , { walsCode := "mdk", iso := "mnk", value := .noMInFirstPersonSingular }
  , { walsCode := "myi", iso := "mpc", value := .noMInFirstPersonSingular }
  , { walsCode := "map", iso := "arn", value := .noMInFirstPersonSingular }
  , { walsCode := "mar", iso := "mrc", value := .noMInFirstPersonSingular }
  , { walsCode := "mrt", iso := "vma", value := .noMInFirstPersonSingular }
  , { walsCode := "mau", iso := "mph", value := .noMInFirstPersonSingular }
  , { walsCode := "may", iso := "ayz", value := .noMInFirstPersonSingular }
  , { walsCode := "mei", iso := "mni", value := .noMInFirstPersonSingular }
  , { walsCode := "mis", iso := "miq", value := .noMInFirstPersonSingular }
  , { walsCode := "mss", iso := "skd", value := .mInFirstPersonSingular }
  , { walsCode := "mtp", iso := "mto", value := .noMInFirstPersonSingular }
  , { walsCode := "mxc", iso := "mig", value := .noMInFirstPersonSingular }
  , { walsCode := "mot", iso := "siw", value := .mInFirstPersonSingular }
  , { walsCode := "mun", iso := "unr", value := .noMInFirstPersonSingular }
  , { walsCode := "nah", iso := "nll", value := .noMInFirstPersonSingular }
  , { walsCode := "kho", iso := "naq", value := .noMInFirstPersonSingular }
  , { walsCode := "nmb", iso := "nab", value := .noMInFirstPersonSingular }
  , { walsCode := "nai", iso := "gld", value := .mInFirstPersonSingular }
  , { walsCode := "nar", iso := "nrb", value := .noMInFirstPersonSingular }
  , { walsCode := "nat", iso := "ncz", value := .noMInFirstPersonSingular }
  , { walsCode := "ntu", iso := "yrk", value := .mInFirstPersonSingular }
  , { walsCode := "ngl", iso := "nig", value := .noMInFirstPersonSingular }
  , { walsCode := "ngi", iso := "wyb", value := .noMInFirstPersonSingular }
  , { walsCode := "nbr", iso := "gym", value := .noMInFirstPersonSingular }
  , { walsCode := "nca", iso := "caq", value := .noMInFirstPersonSingular }
  , { walsCode := "niv", iso := "niv", value := .noMInFirstPersonSingular }
  , { walsCode := "nug", iso := "nuy", value := .noMInFirstPersonSingular }
  , { walsCode := "ood", iso := "ood", value := .noMInFirstPersonSingular }
  , { walsCode := "ond", iso := "one", value := .noMInFirstPersonSingular }
  , { walsCode := "ori", iso := "tag", value := .noMInFirstPersonSingular }
  , { walsCode := "orh", iso := "hae", value := .noMInFirstPersonSingular }
  , { walsCode := "oss", iso := "oss", value := .mInFirstPersonSingular }
  , { walsCode := "otm", iso := "ote", value := .mInFirstPersonSingular }
  , { walsCode := "pai", iso := "pwn", value := .noMInFirstPersonSingular }
  , { walsCode := "pau", iso := "pad", value := .noMInFirstPersonSingular }
  , { walsCode := "prs", iso := "pes", value := .mInFirstPersonSingular }
  , { walsCode := "pip", iso := "ppl", value := .noMInFirstPersonSingular }
  , { walsCode := "prh", iso := "myp", value := .noMInFirstPersonSingular }
  , { walsCode := "pit", iso := "pjt", value := .noMInFirstPersonSingular }
  , { walsCode := "pme", iso := "peb", value := .noMInFirstPersonSingular }
  , { walsCode := "pur", iso := "tsz", value := .noMInFirstPersonSingular }
  , { walsCode := "qim", iso := "qvi", value := .noMInFirstPersonSingular }
  , { walsCode := "qui", iso := "qui", value := .noMInFirstPersonSingular }
  , { walsCode := "ram", iso := "rma", value := .noMInFirstPersonSingular }
  , { walsCode := "rap", iso := "rap", value := .noMInFirstPersonSingular }
  , { walsCode := "rus", iso := "rus", value := .mInFirstPersonSingular }
  , { walsCode := "smt", iso := "uma", value := .noMInFirstPersonSingular }
  , { walsCode := "sah", iso := "saj", value := .noMInFirstPersonSingular }
  , { walsCode := "sal", iso := "sln", value := .noMInFirstPersonSingular }
  , { walsCode := "syu", iso := "sll", value := .mInFirstPersonSingular }
  , { walsCode := "san", iso := "sag", value := .mInFirstPersonSingular }
  , { walsCode := "snm", iso := "xsu", value := .mInFirstPersonSingular }
  , { walsCode := "snc", iso := "see", value := .noMInFirstPersonSingular }
  , { walsCode := "snt", iso := "set", value := .noMInFirstPersonSingular }
  , { walsCode := "shs", iso := "sht", value := .noMInFirstPersonSingular }
  , { walsCode := "sla", iso := "den", value := .noMInFirstPersonSingular }
  , { walsCode := "spa", iso := "spa", value := .mInFirstPersonSingular }
  , { walsCode := "squ", iso := "squ", value := .noMInFirstPersonSingular }
  , { walsCode := "sul", iso := "sua", value := .noMInFirstPersonSingular }
  , { walsCode := "sup", iso := "spp", value := .mInFirstPersonSingular }
  , { walsCode := "swa", iso := "swh", value := .mInFirstPersonSingular }
  , { walsCode := "tag", iso := "tgl", value := .noMInFirstPersonSingular }
  , { walsCode := "tkl", iso := "tkm", value := .noMInFirstPersonSingular }
  , { walsCode := "tau", iso := "tya", value := .noMInFirstPersonSingular }
  , { walsCode := "tlf", iso := "tlf", value := .noMInFirstPersonSingular }
  , { walsCode := "tmr", iso := "tea", value := .noMInFirstPersonSingular }
  , { walsCode := "tib", iso := "bod", value := .noMInFirstPersonSingular }
  , { walsCode := "tja", iso := "dih", value := .noMInFirstPersonSingular }
  , { walsCode := "tmc", iso := "tjm", value := .noMInFirstPersonSingular }
  , { walsCode := "tiw", iso := "tiw", value := .noMInFirstPersonSingular }
  , { walsCode := "tli", iso := "tli", value := .noMInFirstPersonSingular }
  , { walsCode := "ton", iso := "tqw", value := .noMInFirstPersonSingular }
  , { walsCode := "tpa", iso := "top", value := .noMInFirstPersonSingular }
  , { walsCode := "tru", iso := "tpy", value := .noMInFirstPersonSingular }
  , { walsCode := "tuk", iso := "", value := .noMInFirstPersonSingular }
  , { walsCode := "tun", iso := "tun", value := .noMInFirstPersonSingular }
  , { walsCode := "tur", iso := "tur", value := .mInFirstPersonSingular }
  , { walsCode := "tuv", iso := "tyv", value := .mInFirstPersonSingular }
  , { walsCode := "tzu", iso := "tzj", value := .noMInFirstPersonSingular }
  , { walsCode := "ung", iso := "ung", value := .noMInFirstPersonSingular }
  , { walsCode := "uhi", iso := "urf", value := .noMInFirstPersonSingular }
  , { walsCode := "usa", iso := "wnu", value := .mInFirstPersonSingular }
  , { walsCode := "vie", iso := "vie", value := .noMInFirstPersonSingular }
  , { walsCode := "wgl", iso := "wbk", value := .mInFirstPersonSingular }
  , { walsCode := "wao", iso := "auc", value := .mInFirstPersonSingular }
  , { walsCode := "wap", iso := "wao", value := .noMInFirstPersonSingular }
  , { walsCode := "wra", iso := "wba", value := .mInFirstPersonSingular }
  , { walsCode := "wrd", iso := "wrr", value := .noMInFirstPersonSingular }
  , { walsCode := "war", iso := "pav", value := .noMInFirstPersonSingular }
  , { walsCode := "wrn", iso := "wnd", value := .noMInFirstPersonSingular }
  , { walsCode := "was", iso := "was", value := .noMInFirstPersonSingular }
  , { walsCode := "wsk", iso := "wsk", value := .mInFirstPersonSingular }
  , { walsCode := "wem", iso := "xww", value := .noMInFirstPersonSingular }
  , { walsCode := "wic", iso := "wic", value := .noMInFirstPersonSingular }
  , { walsCode := "wch", iso := "mzh", value := .noMInFirstPersonSingular }
  , { walsCode := "win", iso := "wnw", value := .noMInFirstPersonSingular }
  , { walsCode := "wiy", iso := "wiy", value := .noMInFirstPersonSingular }
  , { walsCode := "xok", iso := "xok", value := .noMInFirstPersonSingular }
  , { walsCode := "yag", iso := "yad", value := .noMInFirstPersonSingular }
  , { walsCode := "yaq", iso := "yaq", value := .noMInFirstPersonSingular }
  , { walsCode := "ywl", iso := "yok", value := .noMInFirstPersonSingular }
  , { walsCode := "yim", iso := "yee", value := .mInFirstPersonSingular }
  , { walsCode := "yor", iso := "yor", value := .mInFirstPersonSingular }
  , { walsCode := "yuc", iso := "yuc", value := .noMInFirstPersonSingular }
  , { walsCode := "yko", iso := "yux", value := .mInFirstPersonSingular }
  , { walsCode := "yuk", iso := "gcd", value := .noMInFirstPersonSingular }
  , { walsCode := "yna", iso := "ynk", value := .noMInFirstPersonSingular }
  , { walsCode := "yur", iso := "yur", value := .noMInFirstPersonSingular }
  , { walsCode := "zqc", iso := "zoc", value := .noMInFirstPersonSingular }
  , { walsCode := "zul", iso := "zul", value := .mInFirstPersonSingular }
  , { walsCode := "zun", iso := "zun", value := .noMInFirstPersonSingular }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F136B
