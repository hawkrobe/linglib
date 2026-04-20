import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 137B: M in Second Person Singular
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 137B`.

Chapter 137, 230 languages.
-/

namespace Core.WALS.F137B

/-- WALS 137B values. -/
inductive MInSecondPersonSingular where
  /-- No m in second person singular (152 languages). -/
  | noMInSecondPersonSingular
  /-- m in second person singular (78 languages). -/
  | mInSecondPersonSingular
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 137B dataset (230 languages). -/
def allData : List (Datapoint MInSecondPersonSingular) :=
  [ { walsCode := "abk", iso := "abk", value := .mInSecondPersonSingular }
  , { walsCode := "ace", iso := "ace", value := .noMInSecondPersonSingular }
  , { walsCode := "aco", iso := "kjq", value := .noMInSecondPersonSingular }
  , { walsCode := "ain", iso := "ain", value := .noMInSecondPersonSingular }
  , { walsCode := "ala", iso := "amp", value := .noMInSecondPersonSingular }
  , { walsCode := "ame", iso := "aey", value := .noMInSecondPersonSingular }
  , { walsCode := "amh", iso := "amh", value := .noMInSecondPersonSingular }
  , { walsCode := "ane", iso := "anz", value := .noMInSecondPersonSingular }
  , { walsCode := "apu", iso := "apu", value := .mInSecondPersonSingular }
  , { walsCode := "aeg", iso := "arz", value := .noMInSecondPersonSingular }
  , { walsCode := "arp", iso := "ape", value := .noMInSecondPersonSingular }
  , { walsCode := "amp", iso := "aer", value := .noMInSecondPersonSingular }
  , { walsCode := "asm", iso := "cns", value := .mInSecondPersonSingular }
  , { walsCode := "atk", iso := "aqp", value := .noMInSecondPersonSingular }
  , { walsCode := "awp", iso := "kwi", value := .noMInSecondPersonSingular }
  , { walsCode := "awt", iso := "kmn", value := .noMInSecondPersonSingular }
  , { walsCode := "ayw", iso := "nfl", value := .mInSecondPersonSingular }
  , { walsCode := "bag", iso := "bmi", value := .noMInSecondPersonSingular }
  , { walsCode := "brs", iso := "bsn", value := .mInSecondPersonSingular }
  , { walsCode := "bsq", iso := "eus", value := .noMInSecondPersonSingular }
  , { walsCode := "bej", iso := "bej", value := .noMInSecondPersonSingular }
  , { walsCode := "bel", iso := "byw", value := .noMInSecondPersonSingular }
  , { walsCode := "bma", iso := "tzm", value := .mInSecondPersonSingular }
  , { walsCode := "brk", iso := "bkl", value := .mInSecondPersonSingular }
  , { walsCode := "brr", iso := "bor", value := .noMInSecondPersonSingular }
  , { walsCode := "brm", iso := "mya", value := .noMInSecondPersonSingular }
  , { walsCode := "bur", iso := "bsk", value := .mInSecondPersonSingular }
  , { walsCode := "cax", iso := "", value := .mInSecondPersonSingular }
  , { walsCode := "cnl", iso := "ram", value := .noMInSecondPersonSingular }
  , { walsCode := "csh", iso := "cbs", value := .mInSecondPersonSingular }
  , { walsCode := "cyv", iso := "cyb", value := .noMInSecondPersonSingular }
  , { walsCode := "cha", iso := "cha", value := .mInSecondPersonSingular }
  , { walsCode := "cjo", iso := "pei", value := .noMInSecondPersonSingular }
  , { walsCode := "chi", iso := "cid", value := .mInSecondPersonSingular }
  , { walsCode := "cku", iso := "wac", value := .mInSecondPersonSingular }
  , { walsCode := "ctm", iso := "ctm", value := .noMInSecondPersonSingular }
  , { walsCode := "cho", iso := "chd", value := .mInSecondPersonSingular }
  , { walsCode := "chk", iso := "ckt", value := .noMInSecondPersonSingular }
  , { walsCode := "cin", iso := "inz", value := .mInSecondPersonSingular }
  , { walsCode := "chv", iso := "chv", value := .noMInSecondPersonSingular }
  , { walsCode := "coo", iso := "csz", value := .noMInSecondPersonSingular }
  , { walsCode := "cre", iso := "crk", value := .noMInSecondPersonSingular }
  , { walsCode := "dag", iso := "dgz", value := .noMInSecondPersonSingular }
  , { walsCode := "dni", iso := "dni", value := .noMInSecondPersonSingular }
  , { walsCode := "diy", iso := "dif", value := .noMInSecondPersonSingular }
  , { walsCode := "diz", iso := "mdx", value := .noMInSecondPersonSingular }
  , { walsCode := "djp", iso := "dwu", value := .noMInSecondPersonSingular }
  , { walsCode := "dji", iso := "jig", value := .noMInSecondPersonSingular }
  , { walsCode := "dum", iso := "vam", value := .mInSecondPersonSingular }
  , { walsCode := "dyi", iso := "dbl", value := .noMInSecondPersonSingular }
  , { walsCode := "eng", iso := "eng", value := .noMInSecondPersonSingular }
  , { walsCode := "fij", iso := "fij", value := .mInSecondPersonSingular }
  , { walsCode := "fin", iso := "fin", value := .noMInSecondPersonSingular }
  , { walsCode := "fre", iso := "fra", value := .noMInSecondPersonSingular }
  , { walsCode := "fua", iso := "fub", value := .mInSecondPersonSingular }
  , { walsCode := "fur", iso := "fvr", value := .noMInSecondPersonSingular }
  , { walsCode := "gbb", iso := "gbp", value := .mInSecondPersonSingular }
  , { walsCode := "geo", iso := "kat", value := .noMInSecondPersonSingular }
  , { walsCode := "ger", iso := "deu", value := .noMInSecondPersonSingular }
  , { walsCode := "git", iso := "git", value := .mInSecondPersonSingular }
  , { walsCode := "goo", iso := "gni", value := .noMInSecondPersonSingular }
  , { walsCode := "grb", iso := "grj", value := .mInSecondPersonSingular }
  , { walsCode := "grk", iso := "ell", value := .noMInSecondPersonSingular }
  , { walsCode := "grw", iso := "kal", value := .mInSecondPersonSingular }
  , { walsCode := "gua", iso := "gug", value := .noMInSecondPersonSingular }
  , { walsCode := "gku", iso := "pue", value := .mInSecondPersonSingular }
  , { walsCode := "hai", iso := "hai", value := .noMInSecondPersonSingular }
  , { walsCode := "hat", iso := "had", value := .noMInSecondPersonSingular }
  , { walsCode := "hau", iso := "hau", value := .noMInSecondPersonSingular }
  , { walsCode := "heb", iso := "heb", value := .noMInSecondPersonSingular }
  , { walsCode := "hin", iso := "hin", value := .noMInSecondPersonSingular }
  , { walsCode := "hix", iso := "hix", value := .mInSecondPersonSingular }
  , { walsCode := "hmo", iso := "hnj", value := .noMInSecondPersonSingular }
  , { walsCode := "hua", iso := "ygr", value := .noMInSecondPersonSingular }
  , { walsCode := "hve", iso := "huv", value := .mInSecondPersonSingular }
  , { walsCode := "hun", iso := "hun", value := .noMInSecondPersonSingular }
  , { walsCode := "iau", iso := "tmu", value := .noMInSecondPersonSingular }
  , { walsCode := "imo", iso := "imn", value := .noMInSecondPersonSingular }
  , { walsCode := "ind", iso := "ind", value := .mInSecondPersonSingular }
  , { walsCode := "ing", iso := "inh", value := .noMInSecondPersonSingular }
  , { walsCode := "ite", iso := "itl", value := .noMInSecondPersonSingular }
  , { walsCode := "jak", iso := "jac", value := .noMInSecondPersonSingular }
  , { walsCode := "jpn", iso := "jpn", value := .mInSecondPersonSingular }
  , { walsCode := "jaq", iso := "jqr", value := .mInSecondPersonSingular }
  , { walsCode := "jiv", iso := "jiv", value := .mInSecondPersonSingular }
  , { walsCode := "juh", iso := "ktz", value := .noMInSecondPersonSingular }
  , { walsCode := "knd", iso := "kan", value := .mInSecondPersonSingular }
  , { walsCode := "knr", iso := "knc", value := .mInSecondPersonSingular }
  , { walsCode := "krk", iso := "kyh", value := .mInSecondPersonSingular }
  , { walsCode := "kay", iso := "gyd", value := .noMInSecondPersonSingular }
  , { walsCode := "ket", iso := "ket", value := .noMInSecondPersonSingular }
  , { walsCode := "kew", iso := "kew", value := .noMInSecondPersonSingular }
  , { walsCode := "kha", iso := "khk", value := .noMInSecondPersonSingular }
  , { walsCode := "kio", iso := "kio", value := .mInSecondPersonSingular }
  , { walsCode := "kri", iso := "kzw", value := .noMInSecondPersonSingular }
  , { walsCode := "kiw", iso := "kjd", value := .noMInSecondPersonSingular }
  , { walsCode := "koa", iso := "cku", value := .noMInSecondPersonSingular }
  , { walsCode := "kob", iso := "kpw", value := .noMInSecondPersonSingular }
  , { walsCode := "kmb", iso := "", value := .noMInSecondPersonSingular }
  , { walsCode := "kor", iso := "kor", value := .noMInSecondPersonSingular }
  , { walsCode := "kot", iso := "kfe", value := .noMInSecondPersonSingular }
  , { walsCode := "kse", iso := "ses", value := .noMInSecondPersonSingular }
  , { walsCode := "kro", iso := "kgo", value := .noMInSecondPersonSingular }
  , { walsCode := "kut", iso := "kut", value := .noMInSecondPersonSingular }
  , { walsCode := "kyq", iso := "nuk", value := .noMInSecondPersonSingular }
  , { walsCode := "kat", iso := "kmg", value := .mInSecondPersonSingular }
  , { walsCode := "lkt", iso := "lkt", value := .noMInSecondPersonSingular }
  , { walsCode := "lan", iso := "laj", value := .noMInSecondPersonSingular }
  , { walsCode := "lav", iso := "lvk", value := .noMInSecondPersonSingular }
  , { walsCode := "lez", iso := "lez", value := .noMInSecondPersonSingular }
  , { walsCode := "lda", iso := "lug", value := .noMInSecondPersonSingular }
  , { walsCode := "lug", iso := "lgg", value := .mInSecondPersonSingular }
  , { walsCode := "lui", iso := "lui", value := .mInSecondPersonSingular }
  , { walsCode := "luv", iso := "lue", value := .mInSecondPersonSingular }
  , { walsCode := "maa", iso := "mas", value := .noMInSecondPersonSingular }
  , { walsCode := "mne", iso := "nmu", value := .mInSecondPersonSingular }
  , { walsCode := "mal", iso := "plt", value := .noMInSecondPersonSingular }
  , { walsCode := "mlk", iso := "mpb", value := .noMInSecondPersonSingular }
  , { walsCode := "mnd", iso := "cmn", value := .noMInSecondPersonSingular }
  , { walsCode := "mdk", iso := "mnk", value := .noMInSecondPersonSingular }
  , { walsCode := "myi", iso := "mpc", value := .noMInSecondPersonSingular }
  , { walsCode := "map", iso := "arn", value := .mInSecondPersonSingular }
  , { walsCode := "mar", iso := "mrc", value := .mInSecondPersonSingular }
  , { walsCode := "mrt", iso := "vma", value := .noMInSecondPersonSingular }
  , { walsCode := "mau", iso := "mph", value := .noMInSecondPersonSingular }
  , { walsCode := "may", iso := "ayz", value := .noMInSecondPersonSingular }
  , { walsCode := "mei", iso := "mni", value := .noMInSecondPersonSingular }
  , { walsCode := "mis", iso := "miq", value := .mInSecondPersonSingular }
  , { walsCode := "mss", iso := "skd", value := .mInSecondPersonSingular }
  , { walsCode := "mtp", iso := "mto", value := .mInSecondPersonSingular }
  , { walsCode := "mxc", iso := "mig", value := .noMInSecondPersonSingular }
  , { walsCode := "mot", iso := "siw", value := .noMInSecondPersonSingular }
  , { walsCode := "mun", iso := "unr", value := .mInSecondPersonSingular }
  , { walsCode := "nah", iso := "nll", value := .noMInSecondPersonSingular }
  , { walsCode := "kho", iso := "naq", value := .noMInSecondPersonSingular }
  , { walsCode := "nmb", iso := "nab", value := .noMInSecondPersonSingular }
  , { walsCode := "nai", iso := "gld", value := .noMInSecondPersonSingular }
  , { walsCode := "nar", iso := "nrb", value := .noMInSecondPersonSingular }
  , { walsCode := "nat", iso := "ncz", value := .mInSecondPersonSingular }
  , { walsCode := "ntu", iso := "yrk", value := .noMInSecondPersonSingular }
  , { walsCode := "ngl", iso := "nig", value := .noMInSecondPersonSingular }
  , { walsCode := "ngi", iso := "wyb", value := .noMInSecondPersonSingular }
  , { walsCode := "nbr", iso := "gym", value := .mInSecondPersonSingular }
  , { walsCode := "nca", iso := "caq", value := .mInSecondPersonSingular }
  , { walsCode := "niv", iso := "niv", value := .noMInSecondPersonSingular }
  , { walsCode := "nug", iso := "nuy", value := .noMInSecondPersonSingular }
  , { walsCode := "ood", iso := "ood", value := .mInSecondPersonSingular }
  , { walsCode := "ond", iso := "one", value := .noMInSecondPersonSingular }
  , { walsCode := "ori", iso := "tag", value := .noMInSecondPersonSingular }
  , { walsCode := "orh", iso := "hae", value := .noMInSecondPersonSingular }
  , { walsCode := "oss", iso := "oss", value := .noMInSecondPersonSingular }
  , { walsCode := "otm", iso := "ote", value := .noMInSecondPersonSingular }
  , { walsCode := "pai", iso := "pwn", value := .noMInSecondPersonSingular }
  , { walsCode := "pau", iso := "pad", value := .noMInSecondPersonSingular }
  , { walsCode := "prs", iso := "pes", value := .noMInSecondPersonSingular }
  , { walsCode := "pip", iso := "ppl", value := .mInSecondPersonSingular }
  , { walsCode := "prh", iso := "myp", value := .noMInSecondPersonSingular }
  , { walsCode := "pit", iso := "pjt", value := .noMInSecondPersonSingular }
  , { walsCode := "pme", iso := "peb", value := .mInSecondPersonSingular }
  , { walsCode := "pur", iso := "tsz", value := .noMInSecondPersonSingular }
  , { walsCode := "qim", iso := "qvi", value := .noMInSecondPersonSingular }
  , { walsCode := "qui", iso := "qui", value := .noMInSecondPersonSingular }
  , { walsCode := "ram", iso := "rma", value := .mInSecondPersonSingular }
  , { walsCode := "rap", iso := "rap", value := .noMInSecondPersonSingular }
  , { walsCode := "rus", iso := "rus", value := .noMInSecondPersonSingular }
  , { walsCode := "smt", iso := "uma", value := .mInSecondPersonSingular }
  , { walsCode := "sah", iso := "saj", value := .noMInSecondPersonSingular }
  , { walsCode := "sal", iso := "sln", value := .mInSecondPersonSingular }
  , { walsCode := "syu", iso := "sll", value := .noMInSecondPersonSingular }
  , { walsCode := "san", iso := "sag", value := .mInSecondPersonSingular }
  , { walsCode := "snm", iso := "xsu", value := .noMInSecondPersonSingular }
  , { walsCode := "snc", iso := "see", value := .noMInSecondPersonSingular }
  , { walsCode := "snt", iso := "set", value := .noMInSecondPersonSingular }
  , { walsCode := "shs", iso := "sht", value := .mInSecondPersonSingular }
  , { walsCode := "sla", iso := "den", value := .noMInSecondPersonSingular }
  , { walsCode := "spa", iso := "spa", value := .noMInSecondPersonSingular }
  , { walsCode := "squ", iso := "squ", value := .noMInSecondPersonSingular }
  , { walsCode := "sul", iso := "sua", value := .noMInSecondPersonSingular }
  , { walsCode := "sup", iso := "spp", value := .mInSecondPersonSingular }
  , { walsCode := "swa", iso := "swh", value := .noMInSecondPersonSingular }
  , { walsCode := "tag", iso := "tgl", value := .mInSecondPersonSingular }
  , { walsCode := "tkl", iso := "tkm", value := .mInSecondPersonSingular }
  , { walsCode := "tau", iso := "tya", value := .noMInSecondPersonSingular }
  , { walsCode := "tlf", iso := "tlf", value := .mInSecondPersonSingular }
  , { walsCode := "tmr", iso := "tea", value := .noMInSecondPersonSingular }
  , { walsCode := "tib", iso := "bod", value := .noMInSecondPersonSingular }
  , { walsCode := "tja", iso := "dih", value := .mInSecondPersonSingular }
  , { walsCode := "tmc", iso := "tjm", value := .noMInSecondPersonSingular }
  , { walsCode := "tiw", iso := "tiw", value := .noMInSecondPersonSingular }
  , { walsCode := "tli", iso := "tli", value := .noMInSecondPersonSingular }
  , { walsCode := "ton", iso := "tqw", value := .noMInSecondPersonSingular }
  , { walsCode := "tpa", iso := "top", value := .mInSecondPersonSingular }
  , { walsCode := "tru", iso := "tpy", value := .noMInSecondPersonSingular }
  , { walsCode := "tuk", iso := "", value := .noMInSecondPersonSingular }
  , { walsCode := "tun", iso := "tun", value := .mInSecondPersonSingular }
  , { walsCode := "tur", iso := "tur", value := .noMInSecondPersonSingular }
  , { walsCode := "tuv", iso := "tyv", value := .noMInSecondPersonSingular }
  , { walsCode := "tzu", iso := "tzj", value := .noMInSecondPersonSingular }
  , { walsCode := "ung", iso := "ung", value := .noMInSecondPersonSingular }
  , { walsCode := "uhi", iso := "urf", value := .noMInSecondPersonSingular }
  , { walsCode := "usa", iso := "wnu", value := .noMInSecondPersonSingular }
  , { walsCode := "vie", iso := "vie", value := .mInSecondPersonSingular }
  , { walsCode := "wgl", iso := "wbk", value := .noMInSecondPersonSingular }
  , { walsCode := "wao", iso := "auc", value := .mInSecondPersonSingular }
  , { walsCode := "wap", iso := "wao", value := .mInSecondPersonSingular }
  , { walsCode := "wra", iso := "wba", value := .noMInSecondPersonSingular }
  , { walsCode := "wrd", iso := "wrr", value := .noMInSecondPersonSingular }
  , { walsCode := "war", iso := "pav", value := .mInSecondPersonSingular }
  , { walsCode := "wrn", iso := "wnd", value := .noMInSecondPersonSingular }
  , { walsCode := "was", iso := "was", value := .mInSecondPersonSingular }
  , { walsCode := "wsk", iso := "wsk", value := .mInSecondPersonSingular }
  , { walsCode := "wem", iso := "xww", value := .noMInSecondPersonSingular }
  , { walsCode := "wic", iso := "wic", value := .noMInSecondPersonSingular }
  , { walsCode := "wch", iso := "mzh", value := .mInSecondPersonSingular }
  , { walsCode := "win", iso := "wnw", value := .mInSecondPersonSingular }
  , { walsCode := "wiy", iso := "wiy", value := .mInSecondPersonSingular }
  , { walsCode := "xok", iso := "xok", value := .mInSecondPersonSingular }
  , { walsCode := "yag", iso := "yad", value := .noMInSecondPersonSingular }
  , { walsCode := "yaq", iso := "yaq", value := .mInSecondPersonSingular }
  , { walsCode := "ywl", iso := "yok", value := .mInSecondPersonSingular }
  , { walsCode := "yim", iso := "yee", value := .mInSecondPersonSingular }
  , { walsCode := "yor", iso := "yor", value := .noMInSecondPersonSingular }
  , { walsCode := "yuc", iso := "yuc", value := .noMInSecondPersonSingular }
  , { walsCode := "yko", iso := "yux", value := .noMInSecondPersonSingular }
  , { walsCode := "yuk", iso := "gcd", value := .noMInSecondPersonSingular }
  , { walsCode := "yna", iso := "ynk", value := .mInSecondPersonSingular }
  , { walsCode := "yur", iso := "yur", value := .mInSecondPersonSingular }
  , { walsCode := "zqc", iso := "zoc", value := .mInSecondPersonSingular }
  , { walsCode := "zul", iso := "zul", value := .noMInSecondPersonSingular }
  , { walsCode := "zun", iso := "zun", value := .noMInSecondPersonSingular }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F137B
