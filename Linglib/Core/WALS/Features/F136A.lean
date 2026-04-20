import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 136A: M-T Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 136A`.

Chapter 136, 230 languages.
-/

namespace Core.WALS.F136A

/-- WALS 136A values. -/
inductive MTPronouns where
  /-- No M-T pronouns (200 languages). -/
  | noMTPronouns
  /-- M-T pronouns, paradigmatic (27 languages). -/
  | mTPronounsParadigmatic
  /-- M-T pronouns, non-paradigmatic (3 languages). -/
  | mTPronounsNonParadigmatic
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 136A dataset (230 languages). -/
def allData : List (Datapoint MTPronouns) :=
  [ { walsCode := "abk", iso := "abk", value := .noMTPronouns }
  , { walsCode := "ace", iso := "ace", value := .noMTPronouns }
  , { walsCode := "aco", iso := "kjq", value := .noMTPronouns }
  , { walsCode := "ain", iso := "ain", value := .noMTPronouns }
  , { walsCode := "ala", iso := "amp", value := .noMTPronouns }
  , { walsCode := "ame", iso := "aey", value := .noMTPronouns }
  , { walsCode := "amh", iso := "amh", value := .noMTPronouns }
  , { walsCode := "ane", iso := "anz", value := .noMTPronouns }
  , { walsCode := "apu", iso := "apu", value := .noMTPronouns }
  , { walsCode := "aeg", iso := "arz", value := .noMTPronouns }
  , { walsCode := "arp", iso := "ape", value := .noMTPronouns }
  , { walsCode := "amp", iso := "aer", value := .noMTPronouns }
  , { walsCode := "asm", iso := "cns", value := .noMTPronouns }
  , { walsCode := "atk", iso := "aqp", value := .noMTPronouns }
  , { walsCode := "awp", iso := "kwi", value := .noMTPronouns }
  , { walsCode := "awt", iso := "kmn", value := .noMTPronouns }
  , { walsCode := "ayw", iso := "nfl", value := .noMTPronouns }
  , { walsCode := "bag", iso := "bmi", value := .noMTPronouns }
  , { walsCode := "brs", iso := "bsn", value := .noMTPronouns }
  , { walsCode := "bsq", iso := "eus", value := .noMTPronouns }
  , { walsCode := "bej", iso := "bej", value := .noMTPronouns }
  , { walsCode := "bel", iso := "byw", value := .noMTPronouns }
  , { walsCode := "bma", iso := "tzm", value := .noMTPronouns }
  , { walsCode := "brk", iso := "bkl", value := .noMTPronouns }
  , { walsCode := "brr", iso := "bor", value := .noMTPronouns }
  , { walsCode := "brm", iso := "mya", value := .noMTPronouns }
  , { walsCode := "bur", iso := "bsk", value := .noMTPronouns }
  , { walsCode := "cax", iso := "", value := .noMTPronouns }
  , { walsCode := "cnl", iso := "ram", value := .noMTPronouns }
  , { walsCode := "csh", iso := "cbs", value := .noMTPronouns }
  , { walsCode := "cyv", iso := "cyb", value := .noMTPronouns }
  , { walsCode := "cha", iso := "cha", value := .noMTPronouns }
  , { walsCode := "cjo", iso := "pei", value := .noMTPronouns }
  , { walsCode := "chi", iso := "cid", value := .noMTPronouns }
  , { walsCode := "cku", iso := "wac", value := .noMTPronouns }
  , { walsCode := "ctm", iso := "ctm", value := .noMTPronouns }
  , { walsCode := "cho", iso := "chd", value := .noMTPronouns }
  , { walsCode := "chk", iso := "ckt", value := .mTPronounsParadigmatic }
  , { walsCode := "cin", iso := "inz", value := .noMTPronouns }
  , { walsCode := "chv", iso := "chv", value := .mTPronounsParadigmatic }
  , { walsCode := "coo", iso := "csz", value := .noMTPronouns }
  , { walsCode := "cre", iso := "crk", value := .noMTPronouns }
  , { walsCode := "dag", iso := "dgz", value := .noMTPronouns }
  , { walsCode := "dni", iso := "dni", value := .noMTPronouns }
  , { walsCode := "die", iso := "dih", value := .noMTPronouns }
  , { walsCode := "diy", iso := "dif", value := .noMTPronouns }
  , { walsCode := "diz", iso := "mdx", value := .noMTPronouns }
  , { walsCode := "djp", iso := "dwu", value := .noMTPronouns }
  , { walsCode := "dji", iso := "jig", value := .noMTPronouns }
  , { walsCode := "dum", iso := "vam", value := .noMTPronouns }
  , { walsCode := "dyi", iso := "dbl", value := .noMTPronouns }
  , { walsCode := "eng", iso := "eng", value := .noMTPronouns }
  , { walsCode := "fij", iso := "fij", value := .noMTPronouns }
  , { walsCode := "fin", iso := "fin", value := .mTPronounsParadigmatic }
  , { walsCode := "fre", iso := "fra", value := .mTPronounsParadigmatic }
  , { walsCode := "fua", iso := "fub", value := .mTPronounsParadigmatic }
  , { walsCode := "fur", iso := "fvr", value := .noMTPronouns }
  , { walsCode := "gbb", iso := "gbp", value := .noMTPronouns }
  , { walsCode := "geo", iso := "kat", value := .mTPronounsParadigmatic }
  , { walsCode := "ger", iso := "deu", value := .mTPronounsParadigmatic }
  , { walsCode := "git", iso := "git", value := .noMTPronouns }
  , { walsCode := "goo", iso := "gni", value := .noMTPronouns }
  , { walsCode := "grb", iso := "grj", value := .mTPronounsParadigmatic }
  , { walsCode := "grk", iso := "ell", value := .mTPronounsParadigmatic }
  , { walsCode := "grw", iso := "kal", value := .mTPronounsNonParadigmatic }
  , { walsCode := "gua", iso := "gug", value := .noMTPronouns }
  , { walsCode := "gku", iso := "pue", value := .noMTPronouns }
  , { walsCode := "hai", iso := "hai", value := .noMTPronouns }
  , { walsCode := "hat", iso := "had", value := .noMTPronouns }
  , { walsCode := "hau", iso := "hau", value := .noMTPronouns }
  , { walsCode := "heb", iso := "heb", value := .noMTPronouns }
  , { walsCode := "hin", iso := "hin", value := .mTPronounsParadigmatic }
  , { walsCode := "hix", iso := "hix", value := .noMTPronouns }
  , { walsCode := "hmo", iso := "hnj", value := .noMTPronouns }
  , { walsCode := "hua", iso := "ygr", value := .noMTPronouns }
  , { walsCode := "hve", iso := "huv", value := .noMTPronouns }
  , { walsCode := "hun", iso := "hun", value := .mTPronounsParadigmatic }
  , { walsCode := "iau", iso := "tmu", value := .noMTPronouns }
  , { walsCode := "imo", iso := "imn", value := .noMTPronouns }
  , { walsCode := "ind", iso := "ind", value := .noMTPronouns }
  , { walsCode := "ing", iso := "inh", value := .noMTPronouns }
  , { walsCode := "ite", iso := "itl", value := .mTPronounsParadigmatic }
  , { walsCode := "jak", iso := "jac", value := .noMTPronouns }
  , { walsCode := "jpn", iso := "jpn", value := .noMTPronouns }
  , { walsCode := "jaq", iso := "jqr", value := .noMTPronouns }
  , { walsCode := "jiv", iso := "jiv", value := .noMTPronouns }
  , { walsCode := "juh", iso := "ktz", value := .noMTPronouns }
  , { walsCode := "knd", iso := "kan", value := .noMTPronouns }
  , { walsCode := "knr", iso := "knc", value := .noMTPronouns }
  , { walsCode := "krk", iso := "kyh", value := .noMTPronouns }
  , { walsCode := "kay", iso := "gyd", value := .noMTPronouns }
  , { walsCode := "ket", iso := "ket", value := .noMTPronouns }
  , { walsCode := "kew", iso := "kew", value := .noMTPronouns }
  , { walsCode := "kha", iso := "khk", value := .mTPronounsParadigmatic }
  , { walsCode := "kio", iso := "kio", value := .noMTPronouns }
  , { walsCode := "kri", iso := "kzw", value := .noMTPronouns }
  , { walsCode := "kiw", iso := "kjd", value := .noMTPronouns }
  , { walsCode := "shp", iso := "yak", value := .noMTPronouns }
  , { walsCode := "koa", iso := "cku", value := .noMTPronouns }
  , { walsCode := "kob", iso := "kpw", value := .noMTPronouns }
  , { walsCode := "kmb", iso := "", value := .noMTPronouns }
  , { walsCode := "kor", iso := "kor", value := .noMTPronouns }
  , { walsCode := "kot", iso := "kfe", value := .noMTPronouns }
  , { walsCode := "kse", iso := "ses", value := .noMTPronouns }
  , { walsCode := "kro", iso := "kgo", value := .noMTPronouns }
  , { walsCode := "kut", iso := "kut", value := .noMTPronouns }
  , { walsCode := "kat", iso := "kmg", value := .noMTPronouns }
  , { walsCode := "lkt", iso := "lkt", value := .mTPronounsParadigmatic }
  , { walsCode := "lan", iso := "laj", value := .noMTPronouns }
  , { walsCode := "lav", iso := "lvk", value := .noMTPronouns }
  , { walsCode := "lez", iso := "lez", value := .noMTPronouns }
  , { walsCode := "lda", iso := "lug", value := .noMTPronouns }
  , { walsCode := "lug", iso := "lgg", value := .noMTPronouns }
  , { walsCode := "lui", iso := "lui", value := .noMTPronouns }
  , { walsCode := "luv", iso := "lue", value := .noMTPronouns }
  , { walsCode := "maa", iso := "mas", value := .noMTPronouns }
  , { walsCode := "mne", iso := "nmu", value := .noMTPronouns }
  , { walsCode := "mal", iso := "plt", value := .noMTPronouns }
  , { walsCode := "mlk", iso := "mpb", value := .noMTPronouns }
  , { walsCode := "mnd", iso := "cmn", value := .noMTPronouns }
  , { walsCode := "mdk", iso := "mnk", value := .noMTPronouns }
  , { walsCode := "myi", iso := "mpc", value := .noMTPronouns }
  , { walsCode := "map", iso := "arn", value := .noMTPronouns }
  , { walsCode := "mar", iso := "mrc", value := .noMTPronouns }
  , { walsCode := "mrt", iso := "vma", value := .noMTPronouns }
  , { walsCode := "mau", iso := "mph", value := .noMTPronouns }
  , { walsCode := "may", iso := "ayz", value := .noMTPronouns }
  , { walsCode := "mei", iso := "mni", value := .noMTPronouns }
  , { walsCode := "mis", iso := "miq", value := .noMTPronouns }
  , { walsCode := "mss", iso := "skd", value := .mTPronounsParadigmatic }
  , { walsCode := "mco", iso := "mco", value := .noMTPronouns }
  , { walsCode := "mxc", iso := "mig", value := .noMTPronouns }
  , { walsCode := "mot", iso := "siw", value := .noMTPronouns }
  , { walsCode := "mun", iso := "unr", value := .noMTPronouns }
  , { walsCode := "nah", iso := "nll", value := .noMTPronouns }
  , { walsCode := "kho", iso := "naq", value := .noMTPronouns }
  , { walsCode := "nmb", iso := "nab", value := .noMTPronouns }
  , { walsCode := "nai", iso := "gld", value := .mTPronounsParadigmatic }
  , { walsCode := "nar", iso := "nrb", value := .noMTPronouns }
  , { walsCode := "nat", iso := "ncz", value := .noMTPronouns }
  , { walsCode := "ntu", iso := "yrk", value := .mTPronounsParadigmatic }
  , { walsCode := "ntj", iso := "ntj", value := .noMTPronouns }
  , { walsCode := "ngl", iso := "nig", value := .noMTPronouns }
  , { walsCode := "ngi", iso := "wyb", value := .noMTPronouns }
  , { walsCode := "nbr", iso := "gym", value := .noMTPronouns }
  , { walsCode := "nca", iso := "caq", value := .noMTPronouns }
  , { walsCode := "niv", iso := "niv", value := .noMTPronouns }
  , { walsCode := "nug", iso := "nuy", value := .noMTPronouns }
  , { walsCode := "nuu", iso := "nuk", value := .noMTPronouns }
  , { walsCode := "ood", iso := "ood", value := .noMTPronouns }
  , { walsCode := "ond", iso := "one", value := .noMTPronouns }
  , { walsCode := "ori", iso := "tag", value := .noMTPronouns }
  , { walsCode := "orh", iso := "hae", value := .noMTPronouns }
  , { walsCode := "oss", iso := "oss", value := .mTPronounsParadigmatic }
  , { walsCode := "otm", iso := "ote", value := .noMTPronouns }
  , { walsCode := "pai", iso := "pwn", value := .noMTPronouns }
  , { walsCode := "pau", iso := "pad", value := .noMTPronouns }
  , { walsCode := "prs", iso := "pes", value := .mTPronounsParadigmatic }
  , { walsCode := "pip", iso := "ppl", value := .noMTPronouns }
  , { walsCode := "prh", iso := "myp", value := .noMTPronouns }
  , { walsCode := "pme", iso := "peb", value := .noMTPronouns }
  , { walsCode := "pur", iso := "tsz", value := .noMTPronouns }
  , { walsCode := "qim", iso := "qvi", value := .noMTPronouns }
  , { walsCode := "qui", iso := "qui", value := .noMTPronouns }
  , { walsCode := "ram", iso := "rma", value := .noMTPronouns }
  , { walsCode := "rap", iso := "rap", value := .noMTPronouns }
  , { walsCode := "rus", iso := "rus", value := .mTPronounsParadigmatic }
  , { walsCode := "sah", iso := "saj", value := .noMTPronouns }
  , { walsCode := "sal", iso := "sln", value := .noMTPronouns }
  , { walsCode := "syu", iso := "sll", value := .mTPronounsParadigmatic }
  , { walsCode := "san", iso := "sag", value := .noMTPronouns }
  , { walsCode := "snm", iso := "xsu", value := .noMTPronouns }
  , { walsCode := "snc", iso := "see", value := .noMTPronouns }
  , { walsCode := "snt", iso := "set", value := .noMTPronouns }
  , { walsCode := "shs", iso := "sht", value := .noMTPronouns }
  , { walsCode := "sla", iso := "den", value := .noMTPronouns }
  , { walsCode := "spa", iso := "spa", value := .mTPronounsParadigmatic }
  , { walsCode := "squ", iso := "squ", value := .noMTPronouns }
  , { walsCode := "sul", iso := "sua", value := .noMTPronouns }
  , { walsCode := "sup", iso := "spp", value := .noMTPronouns }
  , { walsCode := "swa", iso := "swh", value := .noMTPronouns }
  , { walsCode := "tag", iso := "tgl", value := .noMTPronouns }
  , { walsCode := "tkl", iso := "tkm", value := .noMTPronouns }
  , { walsCode := "tau", iso := "tya", value := .noMTPronouns }
  , { walsCode := "tlf", iso := "tlf", value := .noMTPronouns }
  , { walsCode := "tmr", iso := "tea", value := .noMTPronouns }
  , { walsCode := "tib", iso := "bod", value := .noMTPronouns }
  , { walsCode := "tmc", iso := "tjm", value := .noMTPronouns }
  , { walsCode := "tiw", iso := "tiw", value := .noMTPronouns }
  , { walsCode := "tli", iso := "tli", value := .noMTPronouns }
  , { walsCode := "ton", iso := "tqw", value := .noMTPronouns }
  , { walsCode := "tpa", iso := "top", value := .noMTPronouns }
  , { walsCode := "tru", iso := "tpy", value := .noMTPronouns }
  , { walsCode := "tuk", iso := "", value := .noMTPronouns }
  , { walsCode := "tun", iso := "tun", value := .noMTPronouns }
  , { walsCode := "tur", iso := "tur", value := .mTPronounsParadigmatic }
  , { walsCode := "tuv", iso := "tyv", value := .mTPronounsParadigmatic }
  , { walsCode := "tzu", iso := "tzj", value := .noMTPronouns }
  , { walsCode := "ung", iso := "ung", value := .noMTPronouns }
  , { walsCode := "uhi", iso := "urf", value := .noMTPronouns }
  , { walsCode := "usa", iso := "wnu", value := .mTPronounsParadigmatic }
  , { walsCode := "vie", iso := "vie", value := .noMTPronouns }
  , { walsCode := "wgl", iso := "wbk", value := .mTPronounsParadigmatic }
  , { walsCode := "wao", iso := "auc", value := .noMTPronouns }
  , { walsCode := "wap", iso := "wao", value := .noMTPronouns }
  , { walsCode := "wra", iso := "wba", value := .noMTPronouns }
  , { walsCode := "wrd", iso := "wrr", value := .noMTPronouns }
  , { walsCode := "war", iso := "pav", value := .noMTPronouns }
  , { walsCode := "wrn", iso := "wnd", value := .noMTPronouns }
  , { walsCode := "was", iso := "was", value := .noMTPronouns }
  , { walsCode := "wsk", iso := "wsk", value := .mTPronounsNonParadigmatic }
  , { walsCode := "wem", iso := "xww", value := .noMTPronouns }
  , { walsCode := "wic", iso := "wic", value := .noMTPronouns }
  , { walsCode := "wch", iso := "mzh", value := .noMTPronouns }
  , { walsCode := "win", iso := "wnw", value := .noMTPronouns }
  , { walsCode := "wiy", iso := "wiy", value := .noMTPronouns }
  , { walsCode := "xok", iso := "xok", value := .noMTPronouns }
  , { walsCode := "yag", iso := "yad", value := .noMTPronouns }
  , { walsCode := "yaq", iso := "yaq", value := .noMTPronouns }
  , { walsCode := "ywl", iso := "yok", value := .noMTPronouns }
  , { walsCode := "yim", iso := "yee", value := .mTPronounsNonParadigmatic }
  , { walsCode := "yor", iso := "yor", value := .noMTPronouns }
  , { walsCode := "yuc", iso := "yuc", value := .noMTPronouns }
  , { walsCode := "yko", iso := "yux", value := .mTPronounsParadigmatic }
  , { walsCode := "yuk", iso := "gcd", value := .noMTPronouns }
  , { walsCode := "yna", iso := "ynk", value := .noMTPronouns }
  , { walsCode := "yur", iso := "yur", value := .noMTPronouns }
  , { walsCode := "zqc", iso := "zoc", value := .noMTPronouns }
  , { walsCode := "zul", iso := "zul", value := .noMTPronouns }
  , { walsCode := "zun", iso := "zun", value := .noMTPronouns }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F136A
