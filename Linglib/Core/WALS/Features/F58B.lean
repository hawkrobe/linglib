import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 58B: Number of Possessive Nouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 58B`.

Chapter 58, 243 languages.
-/

namespace Core.WALS.F58B

/-- WALS 58B values. -/
inductive NumberOfPossessiveNouns where
  /-- None reported (233 languages). -/
  | noneReported
  /-- One (3 languages). -/
  | one
  /-- Two to four (4 languages). -/
  | twoToFour
  /-- Five or more (3 languages). -/
  | fiveOrMore
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 58B dataset (243 languages). -/
def allData : List (Datapoint NumberOfPossessiveNouns) :=
  [ { walsCode := "abk", iso := "abk", value := .noneReported }
  , { walsCode := "aco", iso := "kjq", value := .noneReported }
  , { walsCode := "ain", iso := "ain", value := .noneReported }
  , { walsCode := "ala", iso := "amp", value := .noneReported }
  , { walsCode := "alw", iso := "alh", value := .noneReported }
  , { walsCode := "ame", iso := "aey", value := .noneReported }
  , { walsCode := "amh", iso := "amh", value := .noneReported }
  , { walsCode := "ane", iso := "anz", value := .noneReported }
  , { walsCode := "apu", iso := "apu", value := .noneReported }
  , { walsCode := "aeg", iso := "arz", value := .noneReported }
  , { walsCode := "arp", iso := "ape", value := .noneReported }
  , { walsCode := "arm", iso := "hye", value := .noneReported }
  , { walsCode := "amp", iso := "aer", value := .noneReported }
  , { walsCode := "asm", iso := "cns", value := .noneReported }
  , { walsCode := "awp", iso := "kwi", value := .noneReported }
  , { walsCode := "awt", iso := "kmn", value := .noneReported }
  , { walsCode := "aym", iso := "ayr", value := .noneReported }
  , { walsCode := "bag", iso := "bmi", value := .noneReported }
  , { walsCode := "baa", iso := "bbb", value := .noneReported }
  , { walsCode := "brs", iso := "bsn", value := .noneReported }
  , { walsCode := "bsq", iso := "eus", value := .noneReported }
  , { walsCode := "bzi", iso := "bvz", value := .noneReported }
  , { walsCode := "bej", iso := "bej", value := .noneReported }
  , { walsCode := "bel", iso := "byw", value := .noneReported }
  , { walsCode := "bma", iso := "tzm", value := .noneReported }
  , { walsCode := "brk", iso := "bkl", value := .noneReported }
  , { walsCode := "boa", iso := "kvg", value := .noneReported }
  , { walsCode := "brr", iso := "bor", value := .noneReported }
  , { walsCode := "brh", iso := "brh", value := .noneReported }
  , { walsCode := "brm", iso := "mya", value := .noneReported }
  , { walsCode := "buu", iso := "mhs", value := .noneReported }
  , { walsCode := "bur", iso := "bsk", value := .noneReported }
  , { walsCode := "cax", iso := "", value := .noneReported }
  , { walsCode := "cnl", iso := "ram", value := .noneReported }
  , { walsCode := "cyv", iso := "cyb", value := .noneReported }
  , { walsCode := "cha", iso := "cha", value := .twoToFour }
  , { walsCode := "chy", iso := "cbt", value := .noneReported }
  , { walsCode := "cjo", iso := "pei", value := .twoToFour }
  , { walsCode := "chi", iso := "cid", value := .noneReported }
  , { walsCode := "ctm", iso := "ctm", value := .noneReported }
  , { walsCode := "cho", iso := "chd", value := .noneReported }
  , { walsCode := "chk", iso := "ckt", value := .noneReported }
  , { walsCode := "cin", iso := "inz", value := .noneReported }
  , { walsCode := "cre", iso := "crk", value := .noneReported }
  , { walsCode := "dag", iso := "dgz", value := .noneReported }
  , { walsCode := "dni", iso := "dni", value := .noneReported }
  , { walsCode := "die", iso := "dih", value := .noneReported }
  , { walsCode := "dig", iso := "mhu", value := .noneReported }
  , { walsCode := "diy", iso := "dif", value := .noneReported }
  , { walsCode := "diz", iso := "mdx", value := .noneReported }
  , { walsCode := "djp", iso := "dwu", value := .noneReported }
  , { walsCode := "dre", iso := "dhv", value := .noneReported }
  , { walsCode := "dum", iso := "vam", value := .noneReported }
  , { walsCode := "dyi", iso := "dbl", value := .noneReported }
  , { walsCode := "eka", iso := "ekg", value := .noneReported }
  , { walsCode := "eng", iso := "eng", value := .noneReported }
  , { walsCode := "epe", iso := "sja", value := .noneReported }
  , { walsCode := "eve", iso := "evn", value := .noneReported }
  , { walsCode := "ewe", iso := "ewe", value := .noneReported }
  , { walsCode := "fij", iso := "fij", value := .twoToFour }
  , { walsCode := "fin", iso := "fin", value := .noneReported }
  , { walsCode := "fre", iso := "fra", value := .noneReported }
  , { walsCode := "fua", iso := "fub", value := .noneReported }
  , { walsCode := "fur", iso := "fvr", value := .noneReported }
  , { walsCode := "grr", iso := "wrk", value := .noneReported }
  , { walsCode := "gbb", iso := "gbp", value := .noneReported }
  , { walsCode := "geo", iso := "kat", value := .noneReported }
  , { walsCode := "ger", iso := "deu", value := .noneReported }
  , { walsCode := "goo", iso := "gni", value := .noneReported }
  , { walsCode := "grb", iso := "grj", value := .noneReported }
  , { walsCode := "grk", iso := "ell", value := .noneReported }
  , { walsCode := "grw", iso := "kal", value := .noneReported }
  , { walsCode := "gua", iso := "gug", value := .one }
  , { walsCode := "gmz", iso := "guk", value := .noneReported }
  , { walsCode := "hai", iso := "hai", value := .noneReported }
  , { walsCode := "hat", iso := "had", value := .noneReported }
  , { walsCode := "hau", iso := "hau", value := .noneReported }
  , { walsCode := "heb", iso := "heb", value := .noneReported }
  , { walsCode := "hin", iso := "hin", value := .noneReported }
  , { walsCode := "hix", iso := "hix", value := .noneReported }
  , { walsCode := "hmo", iso := "hnj", value := .noneReported }
  , { walsCode := "hua", iso := "ygr", value := .noneReported }
  , { walsCode := "hve", iso := "huv", value := .noneReported }
  , { walsCode := "hun", iso := "hun", value := .noneReported }
  , { walsCode := "iau", iso := "tmu", value := .noneReported }
  , { walsCode := "ijo", iso := "ijc", value := .noneReported }
  , { walsCode := "ik", iso := "ikx", value := .noneReported }
  , { walsCode := "imo", iso := "imn", value := .noneReported }
  , { walsCode := "ind", iso := "ind", value := .noneReported }
  , { walsCode := "ing", iso := "inh", value := .noneReported }
  , { walsCode := "jak", iso := "jac", value := .noneReported }
  , { walsCode := "jpn", iso := "jpn", value := .noneReported }
  , { walsCode := "juh", iso := "ktz", value := .noneReported }
  , { walsCode := "knk", iso := "kna", value := .noneReported }
  , { walsCode := "knd", iso := "kan", value := .noneReported }
  , { walsCode := "knp", iso := "kcd", value := .noneReported }
  , { walsCode := "knr", iso := "knc", value := .noneReported }
  , { walsCode := "krk", iso := "kyh", value := .noneReported }
  , { walsCode := "kay", iso := "gyd", value := .noneReported }
  , { walsCode := "ket", iso := "ket", value := .noneReported }
  , { walsCode := "kew", iso := "kew", value := .noneReported }
  , { walsCode := "kha", iso := "khk", value := .noneReported }
  , { walsCode := "khs", iso := "kha", value := .noneReported }
  , { walsCode := "kim", iso := "kig", value := .noneReported }
  , { walsCode := "kio", iso := "kio", value := .noneReported }
  , { walsCode := "kri", iso := "kzw", value := .fiveOrMore }
  , { walsCode := "koa", iso := "cku", value := .noneReported }
  , { walsCode := "kob", iso := "kpw", value := .noneReported }
  , { walsCode := "koi", iso := "kbk", value := .noneReported }
  , { walsCode := "kln", iso := "kvw", value := .noneReported }
  , { walsCode := "kzy", iso := "kpv", value := .noneReported }
  , { walsCode := "knu", iso := "kyx", value := .noneReported }
  , { walsCode := "kor", iso := "kor", value := .noneReported }
  , { walsCode := "kch", iso := "khq", value := .noneReported }
  , { walsCode := "kro", iso := "kgo", value := .noneReported }
  , { walsCode := "kui", iso := "kxu", value := .noneReported }
  , { walsCode := "knm", iso := "kun", value := .noneReported }
  , { walsCode := "kut", iso := "kut", value := .noneReported }
  , { walsCode := "kat", iso := "kmg", value := .noneReported }
  , { walsCode := "lkt", iso := "lkt", value := .noneReported }
  , { walsCode := "lan", iso := "laj", value := .noneReported }
  , { walsCode := "lav", iso := "lvk", value := .noneReported }
  , { walsCode := "lez", iso := "lez", value := .noneReported }
  , { walsCode := "lim", iso := "lif", value := .noneReported }
  , { walsCode := "lda", iso := "lug", value := .noneReported }
  , { walsCode := "lug", iso := "lgg", value := .noneReported }
  , { walsCode := "luv", iso := "lue", value := .noneReported }
  , { walsCode := "maa", iso := "mas", value := .noneReported }
  , { walsCode := "mne", iso := "nmu", value := .noneReported }
  , { walsCode := "mal", iso := "plt", value := .noneReported }
  , { walsCode := "mlk", iso := "mpb", value := .noneReported }
  , { walsCode := "mto", iso := "kmj", value := .noneReported }
  , { walsCode := "mnd", iso := "cmn", value := .noneReported }
  , { walsCode := "mdk", iso := "mnk", value := .noneReported }
  , { walsCode := "myi", iso := "mpc", value := .noneReported }
  , { walsCode := "mao", iso := "mri", value := .noneReported }
  , { walsCode := "map", iso := "arn", value := .noneReported }
  , { walsCode := "mrg", iso := "mrt", value := .noneReported }
  , { walsCode := "mar", iso := "mrc", value := .noneReported }
  , { walsCode := "mrh", iso := "mfr", value := .noneReported }
  , { walsCode := "mrt", iso := "vma", value := .noneReported }
  , { walsCode := "mau", iso := "mph", value := .noneReported }
  , { walsCode := "may", iso := "ayz", value := .noneReported }
  , { walsCode := "mei", iso := "mni", value := .noneReported }
  , { walsCode := "mss", iso := "skd", value := .noneReported }
  , { walsCode := "mxc", iso := "mig", value := .noneReported }
  , { walsCode := "mot", iso := "siw", value := .noneReported }
  , { walsCode := "mpa", iso := "mwf", value := .noneReported }
  , { walsCode := "nah", iso := "nll", value := .noneReported }
  , { walsCode := "nkk", iso := "nck", value := .noneReported }
  , { walsCode := "kho", iso := "naq", value := .noneReported }
  , { walsCode := "nai", iso := "gld", value := .noneReported }
  , { walsCode := "nan", iso := "niq", value := .noneReported }
  , { walsCode := "nar", iso := "nrb", value := .noneReported }
  , { walsCode := "ntu", iso := "yrk", value := .noneReported }
  , { walsCode := "nez", iso := "nez", value := .noneReported }
  , { walsCode := "ngi", iso := "wyb", value := .noneReported }
  , { walsCode := "nca", iso := "caq", value := .noneReported }
  , { walsCode := "nim", iso := "nir", value := .noneReported }
  , { walsCode := "nbd", iso := "dgl", value := .noneReported }
  , { walsCode := "nug", iso := "nuy", value := .noneReported }
  , { walsCode := "nyn", iso := "nyh", value := .noneReported }
  , { walsCode := "ond", iso := "one", value := .noneReported }
  , { walsCode := "ori", iso := "tag", value := .noneReported }
  , { walsCode := "orh", iso := "hae", value := .noneReported }
  , { walsCode := "oss", iso := "oss", value := .noneReported }
  , { walsCode := "otm", iso := "ote", value := .noneReported }
  , { walsCode := "pms", iso := "pma", value := .twoToFour }
  , { walsCode := "pai", iso := "pwn", value := .noneReported }
  , { walsCode := "pnr", iso := "pbh", value := .fiveOrMore }
  , { walsCode := "pau", iso := "pad", value := .noneReported }
  , { walsCode := "pwn", iso := "paw", value := .noneReported }
  , { walsCode := "prs", iso := "pes", value := .noneReported }
  , { walsCode := "prh", iso := "myp", value := .noneReported }
  , { walsCode := "poh", iso := "pon", value := .fiveOrMore }
  , { walsCode := "pso", iso := "pom", value := .noneReported }
  , { walsCode := "qim", iso := "qvi", value := .noneReported }
  , { walsCode := "qui", iso := "qui", value := .noneReported }
  , { walsCode := "ram", iso := "rma", value := .noneReported }
  , { walsCode := "rap", iso := "rap", value := .noneReported }
  , { walsCode := "res", iso := "rgr", value := .noneReported }
  , { walsCode := "rus", iso := "rus", value := .noneReported }
  , { walsCode := "sah", iso := "saj", value := .noneReported }
  , { walsCode := "sal", iso := "sln", value := .noneReported }
  , { walsCode := "syu", iso := "sll", value := .noneReported }
  , { walsCode := "sam", iso := "smo", value := .noneReported }
  , { walsCode := "san", iso := "sag", value := .noneReported }
  , { walsCode := "snm", iso := "xsu", value := .noneReported }
  , { walsCode := "snt", iso := "set", value := .noneReported }
  , { walsCode := "siu", iso := "sis", value := .noneReported }
  , { walsCode := "sla", iso := "den", value := .noneReported }
  , { walsCode := "spa", iso := "spa", value := .noneReported }
  , { walsCode := "squ", iso := "squ", value := .noneReported }
  , { walsCode := "sue", iso := "sue", value := .noneReported }
  , { walsCode := "sul", iso := "sua", value := .noneReported }
  , { walsCode := "sup", iso := "spp", value := .noneReported }
  , { walsCode := "swa", iso := "swh", value := .noneReported }
  , { walsCode := "tag", iso := "tgl", value := .noneReported }
  , { walsCode := "tkl", iso := "tkm", value := .noneReported }
  , { walsCode := "tgp", iso := "tpg", value := .noneReported }
  , { walsCode := "tau", iso := "tya", value := .noneReported }
  , { walsCode := "taw", iso := "tbo", value := .noneReported }
  , { walsCode := "tht", iso := "kps", value := .noneReported }
  , { walsCode := "tlf", iso := "tlf", value := .noneReported }
  , { walsCode := "ter", iso := "ttr", value := .noneReported }
  , { walsCode := "tha", iso := "tha", value := .noneReported }
  , { walsCode := "tib", iso := "bod", value := .noneReported }
  , { walsCode := "tiw", iso := "tiw", value := .noneReported }
  , { walsCode := "tli", iso := "tli", value := .noneReported }
  , { walsCode := "ton", iso := "tqw", value := .noneReported }
  , { walsCode := "tot", iso := "tlc", value := .noneReported }
  , { walsCode := "tru", iso := "tpy", value := .one }
  , { walsCode := "tuk", iso := "", value := .noneReported }
  , { walsCode := "tun", iso := "tun", value := .noneReported }
  , { walsCode := "tur", iso := "tur", value := .noneReported }
  , { walsCode := "tuv", iso := "tyv", value := .noneReported }
  , { walsCode := "ung", iso := "ung", value := .noneReported }
  , { walsCode := "uhi", iso := "urf", value := .noneReported }
  , { walsCode := "vie", iso := "vie", value := .noneReported }
  , { walsCode := "wap", iso := "wao", value := .noneReported }
  , { walsCode := "wra", iso := "wba", value := .noneReported }
  , { walsCode := "wry", iso := "wrz", value := .noneReported }
  , { walsCode := "war", iso := "pav", value := .noneReported }
  , { walsCode := "wrs", iso := "wrs", value := .noneReported }
  , { walsCode := "wrl", iso := "wbp", value := .noneReported }
  , { walsCode := "wrn", iso := "wnd", value := .noneReported }
  , { walsCode := "was", iso := "was", value := .one }
  , { walsCode := "wsk", iso := "wsk", value := .noneReported }
  , { walsCode := "wem", iso := "xww", value := .noneReported }
  , { walsCode := "wic", iso := "wic", value := .noneReported }
  , { walsCode := "wch", iso := "mzh", value := .noneReported }
  , { walsCode := "win", iso := "wnw", value := .noneReported }
  , { walsCode := "yag", iso := "yad", value := .noneReported }
  , { walsCode := "yli", iso := "yli", value := .noneReported }
  , { walsCode := "yaq", iso := "yaq", value := .noneReported }
  , { walsCode := "yes", iso := "yss", value := .noneReported }
  , { walsCode := "yim", iso := "yee", value := .noneReported }
  , { walsCode := "yor", iso := "yor", value := .noneReported }
  , { walsCode := "yuc", iso := "yuc", value := .noneReported }
  , { walsCode := "yko", iso := "yux", value := .noneReported }
  , { walsCode := "yur", iso := "yur", value := .noneReported }
  , { walsCode := "zqc", iso := "zoc", value := .noneReported }
  , { walsCode := "zul", iso := "zul", value := .noneReported }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F58B
