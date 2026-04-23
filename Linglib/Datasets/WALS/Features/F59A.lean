import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 59A: Possessive Classification
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 59A`.

Chapter 59, 243 languages.
-/

namespace Datasets.WALS.F59A

/-- WALS 59A values. -/
inductive PossessiveClassification where
  /-- No possessive classification (125 languages). -/
  | noPossessiveClassification
  /-- Two classes (94 languages). -/
  | twoClasses
  /-- Three to five classes (20 languages). -/
  | threeToFiveClasses
  /-- More than five classes (4 languages). -/
  | moreThanFiveClasses
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 59A dataset (243 languages). -/
def allData : List (Datapoint PossessiveClassification) :=
  [ { walsCode := "abk", iso := "abk", value := .noPossessiveClassification }
  , { walsCode := "aco", iso := "kjq", value := .noPossessiveClassification }
  , { walsCode := "ain", iso := "ain", value := .noPossessiveClassification }
  , { walsCode := "ala", iso := "amp", value := .noPossessiveClassification }
  , { walsCode := "alw", iso := "alh", value := .twoClasses }
  , { walsCode := "ame", iso := "aey", value := .moreThanFiveClasses }
  , { walsCode := "amh", iso := "amh", value := .noPossessiveClassification }
  , { walsCode := "ane", iso := "anz", value := .moreThanFiveClasses }
  , { walsCode := "apu", iso := "apu", value := .noPossessiveClassification }
  , { walsCode := "aeg", iso := "arz", value := .noPossessiveClassification }
  , { walsCode := "arp", iso := "ape", value := .noPossessiveClassification }
  , { walsCode := "arm", iso := "hye", value := .noPossessiveClassification }
  , { walsCode := "amp", iso := "aer", value := .twoClasses }
  , { walsCode := "asm", iso := "cns", value := .twoClasses }
  , { walsCode := "awp", iso := "kwi", value := .noPossessiveClassification }
  , { walsCode := "awt", iso := "kmn", value := .noPossessiveClassification }
  , { walsCode := "aym", iso := "ayr", value := .noPossessiveClassification }
  , { walsCode := "bag", iso := "bmi", value := .noPossessiveClassification }
  , { walsCode := "baa", iso := "bbb", value := .noPossessiveClassification }
  , { walsCode := "brs", iso := "bsn", value := .twoClasses }
  , { walsCode := "bsq", iso := "eus", value := .noPossessiveClassification }
  , { walsCode := "bzi", iso := "bvz", value := .noPossessiveClassification }
  , { walsCode := "bej", iso := "bej", value := .noPossessiveClassification }
  , { walsCode := "bel", iso := "byw", value := .noPossessiveClassification }
  , { walsCode := "bma", iso := "tzm", value := .twoClasses }
  , { walsCode := "brk", iso := "bkl", value := .noPossessiveClassification }
  , { walsCode := "boa", iso := "kvg", value := .twoClasses }
  , { walsCode := "brr", iso := "bor", value := .threeToFiveClasses }
  , { walsCode := "brh", iso := "brh", value := .noPossessiveClassification }
  , { walsCode := "brm", iso := "mya", value := .noPossessiveClassification }
  , { walsCode := "buu", iso := "mhs", value := .twoClasses }
  , { walsCode := "bur", iso := "bsk", value := .threeToFiveClasses }
  , { walsCode := "cax", iso := "", value := .noPossessiveClassification }
  , { walsCode := "cnl", iso := "ram", value := .noPossessiveClassification }
  , { walsCode := "cyv", iso := "cyb", value := .moreThanFiveClasses }
  , { walsCode := "cha", iso := "cha", value := .noPossessiveClassification }
  , { walsCode := "chy", iso := "cbt", value := .twoClasses }
  , { walsCode := "cjo", iso := "pei", value := .moreThanFiveClasses }
  , { walsCode := "chi", iso := "cid", value := .twoClasses }
  , { walsCode := "ctm", iso := "ctm", value := .noPossessiveClassification }
  , { walsCode := "cho", iso := "chd", value := .noPossessiveClassification }
  , { walsCode := "chk", iso := "ckt", value := .noPossessiveClassification }
  , { walsCode := "cin", iso := "inz", value := .noPossessiveClassification }
  , { walsCode := "cre", iso := "crk", value := .noPossessiveClassification }
  , { walsCode := "dag", iso := "dgz", value := .twoClasses }
  , { walsCode := "dni", iso := "dni", value := .twoClasses }
  , { walsCode := "die", iso := "dih", value := .twoClasses }
  , { walsCode := "dig", iso := "mhu", value := .noPossessiveClassification }
  , { walsCode := "diy", iso := "dif", value := .twoClasses }
  , { walsCode := "diz", iso := "mdx", value := .twoClasses }
  , { walsCode := "djp", iso := "dwu", value := .noPossessiveClassification }
  , { walsCode := "dre", iso := "dhv", value := .twoClasses }
  , { walsCode := "dum", iso := "vam", value := .twoClasses }
  , { walsCode := "dyi", iso := "dbl", value := .twoClasses }
  , { walsCode := "eka", iso := "ekg", value := .twoClasses }
  , { walsCode := "eng", iso := "eng", value := .noPossessiveClassification }
  , { walsCode := "epe", iso := "sja", value := .noPossessiveClassification }
  , { walsCode := "eve", iso := "evn", value := .noPossessiveClassification }
  , { walsCode := "ewe", iso := "ewe", value := .twoClasses }
  , { walsCode := "fij", iso := "fij", value := .noPossessiveClassification }
  , { walsCode := "fin", iso := "fin", value := .noPossessiveClassification }
  , { walsCode := "fre", iso := "fra", value := .noPossessiveClassification }
  , { walsCode := "fua", iso := "fub", value := .twoClasses }
  , { walsCode := "fur", iso := "fvr", value := .noPossessiveClassification }
  , { walsCode := "grr", iso := "wrk", value := .twoClasses }
  , { walsCode := "gbb", iso := "gbp", value := .twoClasses }
  , { walsCode := "geo", iso := "kat", value := .noPossessiveClassification }
  , { walsCode := "ger", iso := "deu", value := .noPossessiveClassification }
  , { walsCode := "goo", iso := "gni", value := .twoClasses }
  , { walsCode := "grb", iso := "grj", value := .noPossessiveClassification }
  , { walsCode := "grk", iso := "ell", value := .noPossessiveClassification }
  , { walsCode := "grw", iso := "kal", value := .noPossessiveClassification }
  , { walsCode := "gua", iso := "gug", value := .noPossessiveClassification }
  , { walsCode := "gmz", iso := "guk", value := .noPossessiveClassification }
  , { walsCode := "hai", iso := "hai", value := .twoClasses }
  , { walsCode := "hat", iso := "had", value := .twoClasses }
  , { walsCode := "hau", iso := "hau", value := .noPossessiveClassification }
  , { walsCode := "heb", iso := "heb", value := .noPossessiveClassification }
  , { walsCode := "hin", iso := "hin", value := .noPossessiveClassification }
  , { walsCode := "hix", iso := "hix", value := .noPossessiveClassification }
  , { walsCode := "hmo", iso := "hnj", value := .noPossessiveClassification }
  , { walsCode := "hua", iso := "ygr", value := .threeToFiveClasses }
  , { walsCode := "hve", iso := "huv", value := .twoClasses }
  , { walsCode := "hun", iso := "hun", value := .noPossessiveClassification }
  , { walsCode := "iau", iso := "tmu", value := .twoClasses }
  , { walsCode := "ijo", iso := "ijc", value := .twoClasses }
  , { walsCode := "ik", iso := "ikx", value := .noPossessiveClassification }
  , { walsCode := "imo", iso := "imn", value := .twoClasses }
  , { walsCode := "ind", iso := "ind", value := .noPossessiveClassification }
  , { walsCode := "ing", iso := "inh", value := .noPossessiveClassification }
  , { walsCode := "jak", iso := "jac", value := .noPossessiveClassification }
  , { walsCode := "jpn", iso := "jpn", value := .noPossessiveClassification }
  , { walsCode := "juh", iso := "ktz", value := .threeToFiveClasses }
  , { walsCode := "knk", iso := "kna", value := .twoClasses }
  , { walsCode := "knd", iso := "kan", value := .noPossessiveClassification }
  , { walsCode := "knp", iso := "kcd", value := .noPossessiveClassification }
  , { walsCode := "knr", iso := "knc", value := .noPossessiveClassification }
  , { walsCode := "krk", iso := "kyh", value := .noPossessiveClassification }
  , { walsCode := "kay", iso := "gyd", value := .twoClasses }
  , { walsCode := "ket", iso := "ket", value := .noPossessiveClassification }
  , { walsCode := "kew", iso := "kew", value := .noPossessiveClassification }
  , { walsCode := "kha", iso := "khk", value := .noPossessiveClassification }
  , { walsCode := "khs", iso := "kha", value := .noPossessiveClassification }
  , { walsCode := "kim", iso := "kig", value := .twoClasses }
  , { walsCode := "kio", iso := "kio", value := .twoClasses }
  , { walsCode := "kri", iso := "kzw", value := .threeToFiveClasses }
  , { walsCode := "koa", iso := "cku", value := .twoClasses }
  , { walsCode := "kob", iso := "kpw", value := .twoClasses }
  , { walsCode := "koi", iso := "kbk", value := .twoClasses }
  , { walsCode := "kln", iso := "kvw", value := .noPossessiveClassification }
  , { walsCode := "kzy", iso := "kpv", value := .noPossessiveClassification }
  , { walsCode := "knu", iso := "kyx", value := .twoClasses }
  , { walsCode := "kor", iso := "kor", value := .noPossessiveClassification }
  , { walsCode := "kch", iso := "khq", value := .twoClasses }
  , { walsCode := "kro", iso := "kgo", value := .twoClasses }
  , { walsCode := "kiu", iso := "kvd", value := .twoClasses }
  , { walsCode := "knm", iso := "kun", value := .twoClasses }
  , { walsCode := "kut", iso := "kut", value := .noPossessiveClassification }
  , { walsCode := "kat", iso := "kmg", value := .twoClasses }
  , { walsCode := "lkt", iso := "lkt", value := .twoClasses }
  , { walsCode := "lan", iso := "laj", value := .twoClasses }
  , { walsCode := "lav", iso := "lvk", value := .noPossessiveClassification }
  , { walsCode := "lez", iso := "lez", value := .noPossessiveClassification }
  , { walsCode := "lim", iso := "lif", value := .threeToFiveClasses }
  , { walsCode := "lda", iso := "lug", value := .twoClasses }
  , { walsCode := "lug", iso := "lgg", value := .twoClasses }
  , { walsCode := "luv", iso := "lue", value := .twoClasses }
  , { walsCode := "maa", iso := "mas", value := .twoClasses }
  , { walsCode := "mne", iso := "nmu", value := .twoClasses }
  , { walsCode := "mal", iso := "plt", value := .noPossessiveClassification }
  , { walsCode := "mlk", iso := "mpb", value := .twoClasses }
  , { walsCode := "mto", iso := "kmj", value := .noPossessiveClassification }
  , { walsCode := "mnd", iso := "cmn", value := .noPossessiveClassification }
  , { walsCode := "mdk", iso := "mnk", value := .noPossessiveClassification }
  , { walsCode := "myi", iso := "mpc", value := .twoClasses }
  , { walsCode := "mao", iso := "mri", value := .noPossessiveClassification }
  , { walsCode := "map", iso := "arn", value := .noPossessiveClassification }
  , { walsCode := "mrg", iso := "mrt", value := .twoClasses }
  , { walsCode := "mar", iso := "mrc", value := .threeToFiveClasses }
  , { walsCode := "mrh", iso := "mfr", value := .twoClasses }
  , { walsCode := "mrt", iso := "vma", value := .twoClasses }
  , { walsCode := "mau", iso := "mph", value := .twoClasses }
  , { walsCode := "may", iso := "ayz", value := .twoClasses }
  , { walsCode := "mei", iso := "mni", value := .noPossessiveClassification }
  , { walsCode := "mss", iso := "skd", value := .noPossessiveClassification }
  , { walsCode := "mxc", iso := "mig", value := .noPossessiveClassification }
  , { walsCode := "mot", iso := "siw", value := .twoClasses }
  , { walsCode := "mpa", iso := "mwf", value := .noPossessiveClassification }
  , { walsCode := "nah", iso := "nll", value := .noPossessiveClassification }
  , { walsCode := "nkk", iso := "nck", value := .threeToFiveClasses }
  , { walsCode := "kho", iso := "naq", value := .twoClasses }
  , { walsCode := "nai", iso := "gld", value := .twoClasses }
  , { walsCode := "nan", iso := "niq", value := .noPossessiveClassification }
  , { walsCode := "nar", iso := "nrb", value := .noPossessiveClassification }
  , { walsCode := "ntu", iso := "yrk", value := .noPossessiveClassification }
  , { walsCode := "nez", iso := "nez", value := .noPossessiveClassification }
  , { walsCode := "ngi", iso := "wyb", value := .twoClasses }
  , { walsCode := "nca", iso := "caq", value := .noPossessiveClassification }
  , { walsCode := "nim", iso := "nir", value := .twoClasses }
  , { walsCode := "nbd", iso := "dgl", value := .twoClasses }
  , { walsCode := "nug", iso := "nuy", value := .twoClasses }
  , { walsCode := "nyn", iso := "nyh", value := .twoClasses }
  , { walsCode := "ond", iso := "one", value := .noPossessiveClassification }
  , { walsCode := "ori", iso := "tag", value := .noPossessiveClassification }
  , { walsCode := "orh", iso := "hae", value := .twoClasses }
  , { walsCode := "oss", iso := "oss", value := .twoClasses }
  , { walsCode := "otm", iso := "ote", value := .noPossessiveClassification }
  , { walsCode := "pms", iso := "pma", value := .threeToFiveClasses }
  , { walsCode := "pai", iso := "pwn", value := .noPossessiveClassification }
  , { walsCode := "pau", iso := "pad", value := .twoClasses }
  , { walsCode := "pwn", iso := "paw", value := .twoClasses }
  , { walsCode := "prs", iso := "pes", value := .noPossessiveClassification }
  , { walsCode := "prh", iso := "myp", value := .noPossessiveClassification }
  , { walsCode := "poh", iso := "pon", value := .twoClasses }
  , { walsCode := "pso", iso := "pom", value := .threeToFiveClasses }
  , { walsCode := "qim", iso := "qvi", value := .noPossessiveClassification }
  , { walsCode := "qui", iso := "qui", value := .twoClasses }
  , { walsCode := "ram", iso := "rma", value := .twoClasses }
  , { walsCode := "rap", iso := "rap", value := .twoClasses }
  , { walsCode := "res", iso := "rgr", value := .noPossessiveClassification }
  , { walsCode := "rus", iso := "rus", value := .noPossessiveClassification }
  , { walsCode := "sah", iso := "saj", value := .noPossessiveClassification }
  , { walsCode := "sal", iso := "sln", value := .twoClasses }
  , { walsCode := "syu", iso := "sll", value := .threeToFiveClasses }
  , { walsCode := "sam", iso := "smo", value := .noPossessiveClassification }
  , { walsCode := "san", iso := "sag", value := .noPossessiveClassification }
  , { walsCode := "snm", iso := "xsu", value := .twoClasses }
  , { walsCode := "snt", iso := "set", value := .threeToFiveClasses }
  , { walsCode := "siu", iso := "sis", value := .threeToFiveClasses }
  , { walsCode := "sla", iso := "den", value := .threeToFiveClasses }
  , { walsCode := "spa", iso := "spa", value := .noPossessiveClassification }
  , { walsCode := "squ", iso := "squ", value := .noPossessiveClassification }
  , { walsCode := "sue", iso := "sue", value := .noPossessiveClassification }
  , { walsCode := "sul", iso := "sua", value := .twoClasses }
  , { walsCode := "sup", iso := "spp", value := .noPossessiveClassification }
  , { walsCode := "swa", iso := "swh", value := .noPossessiveClassification }
  , { walsCode := "tag", iso := "tgl", value := .noPossessiveClassification }
  , { walsCode := "tkl", iso := "tkm", value := .twoClasses }
  , { walsCode := "tgp", iso := "tpg", value := .twoClasses }
  , { walsCode := "tau", iso := "tya", value := .twoClasses }
  , { walsCode := "taw", iso := "tbo", value := .twoClasses }
  , { walsCode := "tht", iso := "kps", value := .twoClasses }
  , { walsCode := "tlf", iso := "tlf", value := .noPossessiveClassification }
  , { walsCode := "ter", iso := "ttr", value := .twoClasses }
  , { walsCode := "tha", iso := "tha", value := .noPossessiveClassification }
  , { walsCode := "tib", iso := "bod", value := .noPossessiveClassification }
  , { walsCode := "tiw", iso := "tiw", value := .twoClasses }
  , { walsCode := "tli", iso := "tli", value := .twoClasses }
  , { walsCode := "ton", iso := "tqw", value := .twoClasses }
  , { walsCode := "tot", iso := "tlc", value := .noPossessiveClassification }
  , { walsCode := "tru", iso := "tpy", value := .threeToFiveClasses }
  , { walsCode := "tuk", iso := "", value := .twoClasses }
  , { walsCode := "tun", iso := "tun", value := .twoClasses }
  , { walsCode := "tur", iso := "tur", value := .noPossessiveClassification }
  , { walsCode := "tuv", iso := "tyv", value := .noPossessiveClassification }
  , { walsCode := "tzu", iso := "tzj", value := .threeToFiveClasses }
  , { walsCode := "ung", iso := "ung", value := .threeToFiveClasses }
  , { walsCode := "uhi", iso := "urf", value := .twoClasses }
  , { walsCode := "vie", iso := "vie", value := .noPossessiveClassification }
  , { walsCode := "wap", iso := "wao", value := .noPossessiveClassification }
  , { walsCode := "wra", iso := "wba", value := .noPossessiveClassification }
  , { walsCode := "wry", iso := "wrz", value := .noPossessiveClassification }
  , { walsCode := "war", iso := "pav", value := .threeToFiveClasses }
  , { walsCode := "wrs", iso := "wrs", value := .noPossessiveClassification }
  , { walsCode := "wrl", iso := "wbp", value := .noPossessiveClassification }
  , { walsCode := "wrn", iso := "wnd", value := .twoClasses }
  , { walsCode := "was", iso := "was", value := .twoClasses }
  , { walsCode := "wsk", iso := "wsk", value := .twoClasses }
  , { walsCode := "wem", iso := "xww", value := .twoClasses }
  , { walsCode := "wic", iso := "wic", value := .noPossessiveClassification }
  , { walsCode := "wch", iso := "mzh", value := .threeToFiveClasses }
  , { walsCode := "win", iso := "wnw", value := .twoClasses }
  , { walsCode := "yag", iso := "yad", value := .noPossessiveClassification }
  , { walsCode := "yli", iso := "yli", value := .noPossessiveClassification }
  , { walsCode := "yaq", iso := "yaq", value := .noPossessiveClassification }
  , { walsCode := "yes", iso := "yss", value := .noPossessiveClassification }
  , { walsCode := "yim", iso := "yee", value := .noPossessiveClassification }
  , { walsCode := "yor", iso := "yor", value := .noPossessiveClassification }
  , { walsCode := "yuc", iso := "yuc", value := .threeToFiveClasses }
  , { walsCode := "yko", iso := "yux", value := .twoClasses }
  , { walsCode := "yur", iso := "yur", value := .twoClasses }
  , { walsCode := "zqc", iso := "zoc", value := .noPossessiveClassification }
  , { walsCode := "zul", iso := "zul", value := .noPossessiveClassification }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F59A
