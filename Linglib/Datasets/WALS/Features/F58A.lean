import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 58A: Obligatory Possessive Inflection
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 58A`.

Chapter 58, 244 languages.
-/

namespace Datasets.WALS.F58A

/-- WALS 58A values. -/
inductive ObligatoryPossessiveInflection where
  /-- Exists (43 languages). -/
  | exists
  /-- Absent (201 languages). -/
  | absent
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 58A dataset (244 languages). -/
def allData : List (Datapoint ObligatoryPossessiveInflection) :=
  [ { walsCode := "abk", iso := "abk", value := .absent }
  , { walsCode := "aco", iso := "kjq", value := .exists }
  , { walsCode := "ain", iso := "ain", value := .absent }
  , { walsCode := "ala", iso := "amp", value := .absent }
  , { walsCode := "alw", iso := "alh", value := .absent }
  , { walsCode := "ame", iso := "aey", value := .absent }
  , { walsCode := "amh", iso := "amh", value := .absent }
  , { walsCode := "ane", iso := "anz", value := .absent }
  , { walsCode := "apu", iso := "apu", value := .absent }
  , { walsCode := "aeg", iso := "arz", value := .absent }
  , { walsCode := "arp", iso := "ape", value := .absent }
  , { walsCode := "arm", iso := "hye", value := .absent }
  , { walsCode := "amp", iso := "aer", value := .absent }
  , { walsCode := "asm", iso := "cns", value := .exists }
  , { walsCode := "awp", iso := "kwi", value := .absent }
  , { walsCode := "awt", iso := "kmn", value := .absent }
  , { walsCode := "aym", iso := "ayr", value := .absent }
  , { walsCode := "bag", iso := "bmi", value := .absent }
  , { walsCode := "baa", iso := "bbb", value := .absent }
  , { walsCode := "brs", iso := "bsn", value := .exists }
  , { walsCode := "bsq", iso := "eus", value := .absent }
  , { walsCode := "bzi", iso := "bvz", value := .absent }
  , { walsCode := "bej", iso := "bej", value := .absent }
  , { walsCode := "bel", iso := "byw", value := .exists }
  , { walsCode := "bma", iso := "tzm", value := .absent }
  , { walsCode := "brk", iso := "bkl", value := .absent }
  , { walsCode := "boa", iso := "kvg", value := .absent }
  , { walsCode := "brr", iso := "bor", value := .absent }
  , { walsCode := "brh", iso := "brh", value := .absent }
  , { walsCode := "brm", iso := "mya", value := .absent }
  , { walsCode := "buu", iso := "mhs", value := .absent }
  , { walsCode := "bur", iso := "bsk", value := .exists }
  , { walsCode := "cax", iso := "", value := .exists }
  , { walsCode := "cnl", iso := "ram", value := .exists }
  , { walsCode := "cyv", iso := "cyb", value := .absent }
  , { walsCode := "cha", iso := "cha", value := .absent }
  , { walsCode := "chy", iso := "cbt", value := .absent }
  , { walsCode := "cjo", iso := "pei", value := .exists }
  , { walsCode := "chi", iso := "cid", value := .absent }
  , { walsCode := "ctm", iso := "ctm", value := .exists }
  , { walsCode := "cho", iso := "chd", value := .exists }
  , { walsCode := "chk", iso := "ckt", value := .absent }
  , { walsCode := "cin", iso := "inz", value := .exists }
  , { walsCode := "cre", iso := "crk", value := .exists }
  , { walsCode := "dag", iso := "dgz", value := .absent }
  , { walsCode := "dni", iso := "dni", value := .exists }
  , { walsCode := "die", iso := "dih", value := .exists }
  , { walsCode := "dig", iso := "mhu", value := .absent }
  , { walsCode := "diy", iso := "dif", value := .absent }
  , { walsCode := "diz", iso := "mdx", value := .absent }
  , { walsCode := "djp", iso := "dwu", value := .absent }
  , { walsCode := "dre", iso := "dhv", value := .absent }
  , { walsCode := "dum", iso := "vam", value := .absent }
  , { walsCode := "dyi", iso := "dbl", value := .absent }
  , { walsCode := "eka", iso := "ekg", value := .exists }
  , { walsCode := "eng", iso := "eng", value := .absent }
  , { walsCode := "epe", iso := "sja", value := .exists }
  , { walsCode := "eve", iso := "evn", value := .exists }
  , { walsCode := "ewe", iso := "ewe", value := .absent }
  , { walsCode := "fij", iso := "fij", value := .absent }
  , { walsCode := "fin", iso := "fin", value := .absent }
  , { walsCode := "fre", iso := "fra", value := .absent }
  , { walsCode := "fua", iso := "fub", value := .absent }
  , { walsCode := "fur", iso := "fvr", value := .absent }
  , { walsCode := "grr", iso := "wrk", value := .absent }
  , { walsCode := "gbb", iso := "gbp", value := .absent }
  , { walsCode := "geo", iso := "kat", value := .absent }
  , { walsCode := "ger", iso := "deu", value := .absent }
  , { walsCode := "goo", iso := "gni", value := .absent }
  , { walsCode := "grb", iso := "grj", value := .absent }
  , { walsCode := "grk", iso := "ell", value := .absent }
  , { walsCode := "grw", iso := "kal", value := .absent }
  , { walsCode := "gua", iso := "gug", value := .absent }
  , { walsCode := "gmz", iso := "guk", value := .absent }
  , { walsCode := "hai", iso := "hai", value := .exists }
  , { walsCode := "hat", iso := "had", value := .exists }
  , { walsCode := "hau", iso := "hau", value := .absent }
  , { walsCode := "heb", iso := "heb", value := .absent }
  , { walsCode := "hin", iso := "hin", value := .absent }
  , { walsCode := "hix", iso := "hix", value := .exists }
  , { walsCode := "hmo", iso := "hnj", value := .absent }
  , { walsCode := "hua", iso := "ygr", value := .absent }
  , { walsCode := "hve", iso := "huv", value := .absent }
  , { walsCode := "hun", iso := "hun", value := .absent }
  , { walsCode := "iau", iso := "tmu", value := .absent }
  , { walsCode := "ijo", iso := "ijc", value := .absent }
  , { walsCode := "ik", iso := "ikx", value := .absent }
  , { walsCode := "imo", iso := "imn", value := .absent }
  , { walsCode := "ind", iso := "ind", value := .absent }
  , { walsCode := "ing", iso := "inh", value := .absent }
  , { walsCode := "jak", iso := "jac", value := .absent }
  , { walsCode := "jpn", iso := "jpn", value := .absent }
  , { walsCode := "juh", iso := "ktz", value := .absent }
  , { walsCode := "knk", iso := "kna", value := .absent }
  , { walsCode := "knd", iso := "kan", value := .absent }
  , { walsCode := "knp", iso := "kcd", value := .absent }
  , { walsCode := "knr", iso := "knc", value := .absent }
  , { walsCode := "krk", iso := "kyh", value := .exists }
  , { walsCode := "kay", iso := "gyd", value := .absent }
  , { walsCode := "ket", iso := "ket", value := .absent }
  , { walsCode := "kew", iso := "kew", value := .absent }
  , { walsCode := "kha", iso := "khk", value := .absent }
  , { walsCode := "khs", iso := "kha", value := .absent }
  , { walsCode := "kim", iso := "kig", value := .absent }
  , { walsCode := "kio", iso := "kio", value := .absent }
  , { walsCode := "kri", iso := "kzw", value := .absent }
  , { walsCode := "koa", iso := "cku", value := .exists }
  , { walsCode := "kob", iso := "kpw", value := .absent }
  , { walsCode := "koi", iso := "kbk", value := .exists }
  , { walsCode := "kln", iso := "kvw", value := .absent }
  , { walsCode := "kzy", iso := "kpv", value := .absent }
  , { walsCode := "knu", iso := "kyx", value := .absent }
  , { walsCode := "kor", iso := "kor", value := .absent }
  , { walsCode := "kch", iso := "khq", value := .absent }
  , { walsCode := "kro", iso := "kgo", value := .absent }
  , { walsCode := "kiu", iso := "kvd", value := .exists }
  , { walsCode := "knm", iso := "kun", value := .absent }
  , { walsCode := "kut", iso := "kut", value := .exists }
  , { walsCode := "kat", iso := "kmg", value := .absent }
  , { walsCode := "lkt", iso := "lkt", value := .absent }
  , { walsCode := "lan", iso := "laj", value := .absent }
  , { walsCode := "lav", iso := "lvk", value := .absent }
  , { walsCode := "lez", iso := "lez", value := .absent }
  , { walsCode := "lim", iso := "lif", value := .exists }
  , { walsCode := "lda", iso := "lug", value := .absent }
  , { walsCode := "lug", iso := "lgg", value := .absent }
  , { walsCode := "luv", iso := "lue", value := .absent }
  , { walsCode := "maa", iso := "mas", value := .absent }
  , { walsCode := "mne", iso := "nmu", value := .exists }
  , { walsCode := "mal", iso := "plt", value := .absent }
  , { walsCode := "mlk", iso := "mpb", value := .absent }
  , { walsCode := "mto", iso := "kmj", value := .absent }
  , { walsCode := "mnd", iso := "cmn", value := .absent }
  , { walsCode := "mdk", iso := "mnk", value := .absent }
  , { walsCode := "myi", iso := "mpc", value := .absent }
  , { walsCode := "mao", iso := "mri", value := .absent }
  , { walsCode := "map", iso := "arn", value := .absent }
  , { walsCode := "mrg", iso := "mrt", value := .absent }
  , { walsCode := "mar", iso := "mrc", value := .absent }
  , { walsCode := "mrh", iso := "mfr", value := .absent }
  , { walsCode := "mrt", iso := "vma", value := .absent }
  , { walsCode := "mau", iso := "mph", value := .absent }
  , { walsCode := "may", iso := "ayz", value := .absent }
  , { walsCode := "mei", iso := "mni", value := .absent }
  , { walsCode := "mss", iso := "skd", value := .absent }
  , { walsCode := "mxc", iso := "mig", value := .absent }
  , { walsCode := "mot", iso := "siw", value := .absent }
  , { walsCode := "mpa", iso := "mwf", value := .absent }
  , { walsCode := "nah", iso := "nll", value := .absent }
  , { walsCode := "nkk", iso := "nck", value := .absent }
  , { walsCode := "kho", iso := "naq", value := .exists }
  , { walsCode := "nai", iso := "gld", value := .absent }
  , { walsCode := "nan", iso := "niq", value := .absent }
  , { walsCode := "nar", iso := "nrb", value := .absent }
  , { walsCode := "ntu", iso := "yrk", value := .absent }
  , { walsCode := "nez", iso := "nez", value := .exists }
  , { walsCode := "ngi", iso := "wyb", value := .absent }
  , { walsCode := "nca", iso := "caq", value := .absent }
  , { walsCode := "nim", iso := "nir", value := .absent }
  , { walsCode := "nbd", iso := "dgl", value := .absent }
  , { walsCode := "nug", iso := "nuy", value := .absent }
  , { walsCode := "nyn", iso := "nyh", value := .absent }
  , { walsCode := "ond", iso := "one", value := .absent }
  , { walsCode := "ori", iso := "tag", value := .absent }
  , { walsCode := "orh", iso := "hae", value := .absent }
  , { walsCode := "oss", iso := "oss", value := .exists }
  , { walsCode := "otm", iso := "ote", value := .absent }
  , { walsCode := "pms", iso := "pma", value := .exists }
  , { walsCode := "pai", iso := "pwn", value := .absent }
  , { walsCode := "pnr", iso := "pbh", value := .absent }
  , { walsCode := "pau", iso := "pad", value := .absent }
  , { walsCode := "pwn", iso := "paw", value := .exists }
  , { walsCode := "prs", iso := "pes", value := .absent }
  , { walsCode := "prh", iso := "myp", value := .absent }
  , { walsCode := "poh", iso := "pon", value := .absent }
  , { walsCode := "pso", iso := "pom", value := .absent }
  , { walsCode := "qim", iso := "qvi", value := .absent }
  , { walsCode := "qui", iso := "qui", value := .exists }
  , { walsCode := "ram", iso := "rma", value := .absent }
  , { walsCode := "rap", iso := "rap", value := .absent }
  , { walsCode := "res", iso := "rgr", value := .exists }
  , { walsCode := "rus", iso := "rus", value := .absent }
  , { walsCode := "sah", iso := "saj", value := .absent }
  , { walsCode := "sal", iso := "sln", value := .exists }
  , { walsCode := "syu", iso := "sll", value := .absent }
  , { walsCode := "sam", iso := "smo", value := .absent }
  , { walsCode := "san", iso := "sag", value := .absent }
  , { walsCode := "snm", iso := "xsu", value := .absent }
  , { walsCode := "snt", iso := "set", value := .absent }
  , { walsCode := "siu", iso := "sis", value := .absent }
  , { walsCode := "sla", iso := "den", value := .absent }
  , { walsCode := "spa", iso := "spa", value := .absent }
  , { walsCode := "squ", iso := "squ", value := .absent }
  , { walsCode := "sue", iso := "sue", value := .absent }
  , { walsCode := "sul", iso := "sua", value := .absent }
  , { walsCode := "sup", iso := "spp", value := .absent }
  , { walsCode := "swa", iso := "swh", value := .absent }
  , { walsCode := "tag", iso := "tgl", value := .absent }
  , { walsCode := "tkl", iso := "tkm", value := .absent }
  , { walsCode := "tgp", iso := "tpg", value := .exists }
  , { walsCode := "tau", iso := "tya", value := .absent }
  , { walsCode := "taw", iso := "tbo", value := .absent }
  , { walsCode := "tht", iso := "kps", value := .absent }
  , { walsCode := "tlf", iso := "tlf", value := .absent }
  , { walsCode := "ter", iso := "ttr", value := .absent }
  , { walsCode := "tha", iso := "tha", value := .absent }
  , { walsCode := "tib", iso := "bod", value := .absent }
  , { walsCode := "tiw", iso := "tiw", value := .exists }
  , { walsCode := "tli", iso := "tli", value := .absent }
  , { walsCode := "ton", iso := "tqw", value := .absent }
  , { walsCode := "tot", iso := "tlc", value := .exists }
  , { walsCode := "tru", iso := "tpy", value := .absent }
  , { walsCode := "tuk", iso := "", value := .absent }
  , { walsCode := "tun", iso := "tun", value := .exists }
  , { walsCode := "tur", iso := "tur", value := .absent }
  , { walsCode := "tuv", iso := "tyv", value := .absent }
  , { walsCode := "tzu", iso := "tzj", value := .exists }
  , { walsCode := "ung", iso := "ung", value := .absent }
  , { walsCode := "uhi", iso := "urf", value := .absent }
  , { walsCode := "vie", iso := "vie", value := .absent }
  , { walsCode := "wap", iso := "wao", value := .exists }
  , { walsCode := "wra", iso := "wba", value := .absent }
  , { walsCode := "wry", iso := "wrz", value := .absent }
  , { walsCode := "war", iso := "pav", value := .absent }
  , { walsCode := "wrs", iso := "wrs", value := .absent }
  , { walsCode := "wrl", iso := "wbp", value := .absent }
  , { walsCode := "wrn", iso := "wnd", value := .absent }
  , { walsCode := "was", iso := "was", value := .absent }
  , { walsCode := "wsk", iso := "wsk", value := .absent }
  , { walsCode := "wem", iso := "xww", value := .absent }
  , { walsCode := "wic", iso := "wic", value := .absent }
  , { walsCode := "wch", iso := "mzh", value := .exists }
  , { walsCode := "win", iso := "wnw", value := .exists }
  , { walsCode := "yag", iso := "yad", value := .absent }
  , { walsCode := "yli", iso := "yli", value := .absent }
  , { walsCode := "yaq", iso := "yaq", value := .absent }
  , { walsCode := "yes", iso := "yss", value := .absent }
  , { walsCode := "yim", iso := "yee", value := .absent }
  , { walsCode := "yor", iso := "yor", value := .absent }
  , { walsCode := "yuc", iso := "yuc", value := .absent }
  , { walsCode := "yko", iso := "yux", value := .absent }
  , { walsCode := "yur", iso := "yur", value := .absent }
  , { walsCode := "zqc", iso := "zoc", value := .absent }
  , { walsCode := "zul", iso := "zul", value := .absent }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F58A
