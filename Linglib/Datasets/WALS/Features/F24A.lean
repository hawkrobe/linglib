import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 24A: Locus of Marking in Possessive Noun Phrases
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 24A`.

Chapter 24, 236 languages.
-/

namespace Datasets.WALS.F24A

/-- WALS 24A values. -/
inductive LocusOfMarkingInPossessiveNounPhrases where
  /-- Head marking (78 languages). -/
  | headMarking
  /-- Dependent marking (98 languages). -/
  | dependentMarking
  /-- Double marking (22 languages). -/
  | doubleMarking
  /-- No marking (32 languages). -/
  | noMarking
  /-- Other (6 languages). -/
  | other
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 24A dataset (236 languages). -/
def allData : List (Datapoint LocusOfMarkingInPossessiveNounPhrases) :=
  [ { walsCode := "abk", iso := "abk", value := .headMarking }
  , { walsCode := "ace", iso := "ace", value := .headMarking }
  , { walsCode := "aco", iso := "kjq", value := .headMarking }
  , { walsCode := "ain", iso := "ain", value := .headMarking }
  , { walsCode := "ala", iso := "amp", value := .dependentMarking }
  , { walsCode := "amb", iso := "abt", value := .dependentMarking }
  , { walsCode := "ame", iso := "aey", value := .dependentMarking }
  , { walsCode := "ane", iso := "anz", value := .headMarking }
  , { walsCode := "apu", iso := "apu", value := .headMarking }
  , { walsCode := "aeg", iso := "arz", value := .noMarking }
  , { walsCode := "arp", iso := "ape", value := .dependentMarking }
  , { walsCode := "amp", iso := "aer", value := .dependentMarking }
  , { walsCode := "asm", iso := "cns", value := .noMarking }
  , { walsCode := "atk", iso := "aqp", value := .noMarking }
  , { walsCode := "awp", iso := "kwi", value := .dependentMarking }
  , { walsCode := "awt", iso := "kmn", value := .dependentMarking }
  , { walsCode := "aym", iso := "ayr", value := .doubleMarking }
  , { walsCode := "bag", iso := "bmi", value := .noMarking }
  , { walsCode := "brs", iso := "bsn", value := .headMarking }
  , { walsCode := "bsq", iso := "eus", value := .dependentMarking }
  , { walsCode := "bzi", iso := "bvz", value := .dependentMarking }
  , { walsCode := "bej", iso := "bej", value := .dependentMarking }
  , { walsCode := "bel", iso := "byw", value := .doubleMarking }
  , { walsCode := "bma", iso := "tzm", value := .dependentMarking }
  , { walsCode := "bbw", iso := "gup", value := .dependentMarking }
  , { walsCode := "brr", iso := "bor", value := .headMarking }
  , { walsCode := "brh", iso := "brh", value := .dependentMarking }
  , { walsCode := "bri", iso := "bzd", value := .noMarking }
  , { walsCode := "brm", iso := "mya", value := .dependentMarking }
  , { walsCode := "buu", iso := "mhs", value := .headMarking }
  , { walsCode := "bur", iso := "bsk", value := .doubleMarking }
  , { walsCode := "cnl", iso := "ram", value := .dependentMarking }
  , { walsCode := "cyv", iso := "cyb", value := .headMarking }
  , { walsCode := "cha", iso := "cha", value := .headMarking }
  , { walsCode := "chy", iso := "cbt", value := .noMarking }
  , { walsCode := "cjo", iso := "pei", value := .headMarking }
  , { walsCode := "cku", iso := "wac", value := .headMarking }
  , { walsCode := "ctm", iso := "ctm", value := .noMarking }
  , { walsCode := "cho", iso := "chd", value := .headMarking }
  , { walsCode := "chk", iso := "ckt", value := .noMarking }
  , { walsCode := "cin", iso := "inz", value := .headMarking }
  , { walsCode := "ccp", iso := "coc", value := .headMarking }
  , { walsCode := "coo", iso := "csz", value := .headMarking }
  , { walsCode := "cre", iso := "crk", value := .headMarking }
  , { walsCode := "dag", iso := "dgz", value := .headMarking }
  , { walsCode := "dni", iso := "dni", value := .doubleMarking }
  , { walsCode := "diy", iso := "dif", value := .dependentMarking }
  , { walsCode := "diz", iso := "mdx", value := .doubleMarking }
  , { walsCode := "djp", iso := "dwu", value := .dependentMarking }
  , { walsCode := "dji", iso := "jig", value := .doubleMarking }
  , { walsCode := "dum", iso := "vam", value := .headMarking }
  , { walsCode := "dyi", iso := "dbl", value := .dependentMarking }
  , { walsCode := "eka", iso := "ekg", value := .noMarking }
  , { walsCode := "eng", iso := "eng", value := .dependentMarking }
  , { walsCode := "epe", iso := "sja", value := .noMarking }
  , { walsCode := "eve", iso := "evn", value := .doubleMarking }
  , { walsCode := "ewe", iso := "ewe", value := .dependentMarking }
  , { walsCode := "fij", iso := "fij", value := .headMarking }
  , { walsCode := "fin", iso := "fin", value := .doubleMarking }
  , { walsCode := "fre", iso := "fra", value := .dependentMarking }
  , { walsCode := "fur", iso := "fvr", value := .dependentMarking }
  , { walsCode := "grr", iso := "wrk", value := .dependentMarking }
  , { walsCode := "geo", iso := "kat", value := .dependentMarking }
  , { walsCode := "ger", iso := "deu", value := .dependentMarking }
  , { walsCode := "goo", iso := "gni", value := .dependentMarking }
  , { walsCode := "grb", iso := "grj", value := .dependentMarking }
  , { walsCode := "grk", iso := "ell", value := .doubleMarking }
  , { walsCode := "grw", iso := "kal", value := .doubleMarking }
  , { walsCode := "gua", iso := "gug", value := .headMarking }
  , { walsCode := "gmz", iso := "guk", value := .noMarking }
  , { walsCode := "gku", iso := "pue", value := .headMarking }
  , { walsCode := "hai", iso := "hai", value := .headMarking }
  , { walsCode := "hat", iso := "had", value := .headMarking }
  , { walsCode := "hau", iso := "hau", value := .dependentMarking }
  , { walsCode := "heb", iso := "heb", value := .dependentMarking }
  , { walsCode := "hin", iso := "hin", value := .dependentMarking }
  , { walsCode := "hix", iso := "hix", value := .headMarking }
  , { walsCode := "hmo", iso := "hnj", value := .dependentMarking }
  , { walsCode := "hua", iso := "ygr", value := .doubleMarking }
  , { walsCode := "hve", iso := "huv", value := .headMarking }
  , { walsCode := "hun", iso := "hun", value := .headMarking }
  , { walsCode := "iau", iso := "tmu", value := .headMarking }
  , { walsCode := "ice", iso := "isl", value := .dependentMarking }
  , { walsCode := "ijo", iso := "ijc", value := .noMarking }
  , { walsCode := "ik", iso := "ikx", value := .dependentMarking }
  , { walsCode := "ika", iso := "arh", value := .dependentMarking }
  , { walsCode := "imo", iso := "imn", value := .doubleMarking }
  , { walsCode := "ind", iso := "ind", value := .noMarking }
  , { walsCode := "ing", iso := "inh", value := .dependentMarking }
  , { walsCode := "jak", iso := "jac", value := .headMarking }
  , { walsCode := "jpn", iso := "jpn", value := .dependentMarking }
  , { walsCode := "jel", iso := "jek", value := .dependentMarking }
  , { walsCode := "jiv", iso := "jiv", value := .doubleMarking }
  , { walsCode := "juh", iso := "ktz", value := .noMarking }
  , { walsCode := "knd", iso := "kan", value := .dependentMarking }
  , { walsCode := "knp", iso := "kcd", value := .dependentMarking }
  , { walsCode := "knr", iso := "knc", value := .dependentMarking }
  , { walsCode := "krk", iso := "kyh", value := .headMarking }
  , { walsCode := "kay", iso := "gyd", value := .dependentMarking }
  , { walsCode := "ket", iso := "ket", value := .headMarking }
  , { walsCode := "kew", iso := "kew", value := .dependentMarking }
  , { walsCode := "kha", iso := "khk", value := .dependentMarking }
  , { walsCode := "kim", iso := "kig", value := .dependentMarking }
  , { walsCode := "kio", iso := "kio", value := .headMarking }
  , { walsCode := "kri", iso := "kzw", value := .doubleMarking }
  , { walsCode := "kkr", iso := "kiy", value := .noMarking }
  , { walsCode := "kis", iso := "kss", value := .dependentMarking }
  , { walsCode := "koa", iso := "cku", value := .headMarking }
  , { walsCode := "kob", iso := "kpw", value := .noMarking }
  , { walsCode := "kmb", iso := "", value := .dependentMarking }
  , { walsCode := "kor", iso := "kor", value := .dependentMarking }
  , { walsCode := "kch", iso := "khq", value := .dependentMarking }
  , { walsCode := "kro", iso := "kgo", value := .dependentMarking }
  , { walsCode := "kiu", iso := "kvd", value := .headMarking }
  , { walsCode := "knm", iso := "kun", value := .dependentMarking }
  , { walsCode := "kut", iso := "kut", value := .headMarking }
  , { walsCode := "lai", iso := "cnh", value := .noMarking }
  , { walsCode := "lkt", iso := "lkt", value := .headMarking }
  , { walsCode := "lmh", iso := "slp", value := .noMarking }
  , { walsCode := "lan", iso := "laj", value := .headMarking }
  , { walsCode := "lav", iso := "lvk", value := .headMarking }
  , { walsCode := "lez", iso := "lez", value := .dependentMarking }
  , { walsCode := "lug", iso := "lgg", value := .dependentMarking }
  , { walsCode := "luv", iso := "lue", value := .dependentMarking }
  , { walsCode := "mai", iso := "mai", value := .dependentMarking }
  , { walsCode := "mal", iso := "plt", value := .other }
  , { walsCode := "mlk", iso := "mpb", value := .dependentMarking }
  , { walsCode := "mnd", iso := "cmn", value := .dependentMarking }
  , { walsCode := "myi", iso := "mpc", value := .doubleMarking }
  , { walsCode := "mao", iso := "mri", value := .dependentMarking }
  , { walsCode := "map", iso := "arn", value := .headMarking }
  , { walsCode := "mar", iso := "mrc", value := .headMarking }
  , { walsCode := "mrh", iso := "mfr", value := .headMarking }
  , { walsCode := "mrt", iso := "vma", value := .dependentMarking }
  , { walsCode := "mau", iso := "mph", value := .noMarking }
  , { walsCode := "may", iso := "ayz", value := .dependentMarking }
  , { walsCode := "mei", iso := "mni", value := .dependentMarking }
  , { walsCode := "mis", iso := "miq", value := .headMarking }
  , { walsCode := "mss", iso := "skd", value := .doubleMarking }
  , { walsCode := "mxc", iso := "mig", value := .noMarking }
  , { walsCode := "mot", iso := "siw", value := .dependentMarking }
  , { walsCode := "mun", iso := "unr", value := .dependentMarking }
  , { walsCode := "mpa", iso := "mwf", value := .noMarking }
  , { walsCode := "nah", iso := "nll", value := .dependentMarking }
  , { walsCode := "nkk", iso := "nck", value := .other }
  , { walsCode := "kho", iso := "naq", value := .dependentMarking }
  , { walsCode := "nmb", iso := "nab", value := .headMarking }
  , { walsCode := "nar", iso := "nrb", value := .noMarking }
  , { walsCode := "nat", iso := "ncz", value := .headMarking }
  , { walsCode := "ntu", iso := "yrk", value := .dependentMarking }
  , { walsCode := "nep", iso := "npi", value := .dependentMarking }
  , { walsCode := "ntj", iso := "ntj", value := .dependentMarking }
  , { walsCode := "ngi", iso := "wyb", value := .dependentMarking }
  , { walsCode := "nca", iso := "caq", value := .noMarking }
  , { walsCode := "nsg", iso := "ncg", value := .headMarking }
  , { walsCode := "niv", iso := "niv", value := .headMarking }
  , { walsCode := "nbd", iso := "dgl", value := .dependentMarking }
  , { walsCode := "nug", iso := "nuy", value := .dependentMarking }
  , { walsCode := "nuu", iso := "nuk", value := .headMarking }
  , { walsCode := "nyn", iso := "nyh", value := .dependentMarking }
  , { walsCode := "ond", iso := "one", value := .headMarking }
  , { walsCode := "ori", iso := "tag", value := .dependentMarking }
  , { walsCode := "orh", iso := "hae", value := .other }
  , { walsCode := "otm", iso := "ote", value := .headMarking }
  , { walsCode := "pai", iso := "pwn", value := .doubleMarking }
  , { walsCode := "pau", iso := "pad", value := .headMarking }
  , { walsCode := "prs", iso := "pes", value := .headMarking }
  , { walsCode := "pip", iso := "ppl", value := .headMarking }
  , { walsCode := "prh", iso := "myp", value := .noMarking }
  , { walsCode := "pso", iso := "pom", value := .dependentMarking }
  , { walsCode := "pur", iso := "tsz", value := .dependentMarking }
  , { walsCode := "qim", iso := "qvi", value := .dependentMarking }
  , { walsCode := "qui", iso := "qui", value := .headMarking }
  , { walsCode := "ram", iso := "rma", value := .other }
  , { walsCode := "rap", iso := "rap", value := .dependentMarking }
  , { walsCode := "rus", iso := "rus", value := .dependentMarking }
  , { walsCode := "sah", iso := "saj", value := .headMarking }
  , { walsCode := "syu", iso := "sll", value := .noMarking }
  , { walsCode := "sdw", iso := "sad", value := .noMarking }
  , { walsCode := "san", iso := "sag", value := .dependentMarking }
  , { walsCode := "snm", iso := "xsu", value := .dependentMarking }
  , { walsCode := "sml", iso := "sza", value := .noMarking }
  , { walsCode := "shk", iso := "shp", value := .dependentMarking }
  , { walsCode := "siu", iso := "sis", value := .dependentMarking }
  , { walsCode := "sla", iso := "den", value := .headMarking }
  , { walsCode := "spa", iso := "spa", value := .dependentMarking }
  , { walsCode := "squ", iso := "squ", value := .headMarking }
  , { walsCode := "sue", iso := "sue", value := .dependentMarking }
  , { walsCode := "sup", iso := "spp", value := .headMarking }
  , { walsCode := "swa", iso := "swh", value := .dependentMarking }
  , { walsCode := "tag", iso := "tgl", value := .other }
  , { walsCode := "tkl", iso := "tkm", value := .headMarking }
  , { walsCode := "tgp", iso := "tpg", value := .headMarking }
  , { walsCode := "tau", iso := "tya", value := .dependentMarking }
  , { walsCode := "tlf", iso := "tlf", value := .headMarking }
  , { walsCode := "tha", iso := "tha", value := .dependentMarking }
  , { walsCode := "tib", iso := "bod", value := .dependentMarking }
  , { walsCode := "tmc", iso := "tjm", value := .noMarking }
  , { walsCode := "tiw", iso := "tiw", value := .noMarking }
  , { walsCode := "tli", iso := "tli", value := .headMarking }
  , { walsCode := "ton", iso := "tqw", value := .dependentMarking }
  , { walsCode := "tru", iso := "tpy", value := .dependentMarking }
  , { walsCode := "tuk", iso := "", value := .dependentMarking }
  , { walsCode := "tun", iso := "tun", value := .headMarking }
  , { walsCode := "tur", iso := "tur", value := .doubleMarking }
  , { walsCode := "tsh", iso := "par", value := .dependentMarking }
  , { walsCode := "ung", iso := "ung", value := .dependentMarking }
  , { walsCode := "uhi", iso := "urf", value := .dependentMarking }
  , { walsCode := "usa", iso := "wnu", value := .headMarking }
  , { walsCode := "vie", iso := "vie", value := .noMarking }
  , { walsCode := "wao", iso := "auc", value := .noMarking }
  , { walsCode := "wra", iso := "wba", value := .other }
  , { walsCode := "wry", iso := "wrz", value := .dependentMarking }
  , { walsCode := "war", iso := "pav", value := .headMarking }
  , { walsCode := "wrl", iso := "wbp", value := .dependentMarking }
  , { walsCode := "wrn", iso := "wnd", value := .headMarking }
  , { walsCode := "was", iso := "was", value := .headMarking }
  , { walsCode := "wsk", iso := "wsk", value := .headMarking }
  , { walsCode := "wem", iso := "xww", value := .doubleMarking }
  , { walsCode := "wic", iso := "wic", value := .headMarking }
  , { walsCode := "wch", iso := "mzh", value := .headMarking }
  , { walsCode := "win", iso := "wnw", value := .dependentMarking }
  , { walsCode := "xok", iso := "xok", value := .headMarking }
  , { walsCode := "yag", iso := "yad", value := .headMarking }
  , { walsCode := "yli", iso := "yli", value := .headMarking }
  , { walsCode := "yaq", iso := "yaq", value := .doubleMarking }
  , { walsCode := "yes", iso := "yss", value := .headMarking }
  , { walsCode := "yim", iso := "yee", value := .dependentMarking }
  , { walsCode := "yor", iso := "yor", value := .headMarking }
  , { walsCode := "yuc", iso := "yuc", value := .headMarking }
  , { walsCode := "yko", iso := "yux", value := .noMarking }
  , { walsCode := "ypk", iso := "esu", value := .doubleMarking }
  , { walsCode := "yur", iso := "yur", value := .headMarking }
  , { walsCode := "zqc", iso := "zoc", value := .doubleMarking }
  , { walsCode := "zul", iso := "zul", value := .dependentMarking }
  , { walsCode := "zun", iso := "zun", value := .headMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F24A
