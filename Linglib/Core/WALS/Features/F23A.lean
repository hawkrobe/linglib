import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 23A: Locus of Marking in the Clause
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 23A`.

Chapter 23, 236 languages.
-/

namespace Core.WALS.F23A

/-- WALS 23A values. -/
inductive LocusOfMarkingInTheClause where
  /-- Head marking (71 languages). -/
  | headMarking
  /-- Dependent marking (63 languages). -/
  | dependentMarking
  /-- Double marking (58 languages). -/
  | doubleMarking
  /-- No marking (42 languages). -/
  | noMarking
  /-- Other (2 languages). -/
  | other
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 23A dataset (236 languages). -/
def allData : List (Datapoint LocusOfMarkingInTheClause) :=
  [ { walsCode := "abk", iso := "abk", value := .headMarking }
  , { walsCode := "ace", iso := "ace", value := .headMarking }
  , { walsCode := "aco", iso := "kjq", value := .headMarking }
  , { walsCode := "ain", iso := "ain", value := .noMarking }
  , { walsCode := "ala", iso := "amp", value := .headMarking }
  , { walsCode := "amb", iso := "abt", value := .dependentMarking }
  , { walsCode := "ame", iso := "aey", value := .headMarking }
  , { walsCode := "ane", iso := "anz", value := .headMarking }
  , { walsCode := "apu", iso := "apu", value := .headMarking }
  , { walsCode := "aeg", iso := "arz", value := .noMarking }
  , { walsCode := "arp", iso := "ape", value := .headMarking }
  , { walsCode := "amp", iso := "aer", value := .dependentMarking }
  , { walsCode := "asm", iso := "cns", value := .headMarking }
  , { walsCode := "atk", iso := "aqp", value := .headMarking }
  , { walsCode := "awp", iso := "kwi", value := .doubleMarking }
  , { walsCode := "awt", iso := "kmn", value := .dependentMarking }
  , { walsCode := "aym", iso := "ayr", value := .doubleMarking }
  , { walsCode := "bag", iso := "bmi", value := .headMarking }
  , { walsCode := "brs", iso := "bsn", value := .doubleMarking }
  , { walsCode := "bsq", iso := "eus", value := .doubleMarking }
  , { walsCode := "bzi", iso := "bvz", value := .noMarking }
  , { walsCode := "bej", iso := "bej", value := .dependentMarking }
  , { walsCode := "bel", iso := "byw", value := .doubleMarking }
  , { walsCode := "bma", iso := "tzm", value := .dependentMarking }
  , { walsCode := "bbw", iso := "gup", value := .headMarking }
  , { walsCode := "brr", iso := "bor", value := .headMarking }
  , { walsCode := "brh", iso := "brh", value := .dependentMarking }
  , { walsCode := "bri", iso := "bzd", value := .noMarking }
  , { walsCode := "brm", iso := "mya", value := .dependentMarking }
  , { walsCode := "buu", iso := "mhs", value := .noMarking }
  , { walsCode := "bur", iso := "bsk", value := .doubleMarking }
  , { walsCode := "cnl", iso := "ram", value := .headMarking }
  , { walsCode := "cyv", iso := "cyb", value := .noMarking }
  , { walsCode := "cha", iso := "cha", value := .dependentMarking }
  , { walsCode := "chy", iso := "cbt", value := .doubleMarking }
  , { walsCode := "cjo", iso := "pei", value := .headMarking }
  , { walsCode := "cku", iso := "wac", value := .headMarking }
  , { walsCode := "ctm", iso := "ctm", value := .headMarking }
  , { walsCode := "cho", iso := "chd", value := .headMarking }
  , { walsCode := "chk", iso := "ckt", value := .doubleMarking }
  , { walsCode := "cin", iso := "inz", value := .headMarking }
  , { walsCode := "ccp", iso := "coc", value := .doubleMarking }
  , { walsCode := "coo", iso := "csz", value := .headMarking }
  , { walsCode := "cre", iso := "crk", value := .headMarking }
  , { walsCode := "dag", iso := "dgz", value := .headMarking }
  , { walsCode := "dni", iso := "dni", value := .headMarking }
  , { walsCode := "diy", iso := "dif", value := .dependentMarking }
  , { walsCode := "diz", iso := "mdx", value := .dependentMarking }
  , { walsCode := "djp", iso := "dwu", value := .dependentMarking }
  , { walsCode := "dji", iso := "jig", value := .doubleMarking }
  , { walsCode := "dum", iso := "vam", value := .noMarking }
  , { walsCode := "dyi", iso := "dbl", value := .dependentMarking }
  , { walsCode := "eka", iso := "ekg", value := .headMarking }
  , { walsCode := "eng", iso := "eng", value := .dependentMarking }
  , { walsCode := "epe", iso := "sja", value := .dependentMarking }
  , { walsCode := "eve", iso := "evn", value := .dependentMarking }
  , { walsCode := "ewe", iso := "ewe", value := .noMarking }
  , { walsCode := "fij", iso := "fij", value := .headMarking }
  , { walsCode := "fin", iso := "fin", value := .dependentMarking }
  , { walsCode := "fre", iso := "fra", value := .noMarking }
  , { walsCode := "fur", iso := "fvr", value := .dependentMarking }
  , { walsCode := "grr", iso := "wrk", value := .dependentMarking }
  , { walsCode := "geo", iso := "kat", value := .doubleMarking }
  , { walsCode := "ger", iso := "deu", value := .dependentMarking }
  , { walsCode := "goo", iso := "gni", value := .doubleMarking }
  , { walsCode := "grb", iso := "grj", value := .dependentMarking }
  , { walsCode := "grk", iso := "ell", value := .doubleMarking }
  , { walsCode := "grw", iso := "kal", value := .doubleMarking }
  , { walsCode := "gua", iso := "gug", value := .headMarking }
  , { walsCode := "gmz", iso := "guk", value := .dependentMarking }
  , { walsCode := "gku", iso := "pue", value := .noMarking }
  , { walsCode := "hai", iso := "hai", value := .noMarking }
  , { walsCode := "hat", iso := "had", value := .noMarking }
  , { walsCode := "hau", iso := "hau", value := .doubleMarking }
  , { walsCode := "heb", iso := "heb", value := .dependentMarking }
  , { walsCode := "hin", iso := "hin", value := .doubleMarking }
  , { walsCode := "hix", iso := "hix", value := .headMarking }
  , { walsCode := "hmo", iso := "hnj", value := .noMarking }
  , { walsCode := "hua", iso := "ygr", value := .doubleMarking }
  , { walsCode := "hve", iso := "huv", value := .headMarking }
  , { walsCode := "hun", iso := "hun", value := .dependentMarking }
  , { walsCode := "iau", iso := "tmu", value := .noMarking }
  , { walsCode := "ice", iso := "isl", value := .dependentMarking }
  , { walsCode := "ijo", iso := "ijc", value := .noMarking }
  , { walsCode := "ik", iso := "ikx", value := .dependentMarking }
  , { walsCode := "ika", iso := "arh", value := .noMarking }
  , { walsCode := "imo", iso := "imn", value := .doubleMarking }
  , { walsCode := "ind", iso := "ind", value := .noMarking }
  , { walsCode := "ing", iso := "inh", value := .doubleMarking }
  , { walsCode := "jak", iso := "jac", value := .headMarking }
  , { walsCode := "jpn", iso := "jpn", value := .dependentMarking }
  , { walsCode := "jel", iso := "jek", value := .noMarking }
  , { walsCode := "jiv", iso := "jiv", value := .doubleMarking }
  , { walsCode := "juh", iso := "ktz", value := .noMarking }
  , { walsCode := "knd", iso := "kan", value := .dependentMarking }
  , { walsCode := "knp", iso := "kcd", value := .doubleMarking }
  , { walsCode := "knr", iso := "knc", value := .doubleMarking }
  , { walsCode := "krk", iso := "kyh", value := .headMarking }
  , { walsCode := "kay", iso := "gyd", value := .dependentMarking }
  , { walsCode := "ket", iso := "ket", value := .headMarking }
  , { walsCode := "kew", iso := "kew", value := .dependentMarking }
  , { walsCode := "kha", iso := "khk", value := .dependentMarking }
  , { walsCode := "kim", iso := "kig", value := .headMarking }
  , { walsCode := "kio", iso := "kio", value := .headMarking }
  , { walsCode := "kri", iso := "kzw", value := .dependentMarking }
  , { walsCode := "kkr", iso := "kiy", value := .dependentMarking }
  , { walsCode := "kis", iso := "kss", value := .noMarking }
  , { walsCode := "koa", iso := "cku", value := .doubleMarking }
  , { walsCode := "kob", iso := "kpw", value := .noMarking }
  , { walsCode := "kmb", iso := "", value := .noMarking }
  , { walsCode := "kor", iso := "kor", value := .dependentMarking }
  , { walsCode := "kch", iso := "khq", value := .dependentMarking }
  , { walsCode := "kro", iso := "kgo", value := .noMarking }
  , { walsCode := "kiu", iso := "kvd", value := .headMarking }
  , { walsCode := "knm", iso := "kun", value := .dependentMarking }
  , { walsCode := "kut", iso := "kut", value := .doubleMarking }
  , { walsCode := "lai", iso := "cnh", value := .doubleMarking }
  , { walsCode := "lkt", iso := "lkt", value := .headMarking }
  , { walsCode := "lmh", iso := "slp", value := .noMarking }
  , { walsCode := "lan", iso := "laj", value := .headMarking }
  , { walsCode := "lav", iso := "lvk", value := .headMarking }
  , { walsCode := "lez", iso := "lez", value := .dependentMarking }
  , { walsCode := "lug", iso := "lgg", value := .noMarking }
  , { walsCode := "luv", iso := "lue", value := .headMarking }
  , { walsCode := "mai", iso := "mai", value := .dependentMarking }
  , { walsCode := "mal", iso := "plt", value := .dependentMarking }
  , { walsCode := "mlk", iso := "mpb", value := .other }
  , { walsCode := "mnd", iso := "cmn", value := .dependentMarking }
  , { walsCode := "myi", iso := "mpc", value := .doubleMarking }
  , { walsCode := "mao", iso := "mri", value := .dependentMarking }
  , { walsCode := "map", iso := "arn", value := .doubleMarking }
  , { walsCode := "mar", iso := "mrc", value := .doubleMarking }
  , { walsCode := "mrh", iso := "mfr", value := .headMarking }
  , { walsCode := "mrt", iso := "vma", value := .dependentMarking }
  , { walsCode := "mau", iso := "mph", value := .headMarking }
  , { walsCode := "may", iso := "ayz", value := .noMarking }
  , { walsCode := "mei", iso := "mni", value := .dependentMarking }
  , { walsCode := "mis", iso := "miq", value := .noMarking }
  , { walsCode := "mss", iso := "skd", value := .doubleMarking }
  , { walsCode := "mxc", iso := "mig", value := .noMarking }
  , { walsCode := "mot", iso := "siw", value := .doubleMarking }
  , { walsCode := "mun", iso := "unr", value := .doubleMarking }
  , { walsCode := "mpa", iso := "mwf", value := .doubleMarking }
  , { walsCode := "nah", iso := "nll", value := .dependentMarking }
  , { walsCode := "nkk", iso := "nck", value := .headMarking }
  , { walsCode := "kho", iso := "naq", value := .dependentMarking }
  , { walsCode := "nmb", iso := "nab", value := .headMarking }
  , { walsCode := "nar", iso := "nrb", value := .dependentMarking }
  , { walsCode := "nat", iso := "ncz", value := .headMarking }
  , { walsCode := "ntu", iso := "yrk", value := .doubleMarking }
  , { walsCode := "nep", iso := "npi", value := .dependentMarking }
  , { walsCode := "ntj", iso := "ntj", value := .dependentMarking }
  , { walsCode := "ngi", iso := "wyb", value := .dependentMarking }
  , { walsCode := "nca", iso := "caq", value := .noMarking }
  , { walsCode := "nsg", iso := "ncg", value := .headMarking }
  , { walsCode := "niv", iso := "niv", value := .headMarking }
  , { walsCode := "nbd", iso := "dgl", value := .dependentMarking }
  , { walsCode := "nug", iso := "nuy", value := .doubleMarking }
  , { walsCode := "nuu", iso := "nuk", value := .noMarking }
  , { walsCode := "nyn", iso := "nyh", value := .doubleMarking }
  , { walsCode := "ond", iso := "one", value := .headMarking }
  , { walsCode := "ori", iso := "tag", value := .noMarking }
  , { walsCode := "orh", iso := "hae", value := .noMarking }
  , { walsCode := "otm", iso := "ote", value := .headMarking }
  , { walsCode := "pai", iso := "pwn", value := .doubleMarking }
  , { walsCode := "pau", iso := "pad", value := .doubleMarking }
  , { walsCode := "prs", iso := "pes", value := .doubleMarking }
  , { walsCode := "pip", iso := "ppl", value := .headMarking }
  , { walsCode := "prh", iso := "myp", value := .noMarking }
  , { walsCode := "pso", iso := "pom", value := .dependentMarking }
  , { walsCode := "pur", iso := "tsz", value := .dependentMarking }
  , { walsCode := "qim", iso := "qvi", value := .dependentMarking }
  , { walsCode := "qui", iso := "qui", value := .doubleMarking }
  , { walsCode := "ram", iso := "rma", value := .doubleMarking }
  , { walsCode := "rap", iso := "rap", value := .doubleMarking }
  , { walsCode := "rus", iso := "rus", value := .dependentMarking }
  , { walsCode := "sah", iso := "saj", value := .headMarking }
  , { walsCode := "syu", iso := "sll", value := .noMarking }
  , { walsCode := "sdw", iso := "sad", value := .noMarking }
  , { walsCode := "san", iso := "sag", value := .noMarking }
  , { walsCode := "snm", iso := "xsu", value := .headMarking }
  , { walsCode := "sml", iso := "sza", value := .dependentMarking }
  , { walsCode := "shk", iso := "shp", value := .dependentMarking }
  , { walsCode := "siu", iso := "sis", value := .doubleMarking }
  , { walsCode := "sla", iso := "den", value := .headMarking }
  , { walsCode := "spa", iso := "spa", value := .doubleMarking }
  , { walsCode := "squ", iso := "squ", value := .doubleMarking }
  , { walsCode := "sue", iso := "sue", value := .noMarking }
  , { walsCode := "sup", iso := "spp", value := .noMarking }
  , { walsCode := "swa", iso := "swh", value := .headMarking }
  , { walsCode := "tag", iso := "tgl", value := .doubleMarking }
  , { walsCode := "tkl", iso := "tkm", value := .headMarking }
  , { walsCode := "tgp", iso := "tpg", value := .headMarking }
  , { walsCode := "tau", iso := "tya", value := .doubleMarking }
  , { walsCode := "tlf", iso := "tlf", value := .headMarking }
  , { walsCode := "tha", iso := "tha", value := .noMarking }
  , { walsCode := "tib", iso := "bod", value := .dependentMarking }
  , { walsCode := "tmc", iso := "tjm", value := .headMarking }
  , { walsCode := "tiw", iso := "tiw", value := .headMarking }
  , { walsCode := "tli", iso := "tli", value := .headMarking }
  , { walsCode := "ton", iso := "tqw", value := .doubleMarking }
  , { walsCode := "tru", iso := "tpy", value := .dependentMarking }
  , { walsCode := "tuk", iso := "", value := .noMarking }
  , { walsCode := "tun", iso := "tun", value := .headMarking }
  , { walsCode := "tur", iso := "tur", value := .dependentMarking }
  , { walsCode := "tsh", iso := "par", value := .dependentMarking }
  , { walsCode := "ung", iso := "ung", value := .headMarking }
  , { walsCode := "uhi", iso := "urf", value := .dependentMarking }
  , { walsCode := "usa", iso := "wnu", value := .headMarking }
  , { walsCode := "vie", iso := "vie", value := .noMarking }
  , { walsCode := "wao", iso := "auc", value := .noMarking }
  , { walsCode := "wra", iso := "wba", value := .dependentMarking }
  , { walsCode := "wry", iso := "wrz", value := .doubleMarking }
  , { walsCode := "war", iso := "pav", value := .headMarking }
  , { walsCode := "wrl", iso := "wbp", value := .doubleMarking }
  , { walsCode := "wrn", iso := "wnd", value := .headMarking }
  , { walsCode := "was", iso := "was", value := .headMarking }
  , { walsCode := "wsk", iso := "wsk", value := .doubleMarking }
  , { walsCode := "wem", iso := "xww", value := .doubleMarking }
  , { walsCode := "wic", iso := "wic", value := .headMarking }
  , { walsCode := "wch", iso := "mzh", value := .doubleMarking }
  , { walsCode := "win", iso := "wnw", value := .doubleMarking }
  , { walsCode := "xok", iso := "xok", value := .dependentMarking }
  , { walsCode := "yag", iso := "yad", value := .other }
  , { walsCode := "yli", iso := "yli", value := .headMarking }
  , { walsCode := "yaq", iso := "yaq", value := .doubleMarking }
  , { walsCode := "yes", iso := "yss", value := .headMarking }
  , { walsCode := "yim", iso := "yee", value := .headMarking }
  , { walsCode := "yor", iso := "yor", value := .doubleMarking }
  , { walsCode := "yuc", iso := "yuc", value := .headMarking }
  , { walsCode := "yko", iso := "yux", value := .dependentMarking }
  , { walsCode := "ypk", iso := "esu", value := .doubleMarking }
  , { walsCode := "yur", iso := "yur", value := .headMarking }
  , { walsCode := "zqc", iso := "zoc", value := .doubleMarking }
  , { walsCode := "zul", iso := "zul", value := .headMarking }
  , { walsCode := "zun", iso := "zun", value := .doubleMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F23A
