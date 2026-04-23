import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 25A: Locus of Marking: Whole-language Typology
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 25A`.

Chapter 25, 236 languages.
-/

namespace Datasets.WALS.F25A

/-- WALS 25A values. -/
inductive LocusOfMarkingWholeLanguageTypology where
  /-- Head-marking (47 languages). -/
  | headMarking
  /-- Dependent-marking (46 languages). -/
  | dependentMarking
  /-- Double-marking (16 languages). -/
  | doubleMarking
  /-- Zero-marking (6 languages). -/
  | zeroMarking
  /-- Inconsistent or other (121 languages). -/
  | inconsistentOrOther
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 25A dataset (236 languages). -/
def allData : List (Datapoint LocusOfMarkingWholeLanguageTypology) :=
  [ { walsCode := "abk", iso := "abk", value := .headMarking }
  , { walsCode := "ace", iso := "ace", value := .headMarking }
  , { walsCode := "aco", iso := "kjq", value := .headMarking }
  , { walsCode := "ain", iso := "ain", value := .inconsistentOrOther }
  , { walsCode := "ala", iso := "amp", value := .inconsistentOrOther }
  , { walsCode := "amb", iso := "abt", value := .dependentMarking }
  , { walsCode := "ame", iso := "aey", value := .inconsistentOrOther }
  , { walsCode := "ane", iso := "anz", value := .headMarking }
  , { walsCode := "apu", iso := "apu", value := .headMarking }
  , { walsCode := "aeg", iso := "arz", value := .inconsistentOrOther }
  , { walsCode := "arp", iso := "ape", value := .inconsistentOrOther }
  , { walsCode := "amp", iso := "aer", value := .dependentMarking }
  , { walsCode := "asm", iso := "cns", value := .inconsistentOrOther }
  , { walsCode := "atk", iso := "aqp", value := .inconsistentOrOther }
  , { walsCode := "awp", iso := "kwi", value := .inconsistentOrOther }
  , { walsCode := "awt", iso := "kmn", value := .dependentMarking }
  , { walsCode := "aym", iso := "ayr", value := .doubleMarking }
  , { walsCode := "bag", iso := "bmi", value := .inconsistentOrOther }
  , { walsCode := "brs", iso := "bsn", value := .inconsistentOrOther }
  , { walsCode := "bsq", iso := "eus", value := .inconsistentOrOther }
  , { walsCode := "bzi", iso := "bvz", value := .inconsistentOrOther }
  , { walsCode := "bej", iso := "bej", value := .dependentMarking }
  , { walsCode := "bel", iso := "byw", value := .doubleMarking }
  , { walsCode := "bma", iso := "tzm", value := .dependentMarking }
  , { walsCode := "bbw", iso := "gup", value := .inconsistentOrOther }
  , { walsCode := "brr", iso := "bor", value := .inconsistentOrOther }
  , { walsCode := "brh", iso := "brh", value := .dependentMarking }
  , { walsCode := "bri", iso := "bzd", value := .inconsistentOrOther }
  , { walsCode := "brm", iso := "mya", value := .dependentMarking }
  , { walsCode := "buu", iso := "mhs", value := .inconsistentOrOther }
  , { walsCode := "bur", iso := "bsk", value := .doubleMarking }
  , { walsCode := "cnl", iso := "ram", value := .inconsistentOrOther }
  , { walsCode := "cyv", iso := "cyb", value := .inconsistentOrOther }
  , { walsCode := "cha", iso := "cha", value := .inconsistentOrOther }
  , { walsCode := "chy", iso := "cbt", value := .inconsistentOrOther }
  , { walsCode := "cjo", iso := "pei", value := .headMarking }
  , { walsCode := "cku", iso := "wac", value := .headMarking }
  , { walsCode := "ctm", iso := "ctm", value := .inconsistentOrOther }
  , { walsCode := "cho", iso := "chd", value := .headMarking }
  , { walsCode := "chk", iso := "ckt", value := .inconsistentOrOther }
  , { walsCode := "cin", iso := "inz", value := .headMarking }
  , { walsCode := "ccp", iso := "coc", value := .inconsistentOrOther }
  , { walsCode := "coo", iso := "csz", value := .headMarking }
  , { walsCode := "cre", iso := "crk", value := .headMarking }
  , { walsCode := "dag", iso := "dgz", value := .headMarking }
  , { walsCode := "dni", iso := "dni", value := .inconsistentOrOther }
  , { walsCode := "diy", iso := "dif", value := .dependentMarking }
  , { walsCode := "diz", iso := "mdx", value := .inconsistentOrOther }
  , { walsCode := "djp", iso := "dwu", value := .dependentMarking }
  , { walsCode := "dji", iso := "jig", value := .doubleMarking }
  , { walsCode := "dum", iso := "vam", value := .inconsistentOrOther }
  , { walsCode := "dyi", iso := "dbl", value := .dependentMarking }
  , { walsCode := "eka", iso := "ekg", value := .inconsistentOrOther }
  , { walsCode := "eng", iso := "eng", value := .dependentMarking }
  , { walsCode := "epe", iso := "sja", value := .inconsistentOrOther }
  , { walsCode := "eve", iso := "evn", value := .inconsistentOrOther }
  , { walsCode := "ewe", iso := "ewe", value := .inconsistentOrOther }
  , { walsCode := "fij", iso := "fij", value := .headMarking }
  , { walsCode := "fin", iso := "fin", value := .inconsistentOrOther }
  , { walsCode := "fre", iso := "fra", value := .inconsistentOrOther }
  , { walsCode := "fur", iso := "fvr", value := .dependentMarking }
  , { walsCode := "grr", iso := "wrk", value := .dependentMarking }
  , { walsCode := "geo", iso := "kat", value := .inconsistentOrOther }
  , { walsCode := "ger", iso := "deu", value := .dependentMarking }
  , { walsCode := "goo", iso := "gni", value := .inconsistentOrOther }
  , { walsCode := "grb", iso := "grj", value := .dependentMarking }
  , { walsCode := "grk", iso := "ell", value := .doubleMarking }
  , { walsCode := "grw", iso := "kal", value := .doubleMarking }
  , { walsCode := "gua", iso := "gug", value := .headMarking }
  , { walsCode := "gmz", iso := "guk", value := .inconsistentOrOther }
  , { walsCode := "gku", iso := "pue", value := .inconsistentOrOther }
  , { walsCode := "hai", iso := "hai", value := .inconsistentOrOther }
  , { walsCode := "hat", iso := "had", value := .inconsistentOrOther }
  , { walsCode := "hau", iso := "hau", value := .inconsistentOrOther }
  , { walsCode := "heb", iso := "heb", value := .inconsistentOrOther }
  , { walsCode := "hin", iso := "hin", value := .inconsistentOrOther }
  , { walsCode := "hix", iso := "hix", value := .headMarking }
  , { walsCode := "hmo", iso := "hnj", value := .inconsistentOrOther }
  , { walsCode := "hua", iso := "ygr", value := .doubleMarking }
  , { walsCode := "hve", iso := "huv", value := .headMarking }
  , { walsCode := "hun", iso := "hun", value := .inconsistentOrOther }
  , { walsCode := "iau", iso := "tmu", value := .inconsistentOrOther }
  , { walsCode := "ice", iso := "isl", value := .dependentMarking }
  , { walsCode := "ijo", iso := "ijc", value := .zeroMarking }
  , { walsCode := "ik", iso := "ikx", value := .dependentMarking }
  , { walsCode := "ika", iso := "arh", value := .inconsistentOrOther }
  , { walsCode := "imo", iso := "imn", value := .doubleMarking }
  , { walsCode := "ind", iso := "ind", value := .zeroMarking }
  , { walsCode := "ing", iso := "inh", value := .inconsistentOrOther }
  , { walsCode := "jak", iso := "jac", value := .headMarking }
  , { walsCode := "jpn", iso := "jpn", value := .dependentMarking }
  , { walsCode := "jel", iso := "jek", value := .inconsistentOrOther }
  , { walsCode := "jiv", iso := "jiv", value := .doubleMarking }
  , { walsCode := "juh", iso := "ktz", value := .zeroMarking }
  , { walsCode := "knd", iso := "kan", value := .dependentMarking }
  , { walsCode := "knp", iso := "kcd", value := .inconsistentOrOther }
  , { walsCode := "knr", iso := "knc", value := .inconsistentOrOther }
  , { walsCode := "krk", iso := "kyh", value := .headMarking }
  , { walsCode := "kay", iso := "gyd", value := .dependentMarking }
  , { walsCode := "ket", iso := "ket", value := .headMarking }
  , { walsCode := "kew", iso := "kew", value := .dependentMarking }
  , { walsCode := "kha", iso := "khk", value := .dependentMarking }
  , { walsCode := "kim", iso := "kig", value := .inconsistentOrOther }
  , { walsCode := "kio", iso := "kio", value := .inconsistentOrOther }
  , { walsCode := "kri", iso := "kzw", value := .inconsistentOrOther }
  , { walsCode := "kkr", iso := "kiy", value := .inconsistentOrOther }
  , { walsCode := "kis", iso := "kss", value := .inconsistentOrOther }
  , { walsCode := "koa", iso := "cku", value := .inconsistentOrOther }
  , { walsCode := "kob", iso := "kpw", value := .inconsistentOrOther }
  , { walsCode := "kmb", iso := "", value := .inconsistentOrOther }
  , { walsCode := "kor", iso := "kor", value := .dependentMarking }
  , { walsCode := "kch", iso := "khq", value := .dependentMarking }
  , { walsCode := "kro", iso := "kgo", value := .inconsistentOrOther }
  , { walsCode := "kiu", iso := "kvd", value := .headMarking }
  , { walsCode := "knm", iso := "kun", value := .dependentMarking }
  , { walsCode := "kut", iso := "kut", value := .inconsistentOrOther }
  , { walsCode := "lai", iso := "cnh", value := .inconsistentOrOther }
  , { walsCode := "lkt", iso := "lkt", value := .headMarking }
  , { walsCode := "lmh", iso := "slp", value := .zeroMarking }
  , { walsCode := "lan", iso := "laj", value := .headMarking }
  , { walsCode := "lav", iso := "lvk", value := .headMarking }
  , { walsCode := "lez", iso := "lez", value := .dependentMarking }
  , { walsCode := "lug", iso := "lgg", value := .inconsistentOrOther }
  , { walsCode := "luv", iso := "lue", value := .inconsistentOrOther }
  , { walsCode := "mai", iso := "mai", value := .dependentMarking }
  , { walsCode := "mal", iso := "plt", value := .inconsistentOrOther }
  , { walsCode := "mlk", iso := "mpb", value := .inconsistentOrOther }
  , { walsCode := "mnd", iso := "cmn", value := .dependentMarking }
  , { walsCode := "myi", iso := "mpc", value := .doubleMarking }
  , { walsCode := "mao", iso := "mri", value := .dependentMarking }
  , { walsCode := "map", iso := "arn", value := .inconsistentOrOther }
  , { walsCode := "mar", iso := "mrc", value := .inconsistentOrOther }
  , { walsCode := "mrh", iso := "mfr", value := .headMarking }
  , { walsCode := "mrt", iso := "vma", value := .dependentMarking }
  , { walsCode := "mau", iso := "mph", value := .inconsistentOrOther }
  , { walsCode := "may", iso := "ayz", value := .inconsistentOrOther }
  , { walsCode := "mei", iso := "mni", value := .dependentMarking }
  , { walsCode := "mis", iso := "miq", value := .inconsistentOrOther }
  , { walsCode := "mss", iso := "skd", value := .doubleMarking }
  , { walsCode := "mxc", iso := "mig", value := .inconsistentOrOther }
  , { walsCode := "mot", iso := "siw", value := .inconsistentOrOther }
  , { walsCode := "mun", iso := "unr", value := .inconsistentOrOther }
  , { walsCode := "mpa", iso := "mwf", value := .inconsistentOrOther }
  , { walsCode := "nah", iso := "nll", value := .dependentMarking }
  , { walsCode := "nkk", iso := "nck", value := .inconsistentOrOther }
  , { walsCode := "kho", iso := "naq", value := .dependentMarking }
  , { walsCode := "nmb", iso := "nab", value := .headMarking }
  , { walsCode := "nar", iso := "nrb", value := .inconsistentOrOther }
  , { walsCode := "nat", iso := "ncz", value := .headMarking }
  , { walsCode := "ntu", iso := "yrk", value := .inconsistentOrOther }
  , { walsCode := "nep", iso := "npi", value := .dependentMarking }
  , { walsCode := "ntj", iso := "ntj", value := .dependentMarking }
  , { walsCode := "ngi", iso := "wyb", value := .dependentMarking }
  , { walsCode := "nca", iso := "caq", value := .inconsistentOrOther }
  , { walsCode := "nsg", iso := "ncg", value := .headMarking }
  , { walsCode := "niv", iso := "niv", value := .headMarking }
  , { walsCode := "nbd", iso := "dgl", value := .dependentMarking }
  , { walsCode := "nug", iso := "nuy", value := .inconsistentOrOther }
  , { walsCode := "nuu", iso := "nuk", value := .inconsistentOrOther }
  , { walsCode := "nyn", iso := "nyh", value := .inconsistentOrOther }
  , { walsCode := "ond", iso := "one", value := .headMarking }
  , { walsCode := "ori", iso := "tag", value := .inconsistentOrOther }
  , { walsCode := "orh", iso := "hae", value := .inconsistentOrOther }
  , { walsCode := "otm", iso := "ote", value := .headMarking }
  , { walsCode := "pai", iso := "pwn", value := .doubleMarking }
  , { walsCode := "pau", iso := "pad", value := .inconsistentOrOther }
  , { walsCode := "prs", iso := "pes", value := .inconsistentOrOther }
  , { walsCode := "pip", iso := "ppl", value := .headMarking }
  , { walsCode := "prh", iso := "myp", value := .zeroMarking }
  , { walsCode := "pso", iso := "pom", value := .dependentMarking }
  , { walsCode := "pur", iso := "tsz", value := .dependentMarking }
  , { walsCode := "qim", iso := "qvi", value := .dependentMarking }
  , { walsCode := "qui", iso := "qui", value := .inconsistentOrOther }
  , { walsCode := "ram", iso := "rma", value := .inconsistentOrOther }
  , { walsCode := "rap", iso := "rap", value := .inconsistentOrOther }
  , { walsCode := "rus", iso := "rus", value := .dependentMarking }
  , { walsCode := "sah", iso := "saj", value := .headMarking }
  , { walsCode := "syu", iso := "sll", value := .inconsistentOrOther }
  , { walsCode := "sdw", iso := "sad", value := .inconsistentOrOther }
  , { walsCode := "san", iso := "sag", value := .inconsistentOrOther }
  , { walsCode := "snm", iso := "xsu", value := .inconsistentOrOther }
  , { walsCode := "sml", iso := "sza", value := .inconsistentOrOther }
  , { walsCode := "shk", iso := "shp", value := .dependentMarking }
  , { walsCode := "siu", iso := "sis", value := .inconsistentOrOther }
  , { walsCode := "sla", iso := "den", value := .headMarking }
  , { walsCode := "spa", iso := "spa", value := .inconsistentOrOther }
  , { walsCode := "squ", iso := "squ", value := .inconsistentOrOther }
  , { walsCode := "sue", iso := "sue", value := .inconsistentOrOther }
  , { walsCode := "sup", iso := "spp", value := .inconsistentOrOther }
  , { walsCode := "swa", iso := "swh", value := .inconsistentOrOther }
  , { walsCode := "tag", iso := "tgl", value := .inconsistentOrOther }
  , { walsCode := "tkl", iso := "tkm", value := .headMarking }
  , { walsCode := "tgp", iso := "tpg", value := .headMarking }
  , { walsCode := "tau", iso := "tya", value := .inconsistentOrOther }
  , { walsCode := "tlf", iso := "tlf", value := .headMarking }
  , { walsCode := "tha", iso := "tha", value := .inconsistentOrOther }
  , { walsCode := "tib", iso := "bod", value := .dependentMarking }
  , { walsCode := "tmc", iso := "tjm", value := .inconsistentOrOther }
  , { walsCode := "tiw", iso := "tiw", value := .inconsistentOrOther }
  , { walsCode := "tli", iso := "tli", value := .headMarking }
  , { walsCode := "ton", iso := "tqw", value := .inconsistentOrOther }
  , { walsCode := "tru", iso := "tpy", value := .dependentMarking }
  , { walsCode := "tuk", iso := "", value := .inconsistentOrOther }
  , { walsCode := "tun", iso := "tun", value := .headMarking }
  , { walsCode := "tur", iso := "tur", value := .inconsistentOrOther }
  , { walsCode := "tsh", iso := "par", value := .dependentMarking }
  , { walsCode := "ung", iso := "ung", value := .inconsistentOrOther }
  , { walsCode := "uhi", iso := "urf", value := .dependentMarking }
  , { walsCode := "usa", iso := "wnu", value := .headMarking }
  , { walsCode := "vie", iso := "vie", value := .zeroMarking }
  , { walsCode := "wao", iso := "auc", value := .inconsistentOrOther }
  , { walsCode := "wra", iso := "wba", value := .inconsistentOrOther }
  , { walsCode := "wry", iso := "wrz", value := .inconsistentOrOther }
  , { walsCode := "war", iso := "pav", value := .headMarking }
  , { walsCode := "wrl", iso := "wbp", value := .inconsistentOrOther }
  , { walsCode := "wrn", iso := "wnd", value := .headMarking }
  , { walsCode := "was", iso := "was", value := .headMarking }
  , { walsCode := "wsk", iso := "wsk", value := .inconsistentOrOther }
  , { walsCode := "wem", iso := "xww", value := .doubleMarking }
  , { walsCode := "wic", iso := "wic", value := .headMarking }
  , { walsCode := "wch", iso := "mzh", value := .inconsistentOrOther }
  , { walsCode := "win", iso := "wnw", value := .inconsistentOrOther }
  , { walsCode := "xok", iso := "xok", value := .inconsistentOrOther }
  , { walsCode := "yag", iso := "yad", value := .inconsistentOrOther }
  , { walsCode := "yli", iso := "yli", value := .headMarking }
  , { walsCode := "yaq", iso := "yaq", value := .doubleMarking }
  , { walsCode := "yes", iso := "yss", value := .headMarking }
  , { walsCode := "yim", iso := "yee", value := .inconsistentOrOther }
  , { walsCode := "yor", iso := "yor", value := .inconsistentOrOther }
  , { walsCode := "yuc", iso := "yuc", value := .headMarking }
  , { walsCode := "yko", iso := "yux", value := .inconsistentOrOther }
  , { walsCode := "ypk", iso := "esu", value := .doubleMarking }
  , { walsCode := "yur", iso := "yur", value := .headMarking }
  , { walsCode := "zqc", iso := "zoc", value := .doubleMarking }
  , { walsCode := "zul", iso := "zul", value := .inconsistentOrOther }
  , { walsCode := "zun", iso := "zun", value := .inconsistentOrOther }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F25A
