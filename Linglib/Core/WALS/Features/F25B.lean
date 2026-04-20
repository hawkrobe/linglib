import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 25B: Zero Marking of A and P Arguments
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 25B`.

Chapter 25, 235 languages.
-/

namespace Core.WALS.F25B

/-- WALS 25B values. -/
inductive ZeroMarkingOfAAndPArguments where
  /-- Zero-marking (16 languages). -/
  | zeroMarking
  /-- Non-zero marking (219 languages). -/
  | nonZeroMarking
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 25B dataset (235 languages). -/
def allData : List (Datapoint ZeroMarkingOfAAndPArguments) :=
  [ { walsCode := "abk", iso := "abk", value := .nonZeroMarking }
  , { walsCode := "ace", iso := "ace", value := .nonZeroMarking }
  , { walsCode := "aco", iso := "kjq", value := .nonZeroMarking }
  , { walsCode := "ain", iso := "ain", value := .nonZeroMarking }
  , { walsCode := "ala", iso := "amp", value := .nonZeroMarking }
  , { walsCode := "amb", iso := "abt", value := .nonZeroMarking }
  , { walsCode := "ame", iso := "aey", value := .nonZeroMarking }
  , { walsCode := "ane", iso := "anz", value := .nonZeroMarking }
  , { walsCode := "apu", iso := "apu", value := .nonZeroMarking }
  , { walsCode := "aeg", iso := "arz", value := .nonZeroMarking }
  , { walsCode := "arp", iso := "ape", value := .nonZeroMarking }
  , { walsCode := "amp", iso := "aer", value := .nonZeroMarking }
  , { walsCode := "asm", iso := "cns", value := .nonZeroMarking }
  , { walsCode := "atk", iso := "aqp", value := .nonZeroMarking }
  , { walsCode := "awp", iso := "kwi", value := .nonZeroMarking }
  , { walsCode := "awt", iso := "kmn", value := .nonZeroMarking }
  , { walsCode := "aym", iso := "ayr", value := .nonZeroMarking }
  , { walsCode := "bag", iso := "bmi", value := .nonZeroMarking }
  , { walsCode := "brs", iso := "bsn", value := .nonZeroMarking }
  , { walsCode := "bsq", iso := "eus", value := .nonZeroMarking }
  , { walsCode := "bzi", iso := "bvz", value := .zeroMarking }
  , { walsCode := "bej", iso := "bej", value := .nonZeroMarking }
  , { walsCode := "bel", iso := "byw", value := .nonZeroMarking }
  , { walsCode := "bma", iso := "tzm", value := .nonZeroMarking }
  , { walsCode := "bbw", iso := "gup", value := .nonZeroMarking }
  , { walsCode := "brr", iso := "bor", value := .nonZeroMarking }
  , { walsCode := "brh", iso := "brh", value := .nonZeroMarking }
  , { walsCode := "bri", iso := "bzd", value := .nonZeroMarking }
  , { walsCode := "brm", iso := "mya", value := .nonZeroMarking }
  , { walsCode := "buu", iso := "mhs", value := .zeroMarking }
  , { walsCode := "bur", iso := "bsk", value := .nonZeroMarking }
  , { walsCode := "cnl", iso := "ram", value := .nonZeroMarking }
  , { walsCode := "cyv", iso := "cyb", value := .nonZeroMarking }
  , { walsCode := "cha", iso := "cha", value := .nonZeroMarking }
  , { walsCode := "chy", iso := "cbt", value := .nonZeroMarking }
  , { walsCode := "cjo", iso := "pei", value := .nonZeroMarking }
  , { walsCode := "cku", iso := "wac", value := .nonZeroMarking }
  , { walsCode := "ctm", iso := "ctm", value := .nonZeroMarking }
  , { walsCode := "cho", iso := "chd", value := .nonZeroMarking }
  , { walsCode := "chk", iso := "ckt", value := .nonZeroMarking }
  , { walsCode := "cin", iso := "inz", value := .nonZeroMarking }
  , { walsCode := "coo", iso := "csz", value := .nonZeroMarking }
  , { walsCode := "cre", iso := "crk", value := .nonZeroMarking }
  , { walsCode := "dag", iso := "dgz", value := .nonZeroMarking }
  , { walsCode := "dni", iso := "dni", value := .nonZeroMarking }
  , { walsCode := "diy", iso := "dif", value := .nonZeroMarking }
  , { walsCode := "diz", iso := "mdx", value := .nonZeroMarking }
  , { walsCode := "djp", iso := "dwu", value := .nonZeroMarking }
  , { walsCode := "dji", iso := "jig", value := .nonZeroMarking }
  , { walsCode := "dum", iso := "vam", value := .nonZeroMarking }
  , { walsCode := "dyi", iso := "dbl", value := .nonZeroMarking }
  , { walsCode := "eka", iso := "ekg", value := .nonZeroMarking }
  , { walsCode := "eng", iso := "eng", value := .nonZeroMarking }
  , { walsCode := "epe", iso := "sja", value := .nonZeroMarking }
  , { walsCode := "eve", iso := "evn", value := .nonZeroMarking }
  , { walsCode := "ewe", iso := "ewe", value := .zeroMarking }
  , { walsCode := "fij", iso := "fij", value := .nonZeroMarking }
  , { walsCode := "fin", iso := "fin", value := .nonZeroMarking }
  , { walsCode := "fre", iso := "fra", value := .nonZeroMarking }
  , { walsCode := "fur", iso := "fvr", value := .nonZeroMarking }
  , { walsCode := "grr", iso := "wrk", value := .nonZeroMarking }
  , { walsCode := "geo", iso := "kat", value := .nonZeroMarking }
  , { walsCode := "ger", iso := "deu", value := .nonZeroMarking }
  , { walsCode := "goo", iso := "gni", value := .nonZeroMarking }
  , { walsCode := "grb", iso := "grj", value := .nonZeroMarking }
  , { walsCode := "grk", iso := "ell", value := .nonZeroMarking }
  , { walsCode := "grw", iso := "kal", value := .nonZeroMarking }
  , { walsCode := "gua", iso := "gug", value := .nonZeroMarking }
  , { walsCode := "gmz", iso := "guk", value := .nonZeroMarking }
  , { walsCode := "gku", iso := "pue", value := .nonZeroMarking }
  , { walsCode := "hai", iso := "hai", value := .zeroMarking }
  , { walsCode := "hat", iso := "had", value := .nonZeroMarking }
  , { walsCode := "hau", iso := "hau", value := .nonZeroMarking }
  , { walsCode := "heb", iso := "heb", value := .nonZeroMarking }
  , { walsCode := "hin", iso := "hin", value := .nonZeroMarking }
  , { walsCode := "hix", iso := "hix", value := .nonZeroMarking }
  , { walsCode := "hmo", iso := "hnj", value := .zeroMarking }
  , { walsCode := "hua", iso := "ygr", value := .nonZeroMarking }
  , { walsCode := "hve", iso := "huv", value := .nonZeroMarking }
  , { walsCode := "hun", iso := "hun", value := .nonZeroMarking }
  , { walsCode := "iau", iso := "tmu", value := .zeroMarking }
  , { walsCode := "ice", iso := "isl", value := .nonZeroMarking }
  , { walsCode := "ijo", iso := "ijc", value := .zeroMarking }
  , { walsCode := "ik", iso := "ikx", value := .nonZeroMarking }
  , { walsCode := "ika", iso := "arh", value := .nonZeroMarking }
  , { walsCode := "imo", iso := "imn", value := .nonZeroMarking }
  , { walsCode := "ind", iso := "ind", value := .zeroMarking }
  , { walsCode := "ing", iso := "inh", value := .nonZeroMarking }
  , { walsCode := "jak", iso := "jac", value := .nonZeroMarking }
  , { walsCode := "jpn", iso := "jpn", value := .nonZeroMarking }
  , { walsCode := "jel", iso := "jek", value := .zeroMarking }
  , { walsCode := "jiv", iso := "jiv", value := .nonZeroMarking }
  , { walsCode := "juh", iso := "ktz", value := .zeroMarking }
  , { walsCode := "knd", iso := "kan", value := .nonZeroMarking }
  , { walsCode := "knp", iso := "kcd", value := .nonZeroMarking }
  , { walsCode := "knr", iso := "knc", value := .nonZeroMarking }
  , { walsCode := "krk", iso := "kyh", value := .nonZeroMarking }
  , { walsCode := "kay", iso := "gyd", value := .nonZeroMarking }
  , { walsCode := "ket", iso := "ket", value := .nonZeroMarking }
  , { walsCode := "kew", iso := "kew", value := .nonZeroMarking }
  , { walsCode := "kha", iso := "khk", value := .nonZeroMarking }
  , { walsCode := "kim", iso := "kig", value := .nonZeroMarking }
  , { walsCode := "kio", iso := "kio", value := .nonZeroMarking }
  , { walsCode := "kri", iso := "kzw", value := .nonZeroMarking }
  , { walsCode := "kkr", iso := "kiy", value := .nonZeroMarking }
  , { walsCode := "kis", iso := "kss", value := .zeroMarking }
  , { walsCode := "koa", iso := "cku", value := .nonZeroMarking }
  , { walsCode := "kob", iso := "kpw", value := .nonZeroMarking }
  , { walsCode := "kmb", iso := "", value := .nonZeroMarking }
  , { walsCode := "kor", iso := "kor", value := .nonZeroMarking }
  , { walsCode := "kch", iso := "khq", value := .nonZeroMarking }
  , { walsCode := "kro", iso := "kgo", value := .nonZeroMarking }
  , { walsCode := "kui", iso := "kxu", value := .nonZeroMarking }
  , { walsCode := "knm", iso := "kun", value := .nonZeroMarking }
  , { walsCode := "kut", iso := "kut", value := .nonZeroMarking }
  , { walsCode := "lai", iso := "cnh", value := .nonZeroMarking }
  , { walsCode := "lkt", iso := "lkt", value := .nonZeroMarking }
  , { walsCode := "lmh", iso := "slp", value := .zeroMarking }
  , { walsCode := "lan", iso := "laj", value := .nonZeroMarking }
  , { walsCode := "lav", iso := "lvk", value := .nonZeroMarking }
  , { walsCode := "lez", iso := "lez", value := .nonZeroMarking }
  , { walsCode := "lug", iso := "lgg", value := .nonZeroMarking }
  , { walsCode := "luv", iso := "lue", value := .nonZeroMarking }
  , { walsCode := "mai", iso := "mai", value := .nonZeroMarking }
  , { walsCode := "mal", iso := "plt", value := .nonZeroMarking }
  , { walsCode := "mlk", iso := "mpb", value := .nonZeroMarking }
  , { walsCode := "mnd", iso := "cmn", value := .nonZeroMarking }
  , { walsCode := "myi", iso := "mpc", value := .nonZeroMarking }
  , { walsCode := "mao", iso := "mri", value := .nonZeroMarking }
  , { walsCode := "map", iso := "arn", value := .nonZeroMarking }
  , { walsCode := "mar", iso := "mrc", value := .nonZeroMarking }
  , { walsCode := "mrh", iso := "mfr", value := .nonZeroMarking }
  , { walsCode := "mrt", iso := "vma", value := .nonZeroMarking }
  , { walsCode := "mau", iso := "mph", value := .nonZeroMarking }
  , { walsCode := "may", iso := "ayz", value := .nonZeroMarking }
  , { walsCode := "mei", iso := "mni", value := .nonZeroMarking }
  , { walsCode := "mis", iso := "miq", value := .nonZeroMarking }
  , { walsCode := "mss", iso := "skd", value := .nonZeroMarking }
  , { walsCode := "mxc", iso := "mig", value := .nonZeroMarking }
  , { walsCode := "mot", iso := "siw", value := .nonZeroMarking }
  , { walsCode := "mun", iso := "unr", value := .nonZeroMarking }
  , { walsCode := "mpa", iso := "mwf", value := .nonZeroMarking }
  , { walsCode := "nah", iso := "nll", value := .nonZeroMarking }
  , { walsCode := "nkk", iso := "nck", value := .nonZeroMarking }
  , { walsCode := "kho", iso := "naq", value := .nonZeroMarking }
  , { walsCode := "nmb", iso := "nab", value := .nonZeroMarking }
  , { walsCode := "nar", iso := "nrb", value := .nonZeroMarking }
  , { walsCode := "nat", iso := "ncz", value := .nonZeroMarking }
  , { walsCode := "ntu", iso := "yrk", value := .nonZeroMarking }
  , { walsCode := "nep", iso := "npi", value := .nonZeroMarking }
  , { walsCode := "ngi", iso := "wyb", value := .nonZeroMarking }
  , { walsCode := "nca", iso := "caq", value := .nonZeroMarking }
  , { walsCode := "nsg", iso := "ncg", value := .nonZeroMarking }
  , { walsCode := "niv", iso := "niv", value := .nonZeroMarking }
  , { walsCode := "nbd", iso := "dgl", value := .nonZeroMarking }
  , { walsCode := "nug", iso := "nuy", value := .nonZeroMarking }
  , { walsCode := "nuu", iso := "nuk", value := .nonZeroMarking }
  , { walsCode := "nyn", iso := "nyh", value := .nonZeroMarking }
  , { walsCode := "ond", iso := "one", value := .nonZeroMarking }
  , { walsCode := "ori", iso := "tag", value := .nonZeroMarking }
  , { walsCode := "orh", iso := "hae", value := .nonZeroMarking }
  , { walsCode := "otm", iso := "ote", value := .nonZeroMarking }
  , { walsCode := "pai", iso := "pwn", value := .nonZeroMarking }
  , { walsCode := "pau", iso := "pad", value := .nonZeroMarking }
  , { walsCode := "prs", iso := "pes", value := .nonZeroMarking }
  , { walsCode := "pip", iso := "ppl", value := .nonZeroMarking }
  , { walsCode := "prh", iso := "myp", value := .zeroMarking }
  , { walsCode := "pso", iso := "pom", value := .nonZeroMarking }
  , { walsCode := "pur", iso := "tsz", value := .nonZeroMarking }
  , { walsCode := "qim", iso := "qvi", value := .nonZeroMarking }
  , { walsCode := "qui", iso := "qui", value := .nonZeroMarking }
  , { walsCode := "ram", iso := "rma", value := .nonZeroMarking }
  , { walsCode := "rap", iso := "rap", value := .nonZeroMarking }
  , { walsCode := "rus", iso := "rus", value := .nonZeroMarking }
  , { walsCode := "sah", iso := "saj", value := .nonZeroMarking }
  , { walsCode := "syu", iso := "sll", value := .nonZeroMarking }
  , { walsCode := "sdw", iso := "sad", value := .nonZeroMarking }
  , { walsCode := "san", iso := "sag", value := .nonZeroMarking }
  , { walsCode := "snm", iso := "xsu", value := .nonZeroMarking }
  , { walsCode := "sml", iso := "sza", value := .nonZeroMarking }
  , { walsCode := "shk", iso := "shp", value := .nonZeroMarking }
  , { walsCode := "siu", iso := "sis", value := .nonZeroMarking }
  , { walsCode := "sla", iso := "den", value := .nonZeroMarking }
  , { walsCode := "spa", iso := "spa", value := .nonZeroMarking }
  , { walsCode := "squ", iso := "squ", value := .nonZeroMarking }
  , { walsCode := "sue", iso := "sue", value := .nonZeroMarking }
  , { walsCode := "sup", iso := "spp", value := .zeroMarking }
  , { walsCode := "swa", iso := "swh", value := .nonZeroMarking }
  , { walsCode := "tag", iso := "tgl", value := .nonZeroMarking }
  , { walsCode := "tkl", iso := "tkm", value := .nonZeroMarking }
  , { walsCode := "tgp", iso := "tpg", value := .nonZeroMarking }
  , { walsCode := "tau", iso := "tya", value := .nonZeroMarking }
  , { walsCode := "tlf", iso := "tlf", value := .nonZeroMarking }
  , { walsCode := "tha", iso := "tha", value := .zeroMarking }
  , { walsCode := "tib", iso := "bod", value := .nonZeroMarking }
  , { walsCode := "tmc", iso := "tjm", value := .nonZeroMarking }
  , { walsCode := "tiw", iso := "tiw", value := .nonZeroMarking }
  , { walsCode := "tli", iso := "tli", value := .nonZeroMarking }
  , { walsCode := "ton", iso := "tqw", value := .nonZeroMarking }
  , { walsCode := "tru", iso := "tpy", value := .nonZeroMarking }
  , { walsCode := "tuk", iso := "", value := .nonZeroMarking }
  , { walsCode := "tun", iso := "tun", value := .nonZeroMarking }
  , { walsCode := "tur", iso := "tur", value := .nonZeroMarking }
  , { walsCode := "tsh", iso := "par", value := .nonZeroMarking }
  , { walsCode := "ung", iso := "ung", value := .nonZeroMarking }
  , { walsCode := "uhi", iso := "urf", value := .nonZeroMarking }
  , { walsCode := "usa", iso := "wnu", value := .nonZeroMarking }
  , { walsCode := "vie", iso := "vie", value := .zeroMarking }
  , { walsCode := "wao", iso := "auc", value := .nonZeroMarking }
  , { walsCode := "wra", iso := "wba", value := .nonZeroMarking }
  , { walsCode := "wry", iso := "wrz", value := .nonZeroMarking }
  , { walsCode := "war", iso := "pav", value := .nonZeroMarking }
  , { walsCode := "wrl", iso := "wbp", value := .nonZeroMarking }
  , { walsCode := "wrn", iso := "wnd", value := .nonZeroMarking }
  , { walsCode := "was", iso := "was", value := .nonZeroMarking }
  , { walsCode := "wsk", iso := "wsk", value := .nonZeroMarking }
  , { walsCode := "wem", iso := "xww", value := .nonZeroMarking }
  , { walsCode := "wic", iso := "wic", value := .nonZeroMarking }
  , { walsCode := "wch", iso := "mzh", value := .nonZeroMarking }
  , { walsCode := "win", iso := "wnw", value := .nonZeroMarking }
  , { walsCode := "xok", iso := "xok", value := .nonZeroMarking }
  , { walsCode := "yag", iso := "yad", value := .nonZeroMarking }
  , { walsCode := "yli", iso := "yli", value := .nonZeroMarking }
  , { walsCode := "ynk", iso := "kdd", value := .nonZeroMarking }
  , { walsCode := "yaq", iso := "yaq", value := .nonZeroMarking }
  , { walsCode := "yes", iso := "yss", value := .nonZeroMarking }
  , { walsCode := "yim", iso := "yee", value := .nonZeroMarking }
  , { walsCode := "yor", iso := "yor", value := .nonZeroMarking }
  , { walsCode := "yuc", iso := "yuc", value := .nonZeroMarking }
  , { walsCode := "yko", iso := "yux", value := .nonZeroMarking }
  , { walsCode := "ypk", iso := "esu", value := .nonZeroMarking }
  , { walsCode := "yur", iso := "yur", value := .nonZeroMarking }
  , { walsCode := "zqc", iso := "zoc", value := .nonZeroMarking }
  , { walsCode := "zul", iso := "zul", value := .nonZeroMarking }
  , { walsCode := "zun", iso := "zun", value := .nonZeroMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F25B
