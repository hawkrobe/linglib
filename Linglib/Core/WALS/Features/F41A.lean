import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 41A: Distance Contrasts in Demonstratives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 41A`.

Chapter 41, 234 languages.
-/

namespace Core.WALS.F41A

/-- WALS 41A values. -/
inductive DistanceContrastsInDemonstratives where
  /-- No distance contrast (7 languages). -/
  | noDistanceContrast
  /-- Two-way contrast (126 languages). -/
  | twoWayContrast
  /-- Three-way contrast (88 languages). -/
  | threeWayContrast
  /-- Four-way contrast (9 languages). -/
  | fourWayContrast
  /-- Five (or more)-way contrast (4 languages). -/
  | fiveWayContrast
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 41A dataset (234 languages). -/
def allData : List (Datapoint DistanceContrastsInDemonstratives) :=
  [ { walsCode := "ani", iso := "hnh", value := .threeWayContrast }
  , { walsCode := "abk", iso := "abk", value := .twoWayContrast }
  , { walsCode := "ace", iso := "ace", value := .threeWayContrast }
  , { walsCode := "aco", iso := "kjq", value := .threeWayContrast }
  , { walsCode := "afr", iso := "afr", value := .twoWayContrast }
  , { walsCode := "ain", iso := "ain", value := .twoWayContrast }
  , { walsCode := "ala", iso := "amp", value := .twoWayContrast }
  , { walsCode := "aly", iso := "aly", value := .threeWayContrast }
  , { walsCode := "amb", iso := "abt", value := .threeWayContrast }
  , { walsCode := "ame", iso := "aey", value := .threeWayContrast }
  , { walsCode := "any", iso := "anu", value := .threeWayContrast }
  , { walsCode := "ao", iso := "njo", value := .twoWayContrast }
  , { walsCode := "apl", iso := "apy", value := .threeWayContrast }
  , { walsCode := "apu", iso := "apu", value := .twoWayContrast }
  , { walsCode := "abn", iso := "ard", value := .threeWayContrast }
  , { walsCode := "aeg", iso := "arz", value := .twoWayContrast }
  , { walsCode := "arg", iso := "afb", value := .twoWayContrast }
  , { walsCode := "arp", iso := "ape", value := .twoWayContrast }
  , { walsCode := "amp", iso := "aer", value := .threeWayContrast }
  , { walsCode := "asm", iso := "cns", value := .fourWayContrast }
  , { walsCode := "bad", iso := "bde", value := .twoWayContrast }
  , { walsCode := "bak", iso := "bkc", value := .twoWayContrast }
  , { walsCode := "brs", iso := "bsn", value := .threeWayContrast }
  , { walsCode := "bsq", iso := "eus", value := .threeWayContrast }
  , { walsCode := "bel", iso := "byw", value := .twoWayContrast }
  , { walsCode := "bfg", iso := "grr", value := .twoWayContrast }
  , { walsCode := "brm", iso := "mya", value := .twoWayContrast }
  , { walsCode := "bur", iso := "bsk", value := .twoWayContrast }
  , { walsCode := "bya", iso := "bee", value := .twoWayContrast }
  , { walsCode := "cnl", iso := "ram", value := .twoWayContrast }
  , { walsCode := "cnt", iso := "yue", value := .twoWayContrast }
  , { walsCode := "cha", iso := "cha", value := .threeWayContrast }
  , { walsCode := "cle", iso := "cle", value := .threeWayContrast }
  , { walsCode := "chk", iso := "ckt", value := .threeWayContrast }
  , { walsCode := "cmn", iso := "com", value := .threeWayContrast }
  , { walsCode := "coo", iso := "csz", value := .twoWayContrast }
  , { walsCode := "cre", iso := "crk", value := .threeWayContrast }
  , { walsCode := "cub", iso := "cub", value := .twoWayContrast }
  , { walsCode := "cze", iso := "ces", value := .twoWayContrast }
  , { walsCode := "drg", iso := "dar", value := .threeWayContrast }
  , { walsCode := "djr", iso := "ddj", value := .twoWayContrast }
  , { walsCode := "don", iso := "kmc", value := .threeWayContrast }
  , { walsCode := "dre", iso := "dhv", value := .twoWayContrast }
  , { walsCode := "dyi", iso := "dbl", value := .twoWayContrast }
  , { walsCode := "egn", iso := "enn", value := .twoWayContrast }
  , { walsCode := "eng", iso := "eng", value := .twoWayContrast }
  , { walsCode := "epe", iso := "sja", value := .twoWayContrast }
  , { walsCode := "evn", iso := "eve", value := .twoWayContrast }
  , { walsCode := "eve", iso := "evn", value := .twoWayContrast }
  , { walsCode := "ewe", iso := "ewe", value := .twoWayContrast }
  , { walsCode := "ewo", iso := "ewo", value := .threeWayContrast }
  , { walsCode := "fij", iso := "fij", value := .threeWayContrast }
  , { walsCode := "fin", iso := "fin", value := .twoWayContrast }
  , { walsCode := "fre", iso := "fra", value := .noDistanceContrast }
  , { walsCode := "fut", iso := "fut", value := .threeWayContrast }
  , { walsCode := "geo", iso := "kat", value := .threeWayContrast }
  , { walsCode := "ger", iso := "deu", value := .noDistanceContrast }
  , { walsCode := "goo", iso := "gni", value := .twoWayContrast }
  , { walsCode := "grk", iso := "ell", value := .threeWayContrast }
  , { walsCode := "grw", iso := "kal", value := .threeWayContrast }
  , { walsCode := "gua", iso := "gug", value := .threeWayContrast }
  , { walsCode := "guu", iso := "kky", value := .twoWayContrast }
  , { walsCode := "hlu", iso := "hur", value := .threeWayContrast }
  , { walsCode := "hau", iso := "hau", value := .fourWayContrast }
  , { walsCode := "haw", iso := "haw", value := .threeWayContrast }
  , { walsCode := "hdi", iso := "xed", value := .threeWayContrast }
  , { walsCode := "heb", iso := "heb", value := .twoWayContrast }
  , { walsCode := "hix", iso := "hix", value := .threeWayContrast }
  , { walsCode := "hmo", iso := "hnj", value := .threeWayContrast }
  , { walsCode := "hua", iso := "ygr", value := .threeWayContrast }
  , { walsCode := "hun", iso := "hun", value := .twoWayContrast }
  , { walsCode := "hzb", iso := "huz", value := .threeWayContrast }
  , { walsCode := "ika", iso := "arh", value := .threeWayContrast }
  , { walsCode := "imo", iso := "imn", value := .twoWayContrast }
  , { walsCode := "ind", iso := "ind", value := .twoWayContrast }
  , { walsCode := "ing", iso := "inh", value := .twoWayContrast }
  , { walsCode := "inr", iso := "ike", value := .twoWayContrast }
  , { walsCode := "irq", iso := "irk", value := .fourWayContrast }
  , { walsCode := "iri", iso := "gle", value := .threeWayContrast }
  , { walsCode := "ita", iso := "ita", value := .twoWayContrast }
  , { walsCode := "jak", iso := "jac", value := .twoWayContrast }
  , { walsCode := "jpn", iso := "jpn", value := .threeWayContrast }
  , { walsCode := "juh", iso := "ktz", value := .threeWayContrast }
  , { walsCode := "kab", iso := "kbd", value := .twoWayContrast }
  , { walsCode := "kbl", iso := "kab", value := .threeWayContrast }
  , { walsCode := "krr", iso := "kxa", value := .threeWayContrast }
  , { walsCode := "kam", iso := "xbr", value := .fourWayContrast }
  , { walsCode := "knd", iso := "kan", value := .twoWayContrast }
  , { walsCode := "knr", iso := "knc", value := .twoWayContrast }
  , { walsCode := "krg", iso := "sna", value := .twoWayContrast }
  , { walsCode := "kas", iso := "kas", value := .twoWayContrast }
  , { walsCode := "kyl", iso := "eky", value := .twoWayContrast }
  , { walsCode := "kay", iso := "gyd", value := .twoWayContrast }
  , { walsCode := "ker", iso := "ker", value := .noDistanceContrast }
  , { walsCode := "ket", iso := "ket", value := .threeWayContrast }
  , { walsCode := "kha", iso := "khk", value := .twoWayContrast }
  , { walsCode := "khs", iso := "kha", value := .threeWayContrast }
  , { walsCode := "klb", iso := "hbb", value := .threeWayContrast }
  , { walsCode := "klv", iso := "kij", value := .threeWayContrast }
  , { walsCode := "kio", iso := "kio", value := .twoWayContrast }
  , { walsCode := "kis", iso := "kss", value := .twoWayContrast }
  , { walsCode := "klm", iso := "kla", value := .twoWayContrast }
  , { walsCode := "koa", iso := "cku", value := .fiveWayContrast }
  , { walsCode := "kob", iso := "kpw", value := .twoWayContrast }
  , { walsCode := "kok", iso := "trp", value := .twoWayContrast }
  , { walsCode := "kor", iso := "kor", value := .threeWayContrast }
  , { walsCode := "kfe", iso := "kfz", value := .noDistanceContrast }
  , { walsCode := "kos", iso := "kos", value := .threeWayContrast }
  , { walsCode := "kse", iso := "ses", value := .noDistanceContrast }
  , { walsCode := "kro", iso := "kgo", value := .threeWayContrast }
  , { walsCode := "knm", iso := "kun", value := .twoWayContrast }
  , { walsCode := "kut", iso := "kut", value := .threeWayContrast }
  , { walsCode := "kwa", iso := "kwd", value := .twoWayContrast }
  , { walsCode := "kwm", iso := "ksq", value := .twoWayContrast }
  , { walsCode := "lkt", iso := "lkt", value := .threeWayContrast }
  , { walsCode := "lan", iso := "laj", value := .threeWayContrast }
  , { walsCode := "lat", iso := "lav", value := .twoWayContrast }
  , { walsCode := "lav", iso := "lvk", value := .threeWayContrast }
  , { walsCode := "lez", iso := "lez", value := .threeWayContrast }
  , { walsCode := "lim", iso := "lif", value := .twoWayContrast }
  , { walsCode := "lit", iso := "lit", value := .twoWayContrast }
  , { walsCode := "lon", iso := "los", value := .twoWayContrast }
  , { walsCode := "luo", iso := "luo", value := .threeWayContrast }
  , { walsCode := "mac", iso := "mbc", value := .twoWayContrast }
  , { walsCode := "mak", iso := "myh", value := .twoWayContrast }
  , { walsCode := "mal", iso := "plt", value := .fiveWayContrast }
  , { walsCode := "mym", iso := "mal", value := .twoWayContrast }
  , { walsCode := "mlt", iso := "mlt", value := .twoWayContrast }
  , { walsCode := "mam", iso := "mam", value := .noDistanceContrast }
  , { walsCode := "mnm", iso := "mva", value := .twoWayContrast }
  , { walsCode := "mnd", iso := "cmn", value := .twoWayContrast }
  , { walsCode := "mao", iso := "mri", value := .threeWayContrast }
  , { walsCode := "map", iso := "arn", value := .threeWayContrast }
  , { walsCode := "mhi", iso := "mar", value := .twoWayContrast }
  , { walsCode := "mrg", iso := "mrt", value := .twoWayContrast }
  , { walsCode := "mar", iso := "mrc", value := .fiveWayContrast }
  , { walsCode := "msh", iso := "mah", value := .fourWayContrast }
  , { walsCode := "mrt", iso := "vma", value := .twoWayContrast }
  , { walsCode := "mau", iso := "mph", value := .threeWayContrast }
  , { walsCode := "may", iso := "ayz", value := .threeWayContrast }
  , { walsCode := "mei", iso := "mni", value := .twoWayContrast }
  , { walsCode := "mss", iso := "skd", value := .twoWayContrast }
  , { walsCode := "mxc", iso := "mig", value := .twoWayContrast }
  , { walsCode := "miy", iso := "mkf", value := .twoWayContrast }
  , { walsCode := "moj", iso := "mov", value := .twoWayContrast }
  , { walsCode := "mok", iso := "mkj", value := .threeWayContrast }
  , { walsCode := "mul", iso := "mlm", value := .twoWayContrast }
  , { walsCode := "kho", iso := "naq", value := .twoWayContrast }
  , { walsCode := "nan", iso := "niq", value := .threeWayContrast }
  , { walsCode := "nav", iso := "nav", value := .fiveWayContrast }
  , { walsCode := "ndy", iso := "djk", value := .twoWayContrast }
  , { walsCode := "nez", iso := "nez", value := .twoWayContrast }
  , { walsCode := "ngl", iso := "nig", value := .twoWayContrast }
  , { walsCode := "nti", iso := "niy", value := .threeWayContrast }
  , { walsCode := "ngi", iso := "wyb", value := .twoWayContrast }
  , { walsCode := "ngz", iso := "ngi", value := .twoWayContrast }
  , { walsCode := "niv", iso := "niv", value := .twoWayContrast }
  , { walsCode := "nko", iso := "cgg", value := .threeWayContrast }
  , { walsCode := "nbd", iso := "dgl", value := .twoWayContrast }
  , { walsCode := "nku", iso := "xnz", value := .twoWayContrast }
  , { walsCode := "nun", iso := "nut", value := .twoWayContrast }
  , { walsCode := "nug", iso := "nuy", value := .threeWayContrast }
  , { walsCode := "ond", iso := "one", value := .twoWayContrast }
  , { walsCode := "orh", iso := "hae", value := .twoWayContrast }
  , { walsCode := "pkn", iso := "drl", value := .fourWayContrast }
  , { walsCode := "pai", iso := "pwn", value := .twoWayContrast }
  , { walsCode := "pnn", iso := "pag", value := .twoWayContrast }
  , { walsCode := "pan", iso := "pan", value := .twoWayContrast }
  , { walsCode := "psm", iso := "pqm", value := .threeWayContrast }
  , { walsCode := "pau", iso := "pad", value := .threeWayContrast }
  , { walsCode := "prs", iso := "pes", value := .twoWayContrast }
  , { walsCode := "pip", iso := "ppl", value := .twoWayContrast }
  , { walsCode := "prh", iso := "myp", value := .twoWayContrast }
  , { walsCode := "poh", iso := "pon", value := .threeWayContrast }
  , { walsCode := "qhu", iso := "qub", value := .threeWayContrast }
  , { walsCode := "qui", iso := "qui", value := .fourWayContrast }
  , { walsCode := "ram", iso := "rma", value := .twoWayContrast }
  , { walsCode := "rap", iso := "rap", value := .threeWayContrast }
  , { walsCode := "ret", iso := "tnc", value := .twoWayContrast }
  , { walsCode := "rus", iso := "rus", value := .twoWayContrast }
  , { walsCode := "sam", iso := "smo", value := .threeWayContrast }
  , { walsCode := "snm", iso := "xsu", value := .threeWayContrast }
  , { walsCode := "sml", iso := "sza", value := .twoWayContrast }
  , { walsCode := "sla", iso := "den", value := .twoWayContrast }
  , { walsCode := "so", iso := "teu", value := .twoWayContrast }
  , { walsCode := "som", iso := "som", value := .fourWayContrast }
  , { walsCode := "spa", iso := "spa", value := .threeWayContrast }
  , { walsCode := "sup", iso := "spp", value := .noDistanceContrast }
  , { walsCode := "swa", iso := "swh", value := .twoWayContrast }
  , { walsCode := "swt", iso := "ssw", value := .threeWayContrast }
  , { walsCode := "swe", iso := "swe", value := .twoWayContrast }
  , { walsCode := "tag", iso := "tgl", value := .threeWayContrast }
  , { walsCode := "tml", iso := "tam", value := .twoWayContrast }
  , { walsCode := "tas", iso := "shi", value := .threeWayContrast }
  , { walsCode := "tau", iso := "tya", value := .twoWayContrast }
  , { walsCode := "tin", iso := "cir", value := .threeWayContrast }
  , { walsCode := "twn", iso := "twf", value := .threeWayContrast }
  , { walsCode := "tiw", iso := "tiw", value := .twoWayContrast }
  , { walsCode := "tli", iso := "tli", value := .fourWayContrast }
  , { walsCode := "tng", iso := "ton", value := .twoWayContrast }
  , { walsCode := "ton", iso := "tqw", value := .threeWayContrast }
  , { walsCode := "tru", iso := "tpy", value := .twoWayContrast }
  , { walsCode := "tsi", iso := "tsi", value := .twoWayContrast }
  , { walsCode := "tuk", iso := "", value := .threeWayContrast }
  , { walsCode := "tna", iso := "tuv", value := .twoWayContrast }
  , { walsCode := "tur", iso := "tur", value := .twoWayContrast }
  , { walsCode := "tus", iso := "tus", value := .twoWayContrast }
  , { walsCode := "tvl", iso := "tvl", value := .threeWayContrast }
  , { walsCode := "tzu", iso := "tzj", value := .threeWayContrast }
  , { walsCode := "tsh", iso := "par", value := .threeWayContrast }
  , { walsCode := "udh", iso := "ude", value := .twoWayContrast }
  , { walsCode := "urd", iso := "urd", value := .twoWayContrast }
  , { walsCode := "uri", iso := "uri", value := .threeWayContrast }
  , { walsCode := "urk", iso := "urb", value := .threeWayContrast }
  , { walsCode := "ute", iso := "ute", value := .twoWayContrast }
  , { walsCode := "vie", iso := "vie", value := .twoWayContrast }
  , { walsCode := "wam", iso := "wmb", value := .twoWayContrast }
  , { walsCode := "wra", iso := "wba", value := .threeWayContrast }
  , { walsCode := "wrd", iso := "wrr", value := .threeWayContrast }
  , { walsCode := "wrk", iso := "gae", value := .twoWayContrast }
  , { walsCode := "war", iso := "pav", value := .threeWayContrast }
  , { walsCode := "wrg", iso := "wgy", value := .twoWayContrast }
  , { walsCode := "wat", iso := "wbv", value := .threeWayContrast }
  , { walsCode := "wel", iso := "cym", value := .twoWayContrast }
  , { walsCode := "wic", iso := "wic", value := .twoWayContrast }
  , { walsCode := "wly", iso := "wal", value := .twoWayContrast }
  , { walsCode := "ygr", iso := "ygr", value := .threeWayContrast }
  , { walsCode := "yag", iso := "yad", value := .twoWayContrast }
  , { walsCode := "ynk", iso := "kdd", value := .twoWayContrast }
  , { walsCode := "yid", iso := "yii", value := .threeWayContrast }
  , { walsCode := "yim", iso := "yee", value := .threeWayContrast }
  , { walsCode := "yor", iso := "yor", value := .twoWayContrast }
  , { walsCode := "yko", iso := "yux", value := .twoWayContrast }
  , { walsCode := "yus", iso := "ess", value := .twoWayContrast }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F41A
