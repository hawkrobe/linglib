import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 42A: Pronominal and Adnominal Demonstratives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 42A`.

Chapter 42, 201 languages.
-/

namespace Core.WALS.F42A

/-- WALS 42A values. -/
inductive PronominalAndAdnominalDemonstratives where
  /-- Identical (143 languages). -/
  | identical
  /-- Different stem (37 languages). -/
  | differentStem
  /-- Different inflection (21 languages). -/
  | differentInflection
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 42A dataset (201 languages). -/
def allData : List (Datapoint PronominalAndAdnominalDemonstratives) :=
  [ { walsCode := "abk", iso := "abk", value := .identical }
  , { walsCode := "ace", iso := "ace", value := .identical }
  , { walsCode := "aco", iso := "kjq", value := .identical }
  , { walsCode := "afr", iso := "afr", value := .identical }
  , { walsCode := "ain", iso := "ain", value := .differentStem }
  , { walsCode := "ala", iso := "amp", value := .identical }
  , { walsCode := "aly", iso := "aly", value := .identical }
  , { walsCode := "amb", iso := "abt", value := .differentStem }
  , { walsCode := "ame", iso := "aey", value := .identical }
  , { walsCode := "any", iso := "anu", value := .differentStem }
  , { walsCode := "ao", iso := "njo", value := .identical }
  , { walsCode := "apl", iso := "apy", value := .identical }
  , { walsCode := "apu", iso := "apu", value := .identical }
  , { walsCode := "abn", iso := "ard", value := .identical }
  , { walsCode := "aeg", iso := "arz", value := .identical }
  , { walsCode := "arg", iso := "afb", value := .differentStem }
  , { walsCode := "arp", iso := "ape", value := .identical }
  , { walsCode := "amp", iso := "aer", value := .identical }
  , { walsCode := "bab", iso := "bav", value := .identical }
  , { walsCode := "bad", iso := "bde", value := .differentStem }
  , { walsCode := "bak", iso := "bkc", value := .differentStem }
  , { walsCode := "brs", iso := "bsn", value := .identical }
  , { walsCode := "bsq", iso := "eus", value := .identical }
  , { walsCode := "bfg", iso := "grr", value := .differentStem }
  , { walsCode := "bur", iso := "bsk", value := .differentInflection }
  , { walsCode := "bya", iso := "bee", value := .differentInflection }
  , { walsCode := "cnl", iso := "ram", value := .identical }
  , { walsCode := "cnt", iso := "yue", value := .identical }
  , { walsCode := "cha", iso := "cha", value := .identical }
  , { walsCode := "cle", iso := "cle", value := .differentInflection }
  , { walsCode := "chk", iso := "ckt", value := .identical }
  , { walsCode := "cmn", iso := "com", value := .identical }
  , { walsCode := "cre", iso := "crk", value := .identical }
  , { walsCode := "cub", iso := "cub", value := .identical }
  , { walsCode := "cze", iso := "ces", value := .identical }
  , { walsCode := "drg", iso := "dar", value := .identical }
  , { walsCode := "djr", iso := "ddj", value := .identical }
  , { walsCode := "don", iso := "kmc", value := .identical }
  , { walsCode := "dre", iso := "dhv", value := .identical }
  , { walsCode := "dyi", iso := "dbl", value := .identical }
  , { walsCode := "egn", iso := "enn", value := .identical }
  , { walsCode := "eng", iso := "eng", value := .identical }
  , { walsCode := "epe", iso := "sja", value := .differentInflection }
  , { walsCode := "eve", iso := "evn", value := .identical }
  , { walsCode := "ewo", iso := "ewo", value := .identical }
  , { walsCode := "fij", iso := "fij", value := .identical }
  , { walsCode := "fin", iso := "fin", value := .identical }
  , { walsCode := "fre", iso := "fra", value := .differentStem }
  , { walsCode := "fut", iso := "fut", value := .identical }
  , { walsCode := "geo", iso := "kat", value := .differentInflection }
  , { walsCode := "ger", iso := "deu", value := .identical }
  , { walsCode := "grk", iso := "ell", value := .identical }
  , { walsCode := "grw", iso := "kal", value := .identical }
  , { walsCode := "gua", iso := "gug", value := .differentStem }
  , { walsCode := "guu", iso := "kky", value := .identical }
  , { walsCode := "hlu", iso := "hur", value := .differentStem }
  , { walsCode := "hau", iso := "hau", value := .identical }
  , { walsCode := "haw", iso := "haw", value := .identical }
  , { walsCode := "heb", iso := "heb", value := .identical }
  , { walsCode := "hix", iso := "hix", value := .identical }
  , { walsCode := "hmo", iso := "hnj", value := .identical }
  , { walsCode := "hun", iso := "hun", value := .identical }
  , { walsCode := "hzb", iso := "huz", value := .differentInflection }
  , { walsCode := "imo", iso := "imn", value := .identical }
  , { walsCode := "ind", iso := "ind", value := .identical }
  , { walsCode := "inr", iso := "ike", value := .identical }
  , { walsCode := "irq", iso := "irk", value := .differentStem }
  , { walsCode := "iri", iso := "gle", value := .identical }
  , { walsCode := "ita", iso := "ita", value := .identical }
  , { walsCode := "jpn", iso := "jpn", value := .differentInflection }
  , { walsCode := "kab", iso := "kbd", value := .differentInflection }
  , { walsCode := "kbl", iso := "kab", value := .differentStem }
  , { walsCode := "krr", iso := "kxa", value := .identical }
  , { walsCode := "kam", iso := "xbr", value := .identical }
  , { walsCode := "knd", iso := "kan", value := .differentInflection }
  , { walsCode := "krg", iso := "sna", value := .identical }
  , { walsCode := "kas", iso := "kas", value := .identical }
  , { walsCode := "kay", iso := "gyd", value := .identical }
  , { walsCode := "ker", iso := "ker", value := .identical }
  , { walsCode := "ket", iso := "ket", value := .differentInflection }
  , { walsCode := "kha", iso := "khk", value := .differentInflection }
  , { walsCode := "khs", iso := "kha", value := .identical }
  , { walsCode := "klb", iso := "hbb", value := .differentStem }
  , { walsCode := "klv", iso := "kij", value := .identical }
  , { walsCode := "kio", iso := "kio", value := .identical }
  , { walsCode := "kis", iso := "kss", value := .identical }
  , { walsCode := "klm", iso := "kla", value := .identical }
  , { walsCode := "koa", iso := "cku", value := .identical }
  , { walsCode := "kob", iso := "kpw", value := .identical }
  , { walsCode := "kok", iso := "trp", value := .differentStem }
  , { walsCode := "kor", iso := "kor", value := .differentStem }
  , { walsCode := "kfe", iso := "kfz", value := .identical }
  , { walsCode := "kos", iso := "kos", value := .identical }
  , { walsCode := "kse", iso := "ses", value := .identical }
  , { walsCode := "kro", iso := "kgo", value := .identical }
  , { walsCode := "knm", iso := "kun", value := .differentStem }
  , { walsCode := "kut", iso := "kut", value := .identical }
  , { walsCode := "kwm", iso := "ksq", value := .identical }
  , { walsCode := "lkt", iso := "lkt", value := .identical }
  , { walsCode := "lan", iso := "laj", value := .differentStem }
  , { walsCode := "lat", iso := "lav", value := .identical }
  , { walsCode := "lav", iso := "lvk", value := .differentStem }
  , { walsCode := "lez", iso := "lez", value := .differentInflection }
  , { walsCode := "lim", iso := "lif", value := .differentInflection }
  , { walsCode := "lit", iso := "lit", value := .identical }
  , { walsCode := "luo", iso := "luo", value := .differentStem }
  , { walsCode := "mac", iso := "mbc", value := .identical }
  , { walsCode := "mak", iso := "myh", value := .identical }
  , { walsCode := "mal", iso := "plt", value := .identical }
  , { walsCode := "mym", iso := "mal", value := .differentInflection }
  , { walsCode := "mlt", iso := "mlt", value := .identical }
  , { walsCode := "mam", iso := "mam", value := .differentStem }
  , { walsCode := "mnd", iso := "cmn", value := .identical }
  , { walsCode := "mao", iso := "mri", value := .identical }
  , { walsCode := "map", iso := "arn", value := .differentStem }
  , { walsCode := "mhi", iso := "mar", value := .identical }
  , { walsCode := "mrg", iso := "mrt", value := .differentStem }
  , { walsCode := "mar", iso := "mrc", value := .identical }
  , { walsCode := "msh", iso := "mah", value := .identical }
  , { walsCode := "mrt", iso := "vma", value := .identical }
  , { walsCode := "mau", iso := "mph", value := .identical }
  , { walsCode := "may", iso := "ayz", value := .identical }
  , { walsCode := "mei", iso := "mni", value := .identical }
  , { walsCode := "mss", iso := "skd", value := .identical }
  , { walsCode := "miy", iso := "mkf", value := .identical }
  , { walsCode := "moj", iso := "mov", value := .identical }
  , { walsCode := "mul", iso := "mlm", value := .differentStem }
  , { walsCode := "nan", iso := "niq", value := .differentStem }
  , { walsCode := "nav", iso := "nav", value := .identical }
  , { walsCode := "ndy", iso := "djk", value := .differentStem }
  , { walsCode := "nez", iso := "nez", value := .identical }
  , { walsCode := "ngl", iso := "nig", value := .identical }
  , { walsCode := "nti", iso := "niy", value := .identical }
  , { walsCode := "ngi", iso := "wyb", value := .identical }
  , { walsCode := "ngz", iso := "ngi", value := .differentStem }
  , { walsCode := "niv", iso := "niv", value := .differentInflection }
  , { walsCode := "nko", iso := "cgg", value := .identical }
  , { walsCode := "nku", iso := "xnz", value := .identical }
  , { walsCode := "nun", iso := "nut", value := .identical }
  , { walsCode := "nug", iso := "nuy", value := .identical }
  , { walsCode := "ond", iso := "one", value := .identical }
  , { walsCode := "orh", iso := "hae", value := .identical }
  , { walsCode := "pkn", iso := "drl", value := .identical }
  , { walsCode := "put", iso := "ute", value := .identical }
  , { walsCode := "pai", iso := "pwn", value := .identical }
  , { walsCode := "pnn", iso := "pag", value := .differentStem }
  , { walsCode := "pan", iso := "pan", value := .identical }
  , { walsCode := "psm", iso := "pqm", value := .identical }
  , { walsCode := "pau", iso := "pad", value := .identical }
  , { walsCode := "prs", iso := "pes", value := .differentInflection }
  , { walsCode := "pip", iso := "ppl", value := .identical }
  , { walsCode := "prh", iso := "myp", value := .identical }
  , { walsCode := "poh", iso := "pon", value := .differentStem }
  , { walsCode := "qhu", iso := "qub", value := .identical }
  , { walsCode := "rap", iso := "rap", value := .identical }
  , { walsCode := "ret", iso := "tnc", value := .identical }
  , { walsCode := "rus", iso := "rus", value := .identical }
  , { walsCode := "sam", iso := "smo", value := .identical }
  , { walsCode := "sml", iso := "sza", value := .identical }
  , { walsCode := "sla", iso := "den", value := .identical }
  , { walsCode := "so", iso := "teu", value := .differentStem }
  , { walsCode := "som", iso := "som", value := .differentInflection }
  , { walsCode := "spa", iso := "spa", value := .identical }
  , { walsCode := "sup", iso := "spp", value := .identical }
  , { walsCode := "swa", iso := "swh", value := .identical }
  , { walsCode := "swe", iso := "swe", value := .identical }
  , { walsCode := "tag", iso := "tgl", value := .identical }
  , { walsCode := "tml", iso := "tam", value := .differentInflection }
  , { walsCode := "tas", iso := "shi", value := .differentStem }
  , { walsCode := "tau", iso := "tya", value := .differentInflection }
  , { walsCode := "tiw", iso := "tiw", value := .identical }
  , { walsCode := "tng", iso := "ton", value := .differentStem }
  , { walsCode := "tru", iso := "tpy", value := .identical }
  , { walsCode := "tuk", iso := "", value := .identical }
  , { walsCode := "tur", iso := "tur", value := .differentInflection }
  , { walsCode := "tus", iso := "tus", value := .identical }
  , { walsCode := "tvl", iso := "tvl", value := .identical }
  , { walsCode := "tzu", iso := "tzj", value := .identical }
  , { walsCode := "tsh", iso := "par", value := .identical }
  , { walsCode := "udh", iso := "ude", value := .differentInflection }
  , { walsCode := "urd", iso := "urd", value := .identical }
  , { walsCode := "uri", iso := "uri", value := .identical }
  , { walsCode := "urk", iso := "urb", value := .identical }
  , { walsCode := "ute", iso := "ute", value := .identical }
  , { walsCode := "wam", iso := "wmb", value := .identical }
  , { walsCode := "wra", iso := "wba", value := .differentStem }
  , { walsCode := "wrd", iso := "wrr", value := .identical }
  , { walsCode := "wrk", iso := "gae", value := .identical }
  , { walsCode := "war", iso := "pav", value := .differentStem }
  , { walsCode := "wrg", iso := "wgy", value := .identical }
  , { walsCode := "wat", iso := "wbv", value := .identical }
  , { walsCode := "wel", iso := "cym", value := .differentStem }
  , { walsCode := "wic", iso := "wic", value := .identical }
  , { walsCode := "wly", iso := "wal", value := .differentStem }
  , { walsCode := "ygr", iso := "ygr", value := .differentStem }
  , { walsCode := "yag", iso := "yad", value := .identical }
  , { walsCode := "ynk", iso := "kdd", value := .identical }
  , { walsCode := "yim", iso := "yee", value := .identical }
  , { walsCode := "yor", iso := "yor", value := .identical }
  , { walsCode := "yko", iso := "yux", value := .differentStem }
  , { walsCode := "yus", iso := "ess", value := .identical }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F42A
