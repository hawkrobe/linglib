import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 30A: Number of Genders
@cite{corbett-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 30A`.

Chapter 30, 257 languages.
-/

namespace Datasets.WALS.F30A

/-- WALS 30A values. -/
inductive GenderCount where
  /-- None (145 languages). -/
  | none
  /-- Two (50 languages). -/
  | two
  /-- Three (26 languages). -/
  | three
  /-- Four (12 languages). -/
  | four
  /-- Five or more (24 languages). -/
  | fiveOrMore
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 30A dataset (257 languages). -/
def allData : List (Datapoint GenderCount) :=
  [ { walsCode := "abk", iso := "abk", value := .three }
  , { walsCode := "aco", iso := "kjq", value := .none }
  , { walsCode := "ain", iso := "ain", value := .none }
  , { walsCode := "agw", iso := "wbj", value := .two }
  , { walsCode := "ala", iso := "amp", value := .two }
  , { walsCode := "ale", iso := "ale", value := .none }
  , { walsCode := "ame", iso := "aey", value := .none }
  , { walsCode := "amh", iso := "amh", value := .two }
  , { walsCode := "apu", iso := "apu", value := .two }
  , { walsCode := "abn", iso := "ard", value := .none }
  , { walsCode := "aeg", iso := "arz", value := .two }
  , { walsCode := "arg", iso := "afb", value := .two }
  , { walsCode := "asy", iso := "apc", value := .two }
  , { walsCode := "arp", iso := "ape", value := .fiveOrMore }
  , { walsCode := "abo", iso := "arv", value := .two }
  , { walsCode := "arc", iso := "aqc", value := .four }
  , { walsCode := "arm", iso := "hye", value := .none }
  , { walsCode := "asm", iso := "cns", value := .none }
  , { walsCode := "awp", iso := "kwi", value := .none }
  , { walsCode := "bab", iso := "bav", value := .fiveOrMore }
  , { walsCode := "bag", iso := "bmi", value := .none }
  , { walsCode := "brs", iso := "bsn", value := .three }
  , { walsCode := "bsq", iso := "eus", value := .none }
  , { walsCode := "bkr", iso := "btx", value := .none }
  , { walsCode := "baw", iso := "bgr", value := .none }
  , { walsCode := "bys", iso := "bsw", value := .two }
  , { walsCode := "bej", iso := "bej", value := .two }
  , { walsCode := "bma", iso := "tzm", value := .two }
  , { walsCode := "bbw", iso := "gup", value := .four }
  , { walsCode := "brh", iso := "brh", value := .none }
  , { walsCode := "brm", iso := "mya", value := .none }
  , { walsCode := "bur", iso := "bsk", value := .four }
  , { walsCode := "cah", iso := "chl", value := .none }
  , { walsCode := "cax", iso := "", value := .two }
  , { walsCode := "cnl", iso := "ram", value := .none }
  , { walsCode := "cnt", iso := "yue", value := .none }
  , { walsCode := "car", iso := "car", value := .none }
  , { walsCode := "cyv", iso := "cyb", value := .none }
  , { walsCode := "cha", iso := "cha", value := .none }
  , { walsCode := "cic", iso := "nya", value := .fiveOrMore }
  , { walsCode := "chi", iso := "cid", value := .none }
  , { walsCode := "cle", iso := "cle", value := .two }
  , { walsCode := "chk", iso := "ckt", value := .none }
  , { walsCode := "chv", iso := "chv", value := .none }
  , { walsCode := "ccp", iso := "coc", value := .none }
  , { walsCode := "cmn", iso := "com", value := .none }
  , { walsCode := "coo", iso := "csz", value := .none }
  , { walsCode := "cre", iso := "crk", value := .two }
  , { walsCode := "dag", iso := "dgz", value := .none }
  , { walsCode := "dni", iso := "dni", value := .none }
  , { walsCode := "def", iso := "afn", value := .three }
  , { walsCode := "dio", iso := "dyo", value := .fiveOrMore }
  , { walsCode := "diy", iso := "dif", value := .two }
  , { walsCode := "diz", iso := "mdx", value := .two }
  , { walsCode := "djr", iso := "ddj", value := .none }
  , { walsCode := "don", iso := "kmc", value := .none }
  , { walsCode := "dyi", iso := "dbl", value := .four }
  , { walsCode := "eng", iso := "eng", value := .three }
  , { walsCode := "epe", iso := "sja", value := .none }
  , { walsCode := "err", iso := "erg", value := .none }
  , { walsCode := "eve", iso := "evn", value := .none }
  , { walsCode := "ewe", iso := "ewe", value := .none }
  , { walsCode := "fij", iso := "fij", value := .none }
  , { walsCode := "fin", iso := "fin", value := .none }
  , { walsCode := "fre", iso := "fra", value := .two }
  , { walsCode := "fgu", iso := "fuf", value := .fiveOrMore }
  , { walsCode := "gae", iso := "gla", value := .two }
  , { walsCode := "geo", iso := "kat", value := .none }
  , { walsCode := "ger", iso := "deu", value := .three }
  , { walsCode := "gdi", iso := "god", value := .four }
  , { walsCode := "god", iso := "gdo", value := .three }
  , { walsCode := "goo", iso := "gni", value := .none }
  , { walsCode := "grb", iso := "grj", value := .three }
  , { walsCode := "grk", iso := "ell", value := .three }
  , { walsCode := "grw", iso := "kal", value := .none }
  , { walsCode := "gua", iso := "gug", value := .none }
  , { walsCode := "guu", iso := "kky", value := .none }
  , { walsCode := "hai", iso := "hai", value := .none }
  , { walsCode := "hat", iso := "had", value := .none }
  , { walsCode := "hau", iso := "hau", value := .two }
  , { walsCode := "haw", iso := "haw", value := .none }
  , { walsCode := "hay", iso := "vay", value := .none }
  , { walsCode := "heb", iso := "heb", value := .two }
  , { walsCode := "hin", iso := "hin", value := .two }
  , { walsCode := "hix", iso := "hix", value := .two }
  , { walsCode := "hmo", iso := "hnj", value := .none }
  , { walsCode := "hun", iso := "hun", value := .none }
  , { walsCode := "hzb", iso := "huz", value := .fiveOrMore }
  , { walsCode := "iaa", iso := "iai", value := .none }
  , { walsCode := "ice", iso := "isl", value := .three }
  , { walsCode := "igb", iso := "ibo", value := .none }
  , { walsCode := "ika", iso := "arh", value := .none }
  , { walsCode := "imo", iso := "imn", value := .none }
  , { walsCode := "ind", iso := "ind", value := .none }
  , { walsCode := "ing", iso := "inh", value := .fiveOrMore }
  , { walsCode := "irq", iso := "irk", value := .two }
  , { walsCode := "ite", iso := "itl", value := .none }
  , { walsCode := "jaq", iso := "jqr", value := .none }
  , { walsCode := "juh", iso := "ktz", value := .fiveOrMore }
  , { walsCode := "kam", iso := "xbr", value := .none }
  , { walsCode := "knd", iso := "kan", value := .three }
  , { walsCode := "knr", iso := "knc", value := .none }
  , { walsCode := "krk", iso := "kyh", value := .none }
  , { walsCode := "kas", iso := "kas", value := .two }
  , { walsCode := "kay", iso := "gyd", value := .none }
  , { walsCode := "ket", iso := "ket", value := .three }
  , { walsCode := "kew", iso := "kew", value := .none }
  , { walsCode := "khk", iso := "kjh", value := .none }
  , { walsCode := "khl", iso := "klj", value := .none }
  , { walsCode := "kha", iso := "khk", value := .none }
  , { walsCode := "khs", iso := "kha", value := .two }
  , { walsCode := "khm", iso := "khm", value := .none }
  , { walsCode := "kmu", iso := "kjg", value := .two }
  , { walsCode := "klv", iso := "kij", value := .none }
  , { walsCode := "kgz", iso := "kir", value := .none }
  , { walsCode := "kis", iso := "kss", value := .fiveOrMore }
  , { walsCode := "koa", iso := "cku", value := .none }
  , { walsCode := "kob", iso := "kpw", value := .none }
  , { walsCode := "kol", iso := "kfb", value := .two }
  , { walsCode := "kon", iso := "kng", value := .fiveOrMore }
  , { walsCode := "kfe", iso := "kfz", value := .three }
  , { walsCode := "kse", iso := "ses", value := .none }
  , { walsCode := "kut", iso := "kut", value := .none }
  , { walsCode := "lad", iso := "lbj", value := .none }
  , { walsCode := "lah", iso := "lhu", value := .none }
  , { walsCode := "lak", iso := "lbe", value := .four }
  , { walsCode := "lan", iso := "laj", value := .none }
  , { walsCode := "lat", iso := "lav", value := .two }
  , { walsCode := "lav", iso := "lvk", value := .three }
  , { walsCode := "lel", iso := "lln", value := .two }
  , { walsCode := "lep", iso := "lep", value := .none }
  , { walsCode := "lez", iso := "lez", value := .none }
  , { walsCode := "lin", iso := "lin", value := .fiveOrMore }
  , { walsCode := "luv", iso := "lue", value := .fiveOrMore }
  , { walsCode := "mac", iso := "mbc", value := .two }
  , { walsCode := "mak", iso := "myh", value := .none }
  , { walsCode := "mal", iso := "plt", value := .none }
  , { walsCode := "mlt", iso := "mlt", value := .two }
  , { walsCode := "mnd", iso := "cmn", value := .none }
  , { walsCode := "myi", iso := "mpc", value := .three }
  , { walsCode := "mns", iso := "mns", value := .none }
  , { walsCode := "mao", iso := "mri", value := .none }
  , { walsCode := "map", iso := "arn", value := .none }
  , { walsCode := "mhi", iso := "mar", value := .three }
  , { walsCode := "mny", iso := "zmc", value := .none }
  , { walsCode := "mar", iso := "mrc", value := .none }
  , { walsCode := "mrd", iso := "mrz", value := .four }
  , { walsCode := "mrt", iso := "vma", value := .none }
  , { walsCode := "mau", iso := "mph", value := .fiveOrMore }
  , { walsCode := "may", iso := "ayz", value := .two }
  , { walsCode := "mei", iso := "mni", value := .none }
  , { walsCode := "mss", iso := "skd", value := .none }
  , { walsCode := "mxc", iso := "mig", value := .fiveOrMore }
  , { walsCode := "miy", iso := "mkf", value := .two }
  , { walsCode := "mok", iso := "mkj", value := .none }
  , { walsCode := "mos", iso := "cas", value := .two }
  , { walsCode := "mun", iso := "unr", value := .two }
  , { walsCode := "mrl", iso := "mur", value := .none }
  , { walsCode := "nht", iso := "nhg", value := .none }
  , { walsCode := "kho", iso := "naq", value := .three }
  , { walsCode := "ndy", iso := "djk", value := .none }
  , { walsCode := "ntu", iso := "yrk", value := .none }
  , { walsCode := "nez", iso := "nez", value := .none }
  , { walsCode := "ngg", iso := "nam", value := .fiveOrMore }
  , { walsCode := "ngi", iso := "wyb", value := .none }
  , { walsCode := "nca", iso := "caq", value := .three }
  , { walsCode := "niv", iso := "niv", value := .none }
  , { walsCode := "nko", iso := "cgg", value := .fiveOrMore }
  , { walsCode := "nbd", iso := "dgl", value := .none }
  , { walsCode := "nug", iso := "nuy", value := .fiveOrMore }
  , { walsCode := "nym", iso := "nym", value := .fiveOrMore }
  , { walsCode := "nyh", iso := "nih", value := .fiveOrMore }
  , { walsCode := "oji", iso := "", value := .two }
  , { walsCode := "ond", iso := "one", value := .three }
  , { walsCode := "ork", iso := "oaa", value := .none }
  , { walsCode := "orh", iso := "hae", value := .two }
  , { walsCode := "otm", iso := "ote", value := .none }
  , { walsCode := "pai", iso := "pwn", value := .none }
  , { walsCode := "pal", iso := "pau", value := .none }
  , { walsCode := "pan", iso := "pan", value := .two }
  , { walsCode := "psh", iso := "pst", value := .two }
  , { walsCode := "psm", iso := "pqm", value := .two }
  , { walsCode := "pau", iso := "pad", value := .four }
  , { walsCode := "prs", iso := "pes", value := .none }
  , { walsCode := "pil", iso := "piv", value := .none }
  , { walsCode := "pip", iso := "ppl", value := .none }
  , { walsCode := "prh", iso := "myp", value := .four }
  , { walsCode := "pit", iso := "pjt", value := .none }
  , { walsCode := "ppi", iso := "pit", value := .two }
  , { walsCode := "pmc", iso := "poo", value := .none }
  , { walsCode := "qaf", iso := "aar", value := .two }
  , { walsCode := "qim", iso := "qvi", value := .none }
  , { walsCode := "ram", iso := "rma", value := .none }
  , { walsCode := "rap", iso := "rap", value := .none }
  , { walsCode := "ren", iso := "rel", value := .two }
  , { walsCode := "ret", iso := "tnc", value := .three }
  , { walsCode := "rus", iso := "rus", value := .three }
  , { walsCode := "smt", iso := "uma", value := .none }
  , { walsCode := "san", iso := "sag", value := .none }
  , { walsCode := "saw", iso := "hvn", value := .none }
  , { walsCode := "sml", iso := "sza", value := .none }
  , { walsCode := "snc", iso := "see", value := .three }
  , { walsCode := "snt", iso := "set", value := .none }
  , { walsCode := "shk", iso := "shp", value := .none }
  , { walsCode := "shn", iso := "sna", value := .fiveOrMore }
  , { walsCode := "srn", iso := "srq", value := .none }
  , { walsCode := "spa", iso := "spa", value := .two }
  , { walsCode := "sue", iso := "sue", value := .none }
  , { walsCode := "sup", iso := "spp", value := .fiveOrMore }
  , { walsCode := "swa", iso := "swh", value := .fiveOrMore }
  , { walsCode := "tab", iso := "mky", value := .none }
  , { walsCode := "tag", iso := "tgl", value := .two }
  , { walsCode := "tap", iso := "gpn", value := .two }
  , { walsCode := "tml", iso := "tam", value := .three }
  , { walsCode := "tha", iso := "tha", value := .none }
  , { walsCode := "tho", iso := "thp", value := .none }
  , { walsCode := "tib", iso := "bod", value := .none }
  , { walsCode := "tid", iso := "tvo", value := .three }
  , { walsCode := "tgr", iso := "tig", value := .two }
  , { walsCode := "tiw", iso := "tiw", value := .two }
  , { walsCode := "tol", iso := "jic", value := .none }
  , { walsCode := "tot", iso := "tlc", value := .none }
  , { walsCode := "tsz", iso := "ddo", value := .four }
  , { walsCode := "tsi", iso := "tsi", value := .none }
  , { walsCode := "tuk", iso := "", value := .none }
  , { walsCode := "tun", iso := "tun", value := .two }
  , { walsCode := "tur", iso := "tur", value := .none }
  , { walsCode := "tvl", iso := "tvl", value := .none }
  , { walsCode := "tsh", iso := "par", value := .none }
  , { walsCode := "ukr", iso := "ukr", value := .three }
  , { walsCode := "una", iso := "mtg", value := .none }
  , { walsCode := "uhi", iso := "urf", value := .none }
  , { walsCode := "urk", iso := "urb", value := .none }
  , { walsCode := "usa", iso := "wnu", value := .none }
  , { walsCode := "uzb", iso := "", value := .none }
  , { walsCode := "vie", iso := "vie", value := .none }
  , { walsCode := "wam", iso := "wmb", value := .four }
  , { walsCode := "wra", iso := "wba", value := .none }
  , { walsCode := "wrd", iso := "wrr", value := .three }
  , { walsCode := "war", iso := "pav", value := .three }
  , { walsCode := "wat", iso := "wbv", value := .none }
  , { walsCode := "wic", iso := "wic", value := .none }
  , { walsCode := "ykt", iso := "sah", value := .none }
  , { walsCode := "yaq", iso := "yaq", value := .none }
  , { walsCode := "yaz", iso := "yah", value := .two }
  , { walsCode := "yel", iso := "yle", value := .none }
  , { walsCode := "yid", iso := "yii", value := .none }
  , { walsCode := "yim", iso := "yee", value := .fiveOrMore }
  , { walsCode := "yor", iso := "yor", value := .none }
  , { walsCode := "yko", iso := "yux", value := .none }
  , { walsCode := "ylb", iso := "mpj", value := .none }
  , { walsCode := "ypk", iso := "esu", value := .none }
  , { walsCode := "yur", iso := "yur", value := .none }
  , { walsCode := "zan", iso := "zne", value := .four }
  , { walsCode := "zqc", iso := "zoc", value := .none }
  , { walsCode := "zul", iso := "zul", value := .fiveOrMore }
  , { walsCode := "zun", iso := "zun", value := .none }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F30A
