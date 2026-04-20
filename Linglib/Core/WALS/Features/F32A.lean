import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 32A: Systems of Gender Assignment
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 32A`.

Chapter 32, 257 languages.
-/

namespace Core.WALS.F32A

/-- WALS 32A values. -/
inductive SystemsOfGenderAssignment where
  /-- No gender (145 languages). -/
  | noGender
  /-- Semantic (53 languages). -/
  | semantic
  /-- Semantic and formal (59 languages). -/
  | semanticAndFormal
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 32A dataset (257 languages). -/
def allData : List (Datapoint SystemsOfGenderAssignment) :=
  [ { walsCode := "abk", iso := "abk", value := .semantic }
  , { walsCode := "aco", iso := "kjq", value := .noGender }
  , { walsCode := "ain", iso := "ain", value := .noGender }
  , { walsCode := "agw", iso := "wbj", value := .semanticAndFormal }
  , { walsCode := "ala", iso := "amp", value := .semantic }
  , { walsCode := "ale", iso := "ale", value := .noGender }
  , { walsCode := "ame", iso := "aey", value := .noGender }
  , { walsCode := "amh", iso := "amh", value := .semanticAndFormal }
  , { walsCode := "apu", iso := "apu", value := .semanticAndFormal }
  , { walsCode := "abn", iso := "ard", value := .noGender }
  , { walsCode := "aeg", iso := "arz", value := .semanticAndFormal }
  , { walsCode := "arg", iso := "afb", value := .semanticAndFormal }
  , { walsCode := "asy", iso := "apc", value := .semanticAndFormal }
  , { walsCode := "arp", iso := "ape", value := .semanticAndFormal }
  , { walsCode := "abo", iso := "arv", value := .semanticAndFormal }
  , { walsCode := "arc", iso := "aqc", value := .semantic }
  , { walsCode := "arm", iso := "hye", value := .noGender }
  , { walsCode := "asm", iso := "cns", value := .noGender }
  , { walsCode := "awp", iso := "kwi", value := .noGender }
  , { walsCode := "bab", iso := "bav", value := .semanticAndFormal }
  , { walsCode := "bag", iso := "bmi", value := .noGender }
  , { walsCode := "brs", iso := "bsn", value := .semantic }
  , { walsCode := "bsq", iso := "eus", value := .noGender }
  , { walsCode := "bkr", iso := "btx", value := .noGender }
  , { walsCode := "baw", iso := "bgr", value := .noGender }
  , { walsCode := "bys", iso := "bsw", value := .semanticAndFormal }
  , { walsCode := "bej", iso := "bej", value := .semanticAndFormal }
  , { walsCode := "bma", iso := "tzm", value := .semanticAndFormal }
  , { walsCode := "bbw", iso := "gup", value := .semantic }
  , { walsCode := "brh", iso := "brh", value := .noGender }
  , { walsCode := "brm", iso := "mya", value := .noGender }
  , { walsCode := "bur", iso := "bsk", value := .semantic }
  , { walsCode := "cah", iso := "chl", value := .noGender }
  , { walsCode := "cax", iso := "", value := .semantic }
  , { walsCode := "cnl", iso := "ram", value := .noGender }
  , { walsCode := "cnt", iso := "yue", value := .noGender }
  , { walsCode := "car", iso := "car", value := .noGender }
  , { walsCode := "cyv", iso := "cyb", value := .noGender }
  , { walsCode := "cha", iso := "cha", value := .noGender }
  , { walsCode := "cic", iso := "nya", value := .semanticAndFormal }
  , { walsCode := "chi", iso := "cid", value := .noGender }
  , { walsCode := "cle", iso := "cle", value := .semantic }
  , { walsCode := "chk", iso := "ckt", value := .noGender }
  , { walsCode := "chv", iso := "chv", value := .noGender }
  , { walsCode := "ccp", iso := "coc", value := .noGender }
  , { walsCode := "cmn", iso := "com", value := .noGender }
  , { walsCode := "coo", iso := "csz", value := .noGender }
  , { walsCode := "cre", iso := "crk", value := .semantic }
  , { walsCode := "dag", iso := "dgz", value := .noGender }
  , { walsCode := "dni", iso := "dni", value := .noGender }
  , { walsCode := "def", iso := "afn", value := .semantic }
  , { walsCode := "dio", iso := "dyo", value := .semanticAndFormal }
  , { walsCode := "diy", iso := "dif", value := .semantic }
  , { walsCode := "diz", iso := "mdx", value := .semantic }
  , { walsCode := "djr", iso := "ddj", value := .noGender }
  , { walsCode := "don", iso := "kmc", value := .noGender }
  , { walsCode := "dyi", iso := "dbl", value := .semantic }
  , { walsCode := "eng", iso := "eng", value := .semantic }
  , { walsCode := "epe", iso := "sja", value := .noGender }
  , { walsCode := "err", iso := "erg", value := .noGender }
  , { walsCode := "eve", iso := "evn", value := .noGender }
  , { walsCode := "ewe", iso := "ewe", value := .noGender }
  , { walsCode := "fij", iso := "fij", value := .noGender }
  , { walsCode := "fin", iso := "fin", value := .noGender }
  , { walsCode := "fre", iso := "fra", value := .semanticAndFormal }
  , { walsCode := "fgu", iso := "fuf", value := .semanticAndFormal }
  , { walsCode := "gae", iso := "gla", value := .semanticAndFormal }
  , { walsCode := "geo", iso := "kat", value := .noGender }
  , { walsCode := "ger", iso := "deu", value := .semanticAndFormal }
  , { walsCode := "gdi", iso := "god", value := .semanticAndFormal }
  , { walsCode := "god", iso := "gdo", value := .semantic }
  , { walsCode := "goo", iso := "gni", value := .noGender }
  , { walsCode := "grb", iso := "grj", value := .semantic }
  , { walsCode := "grk", iso := "ell", value := .semanticAndFormal }
  , { walsCode := "grw", iso := "kal", value := .noGender }
  , { walsCode := "gua", iso := "gug", value := .noGender }
  , { walsCode := "guu", iso := "kky", value := .noGender }
  , { walsCode := "hai", iso := "hai", value := .noGender }
  , { walsCode := "hat", iso := "had", value := .noGender }
  , { walsCode := "hau", iso := "hau", value := .semanticAndFormal }
  , { walsCode := "haw", iso := "haw", value := .noGender }
  , { walsCode := "hay", iso := "vay", value := .noGender }
  , { walsCode := "heb", iso := "heb", value := .semanticAndFormal }
  , { walsCode := "hin", iso := "hin", value := .semanticAndFormal }
  , { walsCode := "hix", iso := "hix", value := .semantic }
  , { walsCode := "hmo", iso := "hnj", value := .noGender }
  , { walsCode := "hun", iso := "hun", value := .noGender }
  , { walsCode := "hzb", iso := "huz", value := .semantic }
  , { walsCode := "iaa", iso := "iai", value := .noGender }
  , { walsCode := "ice", iso := "isl", value := .semanticAndFormal }
  , { walsCode := "igb", iso := "ibo", value := .noGender }
  , { walsCode := "ika", iso := "arh", value := .noGender }
  , { walsCode := "imo", iso := "imn", value := .noGender }
  , { walsCode := "ind", iso := "ind", value := .noGender }
  , { walsCode := "ing", iso := "inh", value := .semanticAndFormal }
  , { walsCode := "irq", iso := "irk", value := .semanticAndFormal }
  , { walsCode := "ite", iso := "itl", value := .noGender }
  , { walsCode := "jaq", iso := "jqr", value := .noGender }
  , { walsCode := "juh", iso := "ktz", value := .semanticAndFormal }
  , { walsCode := "kam", iso := "xbr", value := .noGender }
  , { walsCode := "knd", iso := "kan", value := .semantic }
  , { walsCode := "knr", iso := "knc", value := .noGender }
  , { walsCode := "krk", iso := "kyh", value := .noGender }
  , { walsCode := "kas", iso := "kas", value := .semanticAndFormal }
  , { walsCode := "kay", iso := "gyd", value := .noGender }
  , { walsCode := "ket", iso := "ket", value := .semantic }
  , { walsCode := "kew", iso := "kew", value := .noGender }
  , { walsCode := "khk", iso := "kjh", value := .noGender }
  , { walsCode := "khl", iso := "klj", value := .noGender }
  , { walsCode := "kha", iso := "khk", value := .noGender }
  , { walsCode := "khs", iso := "kha", value := .semantic }
  , { walsCode := "khm", iso := "khm", value := .noGender }
  , { walsCode := "kmu", iso := "kjg", value := .semantic }
  , { walsCode := "klv", iso := "kij", value := .noGender }
  , { walsCode := "kgz", iso := "kir", value := .noGender }
  , { walsCode := "kis", iso := "kss", value := .semanticAndFormal }
  , { walsCode := "koa", iso := "cku", value := .noGender }
  , { walsCode := "kob", iso := "kpw", value := .noGender }
  , { walsCode := "kol", iso := "kfb", value := .semantic }
  , { walsCode := "kon", iso := "kng", value := .semanticAndFormal }
  , { walsCode := "kfe", iso := "kfz", value := .semantic }
  , { walsCode := "kse", iso := "ses", value := .noGender }
  , { walsCode := "kut", iso := "kut", value := .noGender }
  , { walsCode := "lad", iso := "lbj", value := .noGender }
  , { walsCode := "lah", iso := "lhu", value := .noGender }
  , { walsCode := "lak", iso := "lbe", value := .semantic }
  , { walsCode := "lan", iso := "laj", value := .noGender }
  , { walsCode := "lat", iso := "lav", value := .semanticAndFormal }
  , { walsCode := "lav", iso := "lvk", value := .semanticAndFormal }
  , { walsCode := "lel", iso := "lln", value := .semanticAndFormal }
  , { walsCode := "lep", iso := "lep", value := .noGender }
  , { walsCode := "lez", iso := "lez", value := .noGender }
  , { walsCode := "lin", iso := "lin", value := .semanticAndFormal }
  , { walsCode := "luv", iso := "lue", value := .semanticAndFormal }
  , { walsCode := "mac", iso := "mbc", value := .semantic }
  , { walsCode := "mak", iso := "myh", value := .noGender }
  , { walsCode := "mal", iso := "plt", value := .noGender }
  , { walsCode := "mlt", iso := "mlt", value := .semanticAndFormal }
  , { walsCode := "mnd", iso := "cmn", value := .noGender }
  , { walsCode := "myi", iso := "mpc", value := .semantic }
  , { walsCode := "mns", iso := "mns", value := .noGender }
  , { walsCode := "mao", iso := "mri", value := .noGender }
  , { walsCode := "map", iso := "arn", value := .noGender }
  , { walsCode := "mhi", iso := "mar", value := .semanticAndFormal }
  , { walsCode := "mny", iso := "zmc", value := .noGender }
  , { walsCode := "mar", iso := "mrc", value := .noGender }
  , { walsCode := "mrd", iso := "mrz", value := .semantic }
  , { walsCode := "mrt", iso := "vma", value := .noGender }
  , { walsCode := "mau", iso := "mph", value := .semantic }
  , { walsCode := "may", iso := "ayz", value := .semantic }
  , { walsCode := "mei", iso := "mni", value := .noGender }
  , { walsCode := "mss", iso := "skd", value := .noGender }
  , { walsCode := "mxc", iso := "mig", value := .semantic }
  , { walsCode := "miy", iso := "mkf", value := .semanticAndFormal }
  , { walsCode := "mok", iso := "mkj", value := .noGender }
  , { walsCode := "mos", iso := "cas", value := .semanticAndFormal }
  , { walsCode := "mun", iso := "unr", value := .semantic }
  , { walsCode := "mrl", iso := "mur", value := .noGender }
  , { walsCode := "nht", iso := "nhg", value := .noGender }
  , { walsCode := "kho", iso := "naq", value := .semanticAndFormal }
  , { walsCode := "ndy", iso := "djk", value := .noGender }
  , { walsCode := "ntu", iso := "yrk", value := .noGender }
  , { walsCode := "nez", iso := "nez", value := .noGender }
  , { walsCode := "ngg", iso := "nam", value := .semantic }
  , { walsCode := "ngi", iso := "wyb", value := .noGender }
  , { walsCode := "nca", iso := "caq", value := .semantic }
  , { walsCode := "niv", iso := "niv", value := .noGender }
  , { walsCode := "nko", iso := "cgg", value := .semanticAndFormal }
  , { walsCode := "nbd", iso := "dgl", value := .noGender }
  , { walsCode := "nug", iso := "nuy", value := .semanticAndFormal }
  , { walsCode := "nym", iso := "nym", value := .semanticAndFormal }
  , { walsCode := "nyh", iso := "nih", value := .semanticAndFormal }
  , { walsCode := "oji", iso := "", value := .semantic }
  , { walsCode := "ond", iso := "one", value := .semantic }
  , { walsCode := "ork", iso := "oaa", value := .noGender }
  , { walsCode := "orh", iso := "hae", value := .semanticAndFormal }
  , { walsCode := "otm", iso := "ote", value := .noGender }
  , { walsCode := "pai", iso := "pwn", value := .noGender }
  , { walsCode := "pal", iso := "pau", value := .noGender }
  , { walsCode := "pan", iso := "pan", value := .semanticAndFormal }
  , { walsCode := "psh", iso := "pst", value := .semanticAndFormal }
  , { walsCode := "psm", iso := "pqm", value := .semantic }
  , { walsCode := "pau", iso := "pad", value := .semantic }
  , { walsCode := "prs", iso := "pes", value := .noGender }
  , { walsCode := "pil", iso := "piv", value := .noGender }
  , { walsCode := "pip", iso := "ppl", value := .noGender }
  , { walsCode := "prh", iso := "myp", value := .semantic }
  , { walsCode := "pit", iso := "pjt", value := .noGender }
  , { walsCode := "ppi", iso := "pit", value := .semantic }
  , { walsCode := "pmc", iso := "poo", value := .noGender }
  , { walsCode := "qaf", iso := "aar", value := .semanticAndFormal }
  , { walsCode := "qim", iso := "qvi", value := .noGender }
  , { walsCode := "ram", iso := "rma", value := .noGender }
  , { walsCode := "rap", iso := "rap", value := .noGender }
  , { walsCode := "ren", iso := "rel", value := .semanticAndFormal }
  , { walsCode := "ret", iso := "tnc", value := .semantic }
  , { walsCode := "rus", iso := "rus", value := .semanticAndFormal }
  , { walsCode := "smt", iso := "uma", value := .noGender }
  , { walsCode := "san", iso := "sag", value := .noGender }
  , { walsCode := "saw", iso := "hvn", value := .noGender }
  , { walsCode := "sml", iso := "sza", value := .noGender }
  , { walsCode := "snc", iso := "see", value := .semantic }
  , { walsCode := "snt", iso := "set", value := .noGender }
  , { walsCode := "shk", iso := "shp", value := .noGender }
  , { walsCode := "shn", iso := "sna", value := .semanticAndFormal }
  , { walsCode := "srn", iso := "srq", value := .noGender }
  , { walsCode := "spa", iso := "spa", value := .semanticAndFormal }
  , { walsCode := "sue", iso := "sue", value := .noGender }
  , { walsCode := "sup", iso := "spp", value := .semanticAndFormal }
  , { walsCode := "swa", iso := "swh", value := .semanticAndFormal }
  , { walsCode := "tab", iso := "mky", value := .noGender }
  , { walsCode := "tag", iso := "tgl", value := .semantic }
  , { walsCode := "tap", iso := "gpn", value := .semantic }
  , { walsCode := "tml", iso := "tam", value := .semantic }
  , { walsCode := "tha", iso := "tha", value := .noGender }
  , { walsCode := "tho", iso := "thp", value := .noGender }
  , { walsCode := "tib", iso := "bod", value := .noGender }
  , { walsCode := "tid", iso := "tvo", value := .semantic }
  , { walsCode := "tgr", iso := "tig", value := .semanticAndFormal }
  , { walsCode := "tiw", iso := "tiw", value := .semantic }
  , { walsCode := "tol", iso := "jic", value := .noGender }
  , { walsCode := "tot", iso := "tlc", value := .noGender }
  , { walsCode := "tsz", iso := "ddo", value := .semanticAndFormal }
  , { walsCode := "tsi", iso := "tsi", value := .noGender }
  , { walsCode := "tuk", iso := "", value := .noGender }
  , { walsCode := "tun", iso := "tun", value := .semantic }
  , { walsCode := "tur", iso := "tur", value := .noGender }
  , { walsCode := "tvl", iso := "tvl", value := .noGender }
  , { walsCode := "tsh", iso := "par", value := .noGender }
  , { walsCode := "ukr", iso := "ukr", value := .semanticAndFormal }
  , { walsCode := "una", iso := "mtg", value := .noGender }
  , { walsCode := "uhi", iso := "urf", value := .noGender }
  , { walsCode := "urk", iso := "urb", value := .noGender }
  , { walsCode := "usa", iso := "wnu", value := .noGender }
  , { walsCode := "uzb", iso := "", value := .noGender }
  , { walsCode := "vie", iso := "vie", value := .noGender }
  , { walsCode := "wam", iso := "wmb", value := .semantic }
  , { walsCode := "wra", iso := "wba", value := .noGender }
  , { walsCode := "wrd", iso := "wrr", value := .semantic }
  , { walsCode := "war", iso := "pav", value := .semantic }
  , { walsCode := "wat", iso := "wbv", value := .noGender }
  , { walsCode := "wic", iso := "wic", value := .noGender }
  , { walsCode := "ykt", iso := "sah", value := .noGender }
  , { walsCode := "yaq", iso := "yaq", value := .noGender }
  , { walsCode := "yaz", iso := "yah", value := .semantic }
  , { walsCode := "yel", iso := "yle", value := .noGender }
  , { walsCode := "yid", iso := "yii", value := .noGender }
  , { walsCode := "yim", iso := "yee", value := .semanticAndFormal }
  , { walsCode := "yor", iso := "yor", value := .noGender }
  , { walsCode := "yko", iso := "yux", value := .noGender }
  , { walsCode := "ylb", iso := "mpj", value := .noGender }
  , { walsCode := "ypk", iso := "esu", value := .noGender }
  , { walsCode := "yur", iso := "yur", value := .noGender }
  , { walsCode := "zan", iso := "zne", value := .semantic }
  , { walsCode := "zqc", iso := "zoc", value := .noGender }
  , { walsCode := "zul", iso := "zul", value := .semanticAndFormal }
  , { walsCode := "zun", iso := "zun", value := .noGender }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F32A
