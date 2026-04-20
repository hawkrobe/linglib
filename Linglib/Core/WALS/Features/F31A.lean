import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 31A: Sex-based and Non-sex-based Gender Systems
@cite{corbett-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 31A`.

Chapter 31, 257 languages.
-/

namespace Core.WALS.F31A

/-- WALS 31A values. -/
inductive GenderBasis where
  /-- No gender (145 languages). -/
  | noGender
  /-- Sex-based (84 languages). -/
  | sexBased
  /-- Non-sex-based (28 languages). -/
  | nonSexBased
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 31A dataset (257 languages). -/
def allData : List (Datapoint GenderBasis) :=
  [ { walsCode := "abk", iso := "abk", value := .sexBased }
  , { walsCode := "aco", iso := "kjq", value := .noGender }
  , { walsCode := "ain", iso := "ain", value := .noGender }
  , { walsCode := "agw", iso := "wbj", value := .sexBased }
  , { walsCode := "ala", iso := "amp", value := .sexBased }
  , { walsCode := "ale", iso := "ale", value := .noGender }
  , { walsCode := "ame", iso := "aey", value := .noGender }
  , { walsCode := "amh", iso := "amh", value := .sexBased }
  , { walsCode := "apu", iso := "apu", value := .sexBased }
  , { walsCode := "abn", iso := "ard", value := .noGender }
  , { walsCode := "aeg", iso := "arz", value := .sexBased }
  , { walsCode := "arg", iso := "afb", value := .sexBased }
  , { walsCode := "asy", iso := "apc", value := .sexBased }
  , { walsCode := "arp", iso := "ape", value := .sexBased }
  , { walsCode := "abo", iso := "arv", value := .sexBased }
  , { walsCode := "arc", iso := "aqc", value := .sexBased }
  , { walsCode := "arm", iso := "hye", value := .noGender }
  , { walsCode := "asm", iso := "cns", value := .noGender }
  , { walsCode := "awp", iso := "kwi", value := .noGender }
  , { walsCode := "bab", iso := "bav", value := .nonSexBased }
  , { walsCode := "bag", iso := "bmi", value := .noGender }
  , { walsCode := "brs", iso := "bsn", value := .sexBased }
  , { walsCode := "bsq", iso := "eus", value := .noGender }
  , { walsCode := "bkr", iso := "btx", value := .noGender }
  , { walsCode := "baw", iso := "bgr", value := .noGender }
  , { walsCode := "bys", iso := "bsw", value := .sexBased }
  , { walsCode := "bej", iso := "bej", value := .sexBased }
  , { walsCode := "bma", iso := "tzm", value := .sexBased }
  , { walsCode := "bbw", iso := "gup", value := .sexBased }
  , { walsCode := "brh", iso := "brh", value := .noGender }
  , { walsCode := "brm", iso := "mya", value := .noGender }
  , { walsCode := "bur", iso := "bsk", value := .sexBased }
  , { walsCode := "cah", iso := "chl", value := .noGender }
  , { walsCode := "cax", iso := "", value := .sexBased }
  , { walsCode := "cnl", iso := "ram", value := .noGender }
  , { walsCode := "cnt", iso := "yue", value := .noGender }
  , { walsCode := "car", iso := "car", value := .noGender }
  , { walsCode := "cyv", iso := "cyb", value := .noGender }
  , { walsCode := "cha", iso := "cha", value := .noGender }
  , { walsCode := "cic", iso := "nya", value := .nonSexBased }
  , { walsCode := "chi", iso := "cid", value := .noGender }
  , { walsCode := "cle", iso := "cle", value := .nonSexBased }
  , { walsCode := "chk", iso := "ckt", value := .noGender }
  , { walsCode := "chv", iso := "chv", value := .noGender }
  , { walsCode := "ccp", iso := "coc", value := .noGender }
  , { walsCode := "cmn", iso := "com", value := .noGender }
  , { walsCode := "coo", iso := "csz", value := .noGender }
  , { walsCode := "cre", iso := "crk", value := .nonSexBased }
  , { walsCode := "dag", iso := "dgz", value := .noGender }
  , { walsCode := "dni", iso := "dni", value := .noGender }
  , { walsCode := "def", iso := "afn", value := .sexBased }
  , { walsCode := "dio", iso := "dyo", value := .nonSexBased }
  , { walsCode := "diy", iso := "dif", value := .sexBased }
  , { walsCode := "diz", iso := "mdx", value := .sexBased }
  , { walsCode := "djr", iso := "ddj", value := .noGender }
  , { walsCode := "don", iso := "kmc", value := .noGender }
  , { walsCode := "dyi", iso := "dbl", value := .sexBased }
  , { walsCode := "eng", iso := "eng", value := .sexBased }
  , { walsCode := "epe", iso := "sja", value := .noGender }
  , { walsCode := "err", iso := "erg", value := .noGender }
  , { walsCode := "eve", iso := "evn", value := .noGender }
  , { walsCode := "ewe", iso := "ewe", value := .noGender }
  , { walsCode := "fij", iso := "fij", value := .noGender }
  , { walsCode := "fin", iso := "fin", value := .noGender }
  , { walsCode := "fre", iso := "fra", value := .sexBased }
  , { walsCode := "fgu", iso := "fuf", value := .nonSexBased }
  , { walsCode := "gae", iso := "gla", value := .sexBased }
  , { walsCode := "geo", iso := "kat", value := .noGender }
  , { walsCode := "ger", iso := "deu", value := .sexBased }
  , { walsCode := "gdi", iso := "god", value := .nonSexBased }
  , { walsCode := "god", iso := "gdo", value := .sexBased }
  , { walsCode := "goo", iso := "gni", value := .noGender }
  , { walsCode := "grb", iso := "grj", value := .nonSexBased }
  , { walsCode := "grk", iso := "ell", value := .sexBased }
  , { walsCode := "grw", iso := "kal", value := .noGender }
  , { walsCode := "gua", iso := "gug", value := .noGender }
  , { walsCode := "guu", iso := "kky", value := .noGender }
  , { walsCode := "hai", iso := "hai", value := .noGender }
  , { walsCode := "hat", iso := "had", value := .noGender }
  , { walsCode := "hau", iso := "hau", value := .sexBased }
  , { walsCode := "haw", iso := "haw", value := .noGender }
  , { walsCode := "hay", iso := "vay", value := .noGender }
  , { walsCode := "heb", iso := "heb", value := .sexBased }
  , { walsCode := "hin", iso := "hin", value := .sexBased }
  , { walsCode := "hix", iso := "hix", value := .nonSexBased }
  , { walsCode := "hmo", iso := "hnj", value := .noGender }
  , { walsCode := "hun", iso := "hun", value := .noGender }
  , { walsCode := "hzb", iso := "huz", value := .sexBased }
  , { walsCode := "iaa", iso := "iai", value := .noGender }
  , { walsCode := "ice", iso := "isl", value := .sexBased }
  , { walsCode := "igb", iso := "ibo", value := .noGender }
  , { walsCode := "ika", iso := "arh", value := .noGender }
  , { walsCode := "imo", iso := "imn", value := .noGender }
  , { walsCode := "ind", iso := "ind", value := .noGender }
  , { walsCode := "ing", iso := "inh", value := .sexBased }
  , { walsCode := "irq", iso := "irk", value := .sexBased }
  , { walsCode := "ite", iso := "itl", value := .noGender }
  , { walsCode := "jaq", iso := "jqr", value := .noGender }
  , { walsCode := "juh", iso := "ktz", value := .nonSexBased }
  , { walsCode := "kam", iso := "xbr", value := .noGender }
  , { walsCode := "knd", iso := "kan", value := .sexBased }
  , { walsCode := "knr", iso := "knc", value := .noGender }
  , { walsCode := "krk", iso := "kyh", value := .noGender }
  , { walsCode := "kas", iso := "kas", value := .sexBased }
  , { walsCode := "kay", iso := "gyd", value := .noGender }
  , { walsCode := "ket", iso := "ket", value := .sexBased }
  , { walsCode := "kew", iso := "kew", value := .noGender }
  , { walsCode := "khk", iso := "kjh", value := .noGender }
  , { walsCode := "khl", iso := "klj", value := .noGender }
  , { walsCode := "kha", iso := "khk", value := .noGender }
  , { walsCode := "khs", iso := "kha", value := .sexBased }
  , { walsCode := "khm", iso := "khm", value := .noGender }
  , { walsCode := "kmu", iso := "kjg", value := .sexBased }
  , { walsCode := "klv", iso := "kij", value := .noGender }
  , { walsCode := "kgz", iso := "kir", value := .noGender }
  , { walsCode := "kis", iso := "kss", value := .nonSexBased }
  , { walsCode := "koa", iso := "cku", value := .noGender }
  , { walsCode := "kob", iso := "kpw", value := .noGender }
  , { walsCode := "kol", iso := "kfb", value := .sexBased }
  , { walsCode := "kon", iso := "kng", value := .nonSexBased }
  , { walsCode := "kfe", iso := "kfz", value := .nonSexBased }
  , { walsCode := "kse", iso := "ses", value := .noGender }
  , { walsCode := "kut", iso := "kut", value := .noGender }
  , { walsCode := "lad", iso := "lbj", value := .noGender }
  , { walsCode := "lah", iso := "lhu", value := .noGender }
  , { walsCode := "lak", iso := "lbe", value := .sexBased }
  , { walsCode := "lan", iso := "laj", value := .noGender }
  , { walsCode := "lat", iso := "lav", value := .sexBased }
  , { walsCode := "lav", iso := "lvk", value := .sexBased }
  , { walsCode := "lel", iso := "lln", value := .sexBased }
  , { walsCode := "lep", iso := "lep", value := .noGender }
  , { walsCode := "lez", iso := "lez", value := .noGender }
  , { walsCode := "lin", iso := "lin", value := .nonSexBased }
  , { walsCode := "luv", iso := "lue", value := .nonSexBased }
  , { walsCode := "mac", iso := "mbc", value := .nonSexBased }
  , { walsCode := "mak", iso := "myh", value := .noGender }
  , { walsCode := "mal", iso := "plt", value := .noGender }
  , { walsCode := "mlt", iso := "mlt", value := .sexBased }
  , { walsCode := "mnd", iso := "cmn", value := .noGender }
  , { walsCode := "myi", iso := "mpc", value := .sexBased }
  , { walsCode := "mns", iso := "mns", value := .noGender }
  , { walsCode := "mao", iso := "mri", value := .noGender }
  , { walsCode := "map", iso := "arn", value := .noGender }
  , { walsCode := "mhi", iso := "mar", value := .sexBased }
  , { walsCode := "mny", iso := "zmc", value := .noGender }
  , { walsCode := "mar", iso := "mrc", value := .noGender }
  , { walsCode := "mrd", iso := "mrz", value := .sexBased }
  , { walsCode := "mrt", iso := "vma", value := .noGender }
  , { walsCode := "mau", iso := "mph", value := .sexBased }
  , { walsCode := "may", iso := "ayz", value := .sexBased }
  , { walsCode := "mei", iso := "mni", value := .noGender }
  , { walsCode := "mss", iso := "skd", value := .noGender }
  , { walsCode := "mxc", iso := "mig", value := .sexBased }
  , { walsCode := "miy", iso := "mkf", value := .sexBased }
  , { walsCode := "mok", iso := "mkj", value := .noGender }
  , { walsCode := "mos", iso := "cas", value := .sexBased }
  , { walsCode := "mun", iso := "unr", value := .nonSexBased }
  , { walsCode := "mrl", iso := "mur", value := .noGender }
  , { walsCode := "nht", iso := "nhg", value := .noGender }
  , { walsCode := "kho", iso := "naq", value := .sexBased }
  , { walsCode := "ndy", iso := "djk", value := .noGender }
  , { walsCode := "ntu", iso := "yrk", value := .noGender }
  , { walsCode := "nez", iso := "nez", value := .noGender }
  , { walsCode := "ngg", iso := "nam", value := .sexBased }
  , { walsCode := "ngi", iso := "wyb", value := .noGender }
  , { walsCode := "nca", iso := "caq", value := .nonSexBased }
  , { walsCode := "niv", iso := "niv", value := .noGender }
  , { walsCode := "nko", iso := "cgg", value := .nonSexBased }
  , { walsCode := "nbd", iso := "dgl", value := .noGender }
  , { walsCode := "nug", iso := "nuy", value := .sexBased }
  , { walsCode := "nym", iso := "nym", value := .nonSexBased }
  , { walsCode := "nyh", iso := "nih", value := .nonSexBased }
  , { walsCode := "oji", iso := "", value := .nonSexBased }
  , { walsCode := "ond", iso := "one", value := .sexBased }
  , { walsCode := "ork", iso := "oaa", value := .noGender }
  , { walsCode := "orh", iso := "hae", value := .sexBased }
  , { walsCode := "otm", iso := "ote", value := .noGender }
  , { walsCode := "pai", iso := "pwn", value := .noGender }
  , { walsCode := "pal", iso := "pau", value := .noGender }
  , { walsCode := "pan", iso := "pan", value := .sexBased }
  , { walsCode := "psh", iso := "pst", value := .sexBased }
  , { walsCode := "psm", iso := "pqm", value := .nonSexBased }
  , { walsCode := "pau", iso := "pad", value := .sexBased }
  , { walsCode := "prs", iso := "pes", value := .noGender }
  , { walsCode := "pil", iso := "piv", value := .noGender }
  , { walsCode := "pip", iso := "ppl", value := .noGender }
  , { walsCode := "prh", iso := "myp", value := .sexBased }
  , { walsCode := "pit", iso := "pjt", value := .noGender }
  , { walsCode := "ppi", iso := "pit", value := .sexBased }
  , { walsCode := "pmc", iso := "poo", value := .noGender }
  , { walsCode := "qaf", iso := "aar", value := .sexBased }
  , { walsCode := "qim", iso := "qvi", value := .noGender }
  , { walsCode := "ram", iso := "rma", value := .noGender }
  , { walsCode := "rap", iso := "rap", value := .noGender }
  , { walsCode := "ren", iso := "rel", value := .sexBased }
  , { walsCode := "ret", iso := "tnc", value := .sexBased }
  , { walsCode := "rus", iso := "rus", value := .sexBased }
  , { walsCode := "smt", iso := "uma", value := .noGender }
  , { walsCode := "san", iso := "sag", value := .noGender }
  , { walsCode := "saw", iso := "hvn", value := .noGender }
  , { walsCode := "sml", iso := "sza", value := .noGender }
  , { walsCode := "snc", iso := "see", value := .sexBased }
  , { walsCode := "snt", iso := "set", value := .noGender }
  , { walsCode := "shk", iso := "shp", value := .noGender }
  , { walsCode := "shn", iso := "sna", value := .nonSexBased }
  , { walsCode := "srn", iso := "srq", value := .noGender }
  , { walsCode := "spa", iso := "spa", value := .sexBased }
  , { walsCode := "sue", iso := "sue", value := .noGender }
  , { walsCode := "sup", iso := "spp", value := .nonSexBased }
  , { walsCode := "swa", iso := "swh", value := .nonSexBased }
  , { walsCode := "tab", iso := "mky", value := .noGender }
  , { walsCode := "tag", iso := "tgl", value := .sexBased }
  , { walsCode := "tap", iso := "gpn", value := .sexBased }
  , { walsCode := "tml", iso := "tam", value := .sexBased }
  , { walsCode := "tha", iso := "tha", value := .noGender }
  , { walsCode := "tho", iso := "thp", value := .noGender }
  , { walsCode := "tib", iso := "bod", value := .noGender }
  , { walsCode := "tid", iso := "tvo", value := .sexBased }
  , { walsCode := "tgr", iso := "tig", value := .sexBased }
  , { walsCode := "tiw", iso := "tiw", value := .sexBased }
  , { walsCode := "tol", iso := "jic", value := .noGender }
  , { walsCode := "tot", iso := "tlc", value := .noGender }
  , { walsCode := "tsz", iso := "ddo", value := .sexBased }
  , { walsCode := "tsi", iso := "tsi", value := .noGender }
  , { walsCode := "tuk", iso := "", value := .noGender }
  , { walsCode := "tun", iso := "tun", value := .sexBased }
  , { walsCode := "tur", iso := "tur", value := .noGender }
  , { walsCode := "tvl", iso := "tvl", value := .noGender }
  , { walsCode := "tsh", iso := "par", value := .noGender }
  , { walsCode := "ukr", iso := "ukr", value := .sexBased }
  , { walsCode := "una", iso := "mtg", value := .noGender }
  , { walsCode := "uhi", iso := "urf", value := .noGender }
  , { walsCode := "urk", iso := "urb", value := .noGender }
  , { walsCode := "usa", iso := "wnu", value := .noGender }
  , { walsCode := "uzb", iso := "", value := .noGender }
  , { walsCode := "vie", iso := "vie", value := .noGender }
  , { walsCode := "wam", iso := "wmb", value := .sexBased }
  , { walsCode := "wra", iso := "wba", value := .noGender }
  , { walsCode := "wrd", iso := "wrr", value := .nonSexBased }
  , { walsCode := "war", iso := "pav", value := .sexBased }
  , { walsCode := "wat", iso := "wbv", value := .noGender }
  , { walsCode := "wic", iso := "wic", value := .noGender }
  , { walsCode := "ykt", iso := "sah", value := .noGender }
  , { walsCode := "yaq", iso := "yaq", value := .noGender }
  , { walsCode := "yaz", iso := "yah", value := .sexBased }
  , { walsCode := "yel", iso := "yle", value := .noGender }
  , { walsCode := "yid", iso := "yii", value := .noGender }
  , { walsCode := "yim", iso := "yee", value := .sexBased }
  , { walsCode := "yor", iso := "yor", value := .noGender }
  , { walsCode := "yko", iso := "yux", value := .noGender }
  , { walsCode := "ylb", iso := "mpj", value := .noGender }
  , { walsCode := "ypk", iso := "esu", value := .noGender }
  , { walsCode := "yur", iso := "yur", value := .noGender }
  , { walsCode := "zan", iso := "zne", value := .sexBased }
  , { walsCode := "zqc", iso := "zoc", value := .noGender }
  , { walsCode := "zul", iso := "zul", value := .nonSexBased }
  , { walsCode := "zun", iso := "zun", value := .noGender }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F31A
