import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 111A: Nonperiphrastic Causative Constructions
@cite{song-2013-nonperiphrastic}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 111A`.

Chapter 111, 310 languages.
-/

namespace Datasets.WALS.F111A

/-- WALS 111A values. -/
inductive NonperiphrCausativeType where
  /-- Neither (23 languages). -/
  | neither
  /-- Morphological but no compound (254 languages). -/
  | morphologicalOnly
  /-- Compound but no morphological (9 languages). -/
  | compoundOnly
  /-- Both (24 languages). -/
  | both
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 111A dataset (310 languages). -/
def allData : List (Datapoint NonperiphrCausativeType) :=
  [ { walsCode := "abi", iso := "axb", value := .morphologicalOnly }
  , { walsCode := "abk", iso := "abk", value := .morphologicalOnly }
  , { walsCode := "ace", iso := "ace", value := .morphologicalOnly }
  , { walsCode := "ain", iso := "ain", value := .morphologicalOnly }
  , { walsCode := "aji", iso := "aji", value := .morphologicalOnly }
  , { walsCode := "ala", iso := "amp", value := .both }
  , { walsCode := "aly", iso := "aly", value := .morphologicalOnly }
  , { walsCode := "ame", iso := "aey", value := .morphologicalOnly }
  , { walsCode := "amh", iso := "amh", value := .morphologicalOnly }
  , { walsCode := "apu", iso := "apu", value := .morphologicalOnly }
  , { walsCode := "aeg", iso := "arz", value := .morphologicalOnly }
  , { walsCode := "ana", iso := "aro", value := .morphologicalOnly }
  , { walsCode := "arm", iso := "hye", value := .morphologicalOnly }
  , { walsCode := "aro", iso := "aia", value := .morphologicalOnly }
  , { walsCode := "asm", iso := "cns", value := .morphologicalOnly }
  , { walsCode := "atc", iso := "upv", value := .morphologicalOnly }
  , { walsCode := "awp", iso := "kwi", value := .morphologicalOnly }
  , { walsCode := "awn", iso := "awn", value := .morphologicalOnly }
  , { walsCode := "aym", iso := "ayr", value := .morphologicalOnly }
  , { walsCode := "bab", iso := "bav", value := .morphologicalOnly }
  , { walsCode := "bag", iso := "bmi", value := .neither }
  , { walsCode := "baj", iso := "bdl", value := .morphologicalOnly }
  , { walsCode := "bal", iso := "ban", value := .morphologicalOnly }
  , { walsCode := "bam", iso := "bam", value := .morphologicalOnly }
  , { walsCode := "brs", iso := "bsn", value := .morphologicalOnly }
  , { walsCode := "bsq", iso := "eus", value := .morphologicalOnly }
  , { walsCode := "bkr", iso := "btx", value := .morphologicalOnly }
  , { walsCode := "baw", iso := "bgr", value := .both }
  , { walsCode := "bej", iso := "bej", value := .morphologicalOnly }
  , { walsCode := "bma", iso := "tzm", value := .morphologicalOnly }
  , { walsCode := "blx", iso := "bll", value := .both }
  , { walsCode := "bla", iso := "bla", value := .morphologicalOnly }
  , { walsCode := "brr", iso := "bor", value := .morphologicalOnly }
  , { walsCode := "brh", iso := "brh", value := .morphologicalOnly }
  , { walsCode := "but", iso := "bxm", value := .morphologicalOnly }
  , { walsCode := "brm", iso := "mya", value := .both }
  , { walsCode := "bur", iso := "bsk", value := .morphologicalOnly }
  , { walsCode := "cah", iso := "chl", value := .morphologicalOnly }
  , { walsCode := "cax", iso := "", value := .morphologicalOnly }
  , { walsCode := "car", iso := "car", value := .morphologicalOnly }
  , { walsCode := "crq", iso := "crx", value := .both }
  , { walsCode := "ceb", iso := "ceb", value := .morphologicalOnly }
  , { walsCode := "cld", iso := "cld", value := .morphologicalOnly }
  , { walsCode := "cha", iso := "cha", value := .morphologicalOnly }
  , { walsCode := "cle", iso := "cle", value := .morphologicalOnly }
  , { walsCode := "cct", iso := "cho", value := .morphologicalOnly }
  , { walsCode := "chk", iso := "ckt", value := .morphologicalOnly }
  , { walsCode := "chv", iso := "chv", value := .morphologicalOnly }
  , { walsCode := "coa", iso := "xcw", value := .morphologicalOnly }
  , { walsCode := "cmn", iso := "com", value := .morphologicalOnly }
  , { walsCode := "coo", iso := "csz", value := .morphologicalOnly }
  , { walsCode := "cor", iso := "crn", value := .morphologicalOnly }
  , { walsCode := "cre", iso := "crk", value := .morphologicalOnly }
  , { walsCode := "cui", iso := "cui", value := .morphologicalOnly }
  , { walsCode := "dgr", iso := "dta", value := .morphologicalOnly }
  , { walsCode := "die", iso := "dih", value := .morphologicalOnly }
  , { walsCode := "dio", iso := "dyo", value := .morphologicalOnly }
  , { walsCode := "diy", iso := "dif", value := .morphologicalOnly }
  , { walsCode := "djr", iso := "ddj", value := .neither }
  , { walsCode := "doy", iso := "dow", value := .morphologicalOnly }
  , { walsCode := "dre", iso := "dhv", value := .morphologicalOnly }
  , { walsCode := "eng", iso := "eng", value := .morphologicalOnly }
  , { walsCode := "epe", iso := "sja", value := .morphologicalOnly }
  , { walsCode := "eve", iso := "evn", value := .morphologicalOnly }
  , { walsCode := "ewe", iso := "ewe", value := .neither }
  , { walsCode := "fij", iso := "fij", value := .morphologicalOnly }
  , { walsCode := "fin", iso := "fin", value := .morphologicalOnly }
  , { walsCode := "fre", iso := "fra", value := .both }
  , { walsCode := "fut", iso := "fut", value := .morphologicalOnly }
  , { walsCode := "gar", iso := "grt", value := .morphologicalOnly }
  , { walsCode := "geo", iso := "kat", value := .morphologicalOnly }
  , { walsCode := "ger", iso := "deu", value := .morphologicalOnly }
  , { walsCode := "goo", iso := "gni", value := .neither }
  , { walsCode := "grb", iso := "grj", value := .morphologicalOnly }
  , { walsCode := "grk", iso := "ell", value := .neither }
  , { walsCode := "grw", iso := "kal", value := .morphologicalOnly }
  , { walsCode := "gua", iso := "gug", value := .morphologicalOnly }
  , { walsCode := "guj", iso := "guj", value := .morphologicalOnly }
  , { walsCode := "guu", iso := "kky", value := .morphologicalOnly }
  , { walsCode := "hai", iso := "hai", value := .morphologicalOnly }
  , { walsCode := "hau", iso := "hau", value := .morphologicalOnly }
  , { walsCode := "haw", iso := "haw", value := .morphologicalOnly }
  , { walsCode := "heb", iso := "heb", value := .morphologicalOnly }
  , { walsCode := "hin", iso := "hin", value := .morphologicalOnly }
  , { walsCode := "hix", iso := "hix", value := .morphologicalOnly }
  , { walsCode := "hmo", iso := "hnj", value := .neither }
  , { walsCode := "hmi", iso := "hto", value := .morphologicalOnly }
  , { walsCode := "hun", iso := "hun", value := .morphologicalOnly }
  , { walsCode := "hzb", iso := "huz", value := .morphologicalOnly }
  , { walsCode := "iaa", iso := "iai", value := .morphologicalOnly }
  , { walsCode := "igb", iso := "ibo", value := .morphologicalOnly }
  , { walsCode := "ika", iso := "arh", value := .morphologicalOnly }
  , { walsCode := "ila", iso := "ilb", value := .morphologicalOnly }
  , { walsCode := "ind", iso := "ind", value := .morphologicalOnly }
  , { walsCode := "ing", iso := "inh", value := .morphologicalOnly }
  , { walsCode := "irq", iso := "irk", value := .morphologicalOnly }
  , { walsCode := "iri", iso := "gle", value := .neither }
  , { walsCode := "jak", iso := "jac", value := .morphologicalOnly }
  , { walsCode := "jpn", iso := "jpn", value := .morphologicalOnly }
  , { walsCode := "jaq", iso := "jqr", value := .morphologicalOnly }
  , { walsCode := "juh", iso := "ktz", value := .compoundOnly }
  , { walsCode := "kdz", iso := "kzj", value := .morphologicalOnly }
  , { walsCode := "kls", iso := "fla", value := .morphologicalOnly }
  , { walsCode := "kgu", iso := "ktg", value := .morphologicalOnly }
  , { walsCode := "kmk", iso := "xal", value := .morphologicalOnly }
  , { walsCode := "kam", iso := "xbr", value := .morphologicalOnly }
  , { walsCode := "knd", iso := "kan", value := .morphologicalOnly }
  , { walsCode := "knr", iso := "knc", value := .morphologicalOnly }
  , { walsCode := "krk", iso := "kyh", value := .morphologicalOnly }
  , { walsCode := "kas", iso := "kas", value := .morphologicalOnly }
  , { walsCode := "kyl", iso := "eky", value := .compoundOnly }
  , { walsCode := "kay", iso := "gyd", value := .morphologicalOnly }
  , { walsCode := "kem", iso := "ahg", value := .morphologicalOnly }
  , { walsCode := "ket", iso := "ket", value := .morphologicalOnly }
  , { walsCode := "kew", iso := "kew", value := .morphologicalOnly }
  , { walsCode := "kha", iso := "khk", value := .morphologicalOnly }
  , { walsCode := "khs", iso := "kha", value := .morphologicalOnly }
  , { walsCode := "khm", iso := "khm", value := .morphologicalOnly }
  , { walsCode := "kmu", iso := "kjg", value := .both }
  , { walsCode := "klv", iso := "kij", value := .neither }
  , { walsCode := "kin", iso := "kin", value := .morphologicalOnly }
  , { walsCode := "kio", iso := "kio", value := .morphologicalOnly }
  , { walsCode := "krb", iso := "gil", value := .morphologicalOnly }
  , { walsCode := "kis", iso := "kss", value := .morphologicalOnly }
  , { walsCode := "shp", iso := "yak", value := .morphologicalOnly }
  , { walsCode := "koa", iso := "cku", value := .both }
  , { walsCode := "kob", iso := "kpw", value := .compoundOnly }
  , { walsCode := "kol", iso := "kfb", value := .morphologicalOnly }
  , { walsCode := "kon", iso := "kng", value := .morphologicalOnly }
  , { walsCode := "krn", iso := "kqz", value := .morphologicalOnly }
  , { walsCode := "kor", iso := "kor", value := .morphologicalOnly }
  , { walsCode := "kfe", iso := "kfz", value := .morphologicalOnly }
  , { walsCode := "kos", iso := "kos", value := .morphologicalOnly }
  , { walsCode := "kse", iso := "ses", value := .both }
  , { walsCode := "kro", iso := "kgo", value := .neither }
  , { walsCode := "knm", iso := "kun", value := .morphologicalOnly }
  , { walsCode := "kut", iso := "kut", value := .morphologicalOnly }
  , { walsCode := "kwa", iso := "kwd", value := .morphologicalOnly }
  , { walsCode := "lad", iso := "lbj", value := .morphologicalOnly }
  , { walsCode := "lah", iso := "lhu", value := .both }
  , { walsCode := "lkt", iso := "lkt", value := .both }
  , { walsCode := "lal", iso := "ywt", value := .both }
  , { walsCode := "lmp", iso := "ljp", value := .morphologicalOnly }
  , { walsCode := "lan", iso := "laj", value := .morphologicalOnly }
  , { walsCode := "lat", iso := "lav", value := .morphologicalOnly }
  , { walsCode := "lav", iso := "lvk", value := .morphologicalOnly }
  , { walsCode := "lep", iso := "lep", value := .morphologicalOnly }
  , { walsCode := "let", iso := "lti", value := .morphologicalOnly }
  , { walsCode := "lez", iso := "lez", value := .morphologicalOnly }
  , { walsCode := "lim", iso := "lif", value := .morphologicalOnly }
  , { walsCode := "luv", iso := "lue", value := .morphologicalOnly }
  , { walsCode := "maa", iso := "mas", value := .morphologicalOnly }
  , { walsCode := "mab", iso := "mde", value := .morphologicalOnly }
  , { walsCode := "mac", iso := "mbc", value := .morphologicalOnly }
  , { walsCode := "mak", iso := "myh", value := .morphologicalOnly }
  , { walsCode := "mal", iso := "plt", value := .morphologicalOnly }
  , { walsCode := "mym", iso := "mal", value := .morphologicalOnly }
  , { walsCode := "mnm", iso := "mva", value := .morphologicalOnly }
  , { walsCode := "mnd", iso := "cmn", value := .compoundOnly }
  , { walsCode := "myi", iso := "mpc", value := .both }
  , { walsCode := "mwb", iso := "mbb", value := .morphologicalOnly }
  , { walsCode := "mns", iso := "mns", value := .morphologicalOnly }
  , { walsCode := "mao", iso := "mri", value := .morphologicalOnly }
  , { walsCode := "map", iso := "arn", value := .morphologicalOnly }
  , { walsCode := "mhi", iso := "mar", value := .morphologicalOnly }
  , { walsCode := "mny", iso := "zmc", value := .morphologicalOnly }
  , { walsCode := "mar", iso := "mrc", value := .both }
  , { walsCode := "mrt", iso := "vma", value := .morphologicalOnly }
  , { walsCode := "mau", iso := "mph", value := .morphologicalOnly }
  , { walsCode := "may", iso := "ayz", value := .neither }
  , { walsCode := "mei", iso := "mni", value := .morphologicalOnly }
  , { walsCode := "men", iso := "mez", value := .morphologicalOnly }
  , { walsCode := "mss", iso := "skd", value := .morphologicalOnly }
  , { walsCode := "mxc", iso := "mig", value := .morphologicalOnly }
  , { walsCode := "mul", iso := "mlm", value := .neither }
  , { walsCode := "mna", iso := "mnb", value := .morphologicalOnly }
  , { walsCode := "mun", iso := "unr", value := .both }
  , { walsCode := "mrl", iso := "mur", value := .morphologicalOnly }
  , { walsCode := "nht", iso := "nhg", value := .morphologicalOnly }
  , { walsCode := "kho", iso := "naq", value := .both }
  , { walsCode := "nav", iso := "nav", value := .neither }
  , { walsCode := "ndo", iso := "ndo", value := .morphologicalOnly }
  , { walsCode := "ndy", iso := "djk", value := .neither }
  , { walsCode := "neh", iso := "nsn", value := .morphologicalOnly }
  , { walsCode := "ntu", iso := "yrk", value := .morphologicalOnly }
  , { walsCode := "nez", iso := "nez", value := .morphologicalOnly }
  , { walsCode := "ngl", iso := "nig", value := .morphologicalOnly }
  , { walsCode := "nti", iso := "niy", value := .morphologicalOnly }
  , { walsCode := "ngi", iso := "wyb", value := .morphologicalOnly }
  , { walsCode := "nca", iso := "caq", value := .morphologicalOnly }
  , { walsCode := "niu", iso := "niu", value := .morphologicalOnly }
  , { walsCode := "niv", iso := "niv", value := .morphologicalOnly }
  , { walsCode := "nko", iso := "cgg", value := .morphologicalOnly }
  , { walsCode := "nbd", iso := "dgl", value := .morphologicalOnly }
  , { walsCode := "nug", iso := "nuy", value := .morphologicalOnly }
  , { walsCode := "nym", iso := "nym", value := .morphologicalOnly }
  , { walsCode := "oji", iso := "", value := .morphologicalOnly }
  , { walsCode := "ond", iso := "one", value := .morphologicalOnly }
  , { walsCode := "orh", iso := "hae", value := .morphologicalOnly }
  , { walsCode := "orw", iso := "ssn", value := .morphologicalOnly }
  , { walsCode := "otm", iso := "ote", value := .neither }
  , { walsCode := "pkn", iso := "drl", value := .morphologicalOnly }
  , { walsCode := "pms", iso := "pma", value := .neither }
  , { walsCode := "pai", iso := "pwn", value := .morphologicalOnly }
  , { walsCode := "pal", iso := "pau", value := .morphologicalOnly }
  , { walsCode := "pan", iso := "pan", value := .morphologicalOnly }
  , { walsCode := "pny", iso := "pnw", value := .morphologicalOnly }
  , { walsCode := "psh", iso := "pst", value := .morphologicalOnly }
  , { walsCode := "psm", iso := "pqm", value := .morphologicalOnly }
  , { walsCode := "pau", iso := "pad", value := .morphologicalOnly }
  , { walsCode := "pwn", iso := "paw", value := .morphologicalOnly }
  , { walsCode := "prs", iso := "pes", value := .morphologicalOnly }
  , { walsCode := "pip", iso := "ppl", value := .morphologicalOnly }
  , { walsCode := "prh", iso := "myp", value := .morphologicalOnly }
  , { walsCode := "pit", iso := "pjt", value := .both }
  , { walsCode := "ppi", iso := "pit", value := .morphologicalOnly }
  , { walsCode := "pso", iso := "pom", value := .morphologicalOnly }
  , { walsCode := "pul", iso := "puw", value := .morphologicalOnly }
  , { walsCode := "qim", iso := "qvi", value := .morphologicalOnly }
  , { walsCode := "ram", iso := "rma", value := .both }
  , { walsCode := "rap", iso := "rap", value := .morphologicalOnly }
  , { walsCode := "rej", iso := "rej", value := .neither }
  , { walsCode := "ret", iso := "tnc", value := .morphologicalOnly }
  , { walsCode := "rot", iso := "rtm", value := .morphologicalOnly }
  , { walsCode := "ruk", iso := "dru", value := .morphologicalOnly }
  , { walsCode := "rus", iso := "rus", value := .morphologicalOnly }
  , { walsCode := "sam", iso := "smo", value := .morphologicalOnly }
  , { walsCode := "snm", iso := "xsu", value := .morphologicalOnly }
  , { walsCode := "src", iso := "srs", value := .neither }
  , { walsCode := "saw", iso := "hvn", value := .morphologicalOnly }
  , { walsCode := "sel", iso := "ona", value := .morphologicalOnly }
  , { walsCode := "sml", iso := "sza", value := .morphologicalOnly }
  , { walsCode := "shk", iso := "shp", value := .both }
  , { walsCode := "shn", iso := "sna", value := .morphologicalOnly }
  , { walsCode := "shu", iso := "shs", value := .morphologicalOnly }
  , { walsCode := "snh", iso := "sin", value := .morphologicalOnly }
  , { walsCode := "srn", iso := "srq", value := .morphologicalOnly }
  , { walsCode := "sla", iso := "den", value := .morphologicalOnly }
  , { walsCode := "son", iso := "sov", value := .morphologicalOnly }
  , { walsCode := "sor", iso := "srb", value := .morphologicalOnly }
  , { walsCode := "spa", iso := "spa", value := .both }
  , { walsCode := "squ", iso := "squ", value := .morphologicalOnly }
  , { walsCode := "sun", iso := "sun", value := .morphologicalOnly }
  , { walsCode := "sup", iso := "spp", value := .morphologicalOnly }
  , { walsCode := "swa", iso := "swh", value := .morphologicalOnly }
  , { walsCode := "swt", iso := "ssw", value := .morphologicalOnly }
  , { walsCode := "tab", iso := "mky", value := .morphologicalOnly }
  , { walsCode := "tag", iso := "tgl", value := .morphologicalOnly }
  , { walsCode := "tah", iso := "tah", value := .morphologicalOnly }
  , { walsCode := "tml", iso := "tam", value := .morphologicalOnly }
  , { walsCode := "tas", iso := "shi", value := .morphologicalOnly }
  , { walsCode := "tel", iso := "tel", value := .morphologicalOnly }
  , { walsCode := "tmr", iso := "tea", value := .morphologicalOnly }
  , { walsCode := "tha", iso := "tha", value := .neither }
  , { walsCode := "tib", iso := "bod", value := .neither }
  , { walsCode := "tgk", iso := "tgc", value := .both }
  , { walsCode := "tim", iso := "tih", value := .morphologicalOnly }
  , { walsCode := "tiw", iso := "tiw", value := .morphologicalOnly }
  , { walsCode := "tli", iso := "tli", value := .morphologicalOnly }
  , { walsCode := "tno", iso := "tdn", value := .morphologicalOnly }
  , { walsCode := "tng", iso := "ton", value := .morphologicalOnly }
  , { walsCode := "ton", iso := "tqw", value := .morphologicalOnly }
  , { walsCode := "tru", iso := "tpy", value := .compoundOnly }
  , { walsCode := "tsi", iso := "tsi", value := .morphologicalOnly }
  , { walsCode := "tsw", iso := "tsn", value := .morphologicalOnly }
  , { walsCode := "tuk", iso := "", value := .morphologicalOnly }
  , { walsCode := "tun", iso := "tun", value := .both }
  , { walsCode := "tna", iso := "tuv", value := .morphologicalOnly }
  , { walsCode := "tur", iso := "tur", value := .morphologicalOnly }
  , { walsCode := "tus", iso := "tus", value := .morphologicalOnly }
  , { walsCode := "tvl", iso := "tvl", value := .morphologicalOnly }
  , { walsCode := "tzo", iso := "tzo", value := .morphologicalOnly }
  , { walsCode := "tsh", iso := "par", value := .both }
  , { walsCode := "uli", iso := "uli", value := .morphologicalOnly }
  , { walsCode := "una", iso := "mtg", value := .morphologicalOnly }
  , { walsCode := "ung", iso := "ung", value := .neither }
  , { walsCode := "uhi", iso := "urf", value := .morphologicalOnly }
  , { walsCode := "urk", iso := "urb", value := .morphologicalOnly }
  , { walsCode := "usa", iso := "wnu", value := .morphologicalOnly }
  , { walsCode := "ute", iso := "ute", value := .morphologicalOnly }
  , { walsCode := "uzb", iso := "", value := .morphologicalOnly }
  , { walsCode := "vai", iso := "vai", value := .neither }
  , { walsCode := "vie", iso := "vie", value := .compoundOnly }
  , { walsCode := "wam", iso := "wmb", value := .morphologicalOnly }
  , { walsCode := "wra", iso := "wba", value := .morphologicalOnly }
  , { walsCode := "wrd", iso := "wrr", value := .compoundOnly }
  , { walsCode := "war", iso := "pav", value := .compoundOnly }
  , { walsCode := "wrl", iso := "wbp", value := .morphologicalOnly }
  , { walsCode := "wat", iso := "wbv", value := .morphologicalOnly }
  , { walsCode := "wma", iso := "mqs", value := .morphologicalOnly }
  , { walsCode := "wic", iso := "wic", value := .morphologicalOnly }
  , { walsCode := "wch", iso := "mzh", value := .morphologicalOnly }
  , { walsCode := "wol", iso := "woe", value := .morphologicalOnly }
  , { walsCode := "yag", iso := "yad", value := .morphologicalOnly }
  , { walsCode := "ykt", iso := "sah", value := .morphologicalOnly }
  , { walsCode := "ynk", iso := "kdd", value := .morphologicalOnly }
  , { walsCode := "yap", iso := "yap", value := .morphologicalOnly }
  , { walsCode := "yaq", iso := "yaq", value := .morphologicalOnly }
  , { walsCode := "yay", iso := "pcc", value := .neither }
  , { walsCode := "yel", iso := "yle", value := .morphologicalOnly }
  , { walsCode := "yid", iso := "yii", value := .morphologicalOnly }
  , { walsCode := "yim", iso := "yee", value := .both }
  , { walsCode := "yor", iso := "yor", value := .neither }
  , { walsCode := "yuc", iso := "yuc", value := .compoundOnly }
  , { walsCode := "yko", iso := "yux", value := .morphologicalOnly }
  , { walsCode := "ypk", iso := "esu", value := .morphologicalOnly }
  , { walsCode := "yus", iso := "ess", value := .morphologicalOnly }
  , { walsCode := "yuw", iso := "kld", value := .morphologicalOnly }
  , { walsCode := "zul", iso := "zul", value := .morphologicalOnly }
  , { walsCode := "zun", iso := "zun", value := .morphologicalOnly }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F111A
