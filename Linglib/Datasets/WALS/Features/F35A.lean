import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 35A: Plurality in Independent Personal Pronouns
@cite{haspelmath-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 35A`.

Chapter 35, 261 languages.
-/

namespace Datasets.WALS.F35A

/-- WALS 35A values. -/
inductive PronounPlurality where
  /-- No independent subject pronouns (2 languages). -/
  | noIndependentSubjectPronouns
  /-- Number-indifferent pronouns (9 languages). -/
  | numberIndifferentPronouns
  /-- Person-number affixes (25 languages). -/
  | personNumberAffixes
  /-- Person-number stem (114 languages). -/
  | personNumberStem
  /-- Person-number stem + pronominal plural affix (47 languages). -/
  | personNumberStemPronominalPluralAffix
  /-- Person-number stem + nominal plural affix (22 languages). -/
  | personNumberStemNominalPluralAffix
  /-- Person stem + pronominal plural affix (23 languages). -/
  | personStemPronominalPluralAffix
  /-- Person stem + nominal plural affix (19 languages). -/
  | personStemNominalPluralAffix
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 35A dataset (261 languages). -/
def allData : List (Datapoint PronounPlurality) :=
  [ { walsCode := "abi", iso := "axb", value := .personNumberStem }
  , { walsCode := "abk", iso := "abk", value := .personNumberStem }
  , { walsCode := "aco", iso := "kjq", value := .noIndependentSubjectPronouns }
  , { walsCode := "ain", iso := "ain", value := .personNumberAffixes }
  , { walsCode := "ala", iso := "amp", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "ale", iso := "ale", value := .personNumberAffixes }
  , { walsCode := "ame", iso := "aey", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "amh", iso := "amh", value := .personNumberStem }
  , { walsCode := "apu", iso := "apu", value := .personNumberAffixes }
  , { walsCode := "abn", iso := "ard", value := .personNumberStem }
  , { walsCode := "aeg", iso := "arz", value := .personNumberStem }
  , { walsCode := "ana", iso := "aro", value := .personStemPronominalPluralAffix }
  , { walsCode := "arp", iso := "ape", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "arm", iso := "hye", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "asm", iso := "cns", value := .personStemPronominalPluralAffix }
  , { walsCode := "awp", iso := "kwi", value := .personNumberStem }
  , { walsCode := "aym", iso := "ayr", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "bag", iso := "bmi", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "bam", iso := "bam", value := .personNumberStem }
  , { walsCode := "brs", iso := "bsn", value := .personStemNominalPluralAffix }
  , { walsCode := "bsq", iso := "eus", value := .personNumberStem }
  , { walsCode := "bkr", iso := "btx", value := .personNumberStem }
  , { walsCode := "baw", iso := "bgr", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "bej", iso := "bej", value := .personNumberStem }
  , { walsCode := "bma", iso := "tzm", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "brh", iso := "brh", value := .personNumberStem }
  , { walsCode := "bri", iso := "bzd", value := .personNumberStem }
  , { walsCode := "but", iso := "bxm", value := .personStemNominalPluralAffix }
  , { walsCode := "brm", iso := "mya", value := .numberIndifferentPronouns }
  , { walsCode := "bur", iso := "bsk", value := .personNumberStem }
  , { walsCode := "cah", iso := "chl", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "cnl", iso := "ram", value := .numberIndifferentPronouns }
  , { walsCode := "cnt", iso := "yue", value := .personStemNominalPluralAffix }
  , { walsCode := "car", iso := "car", value := .personNumberStem }
  , { walsCode := "cyv", iso := "cyb", value := .personNumberAffixes }
  , { walsCode := "cha", iso := "cha", value := .personNumberStem }
  , { walsCode := "cle", iso := "cle", value := .personNumberAffixes }
  , { walsCode := "chp", iso := "chp", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ctm", iso := "ctm", value := .personNumberStem }
  , { walsCode := "chk", iso := "ckt", value := .personStemPronominalPluralAffix }
  , { walsCode := "chv", iso := "chv", value := .personStemPronominalPluralAffix }
  , { walsCode := "ccp", iso := "coc", value := .numberIndifferentPronouns }
  , { walsCode := "cmn", iso := "com", value := .personStemPronominalPluralAffix }
  , { walsCode := "coo", iso := "csz", value := .personNumberAffixes }
  , { walsCode := "cre", iso := "crk", value := .personNumberAffixes }
  , { walsCode := "dag", iso := "dgz", value := .personNumberStem }
  , { walsCode := "dgr", iso := "dta", value := .personStemPronominalPluralAffix }
  , { walsCode := "dni", iso := "dni", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "drg", iso := "dar", value := .personStemPronominalPluralAffix }
  , { walsCode := "die", iso := "dih", value := .personStemPronominalPluralAffix }
  , { walsCode := "dio", iso := "dyo", value := .personNumberStem }
  , { walsCode := "djr", iso := "ddj", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "dre", iso := "dhv", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "eka", iso := "ekg", value := .personStemPronominalPluralAffix }
  , { walsCode := "eng", iso := "eng", value := .personNumberStem }
  , { walsCode := "epe", iso := "sja", value := .personNumberStem }
  , { walsCode := "err", iso := "erg", value := .personNumberStem }
  , { walsCode := "eve", iso := "evn", value := .personStemPronominalPluralAffix }
  , { walsCode := "ewe", iso := "ewe", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "fij", iso := "fij", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "fin", iso := "fin", value := .personNumberStem }
  , { walsCode := "fre", iso := "fra", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "fur", iso := "fvr", value := .personNumberStem }
  , { walsCode := "fut", iso := "fut", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "gar", iso := "grt", value := .personNumberStem }
  , { walsCode := "geo", iso := "kat", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ger", iso := "deu", value := .personNumberStem }
  , { walsCode := "goo", iso := "gni", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "grb", iso := "grj", value := .personNumberStem }
  , { walsCode := "grk", iso := "ell", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "grw", iso := "kal", value := .personNumberStem }
  , { walsCode := "gua", iso := "gug", value := .personNumberStem }
  , { walsCode := "guu", iso := "kky", value := .personNumberStem }
  , { walsCode := "hai", iso := "hai", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "ham", iso := "hmt", value := .personNumberStem }
  , { walsCode := "hau", iso := "hau", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "haw", iso := "haw", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "heb", iso := "heb", value := .personNumberStem }
  , { walsCode := "hin", iso := "hin", value := .personNumberStem }
  , { walsCode := "hix", iso := "hix", value := .personNumberStem }
  , { walsCode := "hmo", iso := "hnj", value := .personNumberStem }
  , { walsCode := "hmi", iso := "hto", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "hun", iso := "hun", value := .personNumberStem }
  , { walsCode := "hzb", iso := "huz", value := .personNumberStem }
  , { walsCode := "iba", iso := "iba", value := .personNumberStem }
  , { walsCode := "igb", iso := "ibo", value := .personNumberStem }
  , { walsCode := "ika", iso := "arh", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "imo", iso := "imn", value := .numberIndifferentPronouns }
  , { walsCode := "ind", iso := "ind", value := .personNumberStem }
  , { walsCode := "ing", iso := "inh", value := .personNumberStem }
  , { walsCode := "irq", iso := "irk", value := .personNumberStem }
  , { walsCode := "iri", iso := "gle", value := .personNumberStem }
  , { walsCode := "ite", iso := "itl", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "jak", iso := "jac", value := .personNumberAffixes }
  , { walsCode := "jpn", iso := "jpn", value := .personStemNominalPluralAffix }
  , { walsCode := "juh", iso := "ktz", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "kmk", iso := "xal", value := .personStemPronominalPluralAffix }
  , { walsCode := "kam", iso := "xbr", value := .personNumberAffixes }
  , { walsCode := "knd", iso := "kan", value := .personStemPronominalPluralAffix }
  , { walsCode := "knr", iso := "knc", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "krk", iso := "kyh", value := .personNumberStem }
  , { walsCode := "kyl", iso := "eky", value := .personNumberStem }
  , { walsCode := "kay", iso := "gyd", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ker", iso := "ker", value := .personNumberStem }
  , { walsCode := "ket", iso := "ket", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "kew", iso := "kew", value := .personNumberStem }
  , { walsCode := "kha", iso := "khk", value := .personStemNominalPluralAffix }
  , { walsCode := "khs", iso := "kha", value := .personStemPronominalPluralAffix }
  , { walsCode := "khm", iso := "khm", value := .personNumberStem }
  , { walsCode := "kmu", iso := "kjg", value := .personNumberStem }
  , { walsCode := "klv", iso := "kij", value := .personNumberStem }
  , { walsCode := "kio", iso := "kio", value := .numberIndifferentPronouns }
  , { walsCode := "krb", iso := "gil", value := .personNumberStem }
  , { walsCode := "koa", iso := "cku", value := .personNumberAffixes }
  , { walsCode := "kob", iso := "kpw", value := .personNumberStem }
  , { walsCode := "kon", iso := "kng", value := .personNumberStem }
  , { walsCode := "kor", iso := "kor", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "kfe", iso := "kfz", value := .personNumberAffixes }
  , { walsCode := "kos", iso := "kos", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "kse", iso := "ses", value := .personNumberStem }
  , { walsCode := "kro", iso := "kgo", value := .personNumberStem }
  , { walsCode := "knm", iso := "kun", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "krd", iso := "ckb", value := .personNumberStem }
  , { walsCode := "kut", iso := "kut", value := .personNumberStem }
  , { walsCode := "kwa", iso := "kwd", value := .personNumberStem }
  , { walsCode := "lad", iso := "lbj", value := .personStemNominalPluralAffix }
  , { walsCode := "lah", iso := "lhu", value := .personStemNominalPluralAffix }
  , { walsCode := "lak", iso := "lbe", value := .personNumberStem }
  , { walsCode := "lkt", iso := "lkt", value := .personNumberAffixes }
  , { walsCode := "lan", iso := "laj", value := .personNumberAffixes }
  , { walsCode := "lat", iso := "lav", value := .personNumberStem }
  , { walsCode := "lav", iso := "lvk", value := .personNumberStem }
  , { walsCode := "lep", iso := "lep", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "lez", iso := "lez", value := .personNumberStem }
  , { walsCode := "lim", iso := "lif", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "lin", iso := "lin", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "luv", iso := "lue", value := .personNumberStem }
  , { walsCode := "mab", iso := "mde", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mac", iso := "mbc", value := .personNumberStem }
  , { walsCode := "mak", iso := "myh", value := .personNumberStem }
  , { walsCode := "mal", iso := "plt", value := .personNumberStem }
  , { walsCode := "mnd", iso := "cmn", value := .personStemNominalPluralAffix }
  , { walsCode := "myi", iso := "mpc", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "mns", iso := "mns", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mao", iso := "mri", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "map", iso := "arn", value := .personNumberStem }
  , { walsCode := "mku", iso := "zmr", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mny", iso := "zmc", value := .personNumberStem }
  , { walsCode := "mar", iso := "mrc", value := .numberIndifferentPronouns }
  , { walsCode := "mrd", iso := "mrz", value := .personStemNominalPluralAffix }
  , { walsCode := "mrt", iso := "vma", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mau", iso := "mph", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "may", iso := "ayz", value := .personNumberStem }
  , { walsCode := "meh", iso := "gdq", value := .personNumberStem }
  , { walsCode := "mei", iso := "mni", value := .personStemNominalPluralAffix }
  , { walsCode := "mss", iso := "skd", value := .personNumberStem }
  , { walsCode := "mxc", iso := "mig", value := .personStemNominalPluralAffix }
  , { walsCode := "mok", iso := "mkj", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mna", iso := "mnb", value := .personNumberStem }
  , { walsCode := "mun", iso := "unr", value := .personNumberAffixes }
  , { walsCode := "mrl", iso := "mur", value := .personStemPronominalPluralAffix }
  , { walsCode := "nht", iso := "nhg", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "kho", iso := "naq", value := .personNumberAffixes }
  , { walsCode := "nav", iso := "nav", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "ndy", iso := "djk", value := .personNumberStem }
  , { walsCode := "ntu", iso := "yrk", value := .personStemNominalPluralAffix }
  , { walsCode := "nez", iso := "nez", value := .personNumberStem }
  , { walsCode := "nti", iso := "niy", value := .personStemPronominalPluralAffix }
  , { walsCode := "ngi", iso := "wyb", value := .personNumberStem }
  , { walsCode := "nbr", iso := "gym", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "nic", iso := "ncb", value := .personNumberStem }
  , { walsCode := "niv", iso := "niv", value := .personStemNominalPluralAffix }
  , { walsCode := "nko", iso := "cgg", value := .personNumberStem }
  , { walsCode := "nbd", iso := "dgl", value := .personNumberStem }
  , { walsCode := "nug", iso := "nuy", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "oji", iso := "", value := .personNumberAffixes }
  , { walsCode := "ond", iso := "one", value := .numberIndifferentPronouns }
  , { walsCode := "ork", iso := "oaa", value := .personStemPronominalPluralAffix }
  , { walsCode := "orh", iso := "hae", value := .personNumberStem }
  , { walsCode := "otm", iso := "ote", value := .personNumberAffixes }
  , { walsCode := "pms", iso := "pma", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "pai", iso := "pwn", value := .personNumberStem }
  , { walsCode := "pny", iso := "pnw", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "psm", iso := "pqm", value := .personNumberAffixes }
  , { walsCode := "pau", iso := "pad", value := .personNumberAffixes }
  , { walsCode := "prs", iso := "pes", value := .personNumberStem }
  , { walsCode := "pil", iso := "piv", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "pip", iso := "ppl", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "prh", iso := "myp", value := .numberIndifferentPronouns }
  , { walsCode := "pit", iso := "pjt", value := .personNumberAffixes }
  , { walsCode := "ppi", iso := "pit", value := .personNumberStem }
  , { walsCode := "pso", iso := "pom", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "qaw", iso := "alc", value := .numberIndifferentPronouns }
  , { walsCode := "qhu", iso := "qub", value := .personStemNominalPluralAffix }
  , { walsCode := "qim", iso := "qvi", value := .personNumberStem }
  , { walsCode := "ram", iso := "rma", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "rap", iso := "rap", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ret", iso := "tnc", value := .personStemPronominalPluralAffix }
  , { walsCode := "rus", iso := "rus", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "sam", iso := "smo", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "san", iso := "sag", value := .personNumberStem }
  , { walsCode := "snm", iso := "xsu", value := .personStemPronominalPluralAffix }
  , { walsCode := "sel", iso := "ona", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "sml", iso := "sza", value := .personStemPronominalPluralAffix }
  , { walsCode := "snt", iso := "set", value := .personNumberStem }
  , { walsCode := "shk", iso := "shp", value := .personNumberStem }
  , { walsCode := "sla", iso := "den", value := .personNumberStem }
  , { walsCode := "spa", iso := "spa", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "squ", iso := "squ", value := .personNumberStem }
  , { walsCode := "sue", iso := "sue", value := .personStemPronominalPluralAffix }
  , { walsCode := "sup", iso := "spp", value := .personNumberStem }
  , { walsCode := "swa", iso := "swh", value := .personNumberStem }
  , { walsCode := "tab", iso := "mky", value := .personNumberStem }
  , { walsCode := "tag", iso := "tgl", value := .personNumberStem }
  , { walsCode := "tml", iso := "tam", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "tel", iso := "tel", value := .personNumberStem }
  , { walsCode := "tps", iso := "stp", value := .personNumberAffixes }
  , { walsCode := "tha", iso := "tha", value := .personNumberStem }
  , { walsCode := "tib", iso := "bod", value := .personStemNominalPluralAffix }
  , { walsCode := "tin", iso := "cir", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "tiw", iso := "tiw", value := .personNumberStem }
  , { walsCode := "tli", iso := "tli", value := .personNumberStem }
  , { walsCode := "tol", iso := "jic", value := .personNumberStem }
  , { walsCode := "tms", iso := "dto", value := .personNumberStem }
  , { walsCode := "ton", iso := "tqw", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "tru", iso := "tpy", value := .personStemNominalPluralAffix }
  , { walsCode := "tsi", iso := "tsi", value := .personNumberAffixes }
  , { walsCode := "tuk", iso := "", value := .personNumberStem }
  , { walsCode := "tun", iso := "tun", value := .personNumberAffixes }
  , { walsCode := "tur", iso := "tur", value := .personStemNominalPluralAffix }
  , { walsCode := "tvl", iso := "tvl", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "tsh", iso := "par", value := .personStemNominalPluralAffix }
  , { walsCode := "una", iso := "mtg", value := .personNumberStem }
  , { walsCode := "ung", iso := "ung", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "uhi", iso := "urf", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "urk", iso := "urb", value := .personNumberStem }
  , { walsCode := "usa", iso := "wnu", value := .personNumberStem }
  , { walsCode := "uzb", iso := "", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "vie", iso := "vie", value := .personStemPronominalPluralAffix }
  , { walsCode := "wam", iso := "wmb", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "wra", iso := "wba", value := .personNumberStem }
  , { walsCode := "wrd", iso := "wrr", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "war", iso := "pav", value := .noIndependentSubjectPronouns }
  , { walsCode := "wat", iso := "wbv", value := .personNumberStem }
  , { walsCode := "wic", iso := "wic", value := .personNumberAffixes }
  , { walsCode := "wch", iso := "mzh", value := .personStemNominalPluralAffix }
  , { walsCode := "wlf", iso := "wol", value := .personNumberStem }
  , { walsCode := "yag", iso := "yad", value := .personNumberStem }
  , { walsCode := "ykt", iso := "sah", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "yaq", iso := "yaq", value := .personNumberStem }
  , { walsCode := "yel", iso := "yle", value := .personNumberStem }
  , { walsCode := "yid", iso := "yii", value := .personNumberStem }
  , { walsCode := "yim", iso := "yee", value := .personNumberStem }
  , { walsCode := "yor", iso := "yor", value := .personNumberStem }
  , { walsCode := "yuc", iso := "yuc", value := .personNumberAffixes }
  , { walsCode := "yko", iso := "yux", value := .personStemPronominalPluralAffix }
  , { walsCode := "yna", iso := "ynk", value := .personNumberStem }
  , { walsCode := "yur", iso := "yur", value := .personNumberStem }
  , { walsCode := "zqc", iso := "zoc", value := .personNumberStem }
  , { walsCode := "zul", iso := "zul", value := .personNumberStem }
  , { walsCode := "zun", iso := "zun", value := .personStemPronominalPluralAffix }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F35A
