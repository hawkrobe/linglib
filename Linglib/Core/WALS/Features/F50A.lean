import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 50A: Asymmetrical Case-Marking
@cite{iggesen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 50A`.

Chapter 50, 261 languages.
-/

namespace Core.WALS.F50A

/-- WALS 50A values. -/
inductive AsymmetricalCaseMarking where
  /-- No case-marking (81 languages). -/
  | noCaseMarking
  /-- Symmetrical (79 languages). -/
  | symmetrical
  /-- Additive-quantitatively asymmetrical (53 languages). -/
  | additiveQuantitativelyAsymmetrical
  /-- Subtractive-quantitatively asymmetrical (20 languages). -/
  | subtractiveQuantitativelyAsymmetrical
  /-- Qualitatively asymmetrical (7 languages). -/
  | qualitativelyAsymmetrical
  /-- Syncretism in relevant NP-types (21 languages). -/
  | syncretismInRelevantNpTypes
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 50A dataset (261 languages). -/
def allData : List (Datapoint AsymmetricalCaseMarking) :=
  [ { walsCode := "abi", iso := "axb", value := .noCaseMarking }
  , { walsCode := "abk", iso := "abk", value := .symmetrical }
  , { walsCode := "aco", iso := "kjq", value := .noCaseMarking }
  , { walsCode := "ain", iso := "ain", value := .symmetrical }
  , { walsCode := "ala", iso := "amp", value := .symmetrical }
  , { walsCode := "alb", iso := "sqi", value := .syncretismInRelevantNpTypes }
  , { walsCode := "ale", iso := "ale", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "ame", iso := "aey", value := .noCaseMarking }
  , { walsCode := "amh", iso := "amh", value := .symmetrical }
  , { walsCode := "amu", iso := "ame", value := .symmetrical }
  , { walsCode := "apu", iso := "apu", value := .symmetrical }
  , { walsCode := "arb", iso := "arl", value := .symmetrical }
  , { walsCode := "aeg", iso := "arz", value := .noCaseMarking }
  , { walsCode := "ana", iso := "aro", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "arp", iso := "ape", value := .noCaseMarking }
  , { walsCode := "arm", iso := "hye", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "asm", iso := "cns", value := .noCaseMarking }
  , { walsCode := "awp", iso := "kwi", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "aym", iso := "ayr", value := .symmetrical }
  , { walsCode := "bag", iso := "bmi", value := .noCaseMarking }
  , { walsCode := "bam", iso := "bam", value := .noCaseMarking }
  , { walsCode := "brs", iso := "bsn", value := .symmetrical }
  , { walsCode := "bsq", iso := "eus", value := .syncretismInRelevantNpTypes }
  , { walsCode := "bkr", iso := "btx", value := .noCaseMarking }
  , { walsCode := "baw", iso := "bgr", value := .symmetrical }
  , { walsCode := "bej", iso := "bej", value := .syncretismInRelevantNpTypes }
  , { walsCode := "bec", iso := "ctg", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "bma", iso := "tzm", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "brh", iso := "brh", value := .symmetrical }
  , { walsCode := "bri", iso := "bzd", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "bul", iso := "bul", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "brm", iso := "mya", value := .symmetrical }
  , { walsCode := "bur", iso := "bsk", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "cah", iso := "chl", value := .symmetrical }
  , { walsCode := "cnl", iso := "ram", value := .noCaseMarking }
  , { walsCode := "car", iso := "car", value := .noCaseMarking }
  , { walsCode := "ctl", iso := "cat", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "cyv", iso := "cyb", value := .symmetrical }
  , { walsCode := "cha", iso := "cha", value := .noCaseMarking }
  , { walsCode := "cle", iso := "cle", value := .noCaseMarking }
  , { walsCode := "chk", iso := "ckt", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "cba", iso := "boi", value := .noCaseMarking }
  , { walsCode := "chv", iso := "chv", value := .symmetrical }
  , { walsCode := "cmn", iso := "com", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "coo", iso := "csz", value := .symmetrical }
  , { walsCode := "cre", iso := "crk", value := .symmetrical }
  , { walsCode := "dag", iso := "dgz", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "dni", iso := "dni", value := .symmetrical }
  , { walsCode := "dio", iso := "dyo", value := .noCaseMarking }
  , { walsCode := "don", iso := "kmc", value := .noCaseMarking }
  , { walsCode := "dre", iso := "dhv", value := .noCaseMarking }
  , { walsCode := "dut", iso := "nld", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "dyi", iso := "dbl", value := .qualitativelyAsymmetrical }
  , { walsCode := "eka", iso := "ekg", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "eng", iso := "eng", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "epe", iso := "sja", value := .symmetrical }
  , { walsCode := "est", iso := "ekk", value := .symmetrical }
  , { walsCode := "eve", iso := "evn", value := .symmetrical }
  , { walsCode := "ewe", iso := "ewe", value := .noCaseMarking }
  , { walsCode := "fij", iso := "fij", value := .noCaseMarking }
  , { walsCode := "fin", iso := "fin", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "fre", iso := "fra", value := .noCaseMarking }
  , { walsCode := "frw", iso := "fry", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "fua", iso := "fub", value := .noCaseMarking }
  , { walsCode := "fur", iso := "fvr", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "gar", iso := "grt", value := .symmetrical }
  , { walsCode := "geo", iso := "kat", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "ger", iso := "deu", value := .syncretismInRelevantNpTypes }
  , { walsCode := "gim", iso := "bcq", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "goo", iso := "gni", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "grb", iso := "grj", value := .noCaseMarking }
  , { walsCode := "grk", iso := "ell", value := .syncretismInRelevantNpTypes }
  , { walsCode := "grw", iso := "kal", value := .syncretismInRelevantNpTypes }
  , { walsCode := "gua", iso := "gug", value := .noCaseMarking }
  , { walsCode := "hai", iso := "hai", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ham", iso := "hmt", value := .syncretismInRelevantNpTypes }
  , { walsCode := "hau", iso := "hau", value := .noCaseMarking }
  , { walsCode := "heb", iso := "heb", value := .noCaseMarking }
  , { walsCode := "hix", iso := "hix", value := .noCaseMarking }
  , { walsCode := "hmo", iso := "hnj", value := .noCaseMarking }
  , { walsCode := "hua", iso := "ygr", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "hve", iso := "huv", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "hmi", iso := "hto", value := .symmetrical }
  , { walsCode := "hun", iso := "hun", value := .symmetrical }
  , { walsCode := "hzb", iso := "huz", value := .syncretismInRelevantNpTypes }
  , { walsCode := "iaa", iso := "iai", value := .noCaseMarking }
  , { walsCode := "ice", iso := "isl", value := .syncretismInRelevantNpTypes }
  , { walsCode := "igb", iso := "ibo", value := .noCaseMarking }
  , { walsCode := "ika", iso := "arh", value := .symmetrical }
  , { walsCode := "ilo", iso := "ilo", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "imo", iso := "imn", value := .symmetrical }
  , { walsCode := "ind", iso := "ind", value := .noCaseMarking }
  , { walsCode := "ing", iso := "inh", value := .syncretismInRelevantNpTypes }
  , { walsCode := "irq", iso := "irk", value := .symmetrical }
  , { walsCode := "iri", iso := "gle", value := .symmetrical }
  , { walsCode := "ita", iso := "ita", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "jak", iso := "jac", value := .noCaseMarking }
  , { walsCode := "jpn", iso := "jpn", value := .symmetrical }
  , { walsCode := "juh", iso := "ktz", value := .noCaseMarking }
  , { walsCode := "kly", iso := "mwp", value := .qualitativelyAsymmetrical }
  , { walsCode := "kls", iso := "fla", value := .symmetrical }
  , { walsCode := "knd", iso := "kan", value := .symmetrical }
  , { walsCode := "knr", iso := "knc", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "krk", iso := "kyh", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "kas", iso := "kas", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "kyl", iso := "eky", value := .noCaseMarking }
  , { walsCode := "kay", iso := "gyd", value := .symmetrical }
  , { walsCode := "ker", iso := "ker", value := .symmetrical }
  , { walsCode := "ket", iso := "ket", value := .symmetrical }
  , { walsCode := "kew", iso := "kew", value := .symmetrical }
  , { walsCode := "kha", iso := "khk", value := .symmetrical }
  , { walsCode := "kty", iso := "kca", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "khs", iso := "kha", value := .noCaseMarking }
  , { walsCode := "khm", iso := "khm", value := .noCaseMarking }
  , { walsCode := "kmu", iso := "kjg", value := .noCaseMarking }
  , { walsCode := "klv", iso := "kij", value := .noCaseMarking }
  , { walsCode := "kin", iso := "kin", value := .noCaseMarking }
  , { walsCode := "kio", iso := "kio", value := .symmetrical }
  , { walsCode := "krb", iso := "gil", value := .noCaseMarking }
  , { walsCode := "koa", iso := "cku", value := .symmetrical }
  , { walsCode := "kob", iso := "kpw", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "kmb", iso := "", value := .noCaseMarking }
  , { walsCode := "kon", iso := "kng", value := .noCaseMarking }
  , { walsCode := "kor", iso := "kor", value := .symmetrical }
  , { walsCode := "kfe", iso := "kfz", value := .noCaseMarking }
  , { walsCode := "kos", iso := "kos", value := .noCaseMarking }
  , { walsCode := "kse", iso := "ses", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "kro", iso := "kgo", value := .syncretismInRelevantNpTypes }
  , { walsCode := "knm", iso := "kun", value := .symmetrical }
  , { walsCode := "kut", iso := "kut", value := .noCaseMarking }
  , { walsCode := "lad", iso := "lbj", value := .symmetrical }
  , { walsCode := "lak", iso := "lbe", value := .symmetrical }
  , { walsCode := "lkt", iso := "lkt", value := .noCaseMarking }
  , { walsCode := "lan", iso := "laj", value := .noCaseMarking }
  , { walsCode := "lat", iso := "lav", value := .syncretismInRelevantNpTypes }
  , { walsCode := "lav", iso := "lvk", value := .noCaseMarking }
  , { walsCode := "lep", iso := "lep", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "lez", iso := "lez", value := .syncretismInRelevantNpTypes }
  , { walsCode := "lit", iso := "lit", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "luv", iso := "lue", value := .noCaseMarking }
  , { walsCode := "mab", iso := "mde", value := .symmetrical }
  , { walsCode := "mdr", iso := "mad", value := .noCaseMarking }
  , { walsCode := "mak", iso := "myh", value := .noCaseMarking }
  , { walsCode := "mal", iso := "plt", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "mlk", iso := "mpb", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "mym", iso := "mal", value := .symmetrical }
  , { walsCode := "mnd", iso := "cmn", value := .noCaseMarking }
  , { walsCode := "myi", iso := "mpc", value := .qualitativelyAsymmetrical }
  , { walsCode := "mao", iso := "mri", value := .noCaseMarking }
  , { walsCode := "map", iso := "arn", value := .symmetrical }
  , { walsCode := "mku", iso := "zmr", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "mhi", iso := "mar", value := .symmetrical }
  , { walsCode := "mar", iso := "mrc", value := .symmetrical }
  , { walsCode := "mrd", iso := "mrz", value := .noCaseMarking }
  , { walsCode := "mrt", iso := "vma", value := .syncretismInRelevantNpTypes }
  , { walsCode := "mau", iso := "mph", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "may", iso := "ayz", value := .symmetrical }
  , { walsCode := "mei", iso := "mni", value := .symmetrical }
  , { walsCode := "mss", iso := "skd", value := .symmetrical }
  , { walsCode := "mxc", iso := "mig", value := .noCaseMarking }
  , { walsCode := "mok", iso := "mkj", value := .noCaseMarking }
  , { walsCode := "moe", iso := "myv", value := .symmetrical }
  , { walsCode := "mun", iso := "unr", value := .symmetrical }
  , { walsCode := "mrl", iso := "mur", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "nht", iso := "nhg", value := .noCaseMarking }
  , { walsCode := "kho", iso := "naq", value := .symmetrical }
  , { walsCode := "nav", iso := "nav", value := .noCaseMarking }
  , { walsCode := "ndy", iso := "djk", value := .noCaseMarking }
  , { walsCode := "ntu", iso := "yrk", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "nez", iso := "nez", value := .symmetrical }
  , { walsCode := "nti", iso := "niy", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ngi", iso := "wyb", value := .qualitativelyAsymmetrical }
  , { walsCode := "niv", iso := "niv", value := .symmetrical }
  , { walsCode := "nko", iso := "cgg", value := .noCaseMarking }
  , { walsCode := "nbd", iso := "dgl", value := .symmetrical }
  , { walsCode := "nug", iso := "nuy", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ond", iso := "one", value := .noCaseMarking }
  , { walsCode := "orh", iso := "hae", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "ots", iso := "otm", value := .noCaseMarking }
  , { walsCode := "pms", iso := "pma", value := .noCaseMarking }
  , { walsCode := "pai", iso := "pwn", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "pal", iso := "pau", value := .noCaseMarking }
  , { walsCode := "pan", iso := "pan", value := .syncretismInRelevantNpTypes }
  , { walsCode := "psh", iso := "pst", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "psm", iso := "pqm", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "pau", iso := "pad", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "prs", iso := "pes", value := .symmetrical }
  , { walsCode := "prh", iso := "myp", value := .symmetrical }
  , { walsCode := "pit", iso := "pjt", value := .qualitativelyAsymmetrical }
  , { walsCode := "pol", iso := "pol", value := .syncretismInRelevantNpTypes }
  , { walsCode := "pso", iso := "pom", value := .symmetrical }
  , { walsCode := "pae", iso := "pbb", value := .symmetrical }
  , { walsCode := "qaw", iso := "alc", value := .symmetrical }
  , { walsCode := "qim", iso := "qvi", value := .symmetrical }
  , { walsCode := "ram", iso := "rma", value := .syncretismInRelevantNpTypes }
  , { walsCode := "rap", iso := "rap", value := .noCaseMarking }
  , { walsCode := "rka", iso := "rmy", value := .symmetrical }
  , { walsCode := "rom", iso := "ron", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "rus", iso := "rus", value := .syncretismInRelevantNpTypes }
  , { walsCode := "sno", iso := "sme", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "san", iso := "sag", value := .noCaseMarking }
  , { walsCode := "snm", iso := "xsu", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "sel", iso := "ona", value := .symmetrical }
  , { walsCode := "sml", iso := "sza", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "snt", iso := "set", value := .noCaseMarking }
  , { walsCode := "scr", iso := "hbs", value := .syncretismInRelevantNpTypes }
  , { walsCode := "shk", iso := "shp", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "snh", iso := "sin", value := .symmetrical }
  , { walsCode := "sla", iso := "den", value := .noCaseMarking }
  , { walsCode := "som", iso := "som", value := .symmetrical }
  , { walsCode := "spa", iso := "spa", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "squ", iso := "squ", value := .syncretismInRelevantNpTypes }
  , { walsCode := "sue", iso := "sue", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "sup", iso := "spp", value := .symmetrical }
  , { walsCode := "swa", iso := "swh", value := .noCaseMarking }
  , { walsCode := "swe", iso := "swe", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tab", iso := "mky", value := .noCaseMarking }
  , { walsCode := "tag", iso := "tgl", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tts", iso := "tks", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tha", iso := "tha", value := .noCaseMarking }
  , { walsCode := "tin", iso := "cir", value := .noCaseMarking }
  , { walsCode := "tiw", iso := "tiw", value := .noCaseMarking }
  , { walsCode := "tli", iso := "tli", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tda", iso := "tcx", value := .symmetrical }
  , { walsCode := "tru", iso := "tpy", value := .symmetrical }
  , { walsCode := "tsi", iso := "tsi", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tuk", iso := "", value := .noCaseMarking }
  , { walsCode := "tun", iso := "tun", value := .symmetrical }
  , { walsCode := "tna", iso := "tuv", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "tur", iso := "tur", value := .symmetrical }
  , { walsCode := "tvl", iso := "tvl", value := .noCaseMarking }
  , { walsCode := "udh", iso := "ude", value := .symmetrical }
  , { walsCode := "udm", iso := "udm", value := .symmetrical }
  , { walsCode := "una", iso := "mtg", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ung", iso := "ung", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "urd", iso := "urd", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "urk", iso := "urb", value := .noCaseMarking }
  , { walsCode := "usa", iso := "wnu", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "vie", iso := "vie", value := .noCaseMarking }
  , { walsCode := "wam", iso := "wmb", value := .qualitativelyAsymmetrical }
  , { walsCode := "wra", iso := "wba", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "wrd", iso := "wrr", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "war", iso := "pav", value := .noCaseMarking }
  , { walsCode := "was", iso := "was", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "wel", iso := "cym", value := .noCaseMarking }
  , { walsCode := "wic", iso := "wic", value := .symmetrical }
  , { walsCode := "wch", iso := "mzh", value := .noCaseMarking }
  , { walsCode := "win", iso := "wnw", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "yag", iso := "yad", value := .symmetrical }
  , { walsCode := "yaq", iso := "yaq", value := .symmetrical }
  , { walsCode := "ywl", iso := "yok", value := .symmetrical }
  , { walsCode := "yid", iso := "yii", value := .qualitativelyAsymmetrical }
  , { walsCode := "yim", iso := "yee", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "yor", iso := "yor", value := .noCaseMarking }
  , { walsCode := "yuc", iso := "yuc", value := .symmetrical }
  , { walsCode := "yko", iso := "yux", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ypk", iso := "esu", value := .syncretismInRelevantNpTypes }
  , { walsCode := "yur", iso := "yur", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "zqc", iso := "zoc", value := .symmetrical }
  , { walsCode := "zul", iso := "zul", value := .noCaseMarking }
  , { walsCode := "zun", iso := "zun", value := .additiveQuantitativelyAsymmetrical }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F50A
