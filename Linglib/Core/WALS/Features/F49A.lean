import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 49A: Number of Cases
@cite{iggesen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 49A`.

Chapter 49, 261 languages.
-/

namespace Core.WALS.F49A

/-- WALS 49A values. -/
inductive CaseCount where
  /-- No morphological case-marking (100 languages). -/
  | noMorphologicalCaseMarking
  /-- 2 cases (23 languages). -/
  | cases2
  /-- 3 cases (9 languages). -/
  | cases3
  /-- 4 cases (9 languages). -/
  | cases4
  /-- 5 cases (12 languages). -/
  | cases5
  /-- 6-7 cases (37 languages). -/
  | cases6_7
  /-- 8-9 cases (23 languages). -/
  | cases8_9
  /-- 10 or more cases (24 languages). -/
  | cases10OrMore
  /-- Exclusively borderline case-marking (24 languages). -/
  | exclusivelyBorderlineCaseMarking
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 49A dataset (261 languages). -/
def allData : List (Datapoint CaseCount) :=
  [ { walsCode := "abi", iso := "axb", value := .noMorphologicalCaseMarking }
  , { walsCode := "abk", iso := "abk", value := .cases2 }
  , { walsCode := "aco", iso := "kjq", value := .noMorphologicalCaseMarking }
  , { walsCode := "ain", iso := "ain", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "ala", iso := "amp", value := .cases8_9 }
  , { walsCode := "alb", iso := "sqi", value := .cases4 }
  , { walsCode := "ale", iso := "ale", value := .cases2 }
  , { walsCode := "ame", iso := "aey", value := .noMorphologicalCaseMarking }
  , { walsCode := "amh", iso := "amh", value := .cases2 }
  , { walsCode := "amu", iso := "ame", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "apu", iso := "apu", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "arb", iso := "arl", value := .cases8_9 }
  , { walsCode := "aeg", iso := "arz", value := .noMorphologicalCaseMarking }
  , { walsCode := "ana", iso := "aro", value := .cases5 }
  , { walsCode := "arp", iso := "ape", value := .noMorphologicalCaseMarking }
  , { walsCode := "arm", iso := "hye", value := .cases5 }
  , { walsCode := "asm", iso := "cns", value := .noMorphologicalCaseMarking }
  , { walsCode := "awp", iso := "kwi", value := .cases10OrMore }
  , { walsCode := "aym", iso := "ayr", value := .cases6_7 }
  , { walsCode := "bag", iso := "bmi", value := .noMorphologicalCaseMarking }
  , { walsCode := "bam", iso := "bam", value := .noMorphologicalCaseMarking }
  , { walsCode := "brs", iso := "bsn", value := .cases2 }
  , { walsCode := "bsq", iso := "eus", value := .cases10OrMore }
  , { walsCode := "bkr", iso := "btx", value := .noMorphologicalCaseMarking }
  , { walsCode := "baw", iso := "bgr", value := .cases4 }
  , { walsCode := "bej", iso := "bej", value := .cases2 }
  , { walsCode := "bec", iso := "ctg", value := .cases6_7 }
  , { walsCode := "bma", iso := "tzm", value := .cases2 }
  , { walsCode := "brh", iso := "brh", value := .cases10OrMore }
  , { walsCode := "bri", iso := "bzd", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "bul", iso := "bul", value := .noMorphologicalCaseMarking }
  , { walsCode := "brm", iso := "mya", value := .cases8_9 }
  , { walsCode := "bur", iso := "bsk", value := .cases8_9 }
  , { walsCode := "cah", iso := "chl", value := .cases5 }
  , { walsCode := "cnl", iso := "ram", value := .noMorphologicalCaseMarking }
  , { walsCode := "car", iso := "car", value := .noMorphologicalCaseMarking }
  , { walsCode := "ctl", iso := "cat", value := .noMorphologicalCaseMarking }
  , { walsCode := "cyv", iso := "cyb", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "cha", iso := "cha", value := .noMorphologicalCaseMarking }
  , { walsCode := "cle", iso := "cle", value := .noMorphologicalCaseMarking }
  , { walsCode := "chk", iso := "ckt", value := .cases10OrMore }
  , { walsCode := "cba", iso := "boi", value := .noMorphologicalCaseMarking }
  , { walsCode := "chv", iso := "chv", value := .cases6_7 }
  , { walsCode := "cmn", iso := "com", value := .cases3 }
  , { walsCode := "coo", iso := "csz", value := .cases8_9 }
  , { walsCode := "cre", iso := "crk", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "dag", iso := "dgz", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "dni", iso := "dni", value := .cases6_7 }
  , { walsCode := "dio", iso := "dyo", value := .noMorphologicalCaseMarking }
  , { walsCode := "don", iso := "kmc", value := .noMorphologicalCaseMarking }
  , { walsCode := "dre", iso := "dhv", value := .noMorphologicalCaseMarking }
  , { walsCode := "dut", iso := "nld", value := .noMorphologicalCaseMarking }
  , { walsCode := "dyi", iso := "dbl", value := .cases6_7 }
  , { walsCode := "eka", iso := "ekg", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "eng", iso := "eng", value := .cases2 }
  , { walsCode := "epe", iso := "sja", value := .cases10OrMore }
  , { walsCode := "est", iso := "ekk", value := .cases10OrMore }
  , { walsCode := "eve", iso := "evn", value := .cases10OrMore }
  , { walsCode := "ewe", iso := "ewe", value := .noMorphologicalCaseMarking }
  , { walsCode := "fij", iso := "fij", value := .noMorphologicalCaseMarking }
  , { walsCode := "fin", iso := "fin", value := .cases10OrMore }
  , { walsCode := "fre", iso := "fra", value := .noMorphologicalCaseMarking }
  , { walsCode := "frw", iso := "fry", value := .noMorphologicalCaseMarking }
  , { walsCode := "fua", iso := "fub", value := .noMorphologicalCaseMarking }
  , { walsCode := "fur", iso := "fvr", value := .cases4 }
  , { walsCode := "gar", iso := "grt", value := .cases8_9 }
  , { walsCode := "geo", iso := "kat", value := .cases6_7 }
  , { walsCode := "ger", iso := "deu", value := .cases4 }
  , { walsCode := "gim", iso := "bcq", value := .cases6_7 }
  , { walsCode := "goo", iso := "gni", value := .cases10OrMore }
  , { walsCode := "grb", iso := "grj", value := .noMorphologicalCaseMarking }
  , { walsCode := "grk", iso := "ell", value := .cases3 }
  , { walsCode := "grw", iso := "kal", value := .cases8_9 }
  , { walsCode := "gua", iso := "gug", value := .noMorphologicalCaseMarking }
  , { walsCode := "hai", iso := "hai", value := .noMorphologicalCaseMarking }
  , { walsCode := "ham", iso := "hmt", value := .cases10OrMore }
  , { walsCode := "hau", iso := "hau", value := .noMorphologicalCaseMarking }
  , { walsCode := "heb", iso := "heb", value := .noMorphologicalCaseMarking }
  , { walsCode := "hix", iso := "hix", value := .noMorphologicalCaseMarking }
  , { walsCode := "hmo", iso := "hnj", value := .noMorphologicalCaseMarking }
  , { walsCode := "hua", iso := "ygr", value := .cases8_9 }
  , { walsCode := "hve", iso := "huv", value := .noMorphologicalCaseMarking }
  , { walsCode := "hmi", iso := "hto", value := .cases6_7 }
  , { walsCode := "hun", iso := "hun", value := .cases10OrMore }
  , { walsCode := "hzb", iso := "huz", value := .cases10OrMore }
  , { walsCode := "iaa", iso := "iai", value := .noMorphologicalCaseMarking }
  , { walsCode := "ice", iso := "isl", value := .cases4 }
  , { walsCode := "igb", iso := "ibo", value := .noMorphologicalCaseMarking }
  , { walsCode := "ika", iso := "arh", value := .cases6_7 }
  , { walsCode := "ilo", iso := "ilo", value := .noMorphologicalCaseMarking }
  , { walsCode := "imo", iso := "imn", value := .cases5 }
  , { walsCode := "ind", iso := "ind", value := .noMorphologicalCaseMarking }
  , { walsCode := "ing", iso := "inh", value := .cases10OrMore }
  , { walsCode := "irq", iso := "irk", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "iri", iso := "gle", value := .cases2 }
  , { walsCode := "ita", iso := "ita", value := .noMorphologicalCaseMarking }
  , { walsCode := "jak", iso := "jac", value := .noMorphologicalCaseMarking }
  , { walsCode := "jpn", iso := "jpn", value := .cases8_9 }
  , { walsCode := "juh", iso := "ktz", value := .noMorphologicalCaseMarking }
  , { walsCode := "kly", iso := "mwp", value := .cases8_9 }
  , { walsCode := "kls", iso := "fla", value := .cases6_7 }
  , { walsCode := "knd", iso := "kan", value := .cases6_7 }
  , { walsCode := "knr", iso := "knc", value := .cases6_7 }
  , { walsCode := "krk", iso := "kyh", value := .cases3 }
  , { walsCode := "kas", iso := "kas", value := .cases4 }
  , { walsCode := "kyl", iso := "eky", value := .noMorphologicalCaseMarking }
  , { walsCode := "kay", iso := "gyd", value := .cases10OrMore }
  , { walsCode := "ker", iso := "ker", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "ket", iso := "ket", value := .cases10OrMore }
  , { walsCode := "kew", iso := "kew", value := .cases6_7 }
  , { walsCode := "kha", iso := "khk", value := .cases8_9 }
  , { walsCode := "kty", iso := "kca", value := .cases3 }
  , { walsCode := "khs", iso := "kha", value := .noMorphologicalCaseMarking }
  , { walsCode := "khm", iso := "khm", value := .noMorphologicalCaseMarking }
  , { walsCode := "kmu", iso := "kjg", value := .noMorphologicalCaseMarking }
  , { walsCode := "klv", iso := "kij", value := .noMorphologicalCaseMarking }
  , { walsCode := "kin", iso := "kin", value := .noMorphologicalCaseMarking }
  , { walsCode := "kio", iso := "kio", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "krb", iso := "gil", value := .noMorphologicalCaseMarking }
  , { walsCode := "koa", iso := "cku", value := .cases6_7 }
  , { walsCode := "kob", iso := "kpw", value := .noMorphologicalCaseMarking }
  , { walsCode := "kmb", iso := "", value := .noMorphologicalCaseMarking }
  , { walsCode := "kon", iso := "kng", value := .noMorphologicalCaseMarking }
  , { walsCode := "kor", iso := "kor", value := .cases6_7 }
  , { walsCode := "kfe", iso := "kfz", value := .noMorphologicalCaseMarking }
  , { walsCode := "kos", iso := "kos", value := .noMorphologicalCaseMarking }
  , { walsCode := "kse", iso := "ses", value := .noMorphologicalCaseMarking }
  , { walsCode := "kro", iso := "kgo", value := .cases6_7 }
  , { walsCode := "knm", iso := "kun", value := .cases6_7 }
  , { walsCode := "kut", iso := "kut", value := .noMorphologicalCaseMarking }
  , { walsCode := "lad", iso := "lbj", value := .cases5 }
  , { walsCode := "lak", iso := "lbe", value := .cases10OrMore }
  , { walsCode := "lkt", iso := "lkt", value := .noMorphologicalCaseMarking }
  , { walsCode := "lan", iso := "laj", value := .noMorphologicalCaseMarking }
  , { walsCode := "lat", iso := "lav", value := .cases5 }
  , { walsCode := "lav", iso := "lvk", value := .noMorphologicalCaseMarking }
  , { walsCode := "lep", iso := "lep", value := .cases2 }
  , { walsCode := "lez", iso := "lez", value := .cases10OrMore }
  , { walsCode := "lit", iso := "lit", value := .cases6_7 }
  , { walsCode := "luv", iso := "lue", value := .noMorphologicalCaseMarking }
  , { walsCode := "mab", iso := "mde", value := .cases3 }
  , { walsCode := "mdr", iso := "mad", value := .noMorphologicalCaseMarking }
  , { walsCode := "mak", iso := "myh", value := .noMorphologicalCaseMarking }
  , { walsCode := "mal", iso := "plt", value := .noMorphologicalCaseMarking }
  , { walsCode := "mlk", iso := "mpb", value := .cases6_7 }
  , { walsCode := "mym", iso := "mal", value := .cases6_7 }
  , { walsCode := "mnd", iso := "cmn", value := .noMorphologicalCaseMarking }
  , { walsCode := "myi", iso := "mpc", value := .cases8_9 }
  , { walsCode := "mao", iso := "mri", value := .noMorphologicalCaseMarking }
  , { walsCode := "map", iso := "arn", value := .cases2 }
  , { walsCode := "mku", iso := "zmr", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "mhi", iso := "mar", value := .cases5 }
  , { walsCode := "mar", iso := "mrc", value := .cases6_7 }
  , { walsCode := "mrd", iso := "mrz", value := .noMorphologicalCaseMarking }
  , { walsCode := "mrt", iso := "vma", value := .cases10OrMore }
  , { walsCode := "mau", iso := "mph", value := .noMorphologicalCaseMarking }
  , { walsCode := "may", iso := "ayz", value := .cases2 }
  , { walsCode := "mei", iso := "mni", value := .cases6_7 }
  , { walsCode := "mss", iso := "skd", value := .cases6_7 }
  , { walsCode := "mxc", iso := "mig", value := .noMorphologicalCaseMarking }
  , { walsCode := "mok", iso := "mkj", value := .noMorphologicalCaseMarking }
  , { walsCode := "moe", iso := "myv", value := .cases10OrMore }
  , { walsCode := "mun", iso := "unr", value := .cases8_9 }
  , { walsCode := "mrl", iso := "mur", value := .cases4 }
  , { walsCode := "nht", iso := "nhg", value := .noMorphologicalCaseMarking }
  , { walsCode := "kho", iso := "naq", value := .cases2 }
  , { walsCode := "nav", iso := "nav", value := .noMorphologicalCaseMarking }
  , { walsCode := "ndy", iso := "djk", value := .noMorphologicalCaseMarking }
  , { walsCode := "ntu", iso := "yrk", value := .cases6_7 }
  , { walsCode := "nez", iso := "nez", value := .cases10OrMore }
  , { walsCode := "nti", iso := "niy", value := .noMorphologicalCaseMarking }
  , { walsCode := "ngi", iso := "wyb", value := .cases5 }
  , { walsCode := "niv", iso := "niv", value := .cases8_9 }
  , { walsCode := "nko", iso := "cgg", value := .noMorphologicalCaseMarking }
  , { walsCode := "nbd", iso := "dgl", value := .cases6_7 }
  , { walsCode := "nug", iso := "nuy", value := .cases10OrMore }
  , { walsCode := "ond", iso := "one", value := .noMorphologicalCaseMarking }
  , { walsCode := "orh", iso := "hae", value := .cases6_7 }
  , { walsCode := "ots", iso := "otm", value := .noMorphologicalCaseMarking }
  , { walsCode := "pms", iso := "pma", value := .noMorphologicalCaseMarking }
  , { walsCode := "pai", iso := "pwn", value := .noMorphologicalCaseMarking }
  , { walsCode := "pal", iso := "pau", value := .noMorphologicalCaseMarking }
  , { walsCode := "pan", iso := "pan", value := .cases2 }
  , { walsCode := "psh", iso := "pst", value := .cases3 }
  , { walsCode := "psm", iso := "pqm", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "pau", iso := "pad", value := .cases3 }
  , { walsCode := "prs", iso := "pes", value := .cases2 }
  , { walsCode := "prh", iso := "myp", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "pit", iso := "pjt", value := .cases10OrMore }
  , { walsCode := "pol", iso := "pol", value := .cases6_7 }
  , { walsCode := "pso", iso := "pom", value := .cases6_7 }
  , { walsCode := "pae", iso := "pbb", value := .cases6_7 }
  , { walsCode := "qaw", iso := "alc", value := .cases2 }
  , { walsCode := "qim", iso := "qvi", value := .cases8_9 }
  , { walsCode := "ram", iso := "rma", value := .cases8_9 }
  , { walsCode := "rap", iso := "rap", value := .noMorphologicalCaseMarking }
  , { walsCode := "rka", iso := "rmy", value := .cases6_7 }
  , { walsCode := "rom", iso := "ron", value := .cases2 }
  , { walsCode := "rus", iso := "rus", value := .cases6_7 }
  , { walsCode := "sno", iso := "sme", value := .cases6_7 }
  , { walsCode := "san", iso := "sag", value := .noMorphologicalCaseMarking }
  , { walsCode := "snm", iso := "xsu", value := .cases2 }
  , { walsCode := "sel", iso := "ona", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "sml", iso := "sza", value := .cases3 }
  , { walsCode := "snt", iso := "set", value := .noMorphologicalCaseMarking }
  , { walsCode := "scr", iso := "hbs", value := .cases5 }
  , { walsCode := "shk", iso := "shp", value := .cases6_7 }
  , { walsCode := "snh", iso := "sin", value := .cases5 }
  , { walsCode := "sla", iso := "den", value := .noMorphologicalCaseMarking }
  , { walsCode := "som", iso := "som", value := .cases3 }
  , { walsCode := "spa", iso := "spa", value := .noMorphologicalCaseMarking }
  , { walsCode := "squ", iso := "squ", value := .cases2 }
  , { walsCode := "sue", iso := "sue", value := .cases4 }
  , { walsCode := "sup", iso := "spp", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "swa", iso := "swh", value := .noMorphologicalCaseMarking }
  , { walsCode := "swe", iso := "swe", value := .cases2 }
  , { walsCode := "tab", iso := "mky", value := .noMorphologicalCaseMarking }
  , { walsCode := "tag", iso := "tgl", value := .noMorphologicalCaseMarking }
  , { walsCode := "tts", iso := "tks", value := .cases2 }
  , { walsCode := "tha", iso := "tha", value := .noMorphologicalCaseMarking }
  , { walsCode := "tin", iso := "cir", value := .noMorphologicalCaseMarking }
  , { walsCode := "tiw", iso := "tiw", value := .noMorphologicalCaseMarking }
  , { walsCode := "tli", iso := "tli", value := .cases8_9 }
  , { walsCode := "tda", iso := "tcx", value := .cases10OrMore }
  , { walsCode := "tru", iso := "tpy", value := .cases5 }
  , { walsCode := "tsi", iso := "tsi", value := .noMorphologicalCaseMarking }
  , { walsCode := "tuk", iso := "", value := .noMorphologicalCaseMarking }
  , { walsCode := "tun", iso := "tun", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "tna", iso := "tuv", value := .cases6_7 }
  , { walsCode := "tur", iso := "tur", value := .cases6_7 }
  , { walsCode := "tvl", iso := "tvl", value := .noMorphologicalCaseMarking }
  , { walsCode := "udh", iso := "ude", value := .cases8_9 }
  , { walsCode := "udm", iso := "udm", value := .cases10OrMore }
  , { walsCode := "una", iso := "mtg", value := .noMorphologicalCaseMarking }
  , { walsCode := "ung", iso := "ung", value := .cases8_9 }
  , { walsCode := "urd", iso := "urd", value := .cases2 }
  , { walsCode := "urk", iso := "urb", value := .noMorphologicalCaseMarking }
  , { walsCode := "usa", iso := "wnu", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "vie", iso := "vie", value := .noMorphologicalCaseMarking }
  , { walsCode := "wam", iso := "wmb", value := .cases8_9 }
  , { walsCode := "wra", iso := "wba", value := .cases5 }
  , { walsCode := "wrd", iso := "wrr", value := .cases8_9 }
  , { walsCode := "war", iso := "pav", value := .noMorphologicalCaseMarking }
  , { walsCode := "was", iso := "was", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "wel", iso := "cym", value := .noMorphologicalCaseMarking }
  , { walsCode := "wic", iso := "wic", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "wch", iso := "mzh", value := .noMorphologicalCaseMarking }
  , { walsCode := "win", iso := "wnw", value := .cases4 }
  , { walsCode := "yag", iso := "yad", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "yaq", iso := "yaq", value := .cases2 }
  , { walsCode := "ywl", iso := "yok", value := .cases6_7 }
  , { walsCode := "yid", iso := "yii", value := .cases8_9 }
  , { walsCode := "yim", iso := "yee", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "yor", iso := "yor", value := .noMorphologicalCaseMarking }
  , { walsCode := "yuc", iso := "yuc", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "yko", iso := "yux", value := .cases8_9 }
  , { walsCode := "ypk", iso := "esu", value := .cases6_7 }
  , { walsCode := "yur", iso := "yur", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "zqc", iso := "zoc", value := .cases2 }
  , { walsCode := "zul", iso := "zul", value := .noMorphologicalCaseMarking }
  , { walsCode := "zun", iso := "zun", value := .noMorphologicalCaseMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F49A
