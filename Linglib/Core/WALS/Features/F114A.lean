import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 114A: Subtypes of Asymmetric Standard Negation
@cite{miestamo-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 114A`.

Chapter 114, 297 languages.
-/

namespace Core.WALS.F114A

/-- WALS 114A values. -/
inductive AsymmetricNegationSubtype where
  /-- A/Fin (40 languages). -/
  | aFin
  /-- A/NonReal (20 languages). -/
  | aNonreal
  /-- A/Cat (82 languages). -/
  | aCat
  /-- A/Fin and A/NonReal (9 languages). -/
  | aFinAndANonreal
  /-- A/Fin and A/Cat (21 languages). -/
  | aFinAndACat
  /-- A/NonReal and A/Cat (11 languages). -/
  | aNonrealAndACat
  /-- Non-assignable (114 languages). -/
  | nonAssignable
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 114A dataset (297 languages). -/
def allData : List (Datapoint AsymmetricNegationSubtype) :=
  [ { walsCode := "abi", iso := "axb", value := .aCat }
  , { walsCode := "abk", iso := "abk", value := .aCat }
  , { walsCode := "acm", iso := "acv", value := .aFin }
  , { walsCode := "aco", iso := "kjq", value := .aCat }
  , { walsCode := "ain", iso := "ain", value := .nonAssignable }
  , { walsCode := "ala", iso := "amp", value := .aNonreal }
  , { walsCode := "alb", iso := "sqi", value := .nonAssignable }
  , { walsCode := "ame", iso := "aey", value := .aCat }
  , { walsCode := "adk", iso := "ano", value := .nonAssignable }
  , { walsCode := "apl", iso := "apy", value := .aFin }
  , { walsCode := "apu", iso := "apu", value := .nonAssignable }
  , { walsCode := "aeg", iso := "arz", value := .nonAssignable }
  , { walsCode := "ana", iso := "aro", value := .aFin }
  , { walsCode := "arp", iso := "ape", value := .aNonreal }
  , { walsCode := "arm", iso := "hye", value := .aFin }
  , { walsCode := "asm", iso := "cns", value := .aNonreal }
  , { walsCode := "awp", iso := "kwi", value := .aFinAndACat }
  , { walsCode := "aym", iso := "ayr", value := .aNonreal }
  , { walsCode := "baf", iso := "bfd", value := .aCat }
  , { walsCode := "bag", iso := "bmi", value := .aCat }
  , { walsCode := "bam", iso := "bam", value := .aCat }
  , { walsCode := "brs", iso := "bsn", value := .nonAssignable }
  , { walsCode := "bae", iso := "bae", value := .aFin }
  , { walsCode := "bsq", iso := "eus", value := .aCat }
  , { walsCode := "bkr", iso := "btx", value := .nonAssignable }
  , { walsCode := "baw", iso := "bgr", value := .aCat }
  , { walsCode := "bej", iso := "bej", value := .aFinAndACat }
  , { walsCode := "bco", iso := "blc", value := .aCat }
  , { walsCode := "bma", iso := "tzm", value := .aFinAndACat }
  , { walsCode := "bir", iso := "bom", value := .nonAssignable }
  , { walsCode := "bok", iso := "bqc", value := .aCat }
  , { walsCode := "brr", iso := "bor", value := .aCat }
  , { walsCode := "brh", iso := "brh", value := .aCat }
  , { walsCode := "bua", iso := "bvr", value := .aNonreal }
  , { walsCode := "brm", iso := "mya", value := .aCat }
  , { walsCode := "bur", iso := "bsk", value := .nonAssignable }
  , { walsCode := "cnm", iso := "knm", value := .nonAssignable }
  , { walsCode := "can", iso := "cbu", value := .aCat }
  , { walsCode := "cnl", iso := "ram", value := .nonAssignable }
  , { walsCode := "cnt", iso := "yue", value := .aCat }
  , { walsCode := "car", iso := "car", value := .aFin }
  , { walsCode := "cyv", iso := "cyb", value := .nonAssignable }
  , { walsCode := "cha", iso := "cha", value := .nonAssignable }
  , { walsCode := "chl", iso := "cjh", value := .aFinAndACat }
  , { walsCode := "cle", iso := "cle", value := .nonAssignable }
  , { walsCode := "ckl", iso := "chh", value := .nonAssignable }
  , { walsCode := "crt", iso := "", value := .nonAssignable }
  , { walsCode := "chk", iso := "ckt", value := .aFinAndANonreal }
  , { walsCode := "cba", iso := "boi", value := .nonAssignable }
  , { walsCode := "cmn", iso := "com", value := .aCat }
  , { walsCode := "coo", iso := "csz", value := .nonAssignable }
  , { walsCode := "cre", iso := "crk", value := .nonAssignable }
  , { walsCode := "cui", iso := "cui", value := .aNonrealAndACat }
  , { walsCode := "dag", iso := "dgz", value := .nonAssignable }
  , { walsCode := "dni", iso := "dni", value := .aFin }
  , { walsCode := "deg", iso := "deg", value := .aCat }
  , { walsCode := "dio", iso := "dyo", value := .aCat }
  , { walsCode := "dre", iso := "dhv", value := .nonAssignable }
  , { walsCode := "duk", iso := "dud", value := .aNonrealAndACat }
  , { walsCode := "dum", iso := "vam", value := .nonAssignable }
  , { walsCode := "ebi", iso := "igb", value := .aCat }
  , { walsCode := "eng", iso := "eng", value := .aCat }
  , { walsCode := "epe", iso := "sja", value := .aFinAndACat }
  , { walsCode := "eve", iso := "evn", value := .aFin }
  , { walsCode := "ewe", iso := "ewe", value := .aCat }
  , { walsCode := "fij", iso := "fij", value := .aFin }
  , { walsCode := "fin", iso := "fin", value := .aFin }
  , { walsCode := "fre", iso := "fra", value := .nonAssignable }
  , { walsCode := "fur", iso := "fvr", value := .nonAssignable }
  , { walsCode := "gar", iso := "grt", value := .aCat }
  , { walsCode := "grr", iso := "wrk", value := .nonAssignable }
  , { walsCode := "gbb", iso := "gbp", value := .aFin }
  , { walsCode := "geo", iso := "kat", value := .nonAssignable }
  , { walsCode := "ger", iso := "deu", value := .nonAssignable }
  , { walsCode := "god", iso := "gdo", value := .aCat }
  , { walsCode := "gol", iso := "gol", value := .aCat }
  , { walsCode := "goo", iso := "gni", value := .nonAssignable }
  , { walsCode := "grb", iso := "grj", value := .aNonrealAndACat }
  , { walsCode := "grk", iso := "ell", value := .nonAssignable }
  , { walsCode := "grw", iso := "kal", value := .aCat }
  , { walsCode := "gua", iso := "gug", value := .aCat }
  , { walsCode := "gnn", iso := "gww", value := .nonAssignable }
  , { walsCode := "gku", iso := "pue", value := .nonAssignable }
  , { walsCode := "hai", iso := "hai", value := .nonAssignable }
  , { walsCode := "hcr", iso := "hat", value := .aCat }
  , { walsCode := "hlu", iso := "hur", value := .aFinAndANonreal }
  , { walsCode := "ham", iso := "hmt", value := .aFin }
  , { walsCode := "har", iso := "tmd", value := .aNonreal }
  , { walsCode := "hau", iso := "hau", value := .aCat }
  , { walsCode := "heb", iso := "heb", value := .aFin }
  , { walsCode := "hin", iso := "hin", value := .aCat }
  , { walsCode := "hix", iso := "hix", value := .aFin }
  , { walsCode := "hmo", iso := "hnj", value := .nonAssignable }
  , { walsCode := "hve", iso := "huv", value := .aFin }
  , { walsCode := "hui", iso := "hch", value := .nonAssignable }
  , { walsCode := "hun", iso := "hun", value := .nonAssignable }
  , { walsCode := "hzb", iso := "huz", value := .aCat }
  , { walsCode := "ice", iso := "isl", value := .nonAssignable }
  , { walsCode := "igb", iso := "ibo", value := .aCat }
  , { walsCode := "ige", iso := "ige", value := .aNonreal }
  , { walsCode := "ijo", iso := "ijc", value := .aFinAndACat }
  , { walsCode := "ika", iso := "arh", value := .aFin }
  , { walsCode := "imo", iso := "imn", value := .aFinAndANonreal }
  , { walsCode := "ina", iso := "szp", value := .aFin }
  , { walsCode := "ind", iso := "ind", value := .nonAssignable }
  , { walsCode := "ing", iso := "inh", value := .nonAssignable }
  , { walsCode := "irq", iso := "irk", value := .aFin }
  , { walsCode := "iri", iso := "gle", value := .aCat }
  , { walsCode := "ita", iso := "ita", value := .nonAssignable }
  , { walsCode := "jak", iso := "jac", value := .aNonreal }
  , { walsCode := "jpn", iso := "jpn", value := .aFinAndACat }
  , { walsCode := "jaq", iso := "jqr", value := .aNonreal }
  , { walsCode := "jeb", iso := "jeb", value := .nonAssignable }
  , { walsCode := "juh", iso := "ktz", value := .nonAssignable }
  , { walsCode := "kab", iso := "kbd", value := .aNonrealAndACat }
  , { walsCode := "kae", iso := "tbd", value := .aNonrealAndACat }
  , { walsCode := "knd", iso := "kan", value := .aFinAndACat }
  , { walsCode := "knr", iso := "knc", value := .aCat }
  , { walsCode := "krk", iso := "kyh", value := .aCat }
  , { walsCode := "kyl", iso := "eky", value := .aCat }
  , { walsCode := "kay", iso := "gyd", value := .aFinAndACat }
  , { walsCode := "kem", iso := "ahg", value := .aCat }
  , { walsCode := "ker", iso := "ker", value := .aCat }
  , { walsCode := "ket", iso := "ket", value := .nonAssignable }
  , { walsCode := "kew", iso := "kew", value := .nonAssignable }
  , { walsCode := "kha", iso := "khk", value := .aFin }
  , { walsCode := "khr", iso := "khr", value := .aFin }
  , { walsCode := "khs", iso := "kha", value := .aCat }
  , { walsCode := "khm", iso := "khm", value := .nonAssignable }
  , { walsCode := "kmu", iso := "kjg", value := .nonAssignable }
  , { walsCode := "klv", iso := "kij", value := .nonAssignable }
  , { walsCode := "kio", iso := "kio", value := .aCat }
  , { walsCode := "klm", iso := "kla", value := .nonAssignable }
  , { walsCode := "koa", iso := "cku", value := .aCat }
  , { walsCode := "kob", iso := "kpw", value := .nonAssignable }
  , { walsCode := "koi", iso := "kbk", value := .aCat }
  , { walsCode := "kon", iso := "kng", value := .nonAssignable }
  , { walsCode := "kor", iso := "kor", value := .aFinAndANonreal }
  , { walsCode := "kfe", iso := "kfz", value := .nonAssignable }
  , { walsCode := "kse", iso := "ses", value := .aCat }
  , { walsCode := "kre", iso := "krs", value := .aCat }
  , { walsCode := "kro", iso := "kgo", value := .aFin }
  , { walsCode := "kun", iso := "kvn", value := .nonAssignable }
  , { walsCode := "knm", iso := "kun", value := .aCat }
  , { walsCode := "kut", iso := "kut", value := .nonAssignable }
  , { walsCode := "kwz", iso := "xwa", value := .nonAssignable }
  , { walsCode := "lad", iso := "lbj", value := .aCat }
  , { walsCode := "lah", iso := "lhu", value := .aCat }
  , { walsCode := "lkt", iso := "lkt", value := .nonAssignable }
  , { walsCode := "lan", iso := "laj", value := .nonAssignable }
  , { walsCode := "lar", iso := "lrg", value := .aNonreal }
  , { walsCode := "lat", iso := "lav", value := .aCat }
  , { walsCode := "lav", iso := "lvk", value := .aFinAndACat }
  , { walsCode := "lew", iso := "lww", value := .aFin }
  , { walsCode := "lez", iso := "lez", value := .aCat }
  , { walsCode := "lug", iso := "lgg", value := .aCat }
  , { walsCode := "luv", iso := "lue", value := .aFinAndACat }
  , { walsCode := "maa", iso := "mas", value := .aFin }
  , { walsCode := "mab", iso := "mde", value := .aCat }
  , { walsCode := "mne", iso := "nmu", value := .nonAssignable }
  , { walsCode := "mak", iso := "myh", value := .aFin }
  , { walsCode := "mal", iso := "plt", value := .nonAssignable }
  , { walsCode := "mym", iso := "mal", value := .aFinAndACat }
  , { walsCode := "mam", iso := "mam", value := .aFinAndACat }
  , { walsCode := "mnd", iso := "cmn", value := .aFin }
  , { walsCode := "myi", iso := "mpc", value := .aNonrealAndACat }
  , { walsCode := "mns", iso := "mns", value := .nonAssignable }
  , { walsCode := "mao", iso := "mri", value := .aFin }
  , { walsCode := "map", iso := "arn", value := .nonAssignable }
  , { walsCode := "mku", iso := "zmr", value := .nonAssignable }
  , { walsCode := "mar", iso := "mrc", value := .nonAssignable }
  , { walsCode := "mrt", iso := "vma", value := .nonAssignable }
  , { walsCode := "mas", iso := "mcn", value := .nonAssignable }
  , { walsCode := "mau", iso := "mph", value := .aNonreal }
  , { walsCode := "may", iso := "ayz", value := .nonAssignable }
  , { walsCode := "mei", iso := "mni", value := .aFinAndACat }
  , { walsCode := "mss", iso := "skd", value := .nonAssignable }
  , { walsCode := "mxc", iso := "mig", value := .nonAssignable }
  , { walsCode := "miy", iso := "mkf", value := .aCat }
  , { walsCode := "mos", iso := "cas", value := .nonAssignable }
  , { walsCode := "mun", iso := "unr", value := .nonAssignable }
  , { walsCode := "mrl", iso := "mur", value := .nonAssignable }
  , { walsCode := "nad", iso := "mbj", value := .aFin }
  , { walsCode := "nah", iso := "nll", value := .aFin }
  , { walsCode := "nht", iso := "nhg", value := .nonAssignable }
  , { walsCode := "kho", iso := "naq", value := .aFinAndACat }
  , { walsCode := "nas", iso := "nas", value := .aCat }
  , { walsCode := "nav", iso := "nav", value := .aCat }
  , { walsCode := "ndy", iso := "djk", value := .nonAssignable }
  , { walsCode := "ntu", iso := "yrk", value := .aFin }
  , { walsCode := "nez", iso := "nez", value := .nonAssignable }
  , { walsCode := "nti", iso := "niy", value := .nonAssignable }
  , { walsCode := "ngi", iso := "wyb", value := .nonAssignable }
  , { walsCode := "nca", iso := "caq", value := .nonAssignable }
  , { walsCode := "niv", iso := "niv", value := .aFinAndANonreal }
  , { walsCode := "nko", iso := "cgg", value := .aCat }
  , { walsCode := "nbd", iso := "dgl", value := .aFin }
  , { walsCode := "nug", iso := "nuy", value := .aNonrealAndACat }
  , { walsCode := "nyu", iso := "nyv", value := .aNonreal }
  , { walsCode := "obg", iso := "ogu", value := .aCat }
  , { walsCode := "ond", iso := "one", value := .aCat }
  , { walsCode := "ono", iso := "ons", value := .nonAssignable }
  , { walsCode := "orh", iso := "hae", value := .aFinAndACat }
  , { walsCode := "otm", iso := "ote", value := .aCat }
  , { walsCode := "pms", iso := "pma", value := .aCat }
  , { walsCode := "pai", iso := "pwn", value := .aCat }
  , { walsCode := "psm", iso := "pqm", value := .aCat }
  , { walsCode := "pau", iso := "pad", value := .nonAssignable }
  , { walsCode := "pec", iso := "pay", value := .aCat }
  , { walsCode := "prs", iso := "pes", value := .nonAssignable }
  , { walsCode := "pba", iso := "pia", value := .nonAssignable }
  , { walsCode := "prh", iso := "myp", value := .nonAssignable }
  , { walsCode := "pit", iso := "pjt", value := .aFin }
  , { walsCode := "pso", iso := "pom", value := .aCat }
  , { walsCode := "psj", iso := "poe", value := .nonAssignable }
  , { walsCode := "pur", iso := "tsz", value := .nonAssignable }
  , { walsCode := "pae", iso := "pbb", value := .aCat }
  , { walsCode := "qaw", iso := "alc", value := .nonAssignable }
  , { walsCode := "qim", iso := "qvi", value := .aNonreal }
  , { walsCode := "qui", iso := "qui", value := .aFin }
  , { walsCode := "ram", iso := "rma", value := .aFinAndACat }
  , { walsCode := "rap", iso := "rap", value := .aCat }
  , { walsCode := "rus", iso := "rus", value := .nonAssignable }
  , { walsCode := "san", iso := "sag", value := .nonAssignable }
  , { walsCode := "snm", iso := "xsu", value := .aCat }
  , { walsCode := "sap", iso := "spu", value := .nonAssignable }
  , { walsCode := "saw", iso := "hvn", value := .nonAssignable }
  , { walsCode := "see", iso := "trv", value := .aNonreal }
  , { walsCode := "sel", iso := "ona", value := .aFin }
  , { walsCode := "sml", iso := "sza", value := .aCat }
  , { walsCode := "snt", iso := "set", value := .aFin }
  , { walsCode := "shk", iso := "shp", value := .nonAssignable }
  , { walsCode := "shu", iso := "shs", value := .aFinAndANonreal }
  , { walsCode := "siu", iso := "sis", value := .nonAssignable }
  , { walsCode := "sla", iso := "den", value := .nonAssignable }
  , { walsCode := "so", iso := "teu", value := .aCat }
  , { walsCode := "som", iso := "som", value := .aFinAndACat }
  , { walsCode := "spa", iso := "spa", value := .nonAssignable }
  , { walsCode := "squ", iso := "squ", value := .aFinAndANonreal }
  , { walsCode := "sue", iso := "sue", value := .aFin }
  , { walsCode := "sup", iso := "spp", value := .aFinAndACat }
  , { walsCode := "swa", iso := "swh", value := .aCat }
  , { walsCode := "tab", iso := "mky", value := .nonAssignable }
  , { walsCode := "tag", iso := "tgl", value := .nonAssignable }
  , { walsCode := "tkl", iso := "tkm", value := .aNonreal }
  , { walsCode := "tau", iso := "tya", value := .nonAssignable }
  , { walsCode := "ter", iso := "ttr", value := .aCat }
  , { walsCode := "tha", iso := "tha", value := .nonAssignable }
  , { walsCode := "tib", iso := "bod", value := .aCat }
  , { walsCode := "tiw", iso := "tiw", value := .aNonreal }
  , { walsCode := "tli", iso := "tli", value := .aNonrealAndACat }
  , { walsCode := "tol", iso := "jic", value := .nonAssignable }
  , { walsCode := "tms", iso := "dto", value := .aCat }
  , { walsCode := "ton", iso := "tqw", value := .nonAssignable }
  , { walsCode := "tpa", iso := "top", value := .nonAssignable }
  , { walsCode := "tru", iso := "tpy", value := .aCat }
  , { walsCode := "tsi", iso := "tsi", value := .aNonreal }
  , { walsCode := "tuk", iso := "", value := .nonAssignable }
  , { walsCode := "tun", iso := "tun", value := .aCat }
  , { walsCode := "tur", iso := "tur", value := .aCat }
  , { walsCode := "tuy", iso := "tue", value := .nonAssignable }
  , { walsCode := "ukr", iso := "ukr", value := .nonAssignable }
  , { walsCode := "una", iso := "mtg", value := .nonAssignable }
  , { walsCode := "ung", iso := "ung", value := .aNonreal }
  , { walsCode := "urk", iso := "urb", value := .nonAssignable }
  , { walsCode := "usa", iso := "wnu", value := .aFinAndANonreal }
  , { walsCode := "uzb", iso := "", value := .aCat }
  , { walsCode := "vie", iso := "vie", value := .nonAssignable }
  , { walsCode := "wam", iso := "wmb", value := .aNonreal }
  , { walsCode := "wao", iso := "auc", value := .aFin }
  , { walsCode := "wra", iso := "wba", value := .aFin }
  , { walsCode := "wrd", iso := "wrr", value := .nonAssignable }
  , { walsCode := "wrm", iso := "wsa", value := .nonAssignable }
  , { walsCode := "war", iso := "pav", value := .aFin }
  , { walsCode := "wrn", iso := "wnd", value := .aNonrealAndACat }
  , { walsCode := "was", iso := "was", value := .nonAssignable }
  , { walsCode := "way", iso := "oym", value := .aCat }
  , { walsCode := "wic", iso := "wic", value := .aCat }
  , { walsCode := "wch", iso := "mzh", value := .aNonreal }
  , { walsCode := "win", iso := "wnw", value := .aFin }
  , { walsCode := "wiy", iso := "wiy", value := .aFinAndACat }
  , { walsCode := "yag", iso := "yad", value := .nonAssignable }
  , { walsCode := "yaq", iso := "yaq", value := .nonAssignable }
  , { walsCode := "yar", iso := "yrb", value := .aFin }
  , { walsCode := "yrr", iso := "yae", value := .nonAssignable }
  , { walsCode := "ywl", iso := "yok", value := .nonAssignable }
  , { walsCode := "yid", iso := "yii", value := .nonAssignable }
  , { walsCode := "yim", iso := "yee", value := .aFinAndACat }
  , { walsCode := "yor", iso := "yor", value := .aCat }
  , { walsCode := "yuc", iso := "yuc", value := .nonAssignable }
  , { walsCode := "yko", iso := "yux", value := .aCat }
  , { walsCode := "yus", iso := "ess", value := .aCat }
  , { walsCode := "yur", iso := "yur", value := .aNonrealAndACat }
  , { walsCode := "zap", iso := "zaw", value := .aNonrealAndACat }
  , { walsCode := "zaz", iso := "diq", value := .nonAssignable }
  , { walsCode := "zqc", iso := "zoc", value := .aFinAndANonreal }
  , { walsCode := "zul", iso := "zul", value := .aCat }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F114A
