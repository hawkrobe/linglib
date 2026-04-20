import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 113A: Symmetric and Asymmetric Standard Negation
@cite{miestamo-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 113A`.

Chapter 113, 297 languages.
-/

namespace Core.WALS.F113A

/-- WALS 113A values. -/
inductive NegationSymmetry where
  /-- Symmetric (114 languages). -/
  | symmetric
  /-- Asymmetric (53 languages). -/
  | asymmetric
  /-- Both (130 languages). -/
  | both
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 113A dataset (297 languages). -/
def allData : List (Datapoint NegationSymmetry) :=
  [ { walsCode := "abi", iso := "axb", value := .both }
  , { walsCode := "abk", iso := "abk", value := .both }
  , { walsCode := "acm", iso := "acv", value := .asymmetric }
  , { walsCode := "aco", iso := "kjq", value := .both }
  , { walsCode := "ain", iso := "ain", value := .symmetric }
  , { walsCode := "ala", iso := "amp", value := .both }
  , { walsCode := "alb", iso := "sqi", value := .symmetric }
  , { walsCode := "ame", iso := "aey", value := .both }
  , { walsCode := "adk", iso := "ano", value := .symmetric }
  , { walsCode := "apl", iso := "apy", value := .asymmetric }
  , { walsCode := "apu", iso := "apu", value := .symmetric }
  , { walsCode := "aeg", iso := "arz", value := .symmetric }
  , { walsCode := "ana", iso := "aro", value := .asymmetric }
  , { walsCode := "arp", iso := "ape", value := .both }
  , { walsCode := "arm", iso := "hye", value := .both }
  , { walsCode := "asm", iso := "cns", value := .both }
  , { walsCode := "awp", iso := "kwi", value := .both }
  , { walsCode := "aym", iso := "ayr", value := .asymmetric }
  , { walsCode := "baf", iso := "bfd", value := .both }
  , { walsCode := "bag", iso := "bmi", value := .both }
  , { walsCode := "bam", iso := "bam", value := .both }
  , { walsCode := "brs", iso := "bsn", value := .symmetric }
  , { walsCode := "bae", iso := "bae", value := .asymmetric }
  , { walsCode := "bsq", iso := "eus", value := .asymmetric }
  , { walsCode := "bkr", iso := "btx", value := .symmetric }
  , { walsCode := "baw", iso := "bgr", value := .both }
  , { walsCode := "bej", iso := "bej", value := .both }
  , { walsCode := "bco", iso := "blc", value := .both }
  , { walsCode := "bma", iso := "tzm", value := .asymmetric }
  , { walsCode := "bir", iso := "bom", value := .symmetric }
  , { walsCode := "bok", iso := "bqc", value := .both }
  , { walsCode := "brr", iso := "bor", value := .both }
  , { walsCode := "brh", iso := "brh", value := .both }
  , { walsCode := "bua", iso := "bvr", value := .both }
  , { walsCode := "brm", iso := "mya", value := .asymmetric }
  , { walsCode := "bur", iso := "bsk", value := .symmetric }
  , { walsCode := "cnm", iso := "knm", value := .symmetric }
  , { walsCode := "can", iso := "cbu", value := .both }
  , { walsCode := "cnl", iso := "ram", value := .symmetric }
  , { walsCode := "cnt", iso := "yue", value := .both }
  , { walsCode := "car", iso := "car", value := .asymmetric }
  , { walsCode := "cyv", iso := "cyb", value := .symmetric }
  , { walsCode := "cha", iso := "cha", value := .symmetric }
  , { walsCode := "chl", iso := "cjh", value := .both }
  , { walsCode := "cle", iso := "cle", value := .symmetric }
  , { walsCode := "ckl", iso := "chh", value := .symmetric }
  , { walsCode := "crt", iso := "", value := .symmetric }
  , { walsCode := "chk", iso := "ckt", value := .both }
  , { walsCode := "cba", iso := "boi", value := .symmetric }
  , { walsCode := "cmn", iso := "com", value := .both }
  , { walsCode := "coo", iso := "csz", value := .symmetric }
  , { walsCode := "cre", iso := "crk", value := .symmetric }
  , { walsCode := "cui", iso := "cui", value := .both }
  , { walsCode := "dag", iso := "dgz", value := .symmetric }
  , { walsCode := "dni", iso := "dni", value := .both }
  , { walsCode := "deg", iso := "deg", value := .asymmetric }
  , { walsCode := "dio", iso := "dyo", value := .both }
  , { walsCode := "dre", iso := "dhv", value := .symmetric }
  , { walsCode := "duk", iso := "dud", value := .asymmetric }
  , { walsCode := "dum", iso := "vam", value := .symmetric }
  , { walsCode := "ebi", iso := "igb", value := .asymmetric }
  , { walsCode := "eng", iso := "eng", value := .both }
  , { walsCode := "epe", iso := "sja", value := .asymmetric }
  , { walsCode := "eve", iso := "evn", value := .asymmetric }
  , { walsCode := "ewe", iso := "ewe", value := .both }
  , { walsCode := "fij", iso := "fij", value := .asymmetric }
  , { walsCode := "fin", iso := "fin", value := .asymmetric }
  , { walsCode := "fre", iso := "fra", value := .symmetric }
  , { walsCode := "fur", iso := "fvr", value := .symmetric }
  , { walsCode := "gar", iso := "grt", value := .both }
  , { walsCode := "grr", iso := "wrk", value := .symmetric }
  , { walsCode := "gbb", iso := "gbp", value := .both }
  , { walsCode := "geo", iso := "kat", value := .symmetric }
  , { walsCode := "ger", iso := "deu", value := .symmetric }
  , { walsCode := "god", iso := "gdo", value := .both }
  , { walsCode := "gol", iso := "gol", value := .both }
  , { walsCode := "goo", iso := "gni", value := .symmetric }
  , { walsCode := "grb", iso := "grj", value := .asymmetric }
  , { walsCode := "grk", iso := "ell", value := .symmetric }
  , { walsCode := "grw", iso := "kal", value := .asymmetric }
  , { walsCode := "gua", iso := "gug", value := .both }
  , { walsCode := "gnn", iso := "gww", value := .symmetric }
  , { walsCode := "gku", iso := "pue", value := .symmetric }
  , { walsCode := "hai", iso := "hai", value := .symmetric }
  , { walsCode := "hcr", iso := "hat", value := .both }
  , { walsCode := "hlu", iso := "hur", value := .asymmetric }
  , { walsCode := "ham", iso := "hmt", value := .asymmetric }
  , { walsCode := "har", iso := "tmd", value := .both }
  , { walsCode := "hau", iso := "hau", value := .both }
  , { walsCode := "heb", iso := "heb", value := .both }
  , { walsCode := "hin", iso := "hin", value := .both }
  , { walsCode := "hix", iso := "hix", value := .asymmetric }
  , { walsCode := "hmo", iso := "hnj", value := .symmetric }
  , { walsCode := "hve", iso := "huv", value := .both }
  , { walsCode := "hui", iso := "hch", value := .symmetric }
  , { walsCode := "hun", iso := "hun", value := .symmetric }
  , { walsCode := "hzb", iso := "huz", value := .both }
  , { walsCode := "ice", iso := "isl", value := .symmetric }
  , { walsCode := "igb", iso := "ibo", value := .asymmetric }
  , { walsCode := "ige", iso := "ige", value := .both }
  , { walsCode := "ijo", iso := "ijc", value := .both }
  , { walsCode := "ika", iso := "arh", value := .asymmetric }
  , { walsCode := "imo", iso := "imn", value := .both }
  , { walsCode := "ina", iso := "szp", value := .both }
  , { walsCode := "ind", iso := "ind", value := .symmetric }
  , { walsCode := "ing", iso := "inh", value := .symmetric }
  , { walsCode := "irq", iso := "irk", value := .asymmetric }
  , { walsCode := "iri", iso := "gle", value := .both }
  , { walsCode := "ita", iso := "ita", value := .symmetric }
  , { walsCode := "jak", iso := "jac", value := .both }
  , { walsCode := "jpn", iso := "jpn", value := .asymmetric }
  , { walsCode := "jaq", iso := "jqr", value := .asymmetric }
  , { walsCode := "jeb", iso := "jeb", value := .symmetric }
  , { walsCode := "juh", iso := "ktz", value := .symmetric }
  , { walsCode := "kab", iso := "kbd", value := .both }
  , { walsCode := "kae", iso := "tbd", value := .both }
  , { walsCode := "knd", iso := "kan", value := .asymmetric }
  , { walsCode := "knr", iso := "knc", value := .both }
  , { walsCode := "krk", iso := "kyh", value := .asymmetric }
  , { walsCode := "kyl", iso := "eky", value := .both }
  , { walsCode := "kay", iso := "gyd", value := .both }
  , { walsCode := "kem", iso := "ahg", value := .asymmetric }
  , { walsCode := "ker", iso := "ker", value := .both }
  , { walsCode := "ket", iso := "ket", value := .symmetric }
  , { walsCode := "kew", iso := "kew", value := .symmetric }
  , { walsCode := "kha", iso := "khk", value := .both }
  , { walsCode := "khr", iso := "khr", value := .asymmetric }
  , { walsCode := "khs", iso := "kha", value := .both }
  , { walsCode := "khm", iso := "khm", value := .symmetric }
  , { walsCode := "kmu", iso := "kjg", value := .symmetric }
  , { walsCode := "klv", iso := "kij", value := .symmetric }
  , { walsCode := "kio", iso := "kio", value := .both }
  , { walsCode := "klm", iso := "kla", value := .symmetric }
  , { walsCode := "koa", iso := "cku", value := .both }
  , { walsCode := "kob", iso := "kpw", value := .symmetric }
  , { walsCode := "koi", iso := "kbk", value := .both }
  , { walsCode := "kon", iso := "kng", value := .symmetric }
  , { walsCode := "kor", iso := "kor", value := .both }
  , { walsCode := "kfe", iso := "kfz", value := .symmetric }
  , { walsCode := "kse", iso := "ses", value := .both }
  , { walsCode := "kre", iso := "krs", value := .both }
  , { walsCode := "kro", iso := "kgo", value := .both }
  , { walsCode := "kun", iso := "kvn", value := .symmetric }
  , { walsCode := "knm", iso := "kun", value := .both }
  , { walsCode := "kut", iso := "kut", value := .symmetric }
  , { walsCode := "kwz", iso := "xwa", value := .symmetric }
  , { walsCode := "lad", iso := "lbj", value := .both }
  , { walsCode := "lah", iso := "lhu", value := .both }
  , { walsCode := "lkt", iso := "lkt", value := .symmetric }
  , { walsCode := "lan", iso := "laj", value := .symmetric }
  , { walsCode := "lar", iso := "lrg", value := .both }
  , { walsCode := "lat", iso := "lav", value := .both }
  , { walsCode := "lav", iso := "lvk", value := .both }
  , { walsCode := "lew", iso := "lww", value := .asymmetric }
  , { walsCode := "lez", iso := "lez", value := .both }
  , { walsCode := "lug", iso := "lgg", value := .both }
  , { walsCode := "luv", iso := "lue", value := .both }
  , { walsCode := "maa", iso := "mas", value := .both }
  , { walsCode := "mab", iso := "mde", value := .both }
  , { walsCode := "mne", iso := "nmu", value := .symmetric }
  , { walsCode := "mak", iso := "myh", value := .asymmetric }
  , { walsCode := "mal", iso := "plt", value := .symmetric }
  , { walsCode := "mym", iso := "mal", value := .both }
  , { walsCode := "mam", iso := "mam", value := .both }
  , { walsCode := "mnd", iso := "cmn", value := .both }
  , { walsCode := "myi", iso := "mpc", value := .both }
  , { walsCode := "mns", iso := "mns", value := .symmetric }
  , { walsCode := "mao", iso := "mri", value := .asymmetric }
  , { walsCode := "map", iso := "arn", value := .symmetric }
  , { walsCode := "mku", iso := "zmr", value := .symmetric }
  , { walsCode := "mar", iso := "mrc", value := .symmetric }
  , { walsCode := "mrt", iso := "vma", value := .symmetric }
  , { walsCode := "mas", iso := "mcn", value := .symmetric }
  , { walsCode := "mau", iso := "mph", value := .both }
  , { walsCode := "may", iso := "ayz", value := .symmetric }
  , { walsCode := "mei", iso := "mni", value := .both }
  , { walsCode := "mss", iso := "skd", value := .symmetric }
  , { walsCode := "mxc", iso := "mig", value := .symmetric }
  , { walsCode := "miy", iso := "mkf", value := .both }
  , { walsCode := "mos", iso := "cas", value := .symmetric }
  , { walsCode := "mun", iso := "unr", value := .symmetric }
  , { walsCode := "mrl", iso := "mur", value := .symmetric }
  , { walsCode := "nad", iso := "mbj", value := .asymmetric }
  , { walsCode := "nah", iso := "nll", value := .asymmetric }
  , { walsCode := "nht", iso := "nhg", value := .symmetric }
  , { walsCode := "kho", iso := "naq", value := .both }
  , { walsCode := "nas", iso := "nas", value := .both }
  , { walsCode := "nav", iso := "nav", value := .asymmetric }
  , { walsCode := "ndy", iso := "djk", value := .symmetric }
  , { walsCode := "ntu", iso := "yrk", value := .asymmetric }
  , { walsCode := "nez", iso := "nez", value := .symmetric }
  , { walsCode := "nti", iso := "niy", value := .symmetric }
  , { walsCode := "ngi", iso := "wyb", value := .symmetric }
  , { walsCode := "nca", iso := "caq", value := .symmetric }
  , { walsCode := "niv", iso := "niv", value := .both }
  , { walsCode := "nko", iso := "cgg", value := .both }
  , { walsCode := "nbd", iso := "dgl", value := .asymmetric }
  , { walsCode := "nug", iso := "nuy", value := .both }
  , { walsCode := "nyu", iso := "nyv", value := .both }
  , { walsCode := "obg", iso := "ogu", value := .asymmetric }
  , { walsCode := "ond", iso := "one", value := .both }
  , { walsCode := "ono", iso := "ons", value := .symmetric }
  , { walsCode := "orh", iso := "hae", value := .both }
  , { walsCode := "otm", iso := "ote", value := .both }
  , { walsCode := "pms", iso := "pma", value := .both }
  , { walsCode := "pai", iso := "pwn", value := .both }
  , { walsCode := "psm", iso := "pqm", value := .both }
  , { walsCode := "pau", iso := "pad", value := .symmetric }
  , { walsCode := "pec", iso := "pay", value := .both }
  , { walsCode := "prs", iso := "pes", value := .symmetric }
  , { walsCode := "pba", iso := "pia", value := .symmetric }
  , { walsCode := "prh", iso := "myp", value := .symmetric }
  , { walsCode := "pit", iso := "pjt", value := .both }
  , { walsCode := "pso", iso := "pom", value := .both }
  , { walsCode := "psj", iso := "poe", value := .symmetric }
  , { walsCode := "pur", iso := "tsz", value := .symmetric }
  , { walsCode := "pae", iso := "pbb", value := .both }
  , { walsCode := "qaw", iso := "alc", value := .symmetric }
  , { walsCode := "qim", iso := "qvi", value := .both }
  , { walsCode := "qui", iso := "qui", value := .asymmetric }
  , { walsCode := "ram", iso := "rma", value := .both }
  , { walsCode := "rap", iso := "rap", value := .both }
  , { walsCode := "rus", iso := "rus", value := .symmetric }
  , { walsCode := "san", iso := "sag", value := .symmetric }
  , { walsCode := "snm", iso := "xsu", value := .both }
  , { walsCode := "sap", iso := "spu", value := .symmetric }
  , { walsCode := "saw", iso := "hvn", value := .symmetric }
  , { walsCode := "see", iso := "trv", value := .both }
  , { walsCode := "sel", iso := "ona", value := .asymmetric }
  , { walsCode := "sml", iso := "sza", value := .both }
  , { walsCode := "snt", iso := "set", value := .asymmetric }
  , { walsCode := "shk", iso := "shp", value := .symmetric }
  , { walsCode := "shu", iso := "shs", value := .asymmetric }
  , { walsCode := "siu", iso := "sis", value := .symmetric }
  , { walsCode := "sla", iso := "den", value := .symmetric }
  , { walsCode := "so", iso := "teu", value := .both }
  , { walsCode := "som", iso := "som", value := .asymmetric }
  , { walsCode := "spa", iso := "spa", value := .symmetric }
  , { walsCode := "squ", iso := "squ", value := .asymmetric }
  , { walsCode := "sue", iso := "sue", value := .both }
  , { walsCode := "sup", iso := "spp", value := .both }
  , { walsCode := "swa", iso := "swh", value := .both }
  , { walsCode := "tab", iso := "mky", value := .symmetric }
  , { walsCode := "tag", iso := "tgl", value := .symmetric }
  , { walsCode := "tkl", iso := "tkm", value := .both }
  , { walsCode := "tau", iso := "tya", value := .symmetric }
  , { walsCode := "ter", iso := "ttr", value := .both }
  , { walsCode := "tha", iso := "tha", value := .symmetric }
  , { walsCode := "tib", iso := "bod", value := .both }
  , { walsCode := "tiw", iso := "tiw", value := .both }
  , { walsCode := "tli", iso := "tli", value := .both }
  , { walsCode := "tol", iso := "jic", value := .symmetric }
  , { walsCode := "tms", iso := "dto", value := .asymmetric }
  , { walsCode := "ton", iso := "tqw", value := .symmetric }
  , { walsCode := "tpa", iso := "top", value := .symmetric }
  , { walsCode := "tru", iso := "tpy", value := .both }
  , { walsCode := "tsi", iso := "tsi", value := .both }
  , { walsCode := "tuk", iso := "", value := .symmetric }
  , { walsCode := "tun", iso := "tun", value := .both }
  , { walsCode := "tur", iso := "tur", value := .both }
  , { walsCode := "tuy", iso := "tue", value := .symmetric }
  , { walsCode := "ukr", iso := "ukr", value := .symmetric }
  , { walsCode := "una", iso := "mtg", value := .symmetric }
  , { walsCode := "ung", iso := "ung", value := .both }
  , { walsCode := "urk", iso := "urb", value := .symmetric }
  , { walsCode := "usa", iso := "wnu", value := .both }
  , { walsCode := "uzb", iso := "", value := .both }
  , { walsCode := "vie", iso := "vie", value := .symmetric }
  , { walsCode := "wam", iso := "wmb", value := .both }
  , { walsCode := "wao", iso := "auc", value := .both }
  , { walsCode := "wra", iso := "wba", value := .asymmetric }
  , { walsCode := "wrd", iso := "wrr", value := .symmetric }
  , { walsCode := "wrm", iso := "wsa", value := .symmetric }
  , { walsCode := "war", iso := "pav", value := .asymmetric }
  , { walsCode := "wrn", iso := "wnd", value := .asymmetric }
  , { walsCode := "was", iso := "was", value := .symmetric }
  , { walsCode := "way", iso := "oym", value := .both }
  , { walsCode := "wic", iso := "wic", value := .both }
  , { walsCode := "wch", iso := "mzh", value := .both }
  , { walsCode := "win", iso := "wnw", value := .asymmetric }
  , { walsCode := "wiy", iso := "wiy", value := .both }
  , { walsCode := "yag", iso := "yad", value := .symmetric }
  , { walsCode := "yaq", iso := "yaq", value := .symmetric }
  , { walsCode := "yar", iso := "yrb", value := .both }
  , { walsCode := "yrr", iso := "yae", value := .symmetric }
  , { walsCode := "ywl", iso := "yok", value := .symmetric }
  , { walsCode := "yid", iso := "yii", value := .symmetric }
  , { walsCode := "yim", iso := "yee", value := .asymmetric }
  , { walsCode := "yor", iso := "yor", value := .both }
  , { walsCode := "yuc", iso := "yuc", value := .symmetric }
  , { walsCode := "yko", iso := "yux", value := .both }
  , { walsCode := "yus", iso := "ess", value := .both }
  , { walsCode := "yur", iso := "yur", value := .both }
  , { walsCode := "zap", iso := "zaw", value := .asymmetric }
  , { walsCode := "zaz", iso := "diq", value := .symmetric }
  , { walsCode := "zqc", iso := "zoc", value := .asymmetric }
  , { walsCode := "zul", iso := "zul", value := .both }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F113A
