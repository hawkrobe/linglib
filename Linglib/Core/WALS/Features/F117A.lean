import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 117A: Predicative Possession
@cite{stassen-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 117A`.

Chapter 117, 240 languages.
-/

namespace Core.WALS.F117A

/-- WALS 117A values. -/
inductive PredicativePossession where
  /-- Locational (48 languages). -/
  | locational
  /-- Genitive (22 languages). -/
  | genitive
  /-- Topic (48 languages). -/
  | topic
  /-- Conjunctional (59 languages). -/
  | conjunctional
  /-- 'Have' (63 languages). -/
  | have
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 117A dataset (240 languages). -/
def allData : List (Datapoint PredicativePossession) :=
  [ { walsCode := "abk", iso := "abk", value := .have }
  , { walsCode := "ace", iso := "ace", value := .topic }
  , { walsCode := "acl", iso := "ach", value := .conjunctional }
  , { walsCode := "ahu", iso := "ahh", value := .topic }
  , { walsCode := "agl", iso := "agx", value := .locational }
  , { walsCode := "ain", iso := "ain", value := .have }
  , { walsCode := "akn", iso := "aka", value := .topic }
  , { walsCode := "abm", iso := "akz", value := .locational }
  , { walsCode := "ala", iso := "amp", value := .conjunctional }
  , { walsCode := "alb", iso := "sqi", value := .have }
  , { walsCode := "ame", iso := "aey", value := .conjunctional }
  , { walsCode := "amh", iso := "amh", value := .locational }
  , { walsCode := "apl", iso := "apy", value := .conjunctional }
  , { walsCode := "aeg", iso := "arz", value := .locational }
  , { walsCode := "arc", iso := "aqc", value := .genitive }
  , { walsCode := "arm", iso := "hye", value := .genitive }
  , { walsCode := "amp", iso := "aer", value := .locational }
  , { walsCode := "asm", iso := "cns", value := .topic }
  , { walsCode := "ava", iso := "ava", value := .genitive }
  , { walsCode := "awt", iso := "kmn", value := .topic }
  , { walsCode := "bab", iso := "bav", value := .have }
  , { walsCode := "bam", iso := "bam", value := .locational }
  , { walsCode := "bgg", iso := "bgz", value := .topic }
  , { walsCode := "bar", iso := "bfa", value := .conjunctional }
  , { walsCode := "bsq", iso := "eus", value := .have }
  , { walsCode := "bto", iso := "bbc", value := .topic }
  , { walsCode := "bej", iso := "bej", value := .genitive }
  , { walsCode := "ben", iso := "ben", value := .genitive }
  , { walsCode := "bln", iso := "byn", value := .locational }
  , { walsCode := "bir", iso := "bom", value := .have }
  , { walsCode := "brr", iso := "bor", value := .topic }
  , { walsCode := "bre", iso := "bre", value := .locational }
  , { walsCode := "bri", iso := "bzd", value := .conjunctional }
  , { walsCode := "brm", iso := "mya", value := .locational }
  , { walsCode := "bur", iso := "bsk", value := .genitive }
  , { walsCode := "cnl", iso := "ram", value := .locational }
  , { walsCode := "car", iso := "car", value := .conjunctional }
  , { walsCode := "ceb", iso := "ceb", value := .topic }
  , { walsCode := "chc", iso := "che", value := .genitive }
  , { walsCode := "cmh", iso := "ute", value := .have }
  , { walsCode := "cct", iso := "cho", value := .topic }
  , { walsCode := "chk", iso := "ckt", value := .conjunctional }
  , { walsCode := "cil", iso := "lua", value := .conjunctional }
  , { walsCode := "coo", iso := "csz", value := .conjunctional }
  , { walsCode := "cop", iso := "cop", value := .locational }
  , { walsCode := "cze", iso := "ces", value := .have }
  , { walsCode := "dag", iso := "dgz", value := .conjunctional }
  , { walsCode := "din", iso := "din", value := .have }
  , { walsCode := "dio", iso := "dyo", value := .have }
  , { walsCode := "diy", iso := "dif", value := .conjunctional }
  , { walsCode := "dmk", iso := "dmk", value := .locational }
  , { walsCode := "dua", iso := "dua", value := .conjunctional }
  , { walsCode := "dut", iso := "nld", value := .have }
  , { walsCode := "dyi", iso := "dbl", value := .conjunctional }
  , { walsCode := "eka", iso := "ekg", value := .conjunctional }
  , { walsCode := "eng", iso := "eng", value := .have }
  , { walsCode := "evn", iso := "eve", value := .genitive }
  , { walsCode := "ewe", iso := "ewe", value := .locational }
  , { walsCode := "fij", iso := "fij", value := .locational }
  , { walsCode := "fin", iso := "fin", value := .locational }
  , { walsCode := "fni", iso := "fuv", value := .topic }
  , { walsCode := "gae", iso := "gla", value := .locational }
  , { walsCode := "gll", iso := "gbi", value := .conjunctional }
  , { walsCode := "geo", iso := "kat", value := .have }
  , { walsCode := "nbh", iso := "ghl", value := .locational }
  , { walsCode := "gid", iso := "gih", value := .conjunctional }
  , { walsCode := "goa", iso := "guc", value := .conjunctional }
  , { walsCode := "grk", iso := "ell", value := .have }
  , { walsCode := "grw", iso := "kal", value := .have }
  , { walsCode := "gjj", iso := "gub", value := .topic }
  , { walsCode := "gno", iso := "gvc", value := .have }
  , { walsCode := "gua", iso := "gug", value := .have }
  , { walsCode := "gum", iso := "kgs", value := .genitive }
  , { walsCode := "grn", iso := "gur", value := .have }
  , { walsCode := "hcr", iso := "hat", value := .have }
  , { walsCode := "hau", iso := "hau", value := .conjunctional }
  , { walsCode := "heb", iso := "heb", value := .locational }
  , { walsCode := "hin", iso := "hin", value := .locational }
  , { walsCode := "hix", iso := "hix", value := .conjunctional }
  , { walsCode := "hun", iso := "hun", value := .locational }
  , { walsCode := "igb", iso := "ibo", value := .have }
  , { walsCode := "ind", iso := "ind", value := .topic }
  , { walsCode := "iri", iso := "gle", value := .locational }
  , { walsCode := "jpn", iso := "jpn", value := .locational }
  , { walsCode := "juh", iso := "ktz", value := .have }
  , { walsCode := "kbl", iso := "kab", value := .locational }
  , { walsCode := "kng", iso := "kgp", value := .topic }
  , { walsCode := "knd", iso := "kan", value := .locational }
  , { walsCode := "knr", iso := "knc", value := .conjunctional }
  , { walsCode := "krk", iso := "kyh", value := .topic }
  , { walsCode := "kay", iso := "gyd", value := .conjunctional }
  , { walsCode := "ket", iso := "ket", value := .locational }
  , { walsCode := "kha", iso := "khk", value := .locational }
  , { walsCode := "kty", iso := "kca", value := .have }
  , { walsCode := "khs", iso := "kha", value := .topic }
  , { walsCode := "khm", iso := "khm", value := .topic }
  , { walsCode := "klv", iso := "kij", value := .topic }
  , { walsCode := "koa", iso := "cku", value := .topic }
  , { walsCode := "kob", iso := "kpw", value := .topic }
  , { walsCode := "kor", iso := "kor", value := .locational }
  , { walsCode := "kku", iso := "kfq", value := .locational }
  , { walsCode := "kch", iso := "khq", value := .have }
  , { walsCode := "kpe", iso := "xpe", value := .locational }
  , { walsCode := "kro", iso := "kgo", value := .have }
  , { walsCode := "knm", iso := "kun", value := .have }
  , { walsCode := "kwk", iso := "kwk", value := .have }
  , { walsCode := "lad", iso := "lbj", value := .locational }
  , { walsCode := "lah", iso := "lhu", value := .topic }
  , { walsCode := "lkt", iso := "lkt", value := .have }
  , { walsCode := "lan", iso := "laj", value := .conjunctional }
  , { walsCode := "lat", iso := "lav", value := .locational }
  , { walsCode := "lep", iso := "lep", value := .genitive }
  , { walsCode := "lez", iso := "lez", value := .genitive }
  , { walsCode := "lil", iso := "lil", value := .have }
  , { walsCode := "lim", iso := "lif", value := .genitive }
  , { walsCode := "lnd", iso := "liy", value := .conjunctional }
  , { walsCode := "lis", iso := "lis", value := .topic }
  , { walsCode := "lon", iso := "los", value := .topic }
  , { walsCode := "lda", iso := "lug", value := .conjunctional }
  , { walsCode := "lui", iso := "lui", value := .topic }
  , { walsCode := "maa", iso := "mas", value := .have }
  , { walsCode := "mal", iso := "plt", value := .have }
  , { walsCode := "mlt", iso := "mlt", value := .locational }
  , { walsCode := "mmv", iso := "mdi", value := .conjunctional }
  , { walsCode := "mnc", iso := "mnc", value := .locational }
  , { walsCode := "mnd", iso := "cmn", value := .topic }
  , { walsCode := "myi", iso := "mpc", value := .conjunctional }
  , { walsCode := "mbt", iso := "mdj", value := .conjunctional }
  , { walsCode := "mns", iso := "mns", value := .have }
  , { walsCode := "mao", iso := "mri", value := .genitive }
  , { walsCode := "map", iso := "arn", value := .have }
  , { walsCode := "mrg", iso := "mrt", value := .conjunctional }
  , { walsCode := "mei", iso := "mni", value := .genitive }
  , { walsCode := "mis", iso := "miq", value := .have }
  , { walsCode := "mxp", iso := "mil", value := .conjunctional }
  , { walsCode := "miz", iso := "lus", value := .locational }
  , { walsCode := "moj", iso := "mov", value := .have }
  , { walsCode := "mok", iso := "mkj", value := .topic }
  , { walsCode := "mga", iso := "ndt", value := .conjunctional }
  , { walsCode := "mbo", iso := "mxk", value := .conjunctional }
  , { walsCode := "moo", iso := "mos", value := .have }
  , { walsCode := "moe", iso := "myv", value := .genitive }
  , { walsCode := "mtu", iso := "meu", value := .conjunctional }
  , { walsCode := "mun", iso := "unr", value := .locational }
  , { walsCode := "mup", iso := "sur", value := .conjunctional }
  , { walsCode := "mut", iso := "css", value := .topic }
  , { walsCode := "ngt", iso := "nmf", value := .topic }
  , { walsCode := "nhp", iso := "xpo", value := .have }
  , { walsCode := "kho", iso := "naq", value := .have }
  , { walsCode := "nav", iso := "nav", value := .conjunctional }
  , { walsCode := "ntu", iso := "yrk", value := .genitive }
  , { walsCode := "nep", iso := "npi", value := .genitive }
  , { walsCode := "ngl", iso := "nig", value := .conjunctional }
  , { walsCode := "nbm", iso := "nbm", value := .conjunctional }
  , { walsCode := "nko", iso := "cgg", value := .conjunctional }
  , { walsCode := "nue", iso := "nus", value := .conjunctional }
  , { walsCode := "ood", iso := "ood", value := .have }
  , { walsCode := "ojs", iso := "ojs", value := .have }
  , { walsCode := "orm", iso := "oru", value := .genitive }
  , { walsCode := "orh", iso := "hae", value := .have }
  , { walsCode := "otm", iso := "ote", value := .topic }
  , { walsCode := "pal", iso := "pau", value := .topic }
  , { walsCode := "plr", iso := "fap", value := .have }
  , { walsCode := "pna", iso := "pmf", value := .topic }
  , { walsCode := "pap", iso := "pap", value := .have }
  , { walsCode := "prd", iso := "pci", value := .locational }
  , { walsCode := "pau", iso := "pad", value := .conjunctional }
  , { walsCode := "prs", iso := "pes", value := .have }
  , { walsCode := "prh", iso := "myp", value := .have }
  , { walsCode := "pit", iso := "pjt", value := .conjunctional }
  , { walsCode := "pol", iso := "pol", value := .have }
  , { walsCode := "pae", iso := "pbb", value := .have }
  , { walsCode := "qcu", iso := "quz", value := .genitive }
  , { walsCode := "qim", iso := "qvi", value := .have }
  , { walsCode := "qui", iso := "qui", value := .topic }
  , { walsCode := "rom", iso := "ron", value := .have }
  , { walsCode := "rot", iso := "rtm", value := .conjunctional }
  , { walsCode := "rus", iso := "rus", value := .locational }
  , { walsCode := "slb", iso := "sbe", value := .topic }
  , { walsCode := "sam", iso := "smo", value := .locational }
  , { walsCode := "sdw", iso := "sad", value := .conjunctional }
  , { walsCode := "san", iso := "sag", value := .conjunctional }
  , { walsCode := "sed", iso := "sed", value := .topic }
  , { walsCode := "sel", iso := "ona", value := .topic }
  , { walsCode := "snc", iso := "see", value := .locational }
  , { walsCode := "scr", iso := "hbs", value := .have }
  , { walsCode := "srr", iso := "ser", value := .have }
  , { walsCode := "shk", iso := "shp", value := .locational }
  , { walsCode := "shn", iso := "sna", value := .conjunctional }
  , { walsCode := "shu", iso := "shs", value := .have }
  , { walsCode := "snh", iso := "sin", value := .locational }
  , { walsCode := "sin", iso := "snn", value := .topic }
  , { walsCode := "siu", iso := "sis", value := .conjunctional }
  , { walsCode := "so", iso := "teu", value := .conjunctional }
  , { walsCode := "som", iso := "som", value := .conjunctional }
  , { walsCode := "spa", iso := "spa", value := .have }
  , { walsCode := "sra", iso := "srn", value := .have }
  , { walsCode := "sup", iso := "spp", value := .conjunctional }
  , { walsCode := "swa", iso := "swh", value := .conjunctional }
  , { walsCode := "swe", iso := "swe", value := .have }
  , { walsCode := "tag", iso := "tgl", value := .topic }
  , { walsCode := "tah", iso := "tah", value := .genitive }
  , { walsCode := "taj", iso := "tgk", value := .have }
  , { walsCode := "tml", iso := "tam", value := .locational }
  , { walsCode := "tas", iso := "shi", value := .locational }
  , { walsCode := "tne", iso := "tem", value := .topic }
  , { walsCode := "ter", iso := "ttr", value := .conjunctional }
  , { walsCode := "tha", iso := "tha", value := .topic }
  , { walsCode := "tgk", iso := "tgc", value := .have }
  , { walsCode := "tin", iso := "cir", value := .genitive }
  , { walsCode := "tiw", iso := "tiw", value := .topic }
  , { walsCode := "tla", iso := "ksd", value := .topic }
  , { walsCode := "tno", iso := "tdn", value := .topic }
  , { walsCode := "txj", iso := "too", value := .have }
  , { walsCode := "tug", iso := "thv", value := .locational }
  , { walsCode := "tbu", iso := "", value := .have }
  , { walsCode := "tup", iso := "tpn", value := .topic }
  , { walsCode := "tna", iso := "tuv", value := .topic }
  , { walsCode := "tur", iso := "tur", value := .genitive }
  , { walsCode := "tzu", iso := "tzj", value := .topic }
  , { walsCode := "tsh", iso := "par", value := .have }
  , { walsCode := "urk", iso := "urb", value := .topic }
  , { walsCode := "usa", iso := "wnu", value := .topic }
  , { walsCode := "uzb", iso := "", value := .locational }
  , { walsCode := "vie", iso := "vie", value := .topic }
  , { walsCode := "wap", iso := "wao", value := .have }
  , { walsCode := "wsk", iso := "wsk", value := .conjunctional }
  , { walsCode := "wel", iso := "cym", value := .locational }
  , { walsCode := "wic", iso := "wic", value := .locational }
  , { walsCode := "ykt", iso := "sah", value := .locational }
  , { walsCode := "yaq", iso := "yaq", value := .have }
  , { walsCode := "yav", iso := "yuf", value := .have }
  , { walsCode := "yid", iso := "yii", value := .conjunctional }
  , { walsCode := "yim", iso := "yee", value := .conjunctional }
  , { walsCode := "yor", iso := "yor", value := .have }
  , { walsCode := "yko", iso := "yux", value := .conjunctional }
  , { walsCode := "zan", iso := "zne", value := .conjunctional }
  , { walsCode := "zpi", iso := "zpd", value := .conjunctional }
  , { walsCode := "zqc", iso := "zoc", value := .conjunctional }
  , { walsCode := "zul", iso := "zul", value := .conjunctional }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F117A
