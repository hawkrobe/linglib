import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 63A: Noun Phrase Conjunction
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 63A`.

Chapter 63, 234 languages.
-/

namespace Datasets.WALS.F63A

/-- WALS 63A values. -/
inductive NounPhraseConjunction where
  /-- 'And' different from 'with' (131 languages). -/
  | andDifferentFromWith
  /-- 'And' identical to 'with' (103 languages). -/
  | andIdenticalToWith
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 63A dataset (234 languages). -/
def allData : List (Datapoint NounPhraseConjunction) :=
  [ { walsCode := "abk", iso := "abk", value := .andDifferentFromWith }
  , { walsCode := "ace", iso := "ace", value := .andIdenticalToWith }
  , { walsCode := "acl", iso := "ach", value := .andIdenticalToWith }
  , { walsCode := "ahu", iso := "ahh", value := .andDifferentFromWith }
  , { walsCode := "ain", iso := "ain", value := .andDifferentFromWith }
  , { walsCode := "akn", iso := "aka", value := .andIdenticalToWith }
  , { walsCode := "abm", iso := "akz", value := .andDifferentFromWith }
  , { walsCode := "ala", iso := "amp", value := .andDifferentFromWith }
  , { walsCode := "alb", iso := "sqi", value := .andDifferentFromWith }
  , { walsCode := "ale", iso := "ale", value := .andDifferentFromWith }
  , { walsCode := "ame", iso := "aey", value := .andIdenticalToWith }
  , { walsCode := "amh", iso := "amh", value := .andDifferentFromWith }
  , { walsCode := "adk", iso := "ano", value := .andDifferentFromWith }
  , { walsCode := "apl", iso := "apy", value := .andIdenticalToWith }
  , { walsCode := "aeg", iso := "arz", value := .andDifferentFromWith }
  , { walsCode := "arc", iso := "aqc", value := .andDifferentFromWith }
  , { walsCode := "arm", iso := "hye", value := .andDifferentFromWith }
  , { walsCode := "amp", iso := "aer", value := .andDifferentFromWith }
  , { walsCode := "asm", iso := "cns", value := .andDifferentFromWith }
  , { walsCode := "ava", iso := "ava", value := .andDifferentFromWith }
  , { walsCode := "awt", iso := "kmn", value := .andDifferentFromWith }
  , { walsCode := "bab", iso := "bav", value := .andIdenticalToWith }
  , { walsCode := "bam", iso := "bam", value := .andDifferentFromWith }
  , { walsCode := "bgg", iso := "bgz", value := .andIdenticalToWith }
  , { walsCode := "bar", iso := "bfa", value := .andIdenticalToWith }
  , { walsCode := "bsq", iso := "eus", value := .andDifferentFromWith }
  , { walsCode := "bkr", iso := "btx", value := .andIdenticalToWith }
  , { walsCode := "bej", iso := "bej", value := .andDifferentFromWith }
  , { walsCode := "bma", iso := "tzm", value := .andIdenticalToWith }
  , { walsCode := "bln", iso := "byn", value := .andIdenticalToWith }
  , { walsCode := "bir", iso := "bom", value := .andIdenticalToWith }
  , { walsCode := "bla", iso := "bla", value := .andDifferentFromWith }
  , { walsCode := "bre", iso := "bre", value := .andDifferentFromWith }
  , { walsCode := "bri", iso := "bzd", value := .andDifferentFromWith }
  , { walsCode := "bul", iso := "bul", value := .andDifferentFromWith }
  , { walsCode := "bui", iso := "bzq", value := .andIdenticalToWith }
  , { walsCode := "brm", iso := "mya", value := .andIdenticalToWith }
  , { walsCode := "bur", iso := "bsk", value := .andDifferentFromWith }
  , { walsCode := "cnl", iso := "ram", value := .andIdenticalToWith }
  , { walsCode := "car", iso := "car", value := .andIdenticalToWith }
  , { walsCode := "cha", iso := "cha", value := .andIdenticalToWith }
  , { walsCode := "cso", iso := "ctp", value := .andIdenticalToWith }
  , { walsCode := "cmh", iso := "ute", value := .andIdenticalToWith }
  , { walsCode := "ckl", iso := "chh", value := .andDifferentFromWith }
  , { walsCode := "cct", iso := "cho", value := .andDifferentFromWith }
  , { walsCode := "chk", iso := "ckt", value := .andDifferentFromWith }
  , { walsCode := "cbo", iso := "cao", value := .andIdenticalToWith }
  , { walsCode := "cil", iso := "lua", value := .andIdenticalToWith }
  , { walsCode := "coo", iso := "csz", value := .andDifferentFromWith }
  , { walsCode := "cop", iso := "cop", value := .andIdenticalToWith }
  , { walsCode := "cre", iso := "crk", value := .andDifferentFromWith }
  , { walsCode := "dag", iso := "dgz", value := .andDifferentFromWith }
  , { walsCode := "din", iso := "din", value := .andIdenticalToWith }
  , { walsCode := "diy", iso := "dif", value := .andDifferentFromWith }
  , { walsCode := "dua", iso := "dua", value := .andIdenticalToWith }
  , { walsCode := "dut", iso := "nld", value := .andDifferentFromWith }
  , { walsCode := "dyi", iso := "dbl", value := .andDifferentFromWith }
  , { walsCode := "eka", iso := "ekg", value := .andIdenticalToWith }
  , { walsCode := "eng", iso := "eng", value := .andDifferentFromWith }
  , { walsCode := "est", iso := "ekk", value := .andDifferentFromWith }
  , { walsCode := "evn", iso := "eve", value := .andIdenticalToWith }
  , { walsCode := "ewe", iso := "ewe", value := .andIdenticalToWith }
  , { walsCode := "fij", iso := "fij", value := .andIdenticalToWith }
  , { walsCode := "fin", iso := "fin", value := .andDifferentFromWith }
  , { walsCode := "fre", iso := "fra", value := .andDifferentFromWith }
  , { walsCode := "fni", iso := "fuv", value := .andIdenticalToWith }
  , { walsCode := "gae", iso := "gla", value := .andDifferentFromWith }
  , { walsCode := "gll", iso := "gbi", value := .andIdenticalToWith }
  , { walsCode := "geo", iso := "kat", value := .andDifferentFromWith }
  , { walsCode := "nbh", iso := "ghl", value := .andIdenticalToWith }
  , { walsCode := "gid", iso := "gih", value := .andDifferentFromWith }
  , { walsCode := "goa", iso := "guc", value := .andIdenticalToWith }
  , { walsCode := "grk", iso := "ell", value := .andDifferentFromWith }
  , { walsCode := "grw", iso := "kal", value := .andIdenticalToWith }
  , { walsCode := "gua", iso := "gug", value := .andDifferentFromWith }
  , { walsCode := "gum", iso := "kgs", value := .andDifferentFromWith }
  , { walsCode := "grn", iso := "gur", value := .andIdenticalToWith }
  , { walsCode := "hcr", iso := "hat", value := .andIdenticalToWith }
  , { walsCode := "hau", iso := "hau", value := .andIdenticalToWith }
  , { walsCode := "heb", iso := "heb", value := .andDifferentFromWith }
  , { walsCode := "hin", iso := "hin", value := .andDifferentFromWith }
  , { walsCode := "hix", iso := "hix", value := .andDifferentFromWith }
  , { walsCode := "hun", iso := "hun", value := .andDifferentFromWith }
  , { walsCode := "ice", iso := "isl", value := .andDifferentFromWith }
  , { walsCode := "igb", iso := "ibo", value := .andDifferentFromWith }
  , { walsCode := "ind", iso := "ind", value := .andIdenticalToWith }
  , { walsCode := "iri", iso := "gle", value := .andDifferentFromWith }
  , { walsCode := "jab", iso := "jae", value := .andDifferentFromWith }
  , { walsCode := "jak", iso := "jac", value := .andIdenticalToWith }
  , { walsCode := "jpn", iso := "jpn", value := .andIdenticalToWith }
  , { walsCode := "jaq", iso := "jqr", value := .andIdenticalToWith }
  , { walsCode := "juh", iso := "ktz", value := .andDifferentFromWith }
  , { walsCode := "kng", iso := "kgp", value := .andIdenticalToWith }
  , { walsCode := "kls", iso := "fla", value := .andIdenticalToWith }
  , { walsCode := "knd", iso := "kan", value := .andDifferentFromWith }
  , { walsCode := "knr", iso := "knc", value := .andIdenticalToWith }
  , { walsCode := "kei", iso := "kei", value := .andIdenticalToWith }
  , { walsCode := "ket", iso := "ket", value := .andDifferentFromWith }
  , { walsCode := "kha", iso := "khk", value := .andDifferentFromWith }
  , { walsCode := "kty", iso := "kca", value := .andDifferentFromWith }
  , { walsCode := "khs", iso := "kha", value := .andIdenticalToWith }
  , { walsCode := "khm", iso := "khm", value := .andDifferentFromWith }
  , { walsCode := "kio", iso := "kio", value := .andDifferentFromWith }
  , { walsCode := "kob", iso := "kpw", value := .andIdenticalToWith }
  , { walsCode := "kor", iso := "kor", value := .andDifferentFromWith }
  , { walsCode := "kku", iso := "kfq", value := .andDifferentFromWith }
  , { walsCode := "kpe", iso := "xpe", value := .andIdenticalToWith }
  , { walsCode := "knm", iso := "kun", value := .andIdenticalToWith }
  , { walsCode := "kwa", iso := "kwd", value := .andDifferentFromWith }
  , { walsCode := "kwk", iso := "kwk", value := .andIdenticalToWith }
  , { walsCode := "kat", iso := "kmg", value := .andDifferentFromWith }
  , { walsCode := "lah", iso := "lhu", value := .andDifferentFromWith }
  , { walsCode := "lkt", iso := "lkt", value := .andDifferentFromWith }
  , { walsCode := "lat", iso := "lav", value := .andDifferentFromWith }
  , { walsCode := "lep", iso := "lep", value := .andDifferentFromWith }
  , { walsCode := "lez", iso := "lez", value := .andDifferentFromWith }
  , { walsCode := "lil", iso := "lil", value := .andDifferentFromWith }
  , { walsCode := "lim", iso := "lif", value := .andIdenticalToWith }
  , { walsCode := "lnd", iso := "liy", value := .andIdenticalToWith }
  , { walsCode := "lis", iso := "lis", value := .andIdenticalToWith }
  , { walsCode := "lit", iso := "lit", value := .andDifferentFromWith }
  , { walsCode := "lon", iso := "los", value := .andIdenticalToWith }
  , { walsCode := "lda", iso := "lug", value := .andIdenticalToWith }
  , { walsCode := "maa", iso := "mas", value := .andDifferentFromWith }
  , { walsCode := "mal", iso := "plt", value := .andDifferentFromWith }
  , { walsCode := "mlt", iso := "mlt", value := .andDifferentFromWith }
  , { walsCode := "mmv", iso := "mdi", value := .andIdenticalToWith }
  , { walsCode := "mnm", iso := "mva", value := .andIdenticalToWith }
  , { walsCode := "mnc", iso := "mnc", value := .andDifferentFromWith }
  , { walsCode := "mnd", iso := "cmn", value := .andIdenticalToWith }
  , { walsCode := "myi", iso := "mpc", value := .andDifferentFromWith }
  , { walsCode := "mbt", iso := "mdj", value := .andIdenticalToWith }
  , { walsCode := "mao", iso := "mri", value := .andIdenticalToWith }
  , { walsCode := "map", iso := "arn", value := .andDifferentFromWith }
  , { walsCode := "mrg", iso := "mrt", value := .andIdenticalToWith }
  , { walsCode := "mrd", iso := "mrz", value := .andDifferentFromWith }
  , { walsCode := "mei", iso := "mni", value := .andDifferentFromWith }
  , { walsCode := "men", iso := "mez", value := .andDifferentFromWith }
  , { walsCode := "mcf", iso := "crg", value := .andDifferentFromWith }
  , { walsCode := "mis", iso := "miq", value := .andIdenticalToWith }
  , { walsCode := "mxp", iso := "mil", value := .andIdenticalToWith }
  , { walsCode := "miz", iso := "lus", value := .andIdenticalToWith }
  , { walsCode := "moj", iso := "mov", value := .andIdenticalToWith }
  , { walsCode := "mok", iso := "mkj", value := .andDifferentFromWith }
  , { walsCode := "moo", iso := "mos", value := .andIdenticalToWith }
  , { walsCode := "moe", iso := "myv", value := .andDifferentFromWith }
  , { walsCode := "mtu", iso := "meu", value := .andIdenticalToWith }
  , { walsCode := "mun", iso := "unr", value := .andDifferentFromWith }
  , { walsCode := "mut", iso := "css", value := .andDifferentFromWith }
  , { walsCode := "kho", iso := "naq", value := .andDifferentFromWith }
  , { walsCode := "nar", iso := "nrb", value := .andDifferentFromWith }
  , { walsCode := "nav", iso := "nav", value := .andIdenticalToWith }
  , { walsCode := "ntu", iso := "yrk", value := .andIdenticalToWith }
  , { walsCode := "ngl", iso := "nig", value := .andDifferentFromWith }
  , { walsCode := "ngk", iso := "nam", value := .andIdenticalToWith }
  , { walsCode := "nbm", iso := "nbm", value := .andIdenticalToWith }
  , { walsCode := "nca", iso := "caq", value := .andDifferentFromWith }
  , { walsCode := "nko", iso := "cgg", value := .andIdenticalToWith }
  , { walsCode := "nue", iso := "nus", value := .andIdenticalToWith }
  , { walsCode := "ojs", iso := "ojs", value := .andDifferentFromWith }
  , { walsCode := "orh", iso := "hae", value := .andDifferentFromWith }
  , { walsCode := "otm", iso := "ote", value := .andDifferentFromWith }
  , { walsCode := "pal", iso := "pau", value := .andIdenticalToWith }
  , { walsCode := "plr", iso := "fap", value := .andIdenticalToWith }
  , { walsCode := "pna", iso := "pmf", value := .andIdenticalToWith }
  , { walsCode := "prd", iso := "pci", value := .andDifferentFromWith }
  , { walsCode := "psm", iso := "pqm", value := .andDifferentFromWith }
  , { walsCode := "prs", iso := "pes", value := .andDifferentFromWith }
  , { walsCode := "pip", iso := "ppl", value := .andIdenticalToWith }
  , { walsCode := "pir", iso := "pib", value := .andIdenticalToWith }
  , { walsCode := "pit", iso := "pjt", value := .andDifferentFromWith }
  , { walsCode := "pol", iso := "pol", value := .andDifferentFromWith }
  , { walsCode := "qim", iso := "qvi", value := .andDifferentFromWith }
  , { walsCode := "rka", iso := "rmy", value := .andDifferentFromWith }
  , { walsCode := "rom", iso := "ron", value := .andDifferentFromWith }
  , { walsCode := "rti", iso := "twu", value := .andIdenticalToWith }
  , { walsCode := "rot", iso := "rtm", value := .andIdenticalToWith }
  , { walsCode := "rus", iso := "rus", value := .andDifferentFromWith }
  , { walsCode := "sam", iso := "smo", value := .andIdenticalToWith }
  , { walsCode := "san", iso := "sag", value := .andIdenticalToWith }
  , { walsCode := "sed", iso := "sed", value := .andIdenticalToWith }
  , { walsCode := "sel", iso := "ona", value := .andDifferentFromWith }
  , { walsCode := "scr", iso := "hbs", value := .andDifferentFromWith }
  , { walsCode := "srr", iso := "ser", value := .andDifferentFromWith }
  , { walsCode := "shn", iso := "sna", value := .andIdenticalToWith }
  , { walsCode := "shu", iso := "shs", value := .andIdenticalToWith }
  , { walsCode := "snh", iso := "sin", value := .andDifferentFromWith }
  , { walsCode := "siu", iso := "sis", value := .andDifferentFromWith }
  , { walsCode := "sla", iso := "den", value := .andDifferentFromWith }
  , { walsCode := "som", iso := "som", value := .andDifferentFromWith }
  , { walsCode := "spa", iso := "spa", value := .andDifferentFromWith }
  , { walsCode := "squ", iso := "squ", value := .andDifferentFromWith }
  , { walsCode := "sra", iso := "srn", value := .andIdenticalToWith }
  , { walsCode := "swa", iso := "swh", value := .andIdenticalToWith }
  , { walsCode := "swe", iso := "swe", value := .andDifferentFromWith }
  , { walsCode := "tag", iso := "tgl", value := .andDifferentFromWith }
  , { walsCode := "tah", iso := "tah", value := .andIdenticalToWith }
  , { walsCode := "tml", iso := "tam", value := .andDifferentFromWith }
  , { walsCode := "tne", iso := "tem", value := .andIdenticalToWith }
  , { walsCode := "ter", iso := "ttr", value := .andIdenticalToWith }
  , { walsCode := "tha", iso := "tha", value := .andDifferentFromWith }
  , { walsCode := "tgk", iso := "tgc", value := .andDifferentFromWith }
  , { walsCode := "tgr", iso := "tig", value := .andDifferentFromWith }
  , { walsCode := "tiw", iso := "tiw", value := .andDifferentFromWith }
  , { walsCode := "tli", iso := "tli", value := .andDifferentFromWith }
  , { walsCode := "tpi", iso := "tpi", value := .andDifferentFromWith }
  , { walsCode := "tla", iso := "ksd", value := .andIdenticalToWith }
  , { walsCode := "tno", iso := "tdn", value := .andIdenticalToWith }
  , { walsCode := "tsi", iso := "tsi", value := .andDifferentFromWith }
  , { walsCode := "tbu", iso := "", value := .andDifferentFromWith }
  , { walsCode := "tup", iso := "tpn", value := .andIdenticalToWith }
  , { walsCode := "tna", iso := "tuv", value := .andIdenticalToWith }
  , { walsCode := "tur", iso := "tur", value := .andDifferentFromWith }
  , { walsCode := "tus", iso := "tus", value := .andDifferentFromWith }
  , { walsCode := "tzu", iso := "tzj", value := .andIdenticalToWith }
  , { walsCode := "urk", iso := "urb", value := .andIdenticalToWith }
  , { walsCode := "usa", iso := "wnu", value := .andDifferentFromWith }
  , { walsCode := "uzb", iso := "", value := .andDifferentFromWith }
  , { walsCode := "vie", iso := "vie", value := .andDifferentFromWith }
  , { walsCode := "wap", iso := "wao", value := .andDifferentFromWith }
  , { walsCode := "wrp", iso := "wrp", value := .andDifferentFromWith }
  , { walsCode := "wsk", iso := "wsk", value := .andIdenticalToWith }
  , { walsCode := "wlf", iso := "wol", value := .andIdenticalToWith }
  , { walsCode := "ykt", iso := "sah", value := .andIdenticalToWith }
  , { walsCode := "yaq", iso := "yaq", value := .andDifferentFromWith }
  , { walsCode := "yav", iso := "yuf", value := .andIdenticalToWith }
  , { walsCode := "yid", iso := "yii", value := .andDifferentFromWith }
  , { walsCode := "yor", iso := "yor", value := .andIdenticalToWith }
  , { walsCode := "yko", iso := "yux", value := .andDifferentFromWith }
  , { walsCode := "yur", iso := "yur", value := .andDifferentFromWith }
  , { walsCode := "zai", iso := "zai", value := .andIdenticalToWith }
  , { walsCode := "zar", iso := "dje", value := .andIdenticalToWith }
  , { walsCode := "zqc", iso := "zoc", value := .andDifferentFromWith }
  , { walsCode := "zul", iso := "zul", value := .andIdenticalToWith }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F63A
