import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 36A: The Associative Plural
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 36A`.

Chapter 36, 236 languages.
-/

namespace Datasets.WALS.F36A

/-- WALS 36A values. -/
inductive AssociativePlural where
  /-- Associative same as additive plural (104 languages). -/
  | associativeSameAsAdditivePlural
  /-- Unique affixal associative plural (48 languages). -/
  | uniqueAffixalAssociativePlural
  /-- Unique periphrastic associative plural (47 languages). -/
  | uniquePeriphrasticAssociativePlural
  /-- No associative plural (37 languages). -/
  | noAssociativePlural
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 36A dataset (236 languages). -/
def allData : List (Datapoint AssociativePlural) :=
  [ { walsCode := "abk", iso := "abk", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "aco", iso := "kjq", value := .noAssociativePlural }
  , { walsCode := "adt", iso := "ady", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "afr", iso := "afr", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "agl", iso := "agx", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ain", iso := "ain", value := .associativeSameAsAdditivePlural }
  , { walsCode := "akn", iso := "aka", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ala", iso := "amp", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "alb", iso := "sqi", value := .noAssociativePlural }
  , { walsCode := "alu", iso := "alr", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ame", iso := "aey", value := .noAssociativePlural }
  , { walsCode := "amh", iso := "amh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "apl", iso := "apy", value := .associativeSameAsAdditivePlural }
  , { walsCode := "apu", iso := "apu", value := .noAssociativePlural }
  , { walsCode := "aeg", iso := "arz", value := .noAssociativePlural }
  , { walsCode := "ana", iso := "aro", value := .associativeSameAsAdditivePlural }
  , { walsCode := "arp", iso := "ape", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "arm", iso := "hye", value := .noAssociativePlural }
  , { walsCode := "asm", iso := "cns", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "awt", iso := "kmn", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bgv", iso := "kva", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bam", iso := "bam", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bnd", iso := "bza", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bnw", iso := "bwi", value := .noAssociativePlural }
  , { walsCode := "brs", iso := "bsn", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "bae", iso := "bae", value := .noAssociativePlural }
  , { walsCode := "bsk", iso := "bak", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bsq", iso := "eus", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "bel", iso := "byw", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ben", iso := "ben", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "bdc", iso := "brc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "brh", iso := "brh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "bul", iso := "bul", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "but", iso := "bxm", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "brm", iso := "mya", value := .associativeSameAsAdditivePlural }
  , { walsCode := "buu", iso := "mhs", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "cnt", iso := "yue", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "chm", iso := "cji", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "cha", iso := "cha", value := .associativeSameAsAdditivePlural }
  , { walsCode := "chn", iso := "chx", value := .associativeSameAsAdditivePlural }
  , { walsCode := "chc", iso := "che", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "chk", iso := "ckt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "chv", iso := "chv", value := .associativeSameAsAdditivePlural }
  , { walsCode := "cmn", iso := "com", value := .associativeSameAsAdditivePlural }
  , { walsCode := "cre", iso := "crk", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "cri", iso := "crh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "dni", iso := "dni", value := .associativeSameAsAdditivePlural }
  , { walsCode := "drg", iso := "dar", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "des", iso := "des", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "dut", iso := "nld", value := .noAssociativePlural }
  , { walsCode := "dyi", iso := "dbl", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "eng", iso := "eng", value := .noAssociativePlural }
  , { walsCode := "est", iso := "ekk", value := .noAssociativePlural }
  , { walsCode := "eve", iso := "evn", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ewe", iso := "ewe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "fin", iso := "fin", value := .noAssociativePlural }
  , { walsCode := "fre", iso := "fra", value := .noAssociativePlural }
  , { walsCode := "fri", iso := "fry", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "fua", iso := "fub", value := .associativeSameAsAdditivePlural }
  , { walsCode := "gag", iso := "gag", value := .associativeSameAsAdditivePlural }
  , { walsCode := "gar", iso := "grt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "gbb", iso := "gbp", value := .associativeSameAsAdditivePlural }
  , { walsCode := "geo", iso := "kat", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ger", iso := "deu", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "goo", iso := "gni", value := .associativeSameAsAdditivePlural }
  , { walsCode := "grk", iso := "ell", value := .noAssociativePlural }
  , { walsCode := "grw", iso := "kal", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "gua", iso := "gug", value := .noAssociativePlural }
  , { walsCode := "gud", iso := "gde", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "gji", iso := "gue", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "hau", iso := "hau", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "haw", iso := "haw", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "hwc", iso := "hwc", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "hay", iso := "vay", value := .associativeSameAsAdditivePlural }
  , { walsCode := "heb", iso := "heb", value := .noAssociativePlural }
  , { walsCode := "hin", iso := "hin", value := .noAssociativePlural }
  , { walsCode := "hix", iso := "hix", value := .associativeSameAsAdditivePlural }
  , { walsCode := "hun", iso := "hun", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ice", iso := "isl", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "ifu", iso := "ifb", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "ik", iso := "ikx", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ind", iso := "ind", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "iir", iso := "pmy", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "ing", iso := "inh", value := .noAssociativePlural }
  , { walsCode := "iri", iso := "gle", value := .noAssociativePlural }
  , { walsCode := "ita", iso := "ita", value := .noAssociativePlural }
  , { walsCode := "jcr", iso := "jam", value := .associativeSameAsAdditivePlural }
  , { walsCode := "jpn", iso := "jpn", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kab", iso := "kbd", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kls", iso := "fla", value := .associativeSameAsAdditivePlural }
  , { walsCode := "knd", iso := "kan", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "knr", iso := "knc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "krc", iso := "krc", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ktz", iso := "bsh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "kyl", iso := "eky", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kay", iso := "gyd", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kaz", iso := "kaz", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ker", iso := "ker", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "khk", iso := "kjh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kha", iso := "khk", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kty", iso := "kca", value := .associativeSameAsAdditivePlural }
  , { walsCode := "krb", iso := "gil", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kop", iso := "koi", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kzy", iso := "kpv", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kon", iso := "kng", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kor", iso := "kor", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kry", iso := "kpy", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kse", iso := "ses", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kyn", iso := "koy", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kpe", iso := "xpe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kfc", iso := "rop", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "knq", iso := "rop", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "kro", iso := "kgo", value := .associativeSameAsAdditivePlural }
  , { walsCode := "klg", iso := "kle", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kuq", iso := "kum", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kut", iso := "kut", value := .noAssociativePlural }
  , { walsCode := "lah", iso := "lhu", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lak", iso := "lbe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lkt", iso := "lkt", value := .noAssociativePlural }
  , { walsCode := "lan", iso := "laj", value := .noAssociativePlural }
  , { walsCode := "lao", iso := "lao", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "lav", iso := "lvk", value := .noAssociativePlural }
  , { walsCode := "lep", iso := "lep", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lcr", iso := "", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "lez", iso := "lez", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lim", iso := "lif", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lok", iso := "lok", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lma", iso := "lom", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lda", iso := "lug", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lug", iso := "lgg", value := .associativeSameAsAdditivePlural }
  , { walsCode := "luv", iso := "lue", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mag", iso := "mgp", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mak", iso := "myh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mal", iso := "plt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mym", iso := "mal", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mlt", iso := "mlt", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mds", iso := "xmm", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mbu", iso := "mle", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mnc", iso := "mnc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mnd", iso := "cmn", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mdk", iso := "mnk", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mmb", iso := "mna", value := .associativeSameAsAdditivePlural }
  , { walsCode := "myi", iso := "mpc", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mao", iso := "mri", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mrg", iso := "mrt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mme", iso := "mhr", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mrd", iso := "mrz", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mrt", iso := "vma", value := .noAssociativePlural }
  , { walsCode := "msk", iso := "jle", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mcr", iso := "mfe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mei", iso := "mni", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mxc", iso := "mig", value := .noAssociativePlural }
  , { walsCode := "moe", iso := "myv", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mna", iso := "mnb", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mup", iso := "sur", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mwo", iso := "mlv", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mce", iso := "bzk", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kho", iso := "naq", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "nai", iso := "gld", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ndy", iso := "djk", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "nep", iso := "npi", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nwd", iso := "new", value := .associativeSameAsAdditivePlural }
  , { walsCode := "new", iso := "new", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ngg", iso := "nam", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nga", iso := "nio", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ngi", iso := "wyb", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nia", iso := "nia", value := .associativeSameAsAdditivePlural }
  , { walsCode := "niv", iso := "niv", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nob", iso := "fia", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nor", iso := "nor", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "nug", iso := "nuy", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "nyi", iso := "nyi", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ond", iso := "one", value := .noAssociativePlural }
  , { walsCode := "orc", iso := "oac", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "oss", iso := "oss", value := .associativeSameAsAdditivePlural }
  , { walsCode := "otm", iso := "ote", value := .noAssociativePlural }
  , { walsCode := "plk", iso := "plu", value := .noAssociativePlural }
  , { walsCode := "pan", iso := "pan", value := .associativeSameAsAdditivePlural }
  , { walsCode := "pap", iso := "pap", value := .associativeSameAsAdditivePlural }
  , { walsCode := "pau", iso := "pad", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "prs", iso := "pes", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "pol", iso := "pol", value := .associativeSameAsAdditivePlural }
  , { walsCode := "pmc", iso := "poo", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "por", iso := "por", value := .noAssociativePlural }
  , { walsCode := "fma", iso := "fuc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "qim", iso := "qvi", value := .noAssociativePlural }
  , { walsCode := "rap", iso := "rap", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "rus", iso := "rus", value := .noAssociativePlural }
  , { walsCode := "rut", iso := "rut", value := .associativeSameAsAdditivePlural }
  , { walsCode := "sno", iso := "sme", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "san", iso := "sag", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ses", iso := "sot", value := .associativeSameAsAdditivePlural }
  , { walsCode := "sht", iso := "shj", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "rsh", iso := "sgh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "sil", iso := "dau", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "snh", iso := "sin", value := .associativeSameAsAdditivePlural }
  , { walsCode := "sla", iso := "den", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "spa", iso := "spa", value := .noAssociativePlural }
  , { walsCode := "sup", iso := "spp", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "swa", iso := "swh", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tbs", iso := "tab", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tag", iso := "tgl", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tkl", iso := "tkm", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tam", iso := "taj", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tar", iso := "tae", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tmu", iso := "ttt", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tvo", iso := "tat", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tlf", iso := "tlf", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tha", iso := "tha", value := .noAssociativePlural }
  , { walsCode := "tlo", iso := "tlb", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tof", iso := "kim", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tpi", iso := "tpi", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tms", iso := "dto", value := .associativeSameAsAdditivePlural }
  , { walsCode := "toq", iso := "mlu", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tsz", iso := "ddo", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tuc", iso := "tuo", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tuk", iso := "", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tur", iso := "tur", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tvl", iso := "tvl", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "udh", iso := "ude", value := .associativeSameAsAdditivePlural }
  , { walsCode := "udm", iso := "udm", value := .associativeSameAsAdditivePlural }
  , { walsCode := "urk", iso := "urb", value := .associativeSameAsAdditivePlural }
  , { walsCode := "uyg", iso := "uig", value := .associativeSameAsAdditivePlural }
  , { walsCode := "uzb", iso := "", value := .associativeSameAsAdditivePlural }
  , { walsCode := "vie", iso := "vie", value := .noAssociativePlural }
  , { walsCode := "wrd", iso := "wrr", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "wrk", iso := "gae", value := .noAssociativePlural }
  , { walsCode := "wic", iso := "wic", value := .noAssociativePlural }
  , { walsCode := "wch", iso := "mzh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "yag", iso := "yad", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "yaq", iso := "yaq", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "yid", iso := "yii", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "yor", iso := "yor", value := .associativeSameAsAdditivePlural }
  , { walsCode := "yko", iso := "yux", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ypk", iso := "esu", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "zul", iso := "zul", value := .associativeSameAsAdditivePlural }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F36A
