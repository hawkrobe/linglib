import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 138A: Tea
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 138A`.

Chapter 138, 230 languages.
-/

namespace Core.WALS.F138A

/-- WALS 138A values. -/
inductive Tea where
  /-- Words derived from Sinitic cha (110 languages). -/
  | wordsDerivedFromSiniticCha
  /-- Words derived from Min Nan Chinese te (84 languages). -/
  | wordsDerivedFromMinNanChineseTe
  /-- Others (36 languages). -/
  | others
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 138A dataset (230 languages). -/
def allData : List (Datapoint Tea) :=
  [ { walsCode := "xoo", iso := "nmn", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "abz", iso := "abq", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ace", iso := "ace", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "afr", iso := "afr", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "aht", iso := "aht", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "abm", iso := "akz", value := .others }
  , { walsCode := "alb", iso := "sqi", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "alt", iso := "gsw", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "amh", iso := "amh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "aeg", iso := "arz", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "arm", iso := "hye", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ass", iso := "asm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ast", iso := "ast", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ata", iso := "tay", value := .others }
  , { walsCode := "aze", iso := "", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bdg", iso := "bfq", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "bal", iso := "ban", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "blc", iso := "bgn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bam", iso := "bam", value := .others }
  , { walsCode := "bsk", iso := "bak", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bsq", iso := "eus", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "blr", iso := "bel", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ben", iso := "ben", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bma", iso := "tzm", value := .others }
  , { walsCode := "bre", iso := "bre", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "bru", iso := "bru", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "bul", iso := "bul", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "but", iso := "bxm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "brj", iso := "bji", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "brm", iso := "mya", value := .others }
  , { walsCode := "bur", iso := "bsk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cnt", iso := "yue", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ctl", iso := "cat", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ceb", iso := "ceb", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cme", iso := "cjm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cha", iso := "cha", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "chn", iso := "chx", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "chc", iso := "che", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cmh", iso := "ute", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "che", iso := "chr", value := .others }
  , { walsCode := "cyn", iso := "chy", value := .others }
  , { walsCode := "cic", iso := "nya", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "chp", iso := "chp", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "chr", iso := "crw", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "crh", iso := "cje", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "chv", iso := "chv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ccp", iso := "coc", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "com", iso := "swb", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cre", iso := "crk", value := .others }
  , { walsCode := "cua", iso := "cua", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "cze", iso := "ces", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "dga", iso := "dga", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dah", iso := "dal", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "dsh", iso := "dan", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dhi", iso := "div", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "din", iso := "din", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "dio", iso := "dyo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dua", iso := "dua", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dut", iso := "nld", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "eng", iso := "eng", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "est", iso := "ekk", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "evn", iso := "eve", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "eve", iso := "evn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ewe", iso := "ewe", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ewo", iso := "ewo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "fin", iso := "fin", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "fre", iso := "fra", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "fli", iso := "fuh", value := .others }
  , { walsCode := "fua", iso := "fub", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "gml", iso := "kld", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "geo", iso := "kat", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ger", iso := "deu", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "grt", iso := "gor", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "grk", iso := "ell", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "gdl", iso := "gcf", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "gua", iso := "gug", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "guj", iso := "guj", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "hau", iso := "hau", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "haw", iso := "haw", value := .others }
  , { walsCode := "heb", iso := "heb", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "hil", iso := "hil", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "hin", iso := "hin", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "hre", iso := "hre", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "hun", iso := "hun", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ice", iso := "isl", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ind", iso := "ind", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ing", iso := "inh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "iri", iso := "gle", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ita", iso := "ita", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "inu", iso := "esi", value := .others }
  , { walsCode := "jpn", iso := "jpn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "jav", iso := "jav", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "jmo", iso := "bex", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "juh", iso := "ktz", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kab", iso := "kbd", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kbl", iso := "kab", value := .others }
  , { walsCode := "kmk", iso := "xal", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "knr", iso := "knc", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "krm", iso := "kdr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kkp", iso := "kaa", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ksg", iso := "ksw", value := .others }
  , { walsCode := "krk", iso := "kyh", value := .others }
  , { walsCode := "kaz", iso := "kaz", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "keu", iso := "keu", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ket", iso := "ket", value := .others }
  , { walsCode := "khk", iso := "kjh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kha", iso := "khk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "khs", iso := "kha", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "khm", iso := "khm", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kik", iso := "kik", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kin", iso := "kin", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kgz", iso := "kir", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "koi", iso := "kbk", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kkn", iso := "knn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kor", iso := "kor", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kry", iso := "kpy", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kos", iso := "kos", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kse", iso := "ses", value := .others }
  , { walsCode := "kro", iso := "kgo", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kuq", iso := "kum", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kjn", iso := "kjn", value := .others }
  , { walsCode := "kji", iso := "kmr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lad", iso := "lbj", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lmp", iso := "ljp", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "lao", iso := "lao", value := .others }
  , { walsCode := "lat", iso := "lav", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "lcr", iso := "", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lin", iso := "lin", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "lis", iso := "lis", value := .others }
  , { walsCode := "lit", iso := "lit", value := .others }
  , { walsCode := "lon", iso := "los", value := .others }
  , { walsCode := "lda", iso := "lug", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "luo", iso := "luo", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lux", iso := "ltz", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mdr", iso := "mad", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mks", iso := "mak", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mal", iso := "plt", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mym", iso := "mal", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mlt", iso := "mlt", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mnd", iso := "cmn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mao", iso := "mri", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mku", iso := "zmr", value := .others }
  , { walsCode := "mhi", iso := "mar", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mme", iso := "mhr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "msh", iso := "mah", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mby", iso := "myb", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mnt", iso := "mwv", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "hok", iso := "nan", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "min", iso := "min", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mss", iso := "skd", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mol", iso := "ron", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "moe", iso := "myv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nai", iso := "gld", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nep", iso := "npi", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "new", iso := "new", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nog", iso := "nog", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nor", iso := "nor", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "nbd", iso := "dgl", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nun", iso := "nut", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nyl", iso := "yly", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "occ", iso := "oci", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ojm", iso := "ciw", value := .others }
  , { walsCode := "oya", iso := "ory", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "orh", iso := "hae", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "owc", iso := "gaz", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "oss", iso := "oss", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "pak", iso := "pkn", value := .others }
  , { walsCode := "pan", iso := "pan", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "psh", iso := "pst", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "psm", iso := "pqm", value := .others }
  , { walsCode := "prs", iso := "pes", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "poh", iso := "pon", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "pol", iso := "pol", value := .others }
  , { walsCode := "por", iso := "por", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "pro", iso := "oci", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "qaf", iso := "aar", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "qay", iso := "quy", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ren", iso := "rel", value := .others }
  , { walsCode := "rbg", iso := "rmo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "rka", iso := "rmy", value := .others }
  , { walsCode := "rlo", iso := "rmy", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "rse", iso := "rmn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "rmc", iso := "roh", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "rus", iso := "rus", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "sno", iso := "sme", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "san", iso := "sag", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "scr", iso := "hbs", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ses", iso := "sot", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ssh", iso := "bwo", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "sdh", iso := "snd", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "snh", iso := "sin", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "svk", iso := "slk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "slo", iso := "slv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "som", iso := "som", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "snn", iso := "snk", value := .others }
  , { walsCode := "spa", iso := "spa", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "sra", iso := "srn", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "sun", iso := "sun", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "swa", iso := "swh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "swe", iso := "swe", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "tag", iso := "tgl", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tah", iso := "tah", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "taj", iso := "tgk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tvo", iso := "tat", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tel", iso := "tel", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "tha", iso := "tha", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tib", iso := "bod", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tiw", iso := "tiw", value := .others }
  , { walsCode := "tsw", iso := "tsn", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "tun", iso := "tun", value := .others }
  , { walsCode := "tur", iso := "tur", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tkm", iso := "tuk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tuv", iso := "tyv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "udm", iso := "udm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ukr", iso := "ukr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "uyg", iso := "uig", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "uzb", iso := "", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "vie", iso := "vie", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "wam", iso := "wmb", value := .others }
  , { walsCode := "wel", iso := "cym", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "wlo", iso := "wlo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "wlf", iso := "wol", value := .others }
  , { walsCode := "xho", iso := "xho", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ykt", iso := "sah", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "yms", iso := "jnj", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "yor", iso := "yor", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ypk", iso := "esu", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "zar", iso := "dje", value := .others }
  , { walsCode := "zqc", iso := "zoc", value := .others }
  , { walsCode := "zul", iso := "zul", value := .others }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F138A
