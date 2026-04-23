import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 121A: Comparative Constructions
@cite{stassen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 121A`.

Chapter 121, 167 languages.
-/

namespace Datasets.WALS.F121A

/-- WALS 121A values. -/
inductive ComparativeType where
  /-- Locational (78 languages). -/
  | locational
  /-- Exceed (33 languages). -/
  | exceed
  /-- Conjoined (34 languages). -/
  | conjoined
  /-- Particle (22 languages). -/
  | particle
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 121A dataset (167 languages). -/
def allData : List (Datapoint ComparativeType) :=
  [ { walsCode := "abi", iso := "axb", value := .conjoined }
  , { walsCode := "alb", iso := "sqi", value := .particle }
  , { walsCode := "ale", iso := "ale", value := .locational }
  , { walsCode := "ame", iso := "aey", value := .exceed }
  , { walsCode := "amh", iso := "amh", value := .locational }
  , { walsCode := "adk", iso := "ano", value := .locational }
  , { walsCode := "apl", iso := "apy", value := .conjoined }
  , { walsCode := "arg", iso := "afb", value := .locational }
  , { walsCode := "ams", iso := "arb", value := .locational }
  , { walsCode := "amr", iso := "ary", value := .locational }
  , { walsCode := "arp", iso := "ape", value := .conjoined }
  , { walsCode := "amp", iso := "aer", value := .locational }
  , { walsCode := "aym", iso := "ayr", value := .locational }
  , { walsCode := "bgi", iso := "bgq", value := .locational }
  , { walsCode := "bar", iso := "bfa", value := .exceed }
  , { walsCode := "bae", iso := "bae", value := .locational }
  , { walsCode := "bsq", iso := "eus", value := .particle }
  , { walsCode := "bto", iso := "bbc", value := .particle }
  , { walsCode := "bma", iso := "tzm", value := .locational }
  , { walsCode := "bln", iso := "byn", value := .locational }
  , { walsCode := "biu", iso := "", value := .conjoined }
  , { walsCode := "bre", iso := "bre", value := .locational }
  , { walsCode := "brm", iso := "mya", value := .locational }
  , { walsCode := "bur", iso := "bsk", value := .locational }
  , { walsCode := "car", iso := "car", value := .locational }
  , { walsCode := "ceb", iso := "ceb", value := .locational }
  , { walsCode := "cic", iso := "nya", value := .exceed }
  , { walsCode := "chk", iso := "ckt", value := .locational }
  , { walsCode := "coe", iso := "crd", value := .locational }
  , { walsCode := "cmn", iso := "com", value := .particle }
  , { walsCode := "dga", iso := "dga", value := .exceed }
  , { walsCode := "dgb", iso := "dag", value := .exceed }
  , { walsCode := "dua", iso := "dua", value := .exceed }
  , { walsCode := "dut", iso := "nld", value := .particle }
  , { walsCode := "eka", iso := "ekg", value := .conjoined }
  , { walsCode := "eng", iso := "eng", value := .particle }
  , { walsCode := "evn", iso := "eve", value := .locational }
  , { walsCode := "eve", iso := "evn", value := .locational }
  , { walsCode := "fin", iso := "fin", value := .particle }
  , { walsCode := "fre", iso := "fra", value := .particle }
  , { walsCode := "fus", iso := "fuc", value := .exceed }
  , { walsCode := "gae", iso := "gla", value := .particle }
  , { walsCode := "gbb", iso := "gbp", value := .exceed }
  , { walsCode := "geo", iso := "kat", value := .locational }
  , { walsCode := "goa", iso := "guc", value := .particle }
  , { walsCode := "grk", iso := "ell", value := .particle }
  , { walsCode := "grw", iso := "kal", value := .locational }
  , { walsCode := "gua", iso := "gug", value := .locational }
  , { walsCode := "gum", iso := "kgs", value := .conjoined }
  , { walsCode := "hau", iso := "hau", value := .exceed }
  , { walsCode := "heb", iso := "heb", value := .locational }
  , { walsCode := "hin", iso := "hin", value := .locational }
  , { walsCode := "hix", iso := "hix", value := .conjoined }
  , { walsCode := "hun", iso := "hun", value := .particle }
  , { walsCode := "hzb", iso := "huz", value := .locational }
  , { walsCode := "igb", iso := "ibo", value := .exceed }
  , { walsCode := "ilo", iso := "ilo", value := .particle }
  , { walsCode := "iri", iso := "gle", value := .particle }
  , { walsCode := "jab", iso := "jae", value := .conjoined }
  , { walsCode := "jak", iso := "jac", value := .locational }
  , { walsCode := "jpn", iso := "jpn", value := .locational }
  , { walsCode := "jav", iso := "jav", value := .particle }
  , { walsCode := "kbl", iso := "kab", value := .locational }
  , { walsCode := "kms", iso := "xas", value := .locational }
  , { walsCode := "kan", iso := "ogo", value := .exceed }
  , { walsCode := "knr", iso := "knc", value := .locational }
  , { walsCode := "kas", iso := "kas", value := .locational }
  , { walsCode := "kyp", iso := "txu", value := .conjoined }
  , { walsCode := "kem", iso := "ahg", value := .locational }
  , { walsCode := "khk", iso := "kjh", value := .locational }
  , { walsCode := "kha", iso := "khk", value := .locational }
  , { walsCode := "khm", iso := "khm", value := .exceed }
  , { walsCode := "klw", iso := "klb", value := .conjoined }
  , { walsCode := "kob", iso := "kpw", value := .conjoined }
  , { walsCode := "koi", iso := "kbk", value := .conjoined }
  , { walsCode := "kor", iso := "kor", value := .locational }
  , { walsCode := "kfe", iso := "kfz", value := .exceed }
  , { walsCode := "kro", iso := "kgo", value := .locational }
  , { walsCode := "kug", iso := "cmn", value := .exceed }
  , { walsCode := "lkt", iso := "lkt", value := .conjoined }
  , { walsCode := "lat", iso := "lav", value := .particle }
  , { walsCode := "laz", iso := "lzz", value := .locational }
  , { walsCode := "lez", iso := "lez", value := .locational }
  , { walsCode := "lim", iso := "lif", value := .locational }
  , { walsCode := "lnd", iso := "liy", value := .exceed }
  , { walsCode := "lin", iso := "lin", value := .exceed }
  , { walsCode := "maa", iso := "mas", value := .locational }
  , { walsCode := "mal", iso := "plt", value := .particle }
  , { walsCode := "mlt", iso := "mlt", value := .locational }
  , { walsCode := "mnc", iso := "mnc", value := .locational }
  , { walsCode := "mnd", iso := "cmn", value := .exceed }
  , { walsCode := "myi", iso := "mpc", value := .conjoined }
  , { walsCode := "maw", iso := "mlq", value := .locational }
  , { walsCode := "mao", iso := "mri", value := .conjoined }
  , { walsCode := "map", iso := "arn", value := .locational }
  , { walsCode := "mhi", iso := "mar", value := .locational }
  , { walsCode := "mrg", iso := "mrt", value := .exceed }
  , { walsCode := "mby", iso := "myb", value := .exceed }
  , { walsCode := "men", iso := "mez", value := .conjoined }
  , { walsCode := "mis", iso := "miq", value := .conjoined }
  , { walsCode := "mss", iso := "skd", value := .locational }
  , { walsCode := "mxa", iso := "mib", value := .conjoined }
  , { walsCode := "mbo", iso := "mxk", value := .conjoined }
  , { walsCode := "mtu", iso := "meu", value := .conjoined }
  , { walsCode := "mna", iso := "mnb", value := .conjoined }
  , { walsCode := "mun", iso := "unr", value := .locational }
  , { walsCode := "ngt", iso := "nmf", value := .locational }
  , { walsCode := "kho", iso := "naq", value := .locational }
  , { walsCode := "nan", iso := "niq", value := .exceed }
  , { walsCode := "nav", iso := "nav", value := .locational }
  , { walsCode := "ntu", iso := "yrk", value := .locational }
  , { walsCode := "ngu", iso := "llp", value := .exceed }
  , { walsCode := "nue", iso := "nus", value := .locational }
  , { walsCode := "nug", iso := "nuy", value := .conjoined }
  , { walsCode := "ood", iso := "ood", value := .particle }
  , { walsCode := "obg", iso := "ogu", value := .exceed }
  , { walsCode := "pal", iso := "pau", value := .locational }
  , { walsCode := "ptp", iso := "gfk", value := .conjoined }
  , { walsCode := "pau", iso := "pad", value := .conjoined }
  , { walsCode := "prh", iso := "myp", value := .conjoined }
  , { walsCode := "pir", iso := "pib", value := .locational }
  , { walsCode := "pur", iso := "tsz", value := .locational }
  , { walsCode := "qcu", iso := "quz", value := .locational }
  , { walsCode := "qim", iso := "qvi", value := .locational }
  , { walsCode := "rap", iso := "rap", value := .locational }
  , { walsCode := "rem", iso := "bfw", value := .locational }
  , { walsCode := "rnd", iso := "run", value := .exceed }
  , { walsCode := "rus", iso := "rus", value := .particle }
  , { walsCode := "sal", iso := "sln", value := .locational }
  , { walsCode := "sam", iso := "smo", value := .conjoined }
  , { walsCode := "stl", iso := "sat", value := .locational }
  , { walsCode := "sap", iso := "spu", value := .exceed }
  , { walsCode := "shk", iso := "shp", value := .conjoined }
  , { walsCode := "shn", iso := "sna", value := .exceed }
  , { walsCode := "sik", iso := "ski", value := .conjoined }
  , { walsCode := "siu", iso := "sis", value := .locational }
  , { walsCode := "stn", iso := "nso", value := .exceed }
  , { walsCode := "spa", iso := "spa", value := .particle }
  , { walsCode := "sra", iso := "srn", value := .particle }
  , { walsCode := "swa", iso := "swh", value := .exceed }
  , { walsCode := "taj", iso := "tgk", value := .locational }
  , { walsCode := "taz", iso := "tly", value := .locational }
  , { walsCode := "tml", iso := "tam", value := .locational }
  , { walsCode := "tel", iso := "tel", value := .locational }
  , { walsCode := "tha", iso := "tha", value := .exceed }
  , { walsCode := "tug", iso := "thv", value := .locational }
  , { walsCode := "tbu", iso := "", value := .locational }
  , { walsCode := "tup", iso := "tpn", value := .locational }
  , { walsCode := "tur", iso := "tur", value := .locational }
  , { walsCode := "tvl", iso := "tvl", value := .locational }
  , { walsCode := "tuv", iso := "tyv", value := .locational }
  , { walsCode := "tsh", iso := "par", value := .particle }
  , { walsCode := "uby", iso := "uby", value := .locational }
  , { walsCode := "udm", iso := "udm", value := .locational }
  , { walsCode := "urk", iso := "urb", value := .conjoined }
  , { walsCode := "uzb", iso := "", value := .locational }
  , { walsCode := "vie", iso := "vie", value := .exceed }
  , { walsCode := "wrk", iso := "gae", value := .conjoined }
  , { walsCode := "war", iso := "pav", value := .conjoined }
  , { walsCode := "wlf", iso := "wol", value := .exceed }
  , { walsCode := "yag", iso := "yad", value := .conjoined }
  , { walsCode := "yah", iso := "yag", value := .exceed }
  , { walsCode := "yap", iso := "yap", value := .locational }
  , { walsCode := "yav", iso := "yuf", value := .conjoined }
  , { walsCode := "yin", iso := "yij", value := .conjoined }
  , { walsCode := "yor", iso := "yor", value := .exceed }
  , { walsCode := "zul", iso := "zul", value := .exceed }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F121A
