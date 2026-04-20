import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 54A: Distributive Numerals
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 54A`.

Chapter 54, 251 languages.
-/

namespace Core.WALS.F54A

/-- WALS 54A values. -/
inductive DistributiveNumerals where
  /-- No distributive numerals (62 languages). -/
  | noDistributiveNumerals
  /-- Marked by reduplication (85 languages). -/
  | markedByReduplication
  /-- Marked by prefix (23 languages). -/
  | markedByPrefix
  /-- Marked by suffix (32 languages). -/
  | markedBySuffix
  /-- Marked by preceding word (21 languages). -/
  | markedByPrecedingWord
  /-- Marked by following word (5 languages). -/
  | markedByFollowingWord
  /-- Marked by mixed or other strategies (23 languages). -/
  | markedByMixedOrOtherStrategies
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 54A dataset (251 languages). -/
def allData : List (Datapoint DistributiveNumerals) :=
  [ { walsCode := "abk", iso := "abk", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "afr", iso := "afr", value := .noDistributiveNumerals }
  , { walsCode := "agl", iso := "agx", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ain", iso := "ain", value := .markedByFollowingWord }
  , { walsCode := "akn", iso := "aka", value := .markedByReduplication }
  , { walsCode := "alx", iso := "btz", value := .markedByReduplication }
  , { walsCode := "alb", iso := "sqi", value := .markedByPrecedingWord }
  , { walsCode := "ale", iso := "ale", value := .markedBySuffix }
  , { walsCode := "aml", iso := "omb", value := .markedByReduplication }
  , { walsCode := "ame", iso := "aey", value := .noDistributiveNumerals }
  , { walsCode := "amh", iso := "amh", value := .markedByReduplication }
  , { walsCode := "ami", iso := "ami", value := .noDistributiveNumerals }
  , { walsCode := "anx", iso := "ani", value := .markedByReduplication }
  , { walsCode := "agm", iso := "njm", value := .markedByReduplication }
  , { walsCode := "aeg", iso := "arz", value := .noDistributiveNumerals }
  , { walsCode := "ako", iso := "acy", value := .noDistributiveNumerals }
  , { walsCode := "ars", iso := "ayn", value := .noDistributiveNumerals }
  , { walsCode := "arm", iso := "hye", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ass", iso := "asm", value := .markedByReduplication }
  , { walsCode := "ata", iso := "tay", value := .noDistributiveNumerals }
  , { walsCode := "bgv", iso := "kva", value := .markedByReduplication }
  , { walsCode := "bal", iso := "ban", value := .markedByReduplication }
  , { walsCode := "bsk", iso := "bak", value := .markedBySuffix }
  , { walsCode := "bsq", iso := "eus", value := .markedBySuffix }
  , { walsCode := "bat", iso := "bya", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "bkr", iso := "btx", value := .noDistributiveNumerals }
  , { walsCode := "beg", iso := "dbj", value := .noDistributiveNumerals }
  , { walsCode := "ben", iso := "ben", value := .markedByReduplication }
  , { walsCode := "bez", iso := "kap", value := .markedByReduplication }
  , { walsCode := "biq", iso := "bpr", value := .markedByPrefix }
  , { walsCode := "bkd", iso := "bkd", value := .markedByPrefix }
  , { walsCode := "bok", iso := "bqc", value := .markedByReduplication }
  , { walsCode := "btk", iso := "lbk", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "brh", iso := "brh", value := .markedByReduplication }
  , { walsCode := "bug", iso := "bug", value := .markedByPrefix }
  , { walsCode := "bul", iso := "bul", value := .markedByPrecedingWord }
  , { walsCode := "bpa", iso := "bwr", value := .markedByReduplication }
  , { walsCode := "but", iso := "bxm", value := .markedBySuffix }
  , { walsCode := "brm", iso := "mya", value := .markedBySuffix }
  , { walsCode := "bur", iso := "bsk", value := .markedByReduplication }
  , { walsCode := "cah", iso := "chl", value := .markedByReduplication }
  , { walsCode := "cnt", iso := "yue", value := .noDistributiveNumerals }
  , { walsCode := "cyv", iso := "cyb", value := .markedBySuffix }
  , { walsCode := "cha", iso := "cha", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "chx", iso := "clo", value := .noDistributiveNumerals }
  , { walsCode := "chk", iso := "ckt", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "chv", iso := "chv", value := .markedBySuffix }
  , { walsCode := "cmn", iso := "com", value := .markedByReduplication }
  , { walsCode := "cze", iso := "ces", value := .markedByPrecedingWord }
  , { walsCode := "drg", iso := "dar", value := .markedByReduplication }
  , { walsCode := "dgi", iso := "dgo", value := .markedByReduplication }
  , { walsCode := "dut", iso := "nld", value := .noDistributiveNumerals }
  , { walsCode := "dbr", iso := "nld", value := .noDistributiveNumerals }
  , { walsCode := "dli", iso := "nld", value := .noDistributiveNumerals }
  , { walsCode := "duz", iso := "zea", value := .noDistributiveNumerals }
  , { walsCode := "eng", iso := "eng", value := .noDistributiveNumerals }
  , { walsCode := "err", iso := "erg", value := .markedBySuffix }
  , { walsCode := "eve", iso := "evn", value := .markedBySuffix }
  , { walsCode := "fij", iso := "fij", value := .markedByPrefix }
  , { walsCode := "fin", iso := "fin", value := .noDistributiveNumerals }
  , { walsCode := "fox", iso := "sac", value := .markedByReduplication }
  , { walsCode := "fre", iso := "fra", value := .noDistributiveNumerals }
  , { walsCode := "fue", iso := "fud", value := .markedByPrefix }
  , { walsCode := "gag", iso := "gag", value := .markedBySuffix }
  , { walsCode := "gar", iso := "grt", value := .markedByReduplication }
  , { walsCode := "gav", iso := "gvo", value := .noDistributiveNumerals }
  , { walsCode := "geo", iso := "kat", value := .markedByReduplication }
  , { walsCode := "ger", iso := "deu", value := .markedByPrecedingWord }
  , { walsCode := "gpz", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "gba", iso := "bar", value := .noDistributiveNumerals }
  , { walsCode := "gbl", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gbe", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "gha", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gma", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gos", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "grp", iso := "ksh", value := .noDistributiveNumerals }
  , { walsCode := "gtg", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "gth", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gti", iso := "deu", value := .markedByPrecedingWord }
  , { walsCode := "gau", iso := "bar", value := .noDistributiveNumerals }
  , { walsCode := "gwe", iso := "wep", value := .noDistributiveNumerals }
  , { walsCode := "gzu", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "goo", iso := "gni", value := .noDistributiveNumerals }
  , { walsCode := "grk", iso := "ell", value := .markedByPrecedingWord }
  , { walsCode := "gdf", iso := "gdf", value := .markedByReduplication }
  , { walsCode := "ga", iso := "gaa", value := .markedByReduplication }
  , { walsCode := "hai", iso := "hai", value := .markedBySuffix }
  , { walsCode := "hnn", iso := "hnn", value := .markedByPrefix }
  , { walsCode := "hau", iso := "hau", value := .markedByReduplication }
  , { walsCode := "haw", iso := "haw", value := .markedByPrefix }
  , { walsCode := "heb", iso := "heb", value := .noDistributiveNumerals }
  , { walsCode := "hil", iso := "hil", value := .markedByPrefix }
  , { walsCode := "hin", iso := "hin", value := .markedByReduplication }
  , { walsCode := "hix", iso := "hix", value := .noDistributiveNumerals }
  , { walsCode := "hun", iso := "hun", value := .markedByReduplication }
  , { walsCode := "hzb", iso := "huz", value := .markedByReduplication }
  , { walsCode := "hpd", iso := "jup", value := .noDistributiveNumerals }
  , { walsCode := "ibn", iso := "ibg", value := .markedByPrefix }
  , { walsCode := "imo", iso := "imn", value := .noDistributiveNumerals }
  , { walsCode := "ind", iso := "ind", value := .noDistributiveNumerals }
  , { walsCode := "ing", iso := "inh", value := .markedByReduplication }
  , { walsCode := "irq", iso := "irk", value := .markedByReduplication }
  , { walsCode := "ish", iso := "isk", value := .markedBySuffix }
  , { walsCode := "isn", iso := "isd", value := .markedByPrefix }
  , { walsCode := "itu", iso := "pms", value := .noDistributiveNumerals }
  , { walsCode := "iva", iso := "ivb", value := .markedByPrefix }
  , { walsCode := "jpn", iso := "jpn", value := .markedBySuffix }
  , { walsCode := "jav", iso := "jav", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kab", iso := "kbd", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kbi", iso := "nbu", value := .markedByReduplication }
  , { walsCode := "klq", iso := "kmh", value := .noDistributiveNumerals }
  , { walsCode := "knd", iso := "kan", value := .markedByReduplication }
  , { walsCode := "kyo", iso := "kny", value := .markedByReduplication }
  , { walsCode := "kas", iso := "kas", value := .markedByReduplication }
  , { walsCode := "kay", iso := "gyd", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kef", iso := "kbr", value := .markedByReduplication }
  , { walsCode := "ket", iso := "ket", value := .markedBySuffix }
  , { walsCode := "khk", iso := "kjh", value := .markedBySuffix }
  , { walsCode := "kha", iso := "khk", value := .markedBySuffix }
  , { walsCode := "kty", iso := "kca", value := .markedBySuffix }
  , { walsCode := "khr", iso := "khr", value := .markedByReduplication }
  , { walsCode := "kmu", iso := "kjg", value := .noDistributiveNumerals }
  , { walsCode := "klv", iso := "kij", value := .noDistributiveNumerals }
  , { walsCode := "kgz", iso := "kir", value := .markedBySuffix }
  , { walsCode := "krb", iso := "gil", value := .markedByPrefix }
  , { walsCode := "kod", iso := "kfa", value := .markedByReduplication }
  , { walsCode := "koi", iso := "kbk", value := .markedByReduplication }
  , { walsCode := "kmb", iso := "", value := .noDistributiveNumerals }
  , { walsCode := "kon", iso := "kng", value := .markedByReduplication }
  , { walsCode := "kor", iso := "kor", value := .markedBySuffix }
  , { walsCode := "kku", iso := "kfq", value := .markedByReduplication }
  , { walsCode := "kch", iso := "khq", value := .markedByReduplication }
  , { walsCode := "krd", iso := "ckb", value := .markedByReduplication }
  , { walsCode := "kur", iso := "kru", value := .markedByReduplication }
  , { walsCode := "kuy", iso := "vkt", value := .markedByReduplication }
  , { walsCode := "kut", iso := "kut", value := .noDistributiveNumerals }
  , { walsCode := "kwk", iso := "kwk", value := .markedByReduplication }
  , { walsCode := "lch", iso := "lbt", value := .noDistributiveNumerals }
  , { walsCode := "lak", iso := "lbe", value := .markedByReduplication }
  , { walsCode := "lat", iso := "lav", value := .markedByPrecedingWord }
  , { walsCode := "lez", iso := "lez", value := .markedByReduplication }
  , { walsCode := "lit", iso := "lit", value := .markedByPrecedingWord }
  , { walsCode := "lov", iso := "lbo", value := .noDistributiveNumerals }
  , { walsCode := "luo", iso := "luo", value := .markedByReduplication }
  , { walsCode := "myn", iso := "mhy", value := .markedByReduplication }
  , { walsCode := "mgn", iso := "mdh", value := .markedBySuffix }
  , { walsCode := "mne", iso := "nmu", value := .markedByReduplication }
  , { walsCode := "mal", iso := "plt", value := .markedByFollowingWord }
  , { walsCode := "mmu", iso := "zmi", value := .markedByReduplication }
  , { walsCode := "mym", iso := "mal", value := .markedByReduplication }
  , { walsCode := "mnc", iso := "mnc", value := .markedBySuffix }
  , { walsCode := "mnd", iso := "cmn", value := .noDistributiveNumerals }
  , { walsCode := "mao", iso := "mri", value := .markedByPrefix }
  , { walsCode := "mhi", iso := "mar", value := .markedByReduplication }
  , { walsCode := "mrg", iso := "mrt", value := .markedByReduplication }
  , { walsCode := "mar", iso := "mrc", value := .markedBySuffix }
  , { walsCode := "msh", iso := "mah", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "mrt", iso := "vma", value := .noDistributiveNumerals }
  , { walsCode := "may", iso := "ayz", value := .noDistributiveNumerals }
  , { walsCode := "mei", iso := "mni", value := .markedByReduplication }
  , { walsCode := "mde", iso := "men", value := .markedByReduplication }
  , { walsCode := "hok", iso := "nan", value := .noDistributiveNumerals }
  , { walsCode := "min", iso := "min", value := .markedByReduplication }
  , { walsCode := "mit", iso := "zmq", value := .markedByReduplication }
  , { walsCode := "mlm", iso := "mra", value := .noDistributiveNumerals }
  , { walsCode := "moe", iso := "myv", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "mmo", iso := "mdf", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "mun", iso := "unr", value := .markedByReduplication }
  , { walsCode := "nhn", iso := "ncj", value := .markedByReduplication }
  , { walsCode := "nau", iso := "nau", value := .markedByPrefix }
  , { walsCode := "nel", iso := "nee", value := .noDistributiveNumerals }
  , { walsCode := "ntu", iso := "yrk", value := .markedBySuffix }
  , { walsCode := "nga", iso := "nio", value := .markedBySuffix }
  , { walsCode := "nia", iso := "nia", value := .markedByReduplication }
  , { walsCode := "nca", iso := "caq", value := .markedByPrefix }
  , { walsCode := "nsg", iso := "ncg", value := .markedByPrefix }
  , { walsCode := "niv", iso := "niv", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "nvs", iso := "niv", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "nbd", iso := "dgl", value := .markedByReduplication }
  , { walsCode := "nku", iso := "xnz", value := .markedByReduplication }
  , { walsCode := "nyl", iso := "yly", value := .noDistributiveNumerals }
  , { walsCode := "ork", iso := "oaa", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "oss", iso := "oss", value := .markedBySuffix }
  , { walsCode := "pte", iso := "pck", value := .markedByReduplication }
  , { walsCode := "pnn", iso := "pag", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "psh", iso := "pst", value := .markedByReduplication }
  , { walsCode := "prs", iso := "pes", value := .noDistributiveNumerals }
  , { walsCode := "pip", iso := "ppl", value := .markedByReduplication }
  , { walsCode := "pol", iso := "pol", value := .markedByPrecedingWord }
  , { walsCode := "fma", iso := "fuc", value := .noDistributiveNumerals }
  , { walsCode := "qcu", iso := "quz", value := .markedBySuffix }
  , { walsCode := "qhu", iso := "qub", value := .markedByFollowingWord }
  , { walsCode := "ren", iso := "rel", value := .markedByReduplication }
  , { walsCode := "rom", iso := "ron", value := .markedByPrecedingWord }
  , { walsCode := "rot", iso := "rtm", value := .noDistributiveNumerals }
  , { walsCode := "rru", iso := "nyo", value := .markedByReduplication }
  , { walsCode := "rus", iso := "rus", value := .markedByPrecedingWord }
  , { walsCode := "ski", iso := "sjd", value := .markedByReduplication }
  , { walsCode := "slr", iso := "slr", value := .noDistributiveNumerals }
  , { walsCode := "sam", iso := "smo", value := .markedByPrefix }
  , { walsCode := "stl", iso := "sat", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "skp", iso := "sel", value := .markedByFollowingWord }
  , { walsCode := "sml", iso := "sza", value := .noDistributiveNumerals }
  , { walsCode := "ssh", iso := "bwo", value := .markedByReduplication }
  , { walsCode := "shk", iso := "shp", value := .noDistributiveNumerals }
  , { walsCode := "sdh", iso := "snd", value := .markedByReduplication }
  , { walsCode := "spa", iso := "spa", value := .noDistributiveNumerals }
  , { walsCode := "sup", iso := "spp", value := .markedByReduplication }
  , { walsCode := "swa", iso := "swh", value := .markedByReduplication }
  , { walsCode := "tag", iso := "tgl", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "tgb", iso := "tbw", value := .markedByPrefix }
  , { walsCode := "tml", iso := "tam", value := .markedByReduplication }
  , { walsCode := "tvo", iso := "tat", value := .markedBySuffix }
  , { walsCode := "tsg", iso := "tsg", value := .markedByReduplication }
  , { walsCode := "taw", iso := "tbo", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "tpn", iso := "ntp", value := .markedByReduplication }
  , { walsCode := "ttn", iso := "tet", value := .markedByReduplication }
  , { walsCode := "thd", iso := "tcz", value := .markedByReduplication }
  , { walsCode := "tha", iso := "tha", value := .noDistributiveNumerals }
  , { walsCode := "tib", iso := "bod", value := .markedByReduplication }
  , { walsCode := "tiw", iso := "tiw", value := .markedBySuffix }
  , { walsCode := "tla", iso := "ksd", value := .markedByReduplication }
  , { walsCode := "tng", iso := "ton", value := .markedByPrefix }
  , { walsCode := "tsa", iso := "tkr", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "tsi", iso := "tsi", value := .markedByPrefix }
  , { walsCode := "tso", iso := "tsu", value := .markedByPrefix }
  , { walsCode := "tuk", iso := "", value := .noDistributiveNumerals }
  , { walsCode := "tur", iso := "tur", value := .markedBySuffix }
  , { walsCode := "tvl", iso := "tvl", value := .markedByPrecedingWord }
  , { walsCode := "tuv", iso := "tyv", value := .markedByReduplication }
  , { walsCode := "udh", iso := "ude", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ukr", iso := "ukr", value := .markedByPrecedingWord }
  , { walsCode := "uyg", iso := "uig", value := .markedBySuffix }
  , { walsCode := "vie", iso := "vie", value := .noDistributiveNumerals }
  , { walsCode := "wai", iso := "waw", value := .markedByFollowingWord }
  , { walsCode := "wll", iso := "wls", value := .markedByPrefix }
  , { walsCode := "wra", iso := "wba", value := .noDistributiveNumerals }
  , { walsCode := "war", iso := "pav", value := .noDistributiveNumerals }
  , { walsCode := "was", iso := "was", value := .markedByReduplication }
  , { walsCode := "wly", iso := "wal", value := .markedByReduplication }
  , { walsCode := "ygn", iso := "yai", value := .markedBySuffix }
  , { walsCode := "ykt", iso := "sah", value := .markedBySuffix }
  , { walsCode := "ymi", iso := "tao", value := .markedByPrefix }
  , { walsCode := "yms", iso := "jnj", value := .markedByReduplication }
  , { walsCode := "yes", iso := "yss", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ydb", iso := "ydd", value := .markedByPrecedingWord }
  , { walsCode := "ylt", iso := "ydd", value := .markedByPrecedingWord }
  , { walsCode := "ydl", iso := "ydd", value := .markedByPrecedingWord }
  , { walsCode := "yim", iso := "yee", value := .noDistributiveNumerals }
  , { walsCode := "yor", iso := "yor", value := .markedByReduplication }
  , { walsCode := "yko", iso := "yux", value := .noDistributiveNumerals }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F54A
