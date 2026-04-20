import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 53A: Ordinal Numerals
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 53A`.

Chapter 53, 321 languages.
-/

namespace Core.WALS.F53A

/-- WALS 53A values. -/
inductive OrdinalNumerals where
  /-- None (33 languages). -/
  | none
  /-- One, two, three (3 languages). -/
  | oneTwoThree
  /-- First, two, three (12 languages). -/
  | firstTwoThree
  /-- One-th, two-th, three-th (41 languages). -/
  | oneThTwoThThreeTh
  /-- First/one-th, two-th, three-th (54 languages). -/
  | firstOneThTwoThThreeTh
  /-- First, two-th, three-th (110 languages). -/
  | firstTwoThThreeTh
  /-- First, second, three-th (61 languages). -/
  | firstSecondThreeTh
  /-- Various (7 languages). -/
  | various
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 53A dataset (321 languages). -/
def allData : List (Datapoint OrdinalNumerals) :=
  [ { walsCode := "xoo", iso := "nmn", value := .none }
  , { walsCode := "abk", iso := "abk", value := .firstOneThTwoThThreeTh }
  , { walsCode := "aci", iso := "acr", value := .firstTwoThThreeTh }
  , { walsCode := "aco", iso := "kjq", value := .firstOneThTwoThThreeTh }
  , { walsCode := "afr", iso := "afr", value := .firstTwoThThreeTh }
  , { walsCode := "ain", iso := "ain", value := .none }
  , { walsCode := "ala", iso := "amp", value := .firstTwoThThreeTh }
  , { walsCode := "alb", iso := "sqi", value := .firstTwoThThreeTh }
  , { walsCode := "ale", iso := "ale", value := .firstTwoThThreeTh }
  , { walsCode := "ame", iso := "aey", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ago", iso := "aoa", value := .firstTwoThree }
  , { walsCode := "apu", iso := "apu", value := .none }
  , { walsCode := "abn", iso := "ard", value := .none }
  , { walsCode := "aeg", iso := "arz", value := .firstTwoThThreeTh }
  , { walsCode := "arg", iso := "afb", value := .firstTwoThThreeTh }
  , { walsCode := "amr", iso := "ary", value := .firstSecondThreeTh }
  , { walsCode := "arp", iso := "ape", value := .none }
  , { walsCode := "arm", iso := "hye", value := .firstTwoThThreeTh }
  , { walsCode := "arw", iso := "hyw", value := .firstTwoThThreeTh }
  , { walsCode := "ava", iso := "ava", value := .oneThTwoThThreeTh }
  , { walsCode := "awp", iso := "kwi", value := .none }
  , { walsCode := "awt", iso := "kmn", value := .none }
  , { walsCode := "aym", iso := "ayr", value := .firstTwoThree }
  , { walsCode := "aze", iso := "", value := .firstOneThTwoThThreeTh }
  , { walsCode := "bak", iso := "bkc", value := .firstTwoThThreeTh }
  , { walsCode := "bam", iso := "bam", value := .firstTwoThThreeTh }
  , { walsCode := "bnk", iso := "abb", value := .firstTwoThThreeTh }
  , { walsCode := "brs", iso := "bsn", value := .none }
  , { walsCode := "bsk", iso := "bak", value := .oneThTwoThThreeTh }
  , { walsCode := "bsq", iso := "eus", value := .firstTwoThThreeTh }
  , { walsCode := "blr", iso := "bel", value := .firstSecondThreeTh }
  , { walsCode := "ben", iso := "ben", value := .firstTwoThThreeTh }
  , { walsCode := "bma", iso := "tzm", value := .firstTwoThThreeTh }
  , { walsCode := "bsm", iso := "bis", value := .firstOneThTwoThThreeTh }
  , { walsCode := "bla", iso := "bla", value := .firstTwoThThreeTh }
  , { walsCode := "brh", iso := "brh", value := .firstOneThTwoThThreeTh }
  , { walsCode := "bre", iso := "bre", value := .firstSecondThreeTh }
  , { walsCode := "bub", iso := "bvb", value := .firstTwoThree }
  , { walsCode := "bul", iso := "bul", value := .firstSecondThreeTh }
  , { walsCode := "brm", iso := "mya", value := .various }
  , { walsCode := "bur", iso := "bsk", value := .firstTwoThThreeTh }
  , { walsCode := "cah", iso := "chl", value := .firstOneThTwoThThreeTh }
  , { walsCode := "cak", iso := "cak", value := .firstTwoThThreeTh }
  , { walsCode := "cnl", iso := "ram", value := .none }
  , { walsCode := "cnt", iso := "yue", value := .oneThTwoThThreeTh }
  , { walsCode := "car", iso := "car", value := .oneThTwoThThreeTh }
  , { walsCode := "ctl", iso := "cat", value := .firstSecondThreeTh }
  , { walsCode := "cyv", iso := "cyb", value := .none }
  , { walsCode := "ceb", iso := "ceb", value := .firstTwoThThreeTh }
  , { walsCode := "cha", iso := "cha", value := .firstTwoThThreeTh }
  , { walsCode := "cle", iso := "cle", value := .none }
  , { walsCode := "crg", iso := "gui", value := .firstSecondThreeTh }
  , { walsCode := "cch", iso := "coz", value := .firstTwoThThreeTh }
  , { walsCode := "col", iso := "ctu", value := .firstTwoThThreeTh }
  , { walsCode := "coi", iso := "caa", value := .firstSecondThreeTh }
  , { walsCode := "chk", iso := "ckt", value := .firstOneThTwoThThreeTh }
  , { walsCode := "chv", iso := "chv", value := .oneThTwoThThreeTh }
  , { walsCode := "cog", iso := "kog", value := .various }
  , { walsCode := "cop", iso := "cop", value := .firstTwoThThreeTh }
  , { walsCode := "cor", iso := "crn", value := .oneThTwoThThreeTh }
  , { walsCode := "cze", iso := "ces", value := .firstSecondThreeTh }
  , { walsCode := "cem", iso := "cam", value := .oneThTwoThThreeTh }
  , { walsCode := "dsh", iso := "dan", value := .firstSecondThreeTh }
  , { walsCode := "dio", iso := "dyo", value := .firstTwoThThreeTh }
  , { walsCode := "dre", iso := "dhv", value := .firstTwoThThreeTh }
  , { walsCode := "dua", iso := "dua", value := .firstTwoThThreeTh }
  , { walsCode := "dmi", iso := "dus", value := .none }
  , { walsCode := "dut", iso := "nld", value := .firstTwoThThreeTh }
  , { walsCode := "eng", iso := "eng", value := .firstSecondThreeTh }
  , { walsCode := "est", iso := "ekk", value := .firstSecondThreeTh }
  , { walsCode := "evn", iso := "eve", value := .firstOneThTwoThThreeTh }
  , { walsCode := "eve", iso := "evn", value := .firstSecondThreeTh }
  , { walsCode := "ewe", iso := "ewe", value := .firstTwoThThreeTh }
  , { walsCode := "ewo", iso := "ewo", value := .firstTwoThThreeTh }
  , { walsCode := "far", iso := "fao", value := .firstSecondThreeTh }
  , { walsCode := "fij", iso := "fij", value := .firstTwoThThreeTh }
  , { walsCode := "fin", iso := "fin", value := .firstSecondThreeTh }
  , { walsCode := "fre", iso := "fra", value := .firstSecondThreeTh }
  , { walsCode := "fea", iso := "frs", value := .firstTwoThThreeTh }
  , { walsCode := "fno", iso := "frr", value := .firstSecondThreeTh }
  , { walsCode := "frw", iso := "fry", value := .firstTwoThThreeTh }
  , { walsCode := "fni", iso := "fuv", value := .firstTwoThThreeTh }
  , { walsCode := "gae", iso := "gla", value := .firstTwoThThreeTh }
  , { walsCode := "glc", iso := "glg", value := .firstSecondThreeTh }
  , { walsCode := "gar", iso := "grt", value := .firstOneThTwoThThreeTh }
  , { walsCode := "grf", iso := "cab", value := .firstTwoThThreeTh }
  , { walsCode := "geo", iso := "kat", value := .firstTwoThThreeTh }
  , { walsCode := "ger", iso := "deu", value := .firstTwoThThreeTh }
  , { walsCode := "goa", iso := "guc", value := .firstTwoThree }
  , { walsCode := "gol", iso := "gol", value := .firstTwoThThreeTh }
  , { walsCode := "goo", iso := "gni", value := .none }
  , { walsCode := "grb", iso := "grj", value := .firstTwoThThreeTh }
  , { walsCode := "grk", iso := "ell", value := .firstSecondThreeTh }
  , { walsCode := "gre", iso := "kal", value := .firstSecondThreeTh }
  , { walsCode := "grw", iso := "kal", value := .firstSecondThreeTh }
  , { walsCode := "gua", iso := "gug", value := .firstOneThTwoThThreeTh }
  , { walsCode := "gbc", iso := "pov", value := .firstSecondThreeTh }
  , { walsCode := "guj", iso := "guj", value := .firstTwoThThreeTh }
  , { walsCode := "grn", iso := "gur", value := .firstTwoThThreeTh }
  , { walsCode := "hcr", iso := "hat", value := .firstTwoThThreeTh }
  , { walsCode := "hau", iso := "hau", value := .firstTwoThThreeTh }
  , { walsCode := "haw", iso := "haw", value := .firstOneThTwoThThreeTh }
  , { walsCode := "heb", iso := "heb", value := .firstTwoThThreeTh }
  , { walsCode := "her", iso := "her", value := .firstTwoThThreeTh }
  , { walsCode := "hin", iso := "hin", value := .firstTwoThThreeTh }
  , { walsCode := "hix", iso := "hix", value := .none }
  , { walsCode := "hop", iso := "hop", value := .oneThTwoThThreeTh }
  , { walsCode := "hun", iso := "hun", value := .firstSecondThreeTh }
  , { walsCode := "hzb", iso := "huz", value := .oneThTwoThThreeTh }
  , { walsCode := "ice", iso := "isl", value := .firstSecondThreeTh }
  , { walsCode := "igb", iso := "ibo", value := .firstTwoThThreeTh }
  , { walsCode := "ika", iso := "arh", value := .none }
  , { walsCode := "imo", iso := "imn", value := .none }
  , { walsCode := "ind", iso := "ind", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ing", iso := "inh", value := .firstTwoThThreeTh }
  , { walsCode := "irq", iso := "irk", value := .firstTwoThree }
  , { walsCode := "iri", iso := "gle", value := .firstSecondThreeTh }
  , { walsCode := "ita", iso := "ita", value := .firstSecondThreeTh }
  , { walsCode := "ite", iso := "itl", value := .firstSecondThreeTh }
  , { walsCode := "ixi", iso := "ixl", value := .firstTwoThThreeTh }
  , { walsCode := "izh", iso := "izh", value := .firstSecondThreeTh }
  , { walsCode := "jak", iso := "jac", value := .firstOneThTwoThThreeTh }
  , { walsCode := "jpn", iso := "jpn", value := .oneThTwoThThreeTh }
  , { walsCode := "kek", iso := "kek", value := .firstTwoThThreeTh }
  , { walsCode := "kmk", iso := "xal", value := .oneThTwoThThreeTh }
  , { walsCode := "kms", iso := "xas", value := .firstTwoThThreeTh }
  , { walsCode := "kwe", iso := "knj", value := .firstTwoThThreeTh }
  , { walsCode := "knd", iso := "kan", value := .firstOneThTwoThThreeTh }
  , { walsCode := "knr", iso := "knc", value := .firstOneThTwoThThreeTh }
  , { walsCode := "krl", iso := "krl", value := .firstSecondThreeTh }
  , { walsCode := "kas", iso := "kas", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ksu", iso := "csb", value := .firstSecondThreeTh }
  , { walsCode := "kay", iso := "gyd", value := .none }
  , { walsCode := "kaz", iso := "kaz", value := .oneThTwoThThreeTh }
  , { walsCode := "ker", iso := "ker", value := .firstTwoThThreeTh }
  , { walsCode := "ket", iso := "ket", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kew", iso := "kew", value := .various }
  , { walsCode := "kha", iso := "khk", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kty", iso := "kca", value := .firstSecondThreeTh }
  , { walsCode := "khs", iso := "kha", value := .firstTwoThThreeTh }
  , { walsCode := "khm", iso := "khm", value := .oneThTwoThThreeTh }
  , { walsCode := "klv", iso := "kij", value := .various }
  , { walsCode := "kgz", iso := "kir", value := .oneThTwoThThreeTh }
  , { walsCode := "kis", iso := "kss", value := .firstTwoThThreeTh }
  , { walsCode := "koa", iso := "cku", value := .firstTwoThThreeTh }
  , { walsCode := "kob", iso := "kpw", value := .none }
  , { walsCode := "kod", iso := "kfa", value := .oneThTwoThThreeTh }
  , { walsCode := "koi", iso := "kbk", value := .none }
  , { walsCode := "kzy", iso := "kpv", value := .firstSecondThreeTh }
  , { walsCode := "kor", iso := "kor", value := .oneThTwoThThreeTh }
  , { walsCode := "ktt", iso := "", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kse", iso := "ses", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kpe", iso := "xpe", value := .oneTwoThree }
  , { walsCode := "kro", iso := "kgo", value := .oneTwoThree }
  , { walsCode := "knm", iso := "kun", value := .firstTwoThThreeTh }
  , { walsCode := "kug", iso := "cmn", value := .oneThTwoThThreeTh }
  , { walsCode := "kuo", iso := "kto", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kji", iso := "kmr", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kur", iso := "kru", value := .firstTwoThThreeTh }
  , { walsCode := "kuv", iso := "kxv", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kwr", iso := "tnk", value := .oneThTwoThThreeTh }
  , { walsCode := "kwm", iso := "ksq", value := .firstOneThTwoThThreeTh }
  , { walsCode := "lad", iso := "lbj", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ldn", iso := "lld", value := .firstSecondThreeTh }
  , { walsCode := "lno", iso := "lad", value := .firstSecondThreeTh }
  , { walsCode := "lkt", iso := "lkt", value := .firstTwoThThreeTh }
  , { walsCode := "lan", iso := "laj", value := .firstTwoThree }
  , { walsCode := "lat", iso := "lav", value := .firstSecondThreeTh }
  , { walsCode := "les", iso := "les", value := .firstTwoThThreeTh }
  , { walsCode := "lez", iso := "lez", value := .oneThTwoThThreeTh }
  , { walsCode := "lim", iso := "lif", value := .none }
  , { walsCode := "lit", iso := "lit", value := .firstSecondThreeTh }
  , { walsCode := "liv", iso := "liv", value := .firstSecondThreeTh }
  , { walsCode := "lge", iso := "nds", value := .firstTwoThThreeTh }
  , { walsCode := "luo", iso := "luo", value := .firstOneThTwoThThreeTh }
  , { walsCode := "luv", iso := "lue", value := .firstTwoThThreeTh }
  , { walsCode := "mcd", iso := "mkd", value := .firstSecondThreeTh }
  , { walsCode := "mac", iso := "mbc", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mlc", iso := "mcm", value := .oneThTwoThThreeTh }
  , { walsCode := "mal", iso := "plt", value := .firstTwoThThreeTh }
  , { walsCode := "mly", iso := "zsm", value := .firstTwoThThreeTh }
  , { walsCode := "mym", iso := "mal", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mlt", iso := "mlt", value := .firstTwoThThreeTh }
  , { walsCode := "mam", iso := "mam", value := .firstTwoThThreeTh }
  , { walsCode := "mmv", iso := "mdi", value := .firstTwoThThreeTh }
  , { walsCode := "mnc", iso := "mnc", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mnd", iso := "cmn", value := .oneThTwoThThreeTh }
  , { walsCode := "myi", iso := "mpc", value := .none }
  , { walsCode := "maw", iso := "mlq", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mjk", iso := "mfv", value := .firstTwoThThreeTh }
  , { walsCode := "mns", iso := "mns", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mao", iso := "mri", value := .oneThTwoThThreeTh }
  , { walsCode := "map", iso := "arn", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mra", iso := "mec", value := .none }
  , { walsCode := "mah", iso := "mrj", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mrd", iso := "mrz", value := .none }
  , { walsCode := "msh", iso := "mah", value := .oneThTwoThThreeTh }
  , { walsCode := "mqc", iso := "gcf", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mrt", iso := "vma", value := .none }
  , { walsCode := "msl", iso := "mls", value := .firstTwoThThreeTh }
  , { walsCode := "may", iso := "ayz", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mzc", iso := "maq", value := .firstTwoThThreeTh }
  , { walsCode := "mei", iso := "mni", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mss", iso := "skd", value := .firstSecondThreeTh }
  , { walsCode := "mxa", iso := "mib", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mxc", iso := "mig", value := .none }
  , { walsCode := "mun", iso := "unr", value := .firstTwoThree }
  , { walsCode := "mup", iso := "sur", value := .oneThTwoThThreeTh }
  , { walsCode := "kho", iso := "naq", value := .firstTwoThThreeTh }
  , { walsCode := "nan", iso := "niq", value := .firstTwoThThreeTh }
  , { walsCode := "nav", iso := "nav", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ndy", iso := "djk", value := .firstTwoThThreeTh }
  , { walsCode := "ntu", iso := "yrk", value := .firstSecondThreeTh }
  , { walsCode := "nez", iso := "nez", value := .firstTwoThThreeTh }
  , { walsCode := "nti", iso := "niy", value := .firstTwoThThreeTh }
  , { walsCode := "ngi", iso := "wyb", value := .none }
  , { walsCode := "niv", iso := "niv", value := .firstTwoThree }
  , { walsCode := "nob", iso := "fia", value := .firstTwoThThreeTh }
  , { walsCode := "nog", iso := "nog", value := .firstOneThTwoThThreeTh }
  , { walsCode := "nor", iso := "nor", value := .firstSecondThreeTh }
  , { walsCode := "nug", iso := "nuy", value := .none }
  , { walsCode := "nym", iso := "nym", value := .firstTwoThThreeTh }
  , { walsCode := "occ", iso := "oci", value := .firstSecondThreeTh }
  , { walsCode := "orb", iso := "gax", value := .firstTwoThThreeTh }
  , { walsCode := "orh", iso := "hae", value := .firstTwoThThreeTh }
  , { walsCode := "owc", iso := "gaz", value := .firstOneThTwoThThreeTh }
  , { walsCode := "oss", iso := "oss", value := .firstTwoThThreeTh }
  , { walsCode := "oix", iso := "otz", value := .firstTwoThThreeTh }
  , { walsCode := "otm", iso := "ote", value := .oneThTwoThThreeTh }
  , { walsCode := "pai", iso := "pwn", value := .oneThTwoThThreeTh }
  , { walsCode := "pal", iso := "pau", value := .firstTwoThThreeTh }
  , { walsCode := "pap", iso := "pap", value := .firstTwoThThreeTh }
  , { walsCode := "psh", iso := "pst", value := .firstTwoThThreeTh }
  , { walsCode := "psm", iso := "pqm", value := .firstTwoThThreeTh }
  , { walsCode := "per", iso := "pip", value := .oneThTwoThThreeTh }
  , { walsCode := "prs", iso := "pes", value := .firstOneThTwoThThreeTh }
  , { walsCode := "pia", iso := "pid", value := .various }
  , { walsCode := "pol", iso := "pol", value := .firstSecondThreeTh }
  , { walsCode := "psj", iso := "poe", value := .firstTwoThThreeTh }
  , { walsCode := "pcm", iso := "poc", value := .firstTwoThThreeTh }
  , { walsCode := "por", iso := "por", value := .firstSecondThreeTh }
  , { walsCode := "pri", iso := "pre", value := .firstTwoThree }
  , { walsCode := "qay", iso := "quy", value := .firstOneThTwoThThreeTh }
  , { walsCode := "qec", iso := "qug", value := .firstOneThTwoThThreeTh }
  , { walsCode := "qim", iso := "qvi", value := .firstOneThTwoThThreeTh }
  , { walsCode := "rap", iso := "rap", value := .firstTwoThThreeTh }
  , { walsCode := "rka", iso := "rmy", value := .firstOneThTwoThThreeTh }
  , { walsCode := "rom", iso := "ron", value := .firstTwoThThreeTh }
  , { walsCode := "rmc", iso := "roh", value := .firstSecondThreeTh }
  , { walsCode := "rus", iso := "rus", value := .firstSecondThreeTh }
  , { walsCode := "sno", iso := "sme", value := .firstSecondThreeTh }
  , { walsCode := "slb", iso := "sbe", value := .firstTwoThThreeTh }
  , { walsCode := "sam", iso := "smo", value := .firstTwoThree }
  , { walsCode := "sap", iso := "spu", value := .oneTwoThree }
  , { walsCode := "srd", iso := "sro", value := .oneThTwoThThreeTh }
  , { walsCode := "snc", iso := "see", value := .none }
  , { walsCode := "scr", iso := "hbs", value := .firstSecondThreeTh }
  , { walsCode := "ses", iso := "sot", value := .firstTwoThThreeTh }
  , { walsCode := "sey", iso := "crs", value := .firstTwoThThreeTh }
  , { walsCode := "ssh", iso := "bwo", value := .firstOneThTwoThThreeTh }
  , { walsCode := "shn", iso := "sna", value := .firstTwoThThreeTh }
  , { walsCode := "snh", iso := "sin", value := .firstTwoThThreeTh }
  , { walsCode := "sla", iso := "den", value := .firstTwoThThreeTh }
  , { walsCode := "svk", iso := "slk", value := .firstSecondThreeTh }
  , { walsCode := "slo", iso := "slv", value := .firstSecondThreeTh }
  , { walsCode := "so", iso := "teu", value := .firstSecondThreeTh }
  , { walsCode := "som", iso := "som", value := .oneThTwoThThreeTh }
  , { walsCode := "srl", iso := "dsb", value := .firstSecondThreeTh }
  , { walsCode := "sou", iso := "hsb", value := .firstSecondThreeTh }
  , { walsCode := "spa", iso := "spa", value := .firstSecondThreeTh }
  , { walsCode := "squ", iso := "squ", value := .firstSecondThreeTh }
  , { walsCode := "sup", iso := "spp", value := .firstTwoThThreeTh }
  , { walsCode := "sus", iso := "sus", value := .firstTwoThThreeTh }
  , { walsCode := "swa", iso := "swh", value := .firstSecondThreeTh }
  , { walsCode := "swe", iso := "swe", value := .firstSecondThreeTh }
  , { walsCode := "tab", iso := "mky", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tag", iso := "tgl", value := .firstTwoThThreeTh }
  , { walsCode := "tah", iso := "tah", value := .firstTwoThThreeTh }
  , { walsCode := "tml", iso := "tam", value := .firstTwoThThreeTh }
  , { walsCode := "tvo", iso := "tat", value := .oneThTwoThThreeTh }
  , { walsCode := "tau", iso := "tya", value := .none }
  , { walsCode := "tha", iso := "tha", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tin", iso := "cir", value := .oneThTwoThThreeTh }
  , { walsCode := "tiw", iso := "tiw", value := .none }
  , { walsCode := "toj", iso := "toj", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tpi", iso := "tpi", value := .oneThTwoThThreeTh }
  , { walsCode := "tms", iso := "dto", value := .firstTwoThThreeTh }
  , { walsCode := "txj", iso := "too", value := .oneThTwoThThreeTh }
  , { walsCode := "tru", iso := "tpy", value := .none }
  , { walsCode := "tsa", iso := "tkr", value := .oneThTwoThThreeTh }
  , { walsCode := "tuk", iso := "", value := .firstTwoThree }
  , { walsCode := "tna", iso := "tuv", value := .firstTwoThThreeTh }
  , { walsCode := "tur", iso := "tur", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tkm", iso := "tuk", value := .oneThTwoThThreeTh }
  , { walsCode := "tuv", iso := "tyv", value := .oneThTwoThThreeTh }
  , { walsCode := "tzo", iso := "tzo", value := .firstTwoThThreeTh }
  , { walsCode := "tsh", iso := "par", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ukr", iso := "ukr", value := .firstSecondThreeTh }
  , { walsCode := "una", iso := "mtg", value := .oneThTwoThThreeTh }
  , { walsCode := "usa", iso := "wnu", value := .various }
  , { walsCode := "ute", iso := "ute", value := .firstSecondThreeTh }
  , { walsCode := "uyg", iso := "uig", value := .oneThTwoThThreeTh }
  , { walsCode := "uzb", iso := "", value := .oneThTwoThThreeTh }
  , { walsCode := "vep", iso := "vep", value := .firstSecondThreeTh }
  , { walsCode := "vie", iso := "vie", value := .various }
  , { walsCode := "vot", iso := "vot", value := .firstSecondThreeTh }
  , { walsCode := "wra", iso := "wba", value := .firstTwoThree }
  , { walsCode := "wrd", iso := "wrr", value := .none }
  , { walsCode := "war", iso := "pav", value := .none }
  , { walsCode := "wel", iso := "cym", value := .firstSecondThreeTh }
  , { walsCode := "wly", iso := "wal", value := .firstTwoThThreeTh }
  , { walsCode := "wlf", iso := "wol", value := .firstTwoThThreeTh }
  , { walsCode := "ykt", iso := "sah", value := .firstTwoThThreeTh }
  , { walsCode := "yaq", iso := "yaq", value := .oneThTwoThThreeTh }
  , { walsCode := "yim", iso := "yee", value := .firstTwoThThreeTh }
  , { walsCode := "yor", iso := "yor", value := .oneThTwoThThreeTh }
  , { walsCode := "yko", iso := "yux", value := .firstTwoThThreeTh }
  , { walsCode := "ypk", iso := "esu", value := .firstOneThTwoThThreeTh }
  , { walsCode := "zya", iso := "zav", value := .firstOneThTwoThThreeTh }
  , { walsCode := "zaz", iso := "diq", value := .firstTwoThThreeTh }
  , { walsCode := "zul", iso := "zul", value := .firstTwoThThreeTh }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F53A
