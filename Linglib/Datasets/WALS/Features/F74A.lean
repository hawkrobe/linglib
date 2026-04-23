import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 74A: Situational Possibility
@cite{vanbogaert-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 74A`.

Chapter 74, 234 languages.
-/

namespace Datasets.WALS.F74A

/-- WALS 74A values. -/
inductive SituationalPossibility where
  /-- Affixes on verbs (63 languages). -/
  | affixesOnVerbs
  /-- Verbal constructions (158 languages). -/
  | verbalConstructions
  /-- Other kinds of markers (13 languages). -/
  | otherKindsOfMarkers
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 74A dataset (234 languages). -/
def allData : List (Datapoint SituationalPossibility) :=
  [ { walsCode := "abk", iso := "abk", value := .verbalConstructions }
  , { walsCode := "ace", iso := "ace", value := .verbalConstructions }
  , { walsCode := "aco", iso := "kjq", value := .affixesOnVerbs }
  , { walsCode := "ain", iso := "ain", value := .verbalConstructions }
  , { walsCode := "akn", iso := "aka", value := .verbalConstructions }
  , { walsCode := "alb", iso := "sqi", value := .verbalConstructions }
  , { walsCode := "ame", iso := "aey", value := .otherKindsOfMarkers }
  , { walsCode := "amh", iso := "amh", value := .verbalConstructions }
  , { walsCode := "apu", iso := "apu", value := .verbalConstructions }
  , { walsCode := "aeg", iso := "arz", value := .verbalConstructions }
  , { walsCode := "arg", iso := "afb", value := .verbalConstructions }
  , { walsCode := "amr", iso := "ary", value := .verbalConstructions }
  , { walsCode := "ana", iso := "aro", value := .affixesOnVerbs }
  , { walsCode := "arm", iso := "hye", value := .verbalConstructions }
  , { walsCode := "asm", iso := "cns", value := .affixesOnVerbs }
  , { walsCode := "awp", iso := "kwi", value := .affixesOnVerbs }
  , { walsCode := "aym", iso := "ayr", value := .verbalConstructions }
  , { walsCode := "bab", iso := "bav", value := .verbalConstructions }
  , { walsCode := "bag", iso := "bmi", value := .verbalConstructions }
  , { walsCode := "bal", iso := "ban", value := .verbalConstructions }
  , { walsCode := "bam", iso := "bam", value := .verbalConstructions }
  , { walsCode := "brs", iso := "bsn", value := .verbalConstructions }
  , { walsCode := "bsq", iso := "eus", value := .affixesOnVerbs }
  , { walsCode := "bkr", iso := "btx", value := .affixesOnVerbs }
  , { walsCode := "baw", iso := "bgr", value := .verbalConstructions }
  , { walsCode := "bej", iso := "bej", value := .verbalConstructions }
  , { walsCode := "bma", iso := "tzm", value := .verbalConstructions }
  , { walsCode := "brh", iso := "brh", value := .affixesOnVerbs }
  , { walsCode := "brm", iso := "mya", value := .otherKindsOfMarkers }
  , { walsCode := "cnt", iso := "yue", value := .verbalConstructions }
  , { walsCode := "ctl", iso := "cat", value := .verbalConstructions }
  , { walsCode := "cyv", iso := "cyb", value := .verbalConstructions }
  , { walsCode := "cha", iso := "cha", value := .affixesOnVerbs }
  , { walsCode := "cle", iso := "cle", value := .verbalConstructions }
  , { walsCode := "chk", iso := "ckt", value := .otherKindsOfMarkers }
  , { walsCode := "chv", iso := "chv", value := .affixesOnVerbs }
  , { walsCode := "cre", iso := "crk", value := .verbalConstructions }
  , { walsCode := "dag", iso := "dgz", value := .affixesOnVerbs }
  , { walsCode := "dni", iso := "dni", value := .affixesOnVerbs }
  , { walsCode := "dsh", iso := "dan", value := .verbalConstructions }
  , { walsCode := "dio", iso := "dyo", value := .affixesOnVerbs }
  , { walsCode := "dre", iso := "dhv", value := .verbalConstructions }
  , { walsCode := "dut", iso := "nld", value := .verbalConstructions }
  , { walsCode := "eka", iso := "ekg", value := .affixesOnVerbs }
  , { walsCode := "eng", iso := "eng", value := .verbalConstructions }
  , { walsCode := "eve", iso := "evn", value := .affixesOnVerbs }
  , { walsCode := "ewe", iso := "ewe", value := .verbalConstructions }
  , { walsCode := "far", iso := "fao", value := .verbalConstructions }
  , { walsCode := "fij", iso := "fij", value := .verbalConstructions }
  , { walsCode := "fin", iso := "fin", value := .verbalConstructions }
  , { walsCode := "fre", iso := "fra", value := .verbalConstructions }
  , { walsCode := "fua", iso := "fub", value := .affixesOnVerbs }
  , { walsCode := "fue", iso := "fud", value := .verbalConstructions }
  , { walsCode := "gdk", iso := "gdb", value := .affixesOnVerbs }
  , { walsCode := "gar", iso := "grt", value := .affixesOnVerbs }
  , { walsCode := "geo", iso := "kat", value := .verbalConstructions }
  , { walsCode := "ger", iso := "deu", value := .verbalConstructions }
  , { walsCode := "goj", iso := "gju", value := .affixesOnVerbs }
  , { walsCode := "grk", iso := "ell", value := .verbalConstructions }
  , { walsCode := "grw", iso := "kal", value := .affixesOnVerbs }
  , { walsCode := "hai", iso := "hai", value := .affixesOnVerbs }
  , { walsCode := "ham", iso := "hmt", value := .affixesOnVerbs }
  , { walsCode := "hau", iso := "hau", value := .verbalConstructions }
  , { walsCode := "haw", iso := "haw", value := .verbalConstructions }
  , { walsCode := "heb", iso := "heb", value := .verbalConstructions }
  , { walsCode := "hin", iso := "hin", value := .verbalConstructions }
  , { walsCode := "hmo", iso := "hnj", value := .verbalConstructions }
  , { walsCode := "hmi", iso := "hto", value := .affixesOnVerbs }
  , { walsCode := "hun", iso := "hun", value := .affixesOnVerbs }
  , { walsCode := "hzb", iso := "huz", value := .verbalConstructions }
  , { walsCode := "ice", iso := "isl", value := .verbalConstructions }
  , { walsCode := "igb", iso := "ibo", value := .verbalConstructions }
  , { walsCode := "ika", iso := "arh", value := .affixesOnVerbs }
  , { walsCode := "imo", iso := "imn", value := .affixesOnVerbs }
  , { walsCode := "ind", iso := "ind", value := .affixesOnVerbs }
  , { walsCode := "ing", iso := "inh", value := .verbalConstructions }
  , { walsCode := "irq", iso := "irk", value := .verbalConstructions }
  , { walsCode := "iri", iso := "gle", value := .verbalConstructions }
  , { walsCode := "ita", iso := "ita", value := .verbalConstructions }
  , { walsCode := "jak", iso := "jac", value := .affixesOnVerbs }
  , { walsCode := "jpn", iso := "jpn", value := .affixesOnVerbs }
  , { walsCode := "kam", iso := "xbr", value := .verbalConstructions }
  , { walsCode := "knd", iso := "kan", value := .verbalConstructions }
  , { walsCode := "knr", iso := "knc", value := .verbalConstructions }
  , { walsCode := "kas", iso := "kas", value := .verbalConstructions }
  , { walsCode := "kyl", iso := "eky", value := .otherKindsOfMarkers }
  , { walsCode := "kay", iso := "gyd", value := .affixesOnVerbs }
  , { walsCode := "ker", iso := "ker", value := .verbalConstructions }
  , { walsCode := "ket", iso := "ket", value := .verbalConstructions }
  , { walsCode := "kha", iso := "khk", value := .verbalConstructions }
  , { walsCode := "kty", iso := "kca", value := .verbalConstructions }
  , { walsCode := "khs", iso := "kha", value := .verbalConstructions }
  , { walsCode := "khm", iso := "khm", value := .verbalConstructions }
  , { walsCode := "kmu", iso := "kjg", value := .verbalConstructions }
  , { walsCode := "klv", iso := "kij", value := .affixesOnVerbs }
  , { walsCode := "kio", iso := "kio", value := .affixesOnVerbs }
  , { walsCode := "krb", iso := "gil", value := .verbalConstructions }
  , { walsCode := "koa", iso := "cku", value := .affixesOnVerbs }
  , { walsCode := "kob", iso := "kpw", value := .affixesOnVerbs }
  , { walsCode := "kol", iso := "kfb", value := .verbalConstructions }
  , { walsCode := "kon", iso := "kng", value := .verbalConstructions }
  , { walsCode := "kor", iso := "kor", value := .otherKindsOfMarkers }
  , { walsCode := "kfe", iso := "kfz", value := .verbalConstructions }
  , { walsCode := "kse", iso := "ses", value := .verbalConstructions }
  , { walsCode := "kro", iso := "kgo", value := .verbalConstructions }
  , { walsCode := "kui", iso := "kxu", value := .verbalConstructions }
  , { walsCode := "knm", iso := "kun", value := .verbalConstructions }
  , { walsCode := "kut", iso := "kut", value := .otherKindsOfMarkers }
  , { walsCode := "lad", iso := "lbj", value := .affixesOnVerbs }
  , { walsCode := "lak", iso := "lbe", value := .verbalConstructions }
  , { walsCode := "lkt", iso := "lkt", value := .verbalConstructions }
  , { walsCode := "lan", iso := "laj", value := .verbalConstructions }
  , { walsCode := "lat", iso := "lav", value := .verbalConstructions }
  , { walsCode := "lav", iso := "lvk", value := .affixesOnVerbs }
  , { walsCode := "lep", iso := "lep", value := .verbalConstructions }
  , { walsCode := "lez", iso := "lez", value := .verbalConstructions }
  , { walsCode := "lin", iso := "lin", value := .verbalConstructions }
  , { walsCode := "lit", iso := "lit", value := .verbalConstructions }
  , { walsCode := "mcd", iso := "mkd", value := .verbalConstructions }
  , { walsCode := "mai", iso := "mai", value := .verbalConstructions }
  , { walsCode := "mak", iso := "myh", value := .verbalConstructions }
  , { walsCode := "mal", iso := "plt", value := .verbalConstructions }
  , { walsCode := "mym", iso := "mal", value := .verbalConstructions }
  , { walsCode := "mlt", iso := "mlt", value := .verbalConstructions }
  , { walsCode := "mnd", iso := "cmn", value := .verbalConstructions }
  , { walsCode := "myi", iso := "mpc", value := .affixesOnVerbs }
  , { walsCode := "mns", iso := "mns", value := .verbalConstructions }
  , { walsCode := "mao", iso := "mri", value := .verbalConstructions }
  , { walsCode := "map", iso := "arn", value := .verbalConstructions }
  , { walsCode := "mku", iso := "zmr", value := .verbalConstructions }
  , { walsCode := "mhi", iso := "mar", value := .verbalConstructions }
  , { walsCode := "mrd", iso := "mrz", value := .affixesOnVerbs }
  , { walsCode := "mau", iso := "mph", value := .affixesOnVerbs }
  , { walsCode := "may", iso := "ayz", value := .verbalConstructions }
  , { walsCode := "meh", iso := "gdq", value := .verbalConstructions }
  , { walsCode := "mde", iso := "men", value := .verbalConstructions }
  , { walsCode := "mie", iso := "ium", value := .verbalConstructions }
  , { walsCode := "mss", iso := "skd", value := .affixesOnVerbs }
  , { walsCode := "mxc", iso := "mig", value := .verbalConstructions }
  , { walsCode := "mok", iso := "mkj", value := .verbalConstructions }
  , { walsCode := "mna", iso := "mnb", value := .verbalConstructions }
  , { walsCode := "mdg", iso := "mua", value := .verbalConstructions }
  , { walsCode := "mun", iso := "unr", value := .verbalConstructions }
  , { walsCode := "mrl", iso := "mur", value := .verbalConstructions }
  , { walsCode := "nma", iso := "nbi", value := .otherKindsOfMarkers }
  , { walsCode := "ngt", iso := "nmf", value := .affixesOnVerbs }
  , { walsCode := "nht", iso := "nhg", value := .otherKindsOfMarkers }
  , { walsCode := "kho", iso := "naq", value := .verbalConstructions }
  , { walsCode := "nav", iso := "nav", value := .affixesOnVerbs }
  , { walsCode := "ndy", iso := "djk", value := .verbalConstructions }
  , { walsCode := "ntu", iso := "yrk", value := .verbalConstructions }
  , { walsCode := "nez", iso := "nez", value := .affixesOnVerbs }
  , { walsCode := "ngi", iso := "wyb", value := .verbalConstructions }
  , { walsCode := "niv", iso := "niv", value := .verbalConstructions }
  , { walsCode := "nko", iso := "cgg", value := .verbalConstructions }
  , { walsCode := "nbd", iso := "dgl", value := .otherKindsOfMarkers }
  , { walsCode := "nug", iso := "nuy", value := .affixesOnVerbs }
  , { walsCode := "ond", iso := "one", value := .verbalConstructions }
  , { walsCode := "orh", iso := "hae", value := .verbalConstructions }
  , { walsCode := "otm", iso := "ote", value := .verbalConstructions }
  , { walsCode := "pai", iso := "pwn", value := .affixesOnVerbs }
  , { walsCode := "pan", iso := "pan", value := .verbalConstructions }
  , { walsCode := "psm", iso := "pqm", value := .verbalConstructions }
  , { walsCode := "pau", iso := "pad", value := .verbalConstructions }
  , { walsCode := "prs", iso := "pes", value := .verbalConstructions }
  , { walsCode := "pba", iso := "pia", value := .verbalConstructions }
  , { walsCode := "pit", iso := "pjt", value := .affixesOnVerbs }
  , { walsCode := "pol", iso := "pol", value := .verbalConstructions }
  , { walsCode := "pso", iso := "pom", value := .affixesOnVerbs }
  , { walsCode := "por", iso := "por", value := .verbalConstructions }
  , { walsCode := "qim", iso := "qvi", value := .verbalConstructions }
  , { walsCode := "rap", iso := "rap", value := .verbalConstructions }
  , { walsCode := "rka", iso := "rmy", value := .verbalConstructions }
  , { walsCode := "rom", iso := "ron", value := .verbalConstructions }
  , { walsCode := "run", iso := "rou", value := .affixesOnVerbs }
  , { walsCode := "rus", iso := "rus", value := .verbalConstructions }
  , { walsCode := "sno", iso := "sme", value := .verbalConstructions }
  , { walsCode := "smt", iso := "uma", value := .affixesOnVerbs }
  , { walsCode := "san", iso := "sag", value := .verbalConstructions }
  , { walsCode := "snm", iso := "xsu", value := .verbalConstructions }
  , { walsCode := "sel", iso := "ona", value := .verbalConstructions }
  , { walsCode := "sml", iso := "sza", value := .verbalConstructions }
  , { walsCode := "scr", iso := "hbs", value := .verbalConstructions }
  , { walsCode := "shk", iso := "shp", value := .verbalConstructions }
  , { walsCode := "sla", iso := "den", value := .otherKindsOfMarkers }
  , { walsCode := "slo", iso := "slv", value := .verbalConstructions }
  , { walsCode := "som", iso := "som", value := .verbalConstructions }
  , { walsCode := "spa", iso := "spa", value := .verbalConstructions }
  , { walsCode := "squ", iso := "squ", value := .affixesOnVerbs }
  , { walsCode := "sue", iso := "sue", value := .verbalConstructions }
  , { walsCode := "sup", iso := "spp", value := .verbalConstructions }
  , { walsCode := "swa", iso := "swh", value := .affixesOnVerbs }
  , { walsCode := "swe", iso := "swe", value := .verbalConstructions }
  , { walsCode := "tab", iso := "mky", value := .verbalConstructions }
  , { walsCode := "tag", iso := "tgl", value := .affixesOnVerbs }
  , { walsCode := "tal", iso := "tlj", value := .affixesOnVerbs }
  , { walsCode := "tml", iso := "tam", value := .affixesOnVerbs }
  , { walsCode := "tvo", iso := "tat", value := .verbalConstructions }
  , { walsCode := "tel", iso := "tel", value := .verbalConstructions }
  , { walsCode := "tha", iso := "tha", value := .verbalConstructions }
  , { walsCode := "tgr", iso := "tig", value := .verbalConstructions }
  , { walsCode := "tja", iso := "dih", value := .verbalConstructions }
  , { walsCode := "tli", iso := "tli", value := .affixesOnVerbs }
  , { walsCode := "tor", iso := "rth", value := .verbalConstructions }
  , { walsCode := "tru", iso := "tpy", value := .verbalConstructions }
  , { walsCode := "tbu", iso := "", value := .verbalConstructions }
  , { walsCode := "tuk", iso := "", value := .verbalConstructions }
  , { walsCode := "tun", iso := "tun", value := .verbalConstructions }
  , { walsCode := "tur", iso := "tur", value := .affixesOnVerbs }
  , { walsCode := "tvl", iso := "tvl", value := .verbalConstructions }
  , { walsCode := "tuv", iso := "tyv", value := .verbalConstructions }
  , { walsCode := "udh", iso := "ude", value := .verbalConstructions }
  , { walsCode := "una", iso := "mtg", value := .affixesOnVerbs }
  , { walsCode := "ung", iso := "ung", value := .otherKindsOfMarkers }
  , { walsCode := "usa", iso := "wnu", value := .affixesOnVerbs }
  , { walsCode := "uzb", iso := "", value := .affixesOnVerbs }
  , { walsCode := "vie", iso := "vie", value := .verbalConstructions }
  , { walsCode := "vot", iso := "vot", value := .verbalConstructions }
  , { walsCode := "wam", iso := "wmb", value := .otherKindsOfMarkers }
  , { walsCode := "wra", iso := "wba", value := .affixesOnVerbs }
  , { walsCode := "wel", iso := "cym", value := .verbalConstructions }
  , { walsCode := "wic", iso := "wic", value := .verbalConstructions }
  , { walsCode := "wch", iso := "mzh", value := .verbalConstructions }
  , { walsCode := "wlf", iso := "wol", value := .verbalConstructions }
  , { walsCode := "yaq", iso := "yaq", value := .verbalConstructions }
  , { walsCode := "yim", iso := "yee", value := .affixesOnVerbs }
  , { walsCode := "yor", iso := "yor", value := .verbalConstructions }
  , { walsCode := "yuc", iso := "yuc", value := .affixesOnVerbs }
  , { walsCode := "yko", iso := "yux", value := .verbalConstructions }
  , { walsCode := "ypk", iso := "esu", value := .affixesOnVerbs }
  , { walsCode := "yur", iso := "yur", value := .otherKindsOfMarkers }
  , { walsCode := "zya", iso := "zav", value := .verbalConstructions }
  , { walsCode := "zqc", iso := "zoc", value := .verbalConstructions }
  , { walsCode := "zul", iso := "zul", value := .affixesOnVerbs }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F74A
