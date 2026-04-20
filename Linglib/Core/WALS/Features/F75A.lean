import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 75A: Epistemic Possibility
@cite{vanbogaert-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 75A`.

Chapter 75, 240 languages.
-/

namespace Core.WALS.F75A

/-- WALS 75A values. -/
inductive EpistemicPossibility where
  /-- Verbal constructions (65 languages). -/
  | verbalConstructions
  /-- Affixes on verbs (84 languages). -/
  | affixesOnVerbs
  /-- Other (91 languages). -/
  | other
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 75A dataset (240 languages). -/
def allData : List (Datapoint EpistemicPossibility) :=
  [ { walsCode := "abk", iso := "abk", value := .verbalConstructions }
  , { walsCode := "ace", iso := "ace", value := .verbalConstructions }
  , { walsCode := "aco", iso := "kjq", value := .affixesOnVerbs }
  , { walsCode := "ain", iso := "ain", value := .other }
  , { walsCode := "akn", iso := "aka", value := .other }
  , { walsCode := "alb", iso := "sqi", value := .verbalConstructions }
  , { walsCode := "ame", iso := "aey", value := .other }
  , { walsCode := "amh", iso := "amh", value := .verbalConstructions }
  , { walsCode := "apu", iso := "apu", value := .affixesOnVerbs }
  , { walsCode := "aeg", iso := "arz", value := .verbalConstructions }
  , { walsCode := "arg", iso := "afb", value := .verbalConstructions }
  , { walsCode := "amr", iso := "ary", value := .verbalConstructions }
  , { walsCode := "ana", iso := "aro", value := .affixesOnVerbs }
  , { walsCode := "arm", iso := "hye", value := .other }
  , { walsCode := "asm", iso := "cns", value := .affixesOnVerbs }
  , { walsCode := "awp", iso := "kwi", value := .affixesOnVerbs }
  , { walsCode := "aym", iso := "ayr", value := .other }
  , { walsCode := "bab", iso := "bav", value := .other }
  , { walsCode := "bal", iso := "ban", value := .other }
  , { walsCode := "bam", iso := "bam", value := .verbalConstructions }
  , { walsCode := "brs", iso := "bsn", value := .other }
  , { walsCode := "bsq", iso := "eus", value := .affixesOnVerbs }
  , { walsCode := "bkr", iso := "btx", value := .other }
  , { walsCode := "bto", iso := "bbc", value := .other }
  , { walsCode := "bej", iso := "bej", value := .other }
  , { walsCode := "brh", iso := "brh", value := .affixesOnVerbs }
  , { walsCode := "bri", iso := "bzd", value := .affixesOnVerbs }
  , { walsCode := "brm", iso := "mya", value := .other }
  , { walsCode := "bur", iso := "bsk", value := .affixesOnVerbs }
  , { walsCode := "bet", iso := "bev", value := .verbalConstructions }
  , { walsCode := "cah", iso := "chl", value := .other }
  , { walsCode := "cnl", iso := "ram", value := .other }
  , { walsCode := "cnt", iso := "yue", value := .other }
  , { walsCode := "ctl", iso := "cat", value := .verbalConstructions }
  , { walsCode := "cyv", iso := "cyb", value := .affixesOnVerbs }
  , { walsCode := "cha", iso := "cha", value := .other }
  , { walsCode := "chk", iso := "ckt", value := .other }
  , { walsCode := "chv", iso := "chv", value := .affixesOnVerbs }
  , { walsCode := "cmn", iso := "com", value := .affixesOnVerbs }
  , { walsCode := "coo", iso := "csz", value := .other }
  , { walsCode := "cre", iso := "crk", value := .affixesOnVerbs }
  , { walsCode := "dag", iso := "dgz", value := .affixesOnVerbs }
  , { walsCode := "dni", iso := "dni", value := .affixesOnVerbs }
  , { walsCode := "dsh", iso := "dan", value := .verbalConstructions }
  , { walsCode := "die", iso := "dih", value := .affixesOnVerbs }
  , { walsCode := "dre", iso := "dhv", value := .other }
  , { walsCode := "dut", iso := "nld", value := .verbalConstructions }
  , { walsCode := "eka", iso := "ekg", value := .affixesOnVerbs }
  , { walsCode := "eng", iso := "eng", value := .verbalConstructions }
  , { walsCode := "epe", iso := "sja", value := .affixesOnVerbs }
  , { walsCode := "eve", iso := "evn", value := .affixesOnVerbs }
  , { walsCode := "ewe", iso := "ewe", value := .verbalConstructions }
  , { walsCode := "far", iso := "fao", value := .verbalConstructions }
  , { walsCode := "fij", iso := "fij", value := .other }
  , { walsCode := "fin", iso := "fin", value := .verbalConstructions }
  , { walsCode := "fre", iso := "fra", value := .verbalConstructions }
  , { walsCode := "fua", iso := "fub", value := .affixesOnVerbs }
  , { walsCode := "fur", iso := "fvr", value := .affixesOnVerbs }
  , { walsCode := "gar", iso := "grt", value := .affixesOnVerbs }
  , { walsCode := "geo", iso := "kat", value := .other }
  , { walsCode := "ger", iso := "deu", value := .verbalConstructions }
  , { walsCode := "goo", iso := "gni", value := .affixesOnVerbs }
  , { walsCode := "grb", iso := "grj", value := .verbalConstructions }
  , { walsCode := "grk", iso := "ell", value := .verbalConstructions }
  , { walsCode := "grw", iso := "kal", value := .affixesOnVerbs }
  , { walsCode := "hai", iso := "hai", value := .affixesOnVerbs }
  , { walsCode := "ham", iso := "hmt", value := .affixesOnVerbs }
  , { walsCode := "hau", iso := "hau", value := .verbalConstructions }
  , { walsCode := "haw", iso := "haw", value := .other }
  , { walsCode := "heb", iso := "heb", value := .verbalConstructions }
  , { walsCode := "hin", iso := "hin", value := .verbalConstructions }
  , { walsCode := "hix", iso := "hix", value := .other }
  , { walsCode := "hun", iso := "hun", value := .verbalConstructions }
  , { walsCode := "hzb", iso := "huz", value := .other }
  , { walsCode := "ice", iso := "isl", value := .verbalConstructions }
  , { walsCode := "igb", iso := "ibo", value := .verbalConstructions }
  , { walsCode := "ika", iso := "arh", value := .affixesOnVerbs }
  , { walsCode := "imo", iso := "imn", value := .affixesOnVerbs }
  , { walsCode := "ind", iso := "ind", value := .other }
  , { walsCode := "irq", iso := "irk", value := .other }
  , { walsCode := "iri", iso := "gle", value := .verbalConstructions }
  , { walsCode := "ita", iso := "ita", value := .verbalConstructions }
  , { walsCode := "jak", iso := "jac", value := .other }
  , { walsCode := "jpn", iso := "jpn", value := .other }
  , { walsCode := "juh", iso := "ktz", value := .other }
  , { walsCode := "kam", iso := "xbr", value := .verbalConstructions }
  , { walsCode := "knd", iso := "kan", value := .verbalConstructions }
  , { walsCode := "knr", iso := "knc", value := .other }
  , { walsCode := "krk", iso := "kyh", value := .other }
  , { walsCode := "kas", iso := "kas", value := .verbalConstructions }
  , { walsCode := "kay", iso := "gyd", value := .affixesOnVerbs }
  , { walsCode := "ker", iso := "ker", value := .other }
  , { walsCode := "ket", iso := "ket", value := .other }
  , { walsCode := "kew", iso := "kew", value := .other }
  , { walsCode := "kha", iso := "khk", value := .other }
  , { walsCode := "kty", iso := "kca", value := .other }
  , { walsCode := "khs", iso := "kha", value := .other }
  , { walsCode := "kmu", iso := "kjg", value := .other }
  , { walsCode := "klv", iso := "kij", value := .affixesOnVerbs }
  , { walsCode := "kio", iso := "kio", value := .affixesOnVerbs }
  , { walsCode := "krb", iso := "gil", value := .other }
  , { walsCode := "koa", iso := "cku", value := .affixesOnVerbs }
  , { walsCode := "kob", iso := "kpw", value := .other }
  , { walsCode := "kol", iso := "kfb", value := .verbalConstructions }
  , { walsCode := "kor", iso := "kor", value := .other }
  , { walsCode := "kfe", iso := "kfz", value := .verbalConstructions }
  , { walsCode := "kro", iso := "kgo", value := .other }
  , { walsCode := "kui", iso := "kxu", value := .verbalConstructions }
  , { walsCode := "kut", iso := "kut", value := .other }
  , { walsCode := "lad", iso := "lbj", value := .affixesOnVerbs }
  , { walsCode := "lak", iso := "lbe", value := .verbalConstructions }
  , { walsCode := "lkt", iso := "lkt", value := .affixesOnVerbs }
  , { walsCode := "lan", iso := "laj", value := .other }
  , { walsCode := "lat", iso := "lav", value := .verbalConstructions }
  , { walsCode := "lav", iso := "lvk", value := .other }
  , { walsCode := "lep", iso := "lep", value := .affixesOnVerbs }
  , { walsCode := "lez", iso := "lez", value := .other }
  , { walsCode := "lin", iso := "lin", value := .other }
  , { walsCode := "lit", iso := "lit", value := .verbalConstructions }
  , { walsCode := "luv", iso := "lue", value := .other }
  , { walsCode := "mcd", iso := "mkd", value := .verbalConstructions }
  , { walsCode := "mai", iso := "mai", value := .affixesOnVerbs }
  , { walsCode := "mal", iso := "plt", value := .other }
  , { walsCode := "mym", iso := "mal", value := .verbalConstructions }
  , { walsCode := "mlt", iso := "mlt", value := .verbalConstructions }
  , { walsCode := "mnd", iso := "cmn", value := .verbalConstructions }
  , { walsCode := "myi", iso := "mpc", value := .affixesOnVerbs }
  , { walsCode := "mns", iso := "mns", value := .affixesOnVerbs }
  , { walsCode := "mao", iso := "mri", value := .other }
  , { walsCode := "map", iso := "arn", value := .affixesOnVerbs }
  , { walsCode := "mku", iso := "zmr", value := .other }
  , { walsCode := "mhi", iso := "mar", value := .verbalConstructions }
  , { walsCode := "mar", iso := "mrc", value := .affixesOnVerbs }
  , { walsCode := "mrd", iso := "mrz", value := .other }
  , { walsCode := "mrt", iso := "vma", value := .other }
  , { walsCode := "meh", iso := "gdq", value := .verbalConstructions }
  , { walsCode := "mei", iso := "mni", value := .verbalConstructions }
  , { walsCode := "mie", iso := "ium", value := .other }
  , { walsCode := "mss", iso := "skd", value := .affixesOnVerbs }
  , { walsCode := "mxc", iso := "mig", value := .affixesOnVerbs }
  , { walsCode := "mok", iso := "mkj", value := .verbalConstructions }
  , { walsCode := "mna", iso := "mnb", value := .other }
  , { walsCode := "mdg", iso := "mua", value := .verbalConstructions }
  , { walsCode := "mun", iso := "unr", value := .other }
  , { walsCode := "nma", iso := "nbi", value := .affixesOnVerbs }
  , { walsCode := "ngt", iso := "nmf", value := .affixesOnVerbs }
  , { walsCode := "nht", iso := "nhg", value := .other }
  , { walsCode := "kho", iso := "naq", value := .other }
  , { walsCode := "nav", iso := "nav", value := .affixesOnVerbs }
  , { walsCode := "ndy", iso := "djk", value := .other }
  , { walsCode := "nez", iso := "nez", value := .other }
  , { walsCode := "ngi", iso := "wyb", value := .other }
  , { walsCode := "niv", iso := "niv", value := .affixesOnVerbs }
  , { walsCode := "nko", iso := "cgg", value := .other }
  , { walsCode := "nug", iso := "nuy", value := .other }
  , { walsCode := "ond", iso := "one", value := .affixesOnVerbs }
  , { walsCode := "orh", iso := "hae", value := .verbalConstructions }
  , { walsCode := "otm", iso := "ote", value := .other }
  , { walsCode := "pms", iso := "pma", value := .affixesOnVerbs }
  , { walsCode := "pai", iso := "pwn", value := .affixesOnVerbs }
  , { walsCode := "pan", iso := "pan", value := .verbalConstructions }
  , { walsCode := "psm", iso := "pqm", value := .affixesOnVerbs }
  , { walsCode := "pau", iso := "pad", value := .other }
  , { walsCode := "prs", iso := "pes", value := .other }
  , { walsCode := "pba", iso := "pia", value := .affixesOnVerbs }
  , { walsCode := "prh", iso := "myp", value := .affixesOnVerbs }
  , { walsCode := "pit", iso := "pjt", value := .other }
  , { walsCode := "pol", iso := "pol", value := .verbalConstructions }
  , { walsCode := "pso", iso := "pom", value := .affixesOnVerbs }
  , { walsCode := "por", iso := "por", value := .verbalConstructions }
  , { walsCode := "qaw", iso := "alc", value := .other }
  , { walsCode := "qim", iso := "qvi", value := .affixesOnVerbs }
  , { walsCode := "rap", iso := "rap", value := .other }
  , { walsCode := "rka", iso := "rmy", value := .verbalConstructions }
  , { walsCode := "rom", iso := "ron", value := .verbalConstructions }
  , { walsCode := "rus", iso := "rus", value := .verbalConstructions }
  , { walsCode := "sno", iso := "sme", value := .verbalConstructions }
  , { walsCode := "smt", iso := "uma", value := .other }
  , { walsCode := "san", iso := "sag", value := .other }
  , { walsCode := "snm", iso := "xsu", value := .other }
  , { walsCode := "sel", iso := "ona", value := .affixesOnVerbs }
  , { walsCode := "sml", iso := "sza", value := .affixesOnVerbs }
  , { walsCode := "snt", iso := "set", value := .other }
  , { walsCode := "scr", iso := "hbs", value := .verbalConstructions }
  , { walsCode := "shk", iso := "shp", value := .affixesOnVerbs }
  , { walsCode := "sla", iso := "den", value := .other }
  , { walsCode := "slo", iso := "slv", value := .other }
  , { walsCode := "so", iso := "teu", value := .other }
  , { walsCode := "som", iso := "som", value := .affixesOnVerbs }
  , { walsCode := "spa", iso := "spa", value := .verbalConstructions }
  , { walsCode := "squ", iso := "squ", value := .affixesOnVerbs }
  , { walsCode := "sup", iso := "spp", value := .verbalConstructions }
  , { walsCode := "swa", iso := "swh", value := .affixesOnVerbs }
  , { walsCode := "swe", iso := "swe", value := .verbalConstructions }
  , { walsCode := "tab", iso := "mky", value := .affixesOnVerbs }
  , { walsCode := "tag", iso := "tgl", value := .other }
  , { walsCode := "tml", iso := "tam", value := .affixesOnVerbs }
  , { walsCode := "tvo", iso := "tat", value := .other }
  , { walsCode := "tel", iso := "tel", value := .verbalConstructions }
  , { walsCode := "teo", iso := "tio", value := .other }
  , { walsCode := "tha", iso := "tha", value := .verbalConstructions }
  , { walsCode := "tgr", iso := "tig", value := .other }
  , { walsCode := "tja", iso := "dih", value := .affixesOnVerbs }
  , { walsCode := "tin", iso := "cir", value := .other }
  , { walsCode := "tiw", iso := "tiw", value := .affixesOnVerbs }
  , { walsCode := "tli", iso := "tli", value := .other }
  , { walsCode := "tor", iso := "rth", value := .other }
  , { walsCode := "tru", iso := "tpy", value := .affixesOnVerbs }
  , { walsCode := "tsi", iso := "tsi", value := .affixesOnVerbs }
  , { walsCode := "tuk", iso := "", value := .verbalConstructions }
  , { walsCode := "tur", iso := "tur", value := .affixesOnVerbs }
  , { walsCode := "tvl", iso := "tvl", value := .other }
  , { walsCode := "tuv", iso := "tyv", value := .verbalConstructions }
  , { walsCode := "udh", iso := "ude", value := .affixesOnVerbs }
  , { walsCode := "una", iso := "mtg", value := .affixesOnVerbs }
  , { walsCode := "ung", iso := "ung", value := .other }
  , { walsCode := "urk", iso := "urb", value := .other }
  , { walsCode := "usa", iso := "wnu", value := .affixesOnVerbs }
  , { walsCode := "uzb", iso := "", value := .other }
  , { walsCode := "vie", iso := "vie", value := .verbalConstructions }
  , { walsCode := "vot", iso := "vot", value := .affixesOnVerbs }
  , { walsCode := "wam", iso := "wmb", value := .affixesOnVerbs }
  , { walsCode := "wra", iso := "wba", value := .affixesOnVerbs }
  , { walsCode := "wrd", iso := "wrr", value := .affixesOnVerbs }
  , { walsCode := "war", iso := "pav", value := .affixesOnVerbs }
  , { walsCode := "wel", iso := "cym", value := .other }
  , { walsCode := "wch", iso := "mzh", value := .other }
  , { walsCode := "wlf", iso := "wol", value := .verbalConstructions }
  , { walsCode := "yag", iso := "yad", value := .affixesOnVerbs }
  , { walsCode := "yaq", iso := "yaq", value := .affixesOnVerbs }
  , { walsCode := "yid", iso := "yii", value := .other }
  , { walsCode := "yim", iso := "yee", value := .affixesOnVerbs }
  , { walsCode := "yor", iso := "yor", value := .verbalConstructions }
  , { walsCode := "yuc", iso := "yuc", value := .affixesOnVerbs }
  , { walsCode := "yko", iso := "yux", value := .affixesOnVerbs }
  , { walsCode := "ypk", iso := "esu", value := .affixesOnVerbs }
  , { walsCode := "yur", iso := "yur", value := .other }
  , { walsCode := "zya", iso := "zav", value := .affixesOnVerbs }
  , { walsCode := "zqc", iso := "zoc", value := .affixesOnVerbs }
  , { walsCode := "zul", iso := "zul", value := .affixesOnVerbs }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F75A
