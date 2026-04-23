import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 45A: Politeness Distinctions in Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 45A`.

Chapter 45, 207 languages.
-/

namespace Datasets.WALS.F45A

/-- WALS 45A values. -/
inductive PolitenessDistinctionsInPronouns where
  /-- No politeness distinction (136 languages). -/
  | noPolitenessDistinction
  /-- Binary politeness distinction (49 languages). -/
  | binaryPolitenessDistinction
  /-- Multiple politeness distinctions (15 languages). -/
  | multiplePolitenessDistinctions
  /-- Pronouns avoided for politeness (7 languages). -/
  | pronounsAvoidedForPoliteness
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 45A dataset (207 languages). -/
def allData : List (Datapoint PolitenessDistinctionsInPronouns) :=
  [ { walsCode := "abu", iso := "kgr", value := .noPolitenessDistinction }
  , { walsCode := "aco", iso := "kjq", value := .noPolitenessDistinction }
  , { walsCode := "ain", iso := "ain", value := .binaryPolitenessDistinction }
  , { walsCode := "ala", iso := "amp", value := .noPolitenessDistinction }
  , { walsCode := "alb", iso := "sqi", value := .noPolitenessDistinction }
  , { walsCode := "ame", iso := "aey", value := .noPolitenessDistinction }
  , { walsCode := "ago", iso := "aoa", value := .binaryPolitenessDistinction }
  , { walsCode := "apu", iso := "apu", value := .noPolitenessDistinction }
  , { walsCode := "aeg", iso := "arz", value := .noPolitenessDistinction }
  , { walsCode := "arp", iso := "ape", value := .noPolitenessDistinction }
  , { walsCode := "arm", iso := "hye", value := .binaryPolitenessDistinction }
  , { walsCode := "asm", iso := "cns", value := .noPolitenessDistinction }
  , { walsCode := "awp", iso := "kwi", value := .noPolitenessDistinction }
  , { walsCode := "aym", iso := "ayr", value := .noPolitenessDistinction }
  , { walsCode := "bab", iso := "bav", value := .noPolitenessDistinction }
  , { walsCode := "bag", iso := "bmi", value := .noPolitenessDistinction }
  , { walsCode := "bam", iso := "bam", value := .noPolitenessDistinction }
  , { walsCode := "ble", iso := "bci", value := .noPolitenessDistinction }
  , { walsCode := "brs", iso := "bsn", value := .noPolitenessDistinction }
  , { walsCode := "bsq", iso := "eus", value := .binaryPolitenessDistinction }
  , { walsCode := "bto", iso := "bbc", value := .binaryPolitenessDistinction }
  , { walsCode := "bma", iso := "tzm", value := .noPolitenessDistinction }
  , { walsCode := "brh", iso := "brh", value := .noPolitenessDistinction }
  , { walsCode := "bre", iso := "bre", value := .binaryPolitenessDistinction }
  , { walsCode := "bri", iso := "bzd", value := .noPolitenessDistinction }
  , { walsCode := "brm", iso := "mya", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "bur", iso := "bsk", value := .noPolitenessDistinction }
  , { walsCode := "cnl", iso := "ram", value := .noPolitenessDistinction }
  , { walsCode := "cyv", iso := "cyb", value := .noPolitenessDistinction }
  , { walsCode := "cha", iso := "cha", value := .noPolitenessDistinction }
  , { walsCode := "chk", iso := "ckt", value := .noPolitenessDistinction }
  , { walsCode := "cmn", iso := "com", value := .noPolitenessDistinction }
  , { walsCode := "cop", iso := "cop", value := .noPolitenessDistinction }
  , { walsCode := "crn", iso := "cor", value := .binaryPolitenessDistinction }
  , { walsCode := "cre", iso := "crk", value := .noPolitenessDistinction }
  , { walsCode := "dag", iso := "dgz", value := .noPolitenessDistinction }
  , { walsCode := "dni", iso := "dni", value := .noPolitenessDistinction }
  , { walsCode := "dsh", iso := "dan", value := .binaryPolitenessDistinction }
  , { walsCode := "dmi", iso := "dus", value := .noPolitenessDistinction }
  , { walsCode := "dut", iso := "nld", value := .binaryPolitenessDistinction }
  , { walsCode := "dyi", iso := "dbl", value := .noPolitenessDistinction }
  , { walsCode := "eng", iso := "eng", value := .noPolitenessDistinction }
  , { walsCode := "eve", iso := "evn", value := .noPolitenessDistinction }
  , { walsCode := "ewe", iso := "ewe", value := .noPolitenessDistinction }
  , { walsCode := "fij", iso := "fij", value := .binaryPolitenessDistinction }
  , { walsCode := "fin", iso := "fin", value := .binaryPolitenessDistinction }
  , { walsCode := "fre", iso := "fra", value := .binaryPolitenessDistinction }
  , { walsCode := "fur", iso := "fvr", value := .noPolitenessDistinction }
  , { walsCode := "gae", iso := "gla", value := .binaryPolitenessDistinction }
  , { walsCode := "gar", iso := "grt", value := .noPolitenessDistinction }
  , { walsCode := "geo", iso := "kat", value := .binaryPolitenessDistinction }
  , { walsCode := "ger", iso := "deu", value := .binaryPolitenessDistinction }
  , { walsCode := "goo", iso := "gni", value := .noPolitenessDistinction }
  , { walsCode := "grb", iso := "grj", value := .noPolitenessDistinction }
  , { walsCode := "grk", iso := "ell", value := .binaryPolitenessDistinction }
  , { walsCode := "grw", iso := "kal", value := .noPolitenessDistinction }
  , { walsCode := "gua", iso := "gug", value := .noPolitenessDistinction }
  , { walsCode := "hat", iso := "had", value := .noPolitenessDistinction }
  , { walsCode := "hau", iso := "hau", value := .noPolitenessDistinction }
  , { walsCode := "haw", iso := "haw", value := .noPolitenessDistinction }
  , { walsCode := "heb", iso := "heb", value := .noPolitenessDistinction }
  , { walsCode := "hin", iso := "hin", value := .multiplePolitenessDistinctions }
  , { walsCode := "hix", iso := "hix", value := .noPolitenessDistinction }
  , { walsCode := "hmo", iso := "hnj", value := .noPolitenessDistinction }
  , { walsCode := "hun", iso := "hun", value := .multiplePolitenessDistinctions }
  , { walsCode := "igb", iso := "ibo", value := .noPolitenessDistinction }
  , { walsCode := "imo", iso := "imn", value := .noPolitenessDistinction }
  , { walsCode := "ind", iso := "ind", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "irq", iso := "irk", value := .noPolitenessDistinction }
  , { walsCode := "iri", iso := "gle", value := .noPolitenessDistinction }
  , { walsCode := "ita", iso := "ita", value := .binaryPolitenessDistinction }
  , { walsCode := "jak", iso := "jac", value := .noPolitenessDistinction }
  , { walsCode := "jpn", iso := "jpn", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "jaq", iso := "jqr", value := .noPolitenessDistinction }
  , { walsCode := "juh", iso := "ktz", value := .noPolitenessDistinction }
  , { walsCode := "kam", iso := "xbr", value := .noPolitenessDistinction }
  , { walsCode := "knd", iso := "kan", value := .multiplePolitenessDistinctions }
  , { walsCode := "knr", iso := "knc", value := .noPolitenessDistinction }
  , { walsCode := "krk", iso := "kyh", value := .noPolitenessDistinction }
  , { walsCode := "kas", iso := "kas", value := .binaryPolitenessDistinction }
  , { walsCode := "kyl", iso := "eky", value := .noPolitenessDistinction }
  , { walsCode := "kay", iso := "gyd", value := .noPolitenessDistinction }
  , { walsCode := "ker", iso := "ker", value := .noPolitenessDistinction }
  , { walsCode := "kew", iso := "kew", value := .noPolitenessDistinction }
  , { walsCode := "kha", iso := "khk", value := .binaryPolitenessDistinction }
  , { walsCode := "khs", iso := "kha", value := .binaryPolitenessDistinction }
  , { walsCode := "khm", iso := "khm", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "kmu", iso := "kjg", value := .noPolitenessDistinction }
  , { walsCode := "klv", iso := "kij", value := .noPolitenessDistinction }
  , { walsCode := "kio", iso := "kio", value := .noPolitenessDistinction }
  , { walsCode := "kis", iso := "kss", value := .noPolitenessDistinction }
  , { walsCode := "koa", iso := "cku", value := .noPolitenessDistinction }
  , { walsCode := "kob", iso := "kpw", value := .noPolitenessDistinction }
  , { walsCode := "kmb", iso := "", value := .noPolitenessDistinction }
  , { walsCode := "kon", iso := "kng", value := .noPolitenessDistinction }
  , { walsCode := "kor", iso := "kor", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "kfe", iso := "kfz", value := .binaryPolitenessDistinction }
  , { walsCode := "kos", iso := "kos", value := .binaryPolitenessDistinction }
  , { walsCode := "kse", iso := "ses", value := .noPolitenessDistinction }
  , { walsCode := "kro", iso := "kgo", value := .noPolitenessDistinction }
  , { walsCode := "knm", iso := "kun", value := .noPolitenessDistinction }
  , { walsCode := "kji", iso := "kmr", value := .noPolitenessDistinction }
  , { walsCode := "kut", iso := "kut", value := .noPolitenessDistinction }
  , { walsCode := "lkt", iso := "lkt", value := .noPolitenessDistinction }
  , { walsCode := "lan", iso := "laj", value := .noPolitenessDistinction }
  , { walsCode := "lat", iso := "lav", value := .binaryPolitenessDistinction }
  , { walsCode := "lav", iso := "lvk", value := .noPolitenessDistinction }
  , { walsCode := "lez", iso := "lez", value := .noPolitenessDistinction }
  , { walsCode := "lim", iso := "lif", value := .noPolitenessDistinction }
  , { walsCode := "lit", iso := "lit", value := .multiplePolitenessDistinctions }
  , { walsCode := "luv", iso := "lue", value := .binaryPolitenessDistinction }
  , { walsCode := "mak", iso := "myh", value := .noPolitenessDistinction }
  , { walsCode := "mal", iso := "plt", value := .noPolitenessDistinction }
  , { walsCode := "mym", iso := "mal", value := .multiplePolitenessDistinctions }
  , { walsCode := "mnd", iso := "cmn", value := .binaryPolitenessDistinction }
  , { walsCode := "mmb", iso := "mna", value := .noPolitenessDistinction }
  , { walsCode := "myi", iso := "mpc", value := .noPolitenessDistinction }
  , { walsCode := "mnx", iso := "glv", value := .binaryPolitenessDistinction }
  , { walsCode := "mao", iso := "mri", value := .noPolitenessDistinction }
  , { walsCode := "map", iso := "arn", value := .noPolitenessDistinction }
  , { walsCode := "mhi", iso := "mar", value := .multiplePolitenessDistinctions }
  , { walsCode := "mar", iso := "mrc", value := .noPolitenessDistinction }
  , { walsCode := "mrt", iso := "vma", value := .noPolitenessDistinction }
  , { walsCode := "msl", iso := "mls", value := .noPolitenessDistinction }
  , { walsCode := "mau", iso := "mph", value := .noPolitenessDistinction }
  , { walsCode := "may", iso := "ayz", value := .noPolitenessDistinction }
  , { walsCode := "mei", iso := "mni", value := .noPolitenessDistinction }
  , { walsCode := "mss", iso := "skd", value := .noPolitenessDistinction }
  , { walsCode := "mxc", iso := "mig", value := .binaryPolitenessDistinction }
  , { walsCode := "mrl", iso := "mur", value := .noPolitenessDistinction }
  , { walsCode := "nhh", iso := "", value := .binaryPolitenessDistinction }
  , { walsCode := "nhn", iso := "ncj", value := .binaryPolitenessDistinction }
  , { walsCode := "nht", iso := "nhg", value := .multiplePolitenessDistinctions }
  , { walsCode := "kho", iso := "naq", value := .binaryPolitenessDistinction }
  , { walsCode := "nep", iso := "npi", value := .multiplePolitenessDistinctions }
  , { walsCode := "nez", iso := "nez", value := .noPolitenessDistinction }
  , { walsCode := "nti", iso := "niy", value := .noPolitenessDistinction }
  , { walsCode := "ngi", iso := "wyb", value := .noPolitenessDistinction }
  , { walsCode := "noo", iso := "snf", value := .noPolitenessDistinction }
  , { walsCode := "nor", iso := "nor", value := .binaryPolitenessDistinction }
  , { walsCode := "nbd", iso := "dgl", value := .noPolitenessDistinction }
  , { walsCode := "nug", iso := "nuy", value := .noPolitenessDistinction }
  , { walsCode := "ond", iso := "one", value := .noPolitenessDistinction }
  , { walsCode := "orh", iso := "hae", value := .noPolitenessDistinction }
  , { walsCode := "oss", iso := "oss", value := .noPolitenessDistinction }
  , { walsCode := "otm", iso := "ote", value := .noPolitenessDistinction }
  , { walsCode := "pai", iso := "pwn", value := .noPolitenessDistinction }
  , { walsCode := "pan", iso := "pan", value := .binaryPolitenessDistinction }
  , { walsCode := "psh", iso := "pst", value := .binaryPolitenessDistinction }
  , { walsCode := "per", iso := "pip", value := .noPolitenessDistinction }
  , { walsCode := "prs", iso := "pes", value := .binaryPolitenessDistinction }
  , { walsCode := "pip", iso := "ppl", value := .noPolitenessDistinction }
  , { walsCode := "prh", iso := "myp", value := .noPolitenessDistinction }
  , { walsCode := "pit", iso := "pjt", value := .noPolitenessDistinction }
  , { walsCode := "poh", iso := "pon", value := .multiplePolitenessDistinctions }
  , { walsCode := "pol", iso := "pol", value := .binaryPolitenessDistinction }
  , { walsCode := "pso", iso := "pom", value := .noPolitenessDistinction }
  , { walsCode := "por", iso := "por", value := .binaryPolitenessDistinction }
  , { walsCode := "qim", iso := "qvi", value := .binaryPolitenessDistinction }
  , { walsCode := "ram", iso := "rma", value := .noPolitenessDistinction }
  , { walsCode := "rap", iso := "rap", value := .noPolitenessDistinction }
  , { walsCode := "rom", iso := "ron", value := .multiplePolitenessDistinctions }
  , { walsCode := "rus", iso := "rus", value := .binaryPolitenessDistinction }
  , { walsCode := "san", iso := "sag", value := .binaryPolitenessDistinction }
  , { walsCode := "snm", iso := "xsu", value := .noPolitenessDistinction }
  , { walsCode := "sav", iso := "sdg", value := .noPolitenessDistinction }
  , { walsCode := "snt", iso := "set", value := .noPolitenessDistinction }
  , { walsCode := "sng", iso := "snc", value := .noPolitenessDistinction }
  , { walsCode := "snh", iso := "sin", value := .multiplePolitenessDistinctions }
  , { walsCode := "sla", iso := "den", value := .noPolitenessDistinction }
  , { walsCode := "som", iso := "som", value := .noPolitenessDistinction }
  , { walsCode := "spa", iso := "spa", value := .binaryPolitenessDistinction }
  , { walsCode := "sue", iso := "sue", value := .binaryPolitenessDistinction }
  , { walsCode := "sup", iso := "spp", value := .noPolitenessDistinction }
  , { walsCode := "swa", iso := "swh", value := .noPolitenessDistinction }
  , { walsCode := "swe", iso := "swe", value := .binaryPolitenessDistinction }
  , { walsCode := "tab", iso := "mky", value := .binaryPolitenessDistinction }
  , { walsCode := "tag", iso := "tgl", value := .multiplePolitenessDistinctions }
  , { walsCode := "tml", iso := "tam", value := .multiplePolitenessDistinctions }
  , { walsCode := "taw", iso := "tbo", value := .noPolitenessDistinction }
  , { walsCode := "tay", iso := "cks", value := .binaryPolitenessDistinction }
  , { walsCode := "ttn", iso := "tet", value := .binaryPolitenessDistinction }
  , { walsCode := "tha", iso := "tha", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "tib", iso := "bod", value := .binaryPolitenessDistinction }
  , { walsCode := "tiw", iso := "tiw", value := .noPolitenessDistinction }
  , { walsCode := "tli", iso := "tli", value := .noPolitenessDistinction }
  , { walsCode := "tuk", iso := "", value := .multiplePolitenessDistinctions }
  , { walsCode := "tur", iso := "tur", value := .binaryPolitenessDistinction }
  , { walsCode := "ura", iso := "uur", value := .noPolitenessDistinction }
  , { walsCode := "urd", iso := "urd", value := .multiplePolitenessDistinctions }
  , { walsCode := "vie", iso := "vie", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "wam", iso := "wmb", value := .noPolitenessDistinction }
  , { walsCode := "wra", iso := "wba", value := .noPolitenessDistinction }
  , { walsCode := "war", iso := "pav", value := .noPolitenessDistinction }
  , { walsCode := "wel", iso := "cym", value := .binaryPolitenessDistinction }
  , { walsCode := "wic", iso := "wic", value := .noPolitenessDistinction }
  , { walsCode := "wch", iso := "mzh", value := .noPolitenessDistinction }
  , { walsCode := "yag", iso := "yad", value := .noPolitenessDistinction }
  , { walsCode := "yaq", iso := "yaq", value := .noPolitenessDistinction }
  , { walsCode := "yim", iso := "yee", value := .noPolitenessDistinction }
  , { walsCode := "yin", iso := "yij", value := .noPolitenessDistinction }
  , { walsCode := "yor", iso := "yor", value := .binaryPolitenessDistinction }
  , { walsCode := "yct", iso := "yua", value := .noPolitenessDistinction }
  , { walsCode := "yko", iso := "yux", value := .noPolitenessDistinction }
  , { walsCode := "yur", iso := "yur", value := .noPolitenessDistinction }
  , { walsCode := "zqc", iso := "zoc", value := .noPolitenessDistinction }
  , { walsCode := "zul", iso := "zul", value := .noPolitenessDistinction }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F45A
