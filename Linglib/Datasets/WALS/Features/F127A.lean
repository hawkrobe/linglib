import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 127A: Reason Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 127A`.

Chapter 127, 169 languages.
-/

namespace Datasets.WALS.F127A

/-- WALS 127A values. -/
inductive ReasonClauseType where
  /-- Balanced (90 languages). -/
  | balanced
  /-- Balanced/deranked (37 languages). -/
  | balancedDeranked
  /-- Deranked (42 languages). -/
  | deranked
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 127A dataset (169 languages). -/
def allData : List (Datapoint ReasonClauseType) :=
  [ { walsCode := "abk", iso := "abk", value := .deranked }
  , { walsCode := "abu", iso := "kgr", value := .balanced }
  , { walsCode := "ace", iso := "ace", value := .balanced }
  , { walsCode := "ain", iso := "ain", value := .balanced }
  , { walsCode := "akn", iso := "aka", value := .balancedDeranked }
  , { walsCode := "ala", iso := "amp", value := .deranked }
  , { walsCode := "ame", iso := "aey", value := .balanced }
  , { walsCode := "any", iso := "anu", value := .balanced }
  , { walsCode := "apu", iso := "apu", value := .balanced }
  , { walsCode := "arg", iso := "afb", value := .balancedDeranked }
  , { walsCode := "awp", iso := "kwi", value := .deranked }
  , { walsCode := "brs", iso := "bsn", value := .deranked }
  , { walsCode := "bsq", iso := "eus", value := .balancedDeranked }
  , { walsCode := "bkr", iso := "btx", value := .balanced }
  , { walsCode := "bma", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", iso := "brc", value := .deranked }
  , { walsCode := "brh", iso := "brh", value := .balanced }
  , { walsCode := "bur", iso := "bsk", value := .balanced }
  , { walsCode := "cah", iso := "chl", value := .balancedDeranked }
  , { walsCode := "cnl", iso := "ram", value := .balanced }
  , { walsCode := "cha", iso := "cha", value := .balanced }
  , { walsCode := "cle", iso := "cle", value := .balanced }
  , { walsCode := "dni", iso := "dni", value := .balancedDeranked }
  , { walsCode := "die", iso := "dih", value := .deranked }
  , { walsCode := "djp", iso := "dwu", value := .balancedDeranked }
  , { walsCode := "dre", iso := "dhv", value := .balanced }
  , { walsCode := "emb", iso := "emp", value := .balanced }
  , { walsCode := "eng", iso := "eng", value := .balancedDeranked }
  , { walsCode := "epe", iso := "sja", value := .balanced }
  , { walsCode := "eve", iso := "evn", value := .deranked }
  , { walsCode := "ewe", iso := "ewe", value := .balanced }
  , { walsCode := "fij", iso := "fij", value := .balanced }
  , { walsCode := "fin", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", iso := "fra", value := .balancedDeranked }
  , { walsCode := "fua", iso := "fub", value := .balanced }
  , { walsCode := "geo", iso := "kat", value := .balanced }
  , { walsCode := "ger", iso := "deu", value := .balanced }
  , { walsCode := "gim", iso := "bcq", value := .deranked }
  , { walsCode := "goo", iso := "gni", value := .deranked }
  , { walsCode := "grk", iso := "ell", value := .balanced }
  , { walsCode := "grw", iso := "kal", value := .deranked }
  , { walsCode := "gua", iso := "gug", value := .balanced }
  , { walsCode := "ham", iso := "hmt", value := .deranked }
  , { walsCode := "hau", iso := "hau", value := .balanced }
  , { walsCode := "heb", iso := "heb", value := .balanced }
  , { walsCode := "hin", iso := "hin", value := .balancedDeranked }
  , { walsCode := "hix", iso := "hix", value := .deranked }
  , { walsCode := "hmo", iso := "hnj", value := .balanced }
  , { walsCode := "ho", iso := "hoc", value := .balancedDeranked }
  , { walsCode := "hlp", iso := "yuf", value := .deranked }
  , { walsCode := "hun", iso := "hun", value := .balanced }
  , { walsCode := "hzb", iso := "huz", value := .deranked }
  , { walsCode := "igb", iso := "ibo", value := .deranked }
  , { walsCode := "ijo", iso := "ijc", value := .deranked }
  , { walsCode := "ika", iso := "arh", value := .balanced }
  , { walsCode := "imo", iso := "imn", value := .balanced }
  , { walsCode := "ind", iso := "ind", value := .balanced }
  , { walsCode := "irq", iso := "irk", value := .deranked }
  , { walsCode := "iri", iso := "gle", value := .balancedDeranked }
  , { walsCode := "ita", iso := "ita", value := .balancedDeranked }
  , { walsCode := "jpn", iso := "jpn", value := .balanced }
  , { walsCode := "juh", iso := "ktz", value := .balanced }
  , { walsCode := "kan", iso := "ogo", value := .balanced }
  , { walsCode := "knd", iso := "kan", value := .deranked }
  , { walsCode := "knr", iso := "knc", value := .balanced }
  , { walsCode := "kmj", iso := "kdj", value := .balancedDeranked }
  , { walsCode := "kas", iso := "kas", value := .balancedDeranked }
  , { walsCode := "kay", iso := "gyd", value := .balanced }
  , { walsCode := "kew", iso := "kew", value := .balanced }
  , { walsCode := "khs", iso := "kha", value := .balanced }
  , { walsCode := "klv", iso := "kij", value := .balanced }
  , { walsCode := "kio", iso := "kio", value := .balancedDeranked }
  , { walsCode := "krb", iso := "gil", value := .balanced }
  , { walsCode := "kob", iso := "kpw", value := .balancedDeranked }
  , { walsCode := "kor", iso := "kor", value := .balanced }
  , { walsCode := "kfe", iso := "kfz", value := .balanced }
  , { walsCode := "kro", iso := "kgo", value := .balanced }
  , { walsCode := "lkt", iso := "lkt", value := .balanced }
  , { walsCode := "lan", iso := "laj", value := .balanced }
  , { walsCode := "lav", iso := "lvk", value := .deranked }
  , { walsCode := "lez", iso := "lez", value := .balancedDeranked }
  , { walsCode := "lim", iso := "lif", value := .balancedDeranked }
  , { walsCode := "lnd", iso := "liy", value := .balanced }
  , { walsCode := "luv", iso := "lue", value := .balancedDeranked }
  , { walsCode := "mal", iso := "plt", value := .balanced }
  , { walsCode := "mym", iso := "mal", value := .balancedDeranked }
  , { walsCode := "mnd", iso := "cmn", value := .balanced }
  , { walsCode := "myi", iso := "mpc", value := .balanced }
  , { walsCode := "mao", iso := "mri", value := .balanced }
  , { walsCode := "map", iso := "arn", value := .balancedDeranked }
  , { walsCode := "mku", iso := "zmr", value := .balanced }
  , { walsCode := "mhi", iso := "mar", value := .balancedDeranked }
  , { walsCode := "mar", iso := "mrc", value := .deranked }
  , { walsCode := "mrt", iso := "vma", value := .deranked }
  , { walsCode := "may", iso := "ayz", value := .balanced }
  , { walsCode := "mei", iso := "mni", value := .deranked }
  , { walsCode := "mxc", iso := "mig", value := .balanced }
  , { walsCode := "miy", iso := "mkf", value := .balanced }
  , { walsCode := "mok", iso := "mkj", value := .balanced }
  , { walsCode := "mna", iso := "mnb", value := .balanced }
  , { walsCode := "ngt", iso := "nmf", value := .deranked }
  , { walsCode := "nht", iso := "nhg", value := .balanced }
  , { walsCode := "kho", iso := "naq", value := .balanced }
  , { walsCode := "ndy", iso := "djk", value := .balanced }
  , { walsCode := "nbm", iso := "nbm", value := .balancedDeranked }
  , { walsCode := "nti", iso := "niy", value := .balanced }
  , { walsCode := "ngi", iso := "wyb", value := .deranked }
  , { walsCode := "npi", iso := "pcm", value := .balanced }
  , { walsCode := "niv", iso := "niv", value := .deranked }
  , { walsCode := "nko", iso := "cgg", value := .balancedDeranked }
  , { walsCode := "noo", iso := "snf", value := .balanced }
  , { walsCode := "nbd", iso := "dgl", value := .deranked }
  , { walsCode := "nun", iso := "nut", value := .balanced }
  , { walsCode := "orh", iso := "hae", value := .balanced }
  , { walsCode := "otm", iso := "ote", value := .balanced }
  , { walsCode := "pai", iso := "pwn", value := .balanced }
  , { walsCode := "pan", iso := "pan", value := .balancedDeranked }
  , { walsCode := "psm", iso := "pqm", value := .balancedDeranked }
  , { walsCode := "pau", iso := "pad", value := .deranked }
  , { walsCode := "per", iso := "pip", value := .balanced }
  , { walsCode := "prs", iso := "pes", value := .balanced }
  , { walsCode := "prh", iso := "myp", value := .balanced }
  , { walsCode := "pit", iso := "pjt", value := .deranked }
  , { walsCode := "qhu", iso := "qub", value := .deranked }
  , { walsCode := "ram", iso := "rma", value := .balancedDeranked }
  , { walsCode := "rap", iso := "rap", value := .deranked }
  , { walsCode := "res", iso := "rgr", value := .deranked }
  , { walsCode := "ret", iso := "tnc", value := .deranked }
  , { walsCode := "rus", iso := "rus", value := .balancedDeranked }
  , { walsCode := "san", iso := "sag", value := .balanced }
  , { walsCode := "snm", iso := "xsu", value := .deranked }
  , { walsCode := "sml", iso := "sza", value := .balanced }
  , { walsCode := "sng", iso := "snc", value := .balanced }
  , { walsCode := "sla", iso := "den", value := .balanced }
  , { walsCode := "som", iso := "som", value := .balanced }
  , { walsCode := "spa", iso := "spa", value := .balancedDeranked }
  , { walsCode := "sup", iso := "spp", value := .balanced }
  , { walsCode := "tab", iso := "mky", value := .balanced }
  , { walsCode := "tag", iso := "tgl", value := .balancedDeranked }
  , { walsCode := "tml", iso := "tam", value := .deranked }
  , { walsCode := "thk", iso := "ths", value := .balancedDeranked }
  , { walsCode := "tin", iso := "cir", value := .balanced }
  , { walsCode := "tiw", iso := "tiw", value := .balanced }
  , { walsCode := "tpi", iso := "tpi", value := .balanced }
  , { walsCode := "tru", iso := "tpy", value := .balanced }
  , { walsCode := "tuk", iso := "", value := .balanced }
  , { walsCode := "tur", iso := "tur", value := .balancedDeranked }
  , { walsCode := "tvl", iso := "tvl", value := .balancedDeranked }
  , { walsCode := "tzu", iso := "tzj", value := .balanced }
  , { walsCode := "tsh", iso := "par", value := .deranked }
  , { walsCode := "udh", iso := "ude", value := .deranked }
  , { walsCode := "ung", iso := "ung", value := .balanced }
  , { walsCode := "urk", iso := "urb", value := .balanced }
  , { walsCode := "ute", iso := "ute", value := .deranked }
  , { walsCode := "vai", iso := "vai", value := .deranked }
  , { walsCode := "vie", iso := "vie", value := .balanced }
  , { walsCode := "wam", iso := "wmb", value := .balanced }
  , { walsCode := "wra", iso := "wba", value := .balanced }
  , { walsCode := "wrd", iso := "wrr", value := .balanced }
  , { walsCode := "war", iso := "pav", value := .balancedDeranked }
  , { walsCode := "way", iso := "oym", value := .balancedDeranked }
  , { walsCode := "wma", iso := "mqs", value := .balanced }
  , { walsCode := "yag", iso := "yad", value := .deranked }
  , { walsCode := "yaq", iso := "yaq", value := .balanced }
  , { walsCode := "yim", iso := "yee", value := .balanced }
  , { walsCode := "yor", iso := "yor", value := .balanced }
  , { walsCode := "yko", iso := "yux", value := .deranked }
  , { walsCode := "ypk", iso := "esu", value := .deranked }
  , { walsCode := "zul", iso := "zul", value := .deranked }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F127A
