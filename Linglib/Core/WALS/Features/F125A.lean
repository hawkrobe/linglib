import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 125A: Purpose Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 125A`.

Chapter 125, 170 languages.
-/

namespace Core.WALS.F125A

/-- WALS 125A values. -/
inductive PurposeClauseType where
  /-- Balanced (38 languages). -/
  | balanced
  /-- Balanced/deranked (30 languages). -/
  | balancedDeranked
  /-- Deranked (102 languages). -/
  | deranked
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 125A dataset (170 languages). -/
def allData : List (Datapoint PurposeClauseType) :=
  [ { walsCode := "abk", iso := "abk", value := .balancedDeranked }
  , { walsCode := "abu", iso := "kgr", value := .deranked }
  , { walsCode := "ace", iso := "ace", value := .balanced }
  , { walsCode := "ain", iso := "ain", value := .balanced }
  , { walsCode := "akn", iso := "aka", value := .balancedDeranked }
  , { walsCode := "ala", iso := "amp", value := .deranked }
  , { walsCode := "ame", iso := "aey", value := .balancedDeranked }
  , { walsCode := "any", iso := "anu", value := .balancedDeranked }
  , { walsCode := "arg", iso := "afb", value := .balancedDeranked }
  , { walsCode := "arp", iso := "ape", value := .balanced }
  , { walsCode := "awp", iso := "kwi", value := .deranked }
  , { walsCode := "brs", iso := "bsn", value := .deranked }
  , { walsCode := "bsq", iso := "eus", value := .deranked }
  , { walsCode := "bkr", iso := "btx", value := .balanced }
  , { walsCode := "baw", iso := "bgr", value := .deranked }
  , { walsCode := "bma", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", iso := "brc", value := .deranked }
  , { walsCode := "brh", iso := "brh", value := .balancedDeranked }
  , { walsCode := "bur", iso := "bsk", value := .deranked }
  , { walsCode := "cah", iso := "chl", value := .deranked }
  , { walsCode := "cle", iso := "cle", value := .balanced }
  , { walsCode := "dni", iso := "dni", value := .deranked }
  , { walsCode := "djp", iso := "dwu", value := .deranked }
  , { walsCode := "dre", iso := "dhv", value := .balanced }
  , { walsCode := "emb", iso := "emp", value := .deranked }
  , { walsCode := "eng", iso := "eng", value := .balancedDeranked }
  , { walsCode := "epe", iso := "sja", value := .deranked }
  , { walsCode := "err", iso := "erg", value := .deranked }
  , { walsCode := "eve", iso := "evn", value := .deranked }
  , { walsCode := "fij", iso := "fij", value := .balanced }
  , { walsCode := "fin", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", iso := "fra", value := .deranked }
  , { walsCode := "fua", iso := "fub", value := .deranked }
  , { walsCode := "geo", iso := "kat", value := .balancedDeranked }
  , { walsCode := "ger", iso := "deu", value := .balancedDeranked }
  , { walsCode := "gim", iso := "bcq", value := .deranked }
  , { walsCode := "goo", iso := "gni", value := .balancedDeranked }
  , { walsCode := "grb", iso := "grj", value := .deranked }
  , { walsCode := "grk", iso := "ell", value := .deranked }
  , { walsCode := "grw", iso := "kal", value := .deranked }
  , { walsCode := "gua", iso := "gug", value := .balanced }
  , { walsCode := "gum", iso := "kgs", value := .deranked }
  , { walsCode := "guu", iso := "kky", value := .deranked }
  , { walsCode := "ham", iso := "hmt", value := .deranked }
  , { walsCode := "hau", iso := "hau", value := .deranked }
  , { walsCode := "heb", iso := "heb", value := .balancedDeranked }
  , { walsCode := "hix", iso := "hix", value := .deranked }
  , { walsCode := "hmo", iso := "hnj", value := .balanced }
  , { walsCode := "ho", iso := "hoc", value := .deranked }
  , { walsCode := "hun", iso := "hun", value := .deranked }
  , { walsCode := "hzb", iso := "huz", value := .deranked }
  , { walsCode := "igb", iso := "ibo", value := .deranked }
  , { walsCode := "ijo", iso := "ijc", value := .deranked }
  , { walsCode := "ika", iso := "arh", value := .deranked }
  , { walsCode := "ind", iso := "ind", value := .balanced }
  , { walsCode := "ing", iso := "inh", value := .deranked }
  , { walsCode := "irq", iso := "irk", value := .deranked }
  , { walsCode := "iri", iso := "gle", value := .balancedDeranked }
  , { walsCode := "ita", iso := "ita", value := .deranked }
  , { walsCode := "itz", iso := "itz", value := .deranked }
  , { walsCode := "jpn", iso := "jpn", value := .balancedDeranked }
  , { walsCode := "juh", iso := "ktz", value := .balanced }
  , { walsCode := "kan", iso := "ogo", value := .balancedDeranked }
  , { walsCode := "knd", iso := "kan", value := .deranked }
  , { walsCode := "knr", iso := "knc", value := .deranked }
  , { walsCode := "kmj", iso := "kdj", value := .balancedDeranked }
  , { walsCode := "kas", iso := "kas", value := .deranked }
  , { walsCode := "kay", iso := "gyd", value := .balanced }
  , { walsCode := "kew", iso := "kew", value := .deranked }
  , { walsCode := "kha", iso := "khk", value := .deranked }
  , { walsCode := "khs", iso := "kha", value := .deranked }
  , { walsCode := "kmu", iso := "kjg", value := .balanced }
  , { walsCode := "klv", iso := "kij", value := .balanced }
  , { walsCode := "kio", iso := "kio", value := .deranked }
  , { walsCode := "kob", iso := "kpw", value := .deranked }
  , { walsCode := "kor", iso := "kor", value := .balanced }
  , { walsCode := "kfe", iso := "kfz", value := .balancedDeranked }
  , { walsCode := "kch", iso := "khq", value := .deranked }
  , { walsCode := "kro", iso := "kgo", value := .deranked }
  , { walsCode := "lkt", iso := "lkt", value := .balanced }
  , { walsCode := "lan", iso := "laj", value := .deranked }
  , { walsCode := "lav", iso := "lvk", value := .deranked }
  , { walsCode := "lez", iso := "lez", value := .deranked }
  , { walsCode := "lim", iso := "lif", value := .deranked }
  , { walsCode := "lnd", iso := "liy", value := .balanced }
  , { walsCode := "luv", iso := "lue", value := .deranked }
  , { walsCode := "mal", iso := "plt", value := .balanced }
  , { walsCode := "mym", iso := "mal", value := .deranked }
  , { walsCode := "mnd", iso := "cmn", value := .balanced }
  , { walsCode := "myi", iso := "mpc", value := .deranked }
  , { walsCode := "mao", iso := "mri", value := .deranked }
  , { walsCode := "map", iso := "arn", value := .deranked }
  , { walsCode := "mku", iso := "zmr", value := .balanced }
  , { walsCode := "mhi", iso := "mar", value := .deranked }
  , { walsCode := "mrt", iso := "vma", value := .deranked }
  , { walsCode := "may", iso := "ayz", value := .balanced }
  , { walsCode := "mei", iso := "mni", value := .deranked }
  , { walsCode := "mxc", iso := "mig", value := .balanced }
  , { walsCode := "miy", iso := "mkf", value := .deranked }
  , { walsCode := "mok", iso := "mkj", value := .deranked }
  , { walsCode := "mna", iso := "mnb", value := .balanced }
  , { walsCode := "ngt", iso := "nmf", value := .deranked }
  , { walsCode := "nht", iso := "nhg", value := .balancedDeranked }
  , { walsCode := "kho", iso := "naq", value := .balanced }
  , { walsCode := "ndy", iso := "djk", value := .balancedDeranked }
  , { walsCode := "nbm", iso := "nbm", value := .balancedDeranked }
  , { walsCode := "nti", iso := "niy", value := .deranked }
  , { walsCode := "npi", iso := "pcm", value := .deranked }
  , { walsCode := "niv", iso := "niv", value := .deranked }
  , { walsCode := "nko", iso := "cgg", value := .deranked }
  , { walsCode := "noo", iso := "snf", value := .deranked }
  , { walsCode := "nbd", iso := "dgl", value := .deranked }
  , { walsCode := "nun", iso := "nut", value := .balanced }
  , { walsCode := "nug", iso := "nuy", value := .deranked }
  , { walsCode := "orh", iso := "hae", value := .deranked }
  , { walsCode := "pai", iso := "pwn", value := .balanced }
  , { walsCode := "pan", iso := "pan", value := .deranked }
  , { walsCode := "psm", iso := "pqm", value := .balancedDeranked }
  , { walsCode := "pau", iso := "pad", value := .balancedDeranked }
  , { walsCode := "per", iso := "pip", value := .deranked }
  , { walsCode := "prs", iso := "pes", value := .deranked }
  , { walsCode := "prh", iso := "myp", value := .balancedDeranked }
  , { walsCode := "pit", iso := "pjt", value := .deranked }
  , { walsCode := "pur", iso := "tsz", value := .deranked }
  , { walsCode := "qhu", iso := "qub", value := .deranked }
  , { walsCode := "ram", iso := "rma", value := .deranked }
  , { walsCode := "rap", iso := "rap", value := .deranked }
  , { walsCode := "res", iso := "rgr", value := .deranked }
  , { walsCode := "ret", iso := "tnc", value := .deranked }
  , { walsCode := "rus", iso := "rus", value := .balancedDeranked }
  , { walsCode := "snm", iso := "xsu", value := .deranked }
  , { walsCode := "saw", iso := "hvn", value := .balanced }
  , { walsCode := "sml", iso := "sza", value := .balanced }
  , { walsCode := "shk", iso := "shp", value := .deranked }
  , { walsCode := "sng", iso := "snc", value := .balancedDeranked }
  , { walsCode := "sla", iso := "den", value := .balanced }
  , { walsCode := "som", iso := "som", value := .balanced }
  , { walsCode := "spa", iso := "spa", value := .deranked }
  , { walsCode := "sup", iso := "spp", value := .balancedDeranked }
  , { walsCode := "tab", iso := "mky", value := .balanced }
  , { walsCode := "tag", iso := "tgl", value := .deranked }
  , { walsCode := "tml", iso := "tam", value := .deranked }
  , { walsCode := "thk", iso := "ths", value := .deranked }
  , { walsCode := "tja", iso := "dih", value := .deranked }
  , { walsCode := "tin", iso := "cir", value := .balanced }
  , { walsCode := "tpi", iso := "tpi", value := .balanced }
  , { walsCode := "tru", iso := "tpy", value := .balancedDeranked }
  , { walsCode := "tuk", iso := "", value := .balancedDeranked }
  , { walsCode := "tur", iso := "tur", value := .deranked }
  , { walsCode := "tvl", iso := "tvl", value := .deranked }
  , { walsCode := "tzu", iso := "tzj", value := .deranked }
  , { walsCode := "tsh", iso := "par", value := .deranked }
  , { walsCode := "ung", iso := "ung", value := .deranked }
  , { walsCode := "ute", iso := "ute", value := .deranked }
  , { walsCode := "vai", iso := "vai", value := .deranked }
  , { walsCode := "vie", iso := "vie", value := .balanced }
  , { walsCode := "wam", iso := "wmb", value := .deranked }
  , { walsCode := "wra", iso := "wba", value := .deranked }
  , { walsCode := "wrd", iso := "wrr", value := .deranked }
  , { walsCode := "war", iso := "pav", value := .balanced }
  , { walsCode := "wrg", iso := "wgy", value := .deranked }
  , { walsCode := "way", iso := "oym", value := .balancedDeranked }
  , { walsCode := "wma", iso := "mqs", value := .balanced }
  , { walsCode := "yag", iso := "yad", value := .deranked }
  , { walsCode := "yaq", iso := "yaq", value := .balanced }
  , { walsCode := "yid", iso := "yii", value := .deranked }
  , { walsCode := "yim", iso := "yee", value := .deranked }
  , { walsCode := "yor", iso := "yor", value := .balanced }
  , { walsCode := "yko", iso := "yux", value := .deranked }
  , { walsCode := "zul", iso := "zul", value := .deranked }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F125A
