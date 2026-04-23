import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 128A: Utterance Complement Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 128A`.

Chapter 128, 143 languages.
-/

namespace Datasets.WALS.F128A

/-- WALS 128A values. -/
inductive UtteranceComplementType where
  /-- Balanced (114 languages). -/
  | balanced
  /-- Balanced/deranked (18 languages). -/
  | balancedDeranked
  /-- Deranked (11 languages). -/
  | deranked
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 128A dataset (143 languages). -/
def allData : List (Datapoint UtteranceComplementType) :=
  [ { walsCode := "abk", iso := "abk", value := .balancedDeranked }
  , { walsCode := "abu", iso := "kgr", value := .balanced }
  , { walsCode := "ace", iso := "ace", value := .balanced }
  , { walsCode := "aco", iso := "kjq", value := .balanced }
  , { walsCode := "ain", iso := "ain", value := .balanced }
  , { walsCode := "akn", iso := "aka", value := .balanced }
  , { walsCode := "ame", iso := "aey", value := .balanced }
  , { walsCode := "any", iso := "anu", value := .balanced }
  , { walsCode := "apu", iso := "apu", value := .balanced }
  , { walsCode := "arg", iso := "afb", value := .balancedDeranked }
  , { walsCode := "arp", iso := "ape", value := .balanced }
  , { walsCode := "awp", iso := "kwi", value := .deranked }
  , { walsCode := "brs", iso := "bsn", value := .balanced }
  , { walsCode := "bsq", iso := "eus", value := .balanced }
  , { walsCode := "bkr", iso := "btx", value := .balanced }
  , { walsCode := "bma", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", iso := "brc", value := .balanced }
  , { walsCode := "brh", iso := "brh", value := .balanced }
  , { walsCode := "bur", iso := "bsk", value := .balanced }
  , { walsCode := "cah", iso := "chl", value := .deranked }
  , { walsCode := "cnl", iso := "ram", value := .balanced }
  , { walsCode := "djp", iso := "dwu", value := .balanced }
  , { walsCode := "dre", iso := "dhv", value := .balanced }
  , { walsCode := "emb", iso := "emp", value := .deranked }
  , { walsCode := "eng", iso := "eng", value := .balanced }
  , { walsCode := "epe", iso := "sja", value := .balanced }
  , { walsCode := "err", iso := "erg", value := .balanced }
  , { walsCode := "eve", iso := "evn", value := .deranked }
  , { walsCode := "fij", iso := "fij", value := .balanced }
  , { walsCode := "fin", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", iso := "fra", value := .balancedDeranked }
  , { walsCode := "geo", iso := "kat", value := .balanced }
  , { walsCode := "gim", iso := "bcq", value := .balanced }
  , { walsCode := "goo", iso := "gni", value := .balanced }
  , { walsCode := "grk", iso := "ell", value := .balanced }
  , { walsCode := "grw", iso := "kal", value := .balancedDeranked }
  , { walsCode := "gum", iso := "kgs", value := .balanced }
  , { walsCode := "heb", iso := "heb", value := .balanced }
  , { walsCode := "hin", iso := "hin", value := .balanced }
  , { walsCode := "hix", iso := "hix", value := .balanced }
  , { walsCode := "hmo", iso := "hnj", value := .balanced }
  , { walsCode := "ho", iso := "hoc", value := .balanced }
  , { walsCode := "hun", iso := "hun", value := .balanced }
  , { walsCode := "igb", iso := "ibo", value := .balanced }
  , { walsCode := "ika", iso := "arh", value := .balanced }
  , { walsCode := "ind", iso := "ind", value := .balanced }
  , { walsCode := "ing", iso := "inh", value := .balancedDeranked }
  , { walsCode := "iri", iso := "gle", value := .balanced }
  , { walsCode := "ita", iso := "ita", value := .balancedDeranked }
  , { walsCode := "itz", iso := "itz", value := .balanced }
  , { walsCode := "jak", iso := "jac", value := .balanced }
  , { walsCode := "jpn", iso := "jpn", value := .balanced }
  , { walsCode := "juh", iso := "ktz", value := .balanced }
  , { walsCode := "kan", iso := "ogo", value := .balanced }
  , { walsCode := "knd", iso := "kan", value := .balancedDeranked }
  , { walsCode := "knr", iso := "knc", value := .balanced }
  , { walsCode := "kmj", iso := "kdj", value := .balanced }
  , { walsCode := "kas", iso := "kas", value := .balanced }
  , { walsCode := "kay", iso := "gyd", value := .balanced }
  , { walsCode := "kew", iso := "kew", value := .balanced }
  , { walsCode := "khs", iso := "kha", value := .balanced }
  , { walsCode := "kmu", iso := "kjg", value := .balanced }
  , { walsCode := "kio", iso := "kio", value := .balanced }
  , { walsCode := "kor", iso := "kor", value := .balanced }
  , { walsCode := "kfe", iso := "kfz", value := .balancedDeranked }
  , { walsCode := "kch", iso := "khq", value := .balanced }
  , { walsCode := "kro", iso := "kgo", value := .balancedDeranked }
  , { walsCode := "lkt", iso := "lkt", value := .balanced }
  , { walsCode := "lan", iso := "laj", value := .balanced }
  , { walsCode := "lez", iso := "lez", value := .balancedDeranked }
  , { walsCode := "lim", iso := "lif", value := .balanced }
  , { walsCode := "lnd", iso := "liy", value := .balanced }
  , { walsCode := "mym", iso := "mal", value := .balanced }
  , { walsCode := "mnd", iso := "cmn", value := .balanced }
  , { walsCode := "myi", iso := "mpc", value := .balanced }
  , { walsCode := "mhi", iso := "mar", value := .balanced }
  , { walsCode := "mar", iso := "mrc", value := .balancedDeranked }
  , { walsCode := "mrt", iso := "vma", value := .deranked }
  , { walsCode := "may", iso := "ayz", value := .balanced }
  , { walsCode := "mei", iso := "mni", value := .balanced }
  , { walsCode := "mxc", iso := "mig", value := .balanced }
  , { walsCode := "miy", iso := "mkf", value := .balanced }
  , { walsCode := "mna", iso := "mnb", value := .balanced }
  , { walsCode := "mup", iso := "sur", value := .balancedDeranked }
  , { walsCode := "ngt", iso := "nmf", value := .balanced }
  , { walsCode := "nht", iso := "nhg", value := .balanced }
  , { walsCode := "kho", iso := "naq", value := .balanced }
  , { walsCode := "nan", iso := "niq", value := .balanced }
  , { walsCode := "ndy", iso := "djk", value := .balanced }
  , { walsCode := "nbm", iso := "nbm", value := .balanced }
  , { walsCode := "ngi", iso := "wyb", value := .balanced }
  , { walsCode := "npi", iso := "pcm", value := .balanced }
  , { walsCode := "niv", iso := "niv", value := .deranked }
  , { walsCode := "nko", iso := "cgg", value := .balanced }
  , { walsCode := "noo", iso := "snf", value := .balanced }
  , { walsCode := "nbd", iso := "dgl", value := .balanced }
  , { walsCode := "nun", iso := "nut", value := .balanced }
  , { walsCode := "nug", iso := "nuy", value := .balanced }
  , { walsCode := "orb", iso := "gax", value := .balanced }
  , { walsCode := "otm", iso := "ote", value := .balanced }
  , { walsCode := "pms", iso := "pma", value := .balanced }
  , { walsCode := "pan", iso := "pan", value := .balanced }
  , { walsCode := "per", iso := "pip", value := .balanced }
  , { walsCode := "prs", iso := "pes", value := .balanced }
  , { walsCode := "prh", iso := "myp", value := .balanced }
  , { walsCode := "pit", iso := "pjt", value := .balanced }
  , { walsCode := "qhu", iso := "qub", value := .balanced }
  , { walsCode := "ram", iso := "rma", value := .balanced }
  , { walsCode := "res", iso := "rgr", value := .deranked }
  , { walsCode := "ret", iso := "tnc", value := .balanced }
  , { walsCode := "rus", iso := "rus", value := .balanced }
  , { walsCode := "saw", iso := "hvn", value := .balanced }
  , { walsCode := "sml", iso := "sza", value := .balanced }
  , { walsCode := "sla", iso := "den", value := .balanced }
  , { walsCode := "spa", iso := "spa", value := .balancedDeranked }
  , { walsCode := "squ", iso := "squ", value := .deranked }
  , { walsCode := "sup", iso := "spp", value := .balanced }
  , { walsCode := "swa", iso := "swh", value := .balanced }
  , { walsCode := "tab", iso := "mky", value := .balanced }
  , { walsCode := "tag", iso := "tgl", value := .balanced }
  , { walsCode := "tml", iso := "tam", value := .deranked }
  , { walsCode := "thk", iso := "ths", value := .deranked }
  , { walsCode := "tpi", iso := "tpi", value := .balanced }
  , { walsCode := "tru", iso := "tpy", value := .deranked }
  , { walsCode := "tuk", iso := "", value := .balanced }
  , { walsCode := "tur", iso := "tur", value := .balancedDeranked }
  , { walsCode := "tvl", iso := "tvl", value := .balanced }
  , { walsCode := "tzu", iso := "tzj", value := .balanced }
  , { walsCode := "tsh", iso := "par", value := .balanced }
  , { walsCode := "udh", iso := "ude", value := .balancedDeranked }
  , { walsCode := "ung", iso := "ung", value := .balanced }
  , { walsCode := "urk", iso := "urb", value := .balanced }
  , { walsCode := "ute", iso := "ute", value := .balanced }
  , { walsCode := "vai", iso := "vai", value := .balanced }
  , { walsCode := "vie", iso := "vie", value := .balanced }
  , { walsCode := "wra", iso := "wba", value := .balanced }
  , { walsCode := "war", iso := "pav", value := .balanced }
  , { walsCode := "way", iso := "oym", value := .balanced }
  , { walsCode := "wma", iso := "mqs", value := .balanced }
  , { walsCode := "yag", iso := "yad", value := .balanced }
  , { walsCode := "yaq", iso := "yaq", value := .balanced }
  , { walsCode := "yor", iso := "yor", value := .balanced }
  , { walsCode := "yko", iso := "yux", value := .balancedDeranked }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F128A
