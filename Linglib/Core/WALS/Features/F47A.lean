import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 47A: Intensifiers and Reflexive Pronouns
@cite{koenig-siemund-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 47A`.

Chapter 47, 168 languages.
-/

namespace Core.WALS.F47A

/-- WALS 47A values. -/
inductive IntensifierReflexive where
  /-- Identical (94 languages). -/
  | identical
  /-- Differentiated (74 languages). -/
  | differentiated
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 47A dataset (168 languages). -/
def allData : List (Datapoint IntensifierReflexive) :=
  [ { walsCode := "abk", iso := "abk", value := .differentiated }
  , { walsCode := "afr", iso := "afr", value := .identical }
  , { walsCode := "ala", iso := "amp", value := .identical }
  , { walsCode := "ame", iso := "aey", value := .identical }
  , { walsCode := "amh", iso := "amh", value := .identical }
  , { walsCode := "apu", iso := "apu", value := .differentiated }
  , { walsCode := "arg", iso := "afb", value := .identical }
  , { walsCode := "arm", iso := "hye", value := .identical }
  , { walsCode := "asm", iso := "cns", value := .identical }
  , { walsCode := "awp", iso := "kwi", value := .differentiated }
  , { walsCode := "bag", iso := "bmi", value := .identical }
  , { walsCode := "bgv", iso := "kva", value := .identical }
  , { walsCode := "bsq", iso := "eus", value := .differentiated }
  , { walsCode := "bkr", iso := "btx", value := .differentiated }
  , { walsCode := "ben", iso := "ben", value := .identical }
  , { walsCode := "brh", iso := "brh", value := .identical }
  , { walsCode := "bul", iso := "bul", value := .differentiated }
  , { walsCode := "brm", iso := "mya", value := .identical }
  , { walsCode := "bur", iso := "bsk", value := .identical }
  , { walsCode := "cnl", iso := "ram", value := .differentiated }
  , { walsCode := "cnt", iso := "yue", value := .identical }
  , { walsCode := "ctl", iso := "cat", value := .differentiated }
  , { walsCode := "cha", iso := "cha", value := .identical }
  , { walsCode := "cle", iso := "cle", value := .identical }
  , { walsCode := "cmn", iso := "com", value := .differentiated }
  , { walsCode := "coo", iso := "csz", value := .differentiated }
  , { walsCode := "cub", iso := "cub", value := .differentiated }
  , { walsCode := "dsh", iso := "dan", value := .identical }
  , { walsCode := "dre", iso := "dhv", value := .differentiated }
  , { walsCode := "dut", iso := "nld", value := .identical }
  , { walsCode := "eng", iso := "eng", value := .identical }
  , { walsCode := "eve", iso := "evn", value := .identical }
  , { walsCode := "ewe", iso := "ewe", value := .differentiated }
  , { walsCode := "fij", iso := "fij", value := .differentiated }
  , { walsCode := "fin", iso := "fin", value := .identical }
  , { walsCode := "fre", iso := "fra", value := .differentiated }
  , { walsCode := "fur", iso := "fvr", value := .identical }
  , { walsCode := "gar", iso := "grt", value := .identical }
  , { walsCode := "geo", iso := "kat", value := .identical }
  , { walsCode := "ger", iso := "deu", value := .differentiated }
  , { walsCode := "god", iso := "gdo", value := .identical }
  , { walsCode := "goo", iso := "gni", value := .identical }
  , { walsCode := "grk", iso := "ell", value := .differentiated }
  , { walsCode := "grw", iso := "kal", value := .identical }
  , { walsCode := "guj", iso := "guj", value := .identical }
  , { walsCode := "heb", iso := "heb", value := .identical }
  , { walsCode := "hin", iso := "hin", value := .identical }
  , { walsCode := "hix", iso := "hix", value := .differentiated }
  , { walsCode := "hmo", iso := "hnj", value := .identical }
  , { walsCode := "hun", iso := "hun", value := .identical }
  , { walsCode := "ice", iso := "isl", value := .differentiated }
  , { walsCode := "imo", iso := "imn", value := .identical }
  , { walsCode := "ind", iso := "ind", value := .identical }
  , { walsCode := "ing", iso := "inh", value := .identical }
  , { walsCode := "iri", iso := "gle", value := .identical }
  , { walsCode := "ita", iso := "ita", value := .differentiated }
  , { walsCode := "jpn", iso := "jpn", value := .identical }
  , { walsCode := "jun", iso := "jun", value := .identical }
  , { walsCode := "juh", iso := "ktz", value := .identical }
  , { walsCode := "knd", iso := "kan", value := .identical }
  , { walsCode := "krk", iso := "kyh", value := .differentiated }
  , { walsCode := "kas", iso := "kas", value := .identical }
  , { walsCode := "kay", iso := "gyd", value := .identical }
  , { walsCode := "ket", iso := "ket", value := .differentiated }
  , { walsCode := "kha", iso := "khk", value := .identical }
  , { walsCode := "khs", iso := "kha", value := .differentiated }
  , { walsCode := "khm", iso := "khm", value := .identical }
  , { walsCode := "kmu", iso := "kjg", value := .differentiated }
  , { walsCode := "kin", iso := "kin", value := .differentiated }
  , { walsCode := "kio", iso := "kio", value := .differentiated }
  , { walsCode := "koa", iso := "cku", value := .differentiated }
  , { walsCode := "kob", iso := "kpw", value := .identical }
  , { walsCode := "kor", iso := "kor", value := .identical }
  , { walsCode := "kfe", iso := "kfz", value := .identical }
  , { walsCode := "ktt", iso := "", value := .differentiated }
  , { walsCode := "kch", iso := "khq", value := .differentiated }
  , { walsCode := "kse", iso := "ses", value := .differentiated }
  , { walsCode := "knm", iso := "kun", value := .differentiated }
  , { walsCode := "kut", iso := "kut", value := .differentiated }
  , { walsCode := "lkt", iso := "lkt", value := .differentiated }
  , { walsCode := "lan", iso := "laj", value := .identical }
  , { walsCode := "lat", iso := "lav", value := .differentiated }
  , { walsCode := "lav", iso := "lvk", value := .identical }
  , { walsCode := "lez", iso := "lez", value := .identical }
  , { walsCode := "lit", iso := "lit", value := .differentiated }
  , { walsCode := "luv", iso := "lue", value := .differentiated }
  , { walsCode := "mal", iso := "plt", value := .identical }
  , { walsCode := "mym", iso := "mal", value := .identical }
  , { walsCode := "mlt", iso := "mlt", value := .identical }
  , { walsCode := "mnd", iso := "cmn", value := .identical }
  , { walsCode := "mns", iso := "mns", value := .identical }
  , { walsCode := "mao", iso := "mri", value := .differentiated }
  , { walsCode := "map", iso := "arn", value := .differentiated }
  , { walsCode := "mhi", iso := "mar", value := .identical }
  , { walsCode := "mar", iso := "mrc", value := .identical }
  , { walsCode := "mau", iso := "mph", value := .differentiated }
  , { walsCode := "mei", iso := "mni", value := .identical }
  , { walsCode := "mxc", iso := "mig", value := .identical }
  , { walsCode := "miy", iso := "mkf", value := .identical }
  , { walsCode := "miz", iso := "lus", value := .identical }
  , { walsCode := "mup", iso := "sur", value := .identical }
  , { walsCode := "nht", iso := "nhg", value := .differentiated }
  , { walsCode := "nav", iso := "nav", value := .differentiated }
  , { walsCode := "ndy", iso := "djk", value := .identical }
  , { walsCode := "nez", iso := "nez", value := .differentiated }
  , { walsCode := "nti", iso := "niy", value := .differentiated }
  , { walsCode := "ngi", iso := "wyb", value := .differentiated }
  , { walsCode := "nko", iso := "cgg", value := .identical }
  , { walsCode := "nor", iso := "nor", value := .identical }
  , { walsCode := "nbd", iso := "dgl", value := .differentiated }
  , { walsCode := "nug", iso := "nuy", value := .differentiated }
  , { walsCode := "ond", iso := "one", value := .differentiated }
  , { walsCode := "oya", iso := "ory", value := .identical }
  , { walsCode := "orh", iso := "hae", value := .differentiated }
  , { walsCode := "otm", iso := "ote", value := .identical }
  , { walsCode := "pan", iso := "pan", value := .identical }
  , { walsCode := "pau", iso := "pad", value := .differentiated }
  , { walsCode := "prs", iso := "pes", value := .identical }
  , { walsCode := "prh", iso := "myp", value := .differentiated }
  , { walsCode := "pit", iso := "pjt", value := .identical }
  , { walsCode := "pod", iso := "pbi", value := .identical }
  , { walsCode := "pol", iso := "pol", value := .differentiated }
  , { walsCode := "por", iso := "por", value := .differentiated }
  , { walsCode := "qhu", iso := "qub", value := .identical }
  , { walsCode := "ram", iso := "rma", value := .differentiated }
  , { walsCode := "rap", iso := "rap", value := .identical }
  , { walsCode := "rom", iso := "ron", value := .differentiated }
  , { walsCode := "rus", iso := "rus", value := .differentiated }
  , { walsCode := "shk", iso := "shp", value := .differentiated }
  , { walsCode := "shn", iso := "sna", value := .differentiated }
  , { walsCode := "snh", iso := "sin", value := .identical }
  , { walsCode := "svk", iso := "slk", value := .differentiated }
  , { walsCode := "som", iso := "som", value := .differentiated }
  , { walsCode := "snn", iso := "snk", value := .identical }
  , { walsCode := "spa", iso := "spa", value := .differentiated }
  , { walsCode := "sue", iso := "sue", value := .identical }
  , { walsCode := "sup", iso := "spp", value := .differentiated }
  , { walsCode := "swa", iso := "swh", value := .differentiated }
  , { walsCode := "swe", iso := "swe", value := .identical }
  , { walsCode := "tag", iso := "tgl", value := .differentiated }
  , { walsCode := "tml", iso := "tam", value := .identical }
  , { walsCode := "tas", iso := "shi", value := .identical }
  , { walsCode := "tel", iso := "tel", value := .identical }
  , { walsCode := "tha", iso := "tha", value := .identical }
  , { walsCode := "tiw", iso := "tiw", value := .identical }
  , { walsCode := "tru", iso := "tpy", value := .identical }
  , { walsCode := "tsa", iso := "tkr", value := .identical }
  , { walsCode := "tuk", iso := "", value := .identical }
  , { walsCode := "tna", iso := "tuv", value := .identical }
  , { walsCode := "tur", iso := "tur", value := .identical }
  , { walsCode := "ung", iso := "ung", value := .identical }
  , { walsCode := "urh", iso := "urh", value := .identical }
  , { walsCode := "urk", iso := "urb", value := .differentiated }
  , { walsCode := "usa", iso := "wnu", value := .differentiated }
  , { walsCode := "ven", iso := "ven", value := .differentiated }
  , { walsCode := "vie", iso := "vie", value := .identical }
  , { walsCode := "wam", iso := "wmb", value := .differentiated }
  , { walsCode := "wra", iso := "wba", value := .identical }
  , { walsCode := "war", iso := "pav", value := .differentiated }
  , { walsCode := "wel", iso := "cym", value := .identical }
  , { walsCode := "wic", iso := "wic", value := .differentiated }
  , { walsCode := "wlf", iso := "wol", value := .identical }
  , { walsCode := "yaq", iso := "yaq", value := .differentiated }
  , { walsCode := "ydd", iso := "ydd", value := .differentiated }
  , { walsCode := "yim", iso := "yee", value := .identical }
  , { walsCode := "yor", iso := "yor", value := .differentiated }
  , { walsCode := "zqc", iso := "zoc", value := .differentiated }
  , { walsCode := "zul", iso := "zul", value := .differentiated }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F47A
