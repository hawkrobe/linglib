import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 43A: Third Person Pronouns and Demonstratives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 43A`.

Chapter 43, 225 languages.
-/

namespace Core.WALS.F43A

/-- WALS 43A values. -/
inductive ThirdPersonPronounsAndDemonstratives where
  /-- Unrelated (100 languages). -/
  | unrelated
  /-- Related for all demonstratives (52 languages). -/
  | relatedForAllDemonstratives
  /-- Related to remote demonstratives (18 languages). -/
  | relatedToRemoteDemonstratives
  /-- Related to non-remote demonstratives (14 languages). -/
  | relatedToNonRemoteDemonstratives
  /-- Related by gender markers (24 languages). -/
  | relatedByGenderMarkers
  /-- Related for non-human reference (17 languages). -/
  | relatedForNonHumanReference
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 43A dataset (225 languages). -/
def allData : List (Datapoint ThirdPersonPronounsAndDemonstratives) :=
  [ { walsCode := "ain", iso := "ain", value := .unrelated }
  , { walsCode := "ala", iso := "amp", value := .relatedByGenderMarkers }
  , { walsCode := "ale", iso := "ale", value := .relatedForAllDemonstratives }
  , { walsCode := "amb", iso := "abt", value := .relatedForAllDemonstratives }
  , { walsCode := "ame", iso := "aey", value := .unrelated }
  , { walsCode := "agm", iso := "njm", value := .unrelated }
  , { walsCode := "apu", iso := "apu", value := .relatedByGenderMarkers }
  , { walsCode := "aeg", iso := "arz", value := .relatedByGenderMarkers }
  , { walsCode := "arp", iso := "ape", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "arm", iso := "hye", value := .relatedToRemoteDemonstratives }
  , { walsCode := "amp", iso := "aer", value := .unrelated }
  , { walsCode := "asm", iso := "cns", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "ath", iso := "aph", value := .relatedToRemoteDemonstratives }
  , { walsCode := "awp", iso := "kwi", value := .relatedForNonHumanReference }
  , { walsCode := "bab", iso := "bav", value := .relatedByGenderMarkers }
  , { walsCode := "bag", iso := "bmi", value := .unrelated }
  , { walsCode := "brs", iso := "bsn", value := .relatedToRemoteDemonstratives }
  , { walsCode := "bsq", iso := "eus", value := .relatedForAllDemonstratives }
  , { walsCode := "baw", iso := "bgr", value := .unrelated }
  , { walsCode := "bma", iso := "tzm", value := .unrelated }
  , { walsCode := "brh", iso := "brh", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "but", iso := "bxm", value := .relatedForAllDemonstratives }
  , { walsCode := "brm", iso := "mya", value := .unrelated }
  , { walsCode := "bur", iso := "bsk", value := .relatedToRemoteDemonstratives }
  , { walsCode := "cax", iso := "", value := .relatedForAllDemonstratives }
  , { walsCode := "cnl", iso := "ram", value := .unrelated }
  , { walsCode := "cnt", iso := "yue", value := .unrelated }
  , { walsCode := "cyv", iso := "cyb", value := .relatedForAllDemonstratives }
  , { walsCode := "cld", iso := "cld", value := .relatedForAllDemonstratives }
  , { walsCode := "cha", iso := "cha", value := .unrelated }
  , { walsCode := "cmh", iso := "ute", value := .relatedForAllDemonstratives }
  , { walsCode := "cle", iso := "cle", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "chk", iso := "ckt", value := .unrelated }
  , { walsCode := "chv", iso := "chv", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "cre", iso := "crk", value := .unrelated }
  , { walsCode := "cub", iso := "cub", value := .relatedForAllDemonstratives }
  , { walsCode := "dni", iso := "dni", value := .relatedToRemoteDemonstratives }
  , { walsCode := "dig", iso := "mhu", value := .relatedForAllDemonstratives }
  , { walsCode := "dio", iso := "dyo", value := .relatedByGenderMarkers }
  , { walsCode := "djr", iso := "ddj", value := .unrelated }
  , { walsCode := "don", iso := "kmc", value := .unrelated }
  , { walsCode := "dmi", iso := "dus", value := .relatedForNonHumanReference }
  , { walsCode := "eng", iso := "eng", value := .relatedForAllDemonstratives }
  , { walsCode := "epe", iso := "sja", value := .unrelated }
  , { walsCode := "err", iso := "erg", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "eve", iso := "evn", value := .unrelated }
  , { walsCode := "fij", iso := "fij", value := .unrelated }
  , { walsCode := "fin", iso := "fin", value := .unrelated }
  , { walsCode := "fre", iso := "fra", value := .relatedByGenderMarkers }
  , { walsCode := "fut", iso := "fut", value := .unrelated }
  , { walsCode := "gar", iso := "grt", value := .relatedForNonHumanReference }
  , { walsCode := "geo", iso := "kat", value := .relatedToRemoteDemonstratives }
  , { walsCode := "ger", iso := "deu", value := .relatedByGenderMarkers }
  , { walsCode := "gdi", iso := "god", value := .relatedForNonHumanReference }
  , { walsCode := "god", iso := "gdo", value := .relatedByGenderMarkers }
  , { walsCode := "goo", iso := "gni", value := .unrelated }
  , { walsCode := "grb", iso := "grj", value := .relatedByGenderMarkers }
  , { walsCode := "grw", iso := "kal", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "gua", iso := "gug", value := .unrelated }
  , { walsCode := "guu", iso := "kky", value := .relatedForNonHumanReference }
  , { walsCode := "hau", iso := "hau", value := .unrelated }
  , { walsCode := "haw", iso := "haw", value := .relatedToRemoteDemonstratives }
  , { walsCode := "heb", iso := "heb", value := .relatedForAllDemonstratives }
  , { walsCode := "hin", iso := "hin", value := .relatedForAllDemonstratives }
  , { walsCode := "hix", iso := "hix", value := .relatedForAllDemonstratives }
  , { walsCode := "hun", iso := "hun", value := .relatedForNonHumanReference }
  , { walsCode := "hzb", iso := "huz", value := .relatedForAllDemonstratives }
  , { walsCode := "ika", iso := "arh", value := .unrelated }
  , { walsCode := "ila", iso := "ilb", value := .relatedByGenderMarkers }
  , { walsCode := "imo", iso := "imn", value := .unrelated }
  , { walsCode := "ind", iso := "ind", value := .unrelated }
  , { walsCode := "ing", iso := "inh", value := .unrelated }
  , { walsCode := "irq", iso := "irk", value := .unrelated }
  , { walsCode := "iri", iso := "gle", value := .relatedToRemoteDemonstratives }
  , { walsCode := "jak", iso := "jac", value := .unrelated }
  , { walsCode := "jpn", iso := "jpn", value := .unrelated }
  , { walsCode := "jaq", iso := "jqr", value := .relatedForNonHumanReference }
  , { walsCode := "jun", iso := "jun", value := .unrelated }
  , { walsCode := "juh", iso := "ktz", value := .relatedByGenderMarkers }
  , { walsCode := "kam", iso := "xbr", value := .relatedForAllDemonstratives }
  , { walsCode := "knd", iso := "kan", value := .relatedToRemoteDemonstratives }
  , { walsCode := "knr", iso := "knc", value := .unrelated }
  , { walsCode := "kws", iso := "xaw", value := .relatedForAllDemonstratives }
  , { walsCode := "kyl", iso := "eky", value := .unrelated }
  , { walsCode := "kay", iso := "gyd", value := .relatedForNonHumanReference }
  , { walsCode := "kew", iso := "kew", value := .unrelated }
  , { walsCode := "kha", iso := "khk", value := .relatedForAllDemonstratives }
  , { walsCode := "khr", iso := "khr", value := .relatedForAllDemonstratives }
  , { walsCode := "khs", iso := "kha", value := .relatedForAllDemonstratives }
  , { walsCode := "kmu", iso := "kjg", value := .unrelated }
  , { walsCode := "klv", iso := "kij", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "krb", iso := "gil", value := .unrelated }
  , { walsCode := "kis", iso := "kss", value := .relatedByGenderMarkers }
  , { walsCode := "shp", iso := "yak", value := .unrelated }
  , { walsCode := "koa", iso := "cku", value := .unrelated }
  , { walsCode := "kob", iso := "kpw", value := .unrelated }
  , { walsCode := "kor", iso := "kor", value := .unrelated }
  , { walsCode := "kfe", iso := "kfz", value := .unrelated }
  , { walsCode := "kos", iso := "kos", value := .unrelated }
  , { walsCode := "kch", iso := "khq", value := .unrelated }
  , { walsCode := "kse", iso := "ses", value := .unrelated }
  , { walsCode := "kwk", iso := "kwk", value := .unrelated }
  , { walsCode := "lah", iso := "lhu", value := .unrelated }
  , { walsCode := "lkt", iso := "lkt", value := .unrelated }
  , { walsCode := "lmp", iso := "ljp", value := .relatedForNonHumanReference }
  , { walsCode := "lan", iso := "laj", value := .unrelated }
  , { walsCode := "lat", iso := "lav", value := .relatedByGenderMarkers }
  , { walsCode := "lav", iso := "lvk", value := .relatedForAllDemonstratives }
  , { walsCode := "lep", iso := "lep", value := .unrelated }
  , { walsCode := "lez", iso := "lez", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "lil", iso := "lil", value := .unrelated }
  , { walsCode := "lim", iso := "lif", value := .relatedToRemoteDemonstratives }
  , { walsCode := "luv", iso := "lue", value := .relatedByGenderMarkers }
  , { walsCode := "mac", iso := "mbc", value := .relatedForAllDemonstratives }
  , { walsCode := "mym", iso := "mal", value := .relatedForAllDemonstratives }
  , { walsCode := "mlt", iso := "mlt", value := .relatedByGenderMarkers }
  , { walsCode := "mnd", iso := "cmn", value := .relatedForNonHumanReference }
  , { walsCode := "myi", iso := "mpc", value := .relatedForAllDemonstratives }
  , { walsCode := "mao", iso := "mri", value := .relatedToRemoteDemonstratives }
  , { walsCode := "map", iso := "arn", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "mhi", iso := "mar", value := .relatedForAllDemonstratives }
  , { walsCode := "mrg", iso := "mrt", value := .unrelated }
  , { walsCode := "mar", iso := "mrc", value := .relatedForAllDemonstratives }
  , { walsCode := "msh", iso := "mah", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "mrt", iso := "vma", value := .unrelated }
  , { walsCode := "mau", iso := "mph", value := .relatedByGenderMarkers }
  , { walsCode := "may", iso := "ayz", value := .relatedByGenderMarkers }
  , { walsCode := "mby", iso := "myb", value := .unrelated }
  , { walsCode := "mei", iso := "mni", value := .relatedForAllDemonstratives }
  , { walsCode := "mic", iso := "mic", value := .unrelated }
  , { walsCode := "mss", iso := "skd", value := .relatedForAllDemonstratives }
  , { walsCode := "mxc", iso := "mig", value := .unrelated }
  , { walsCode := "mxo", iso := "mie", value := .unrelated }
  , { walsCode := "mxy", iso := "mpm", value := .unrelated }
  , { walsCode := "miy", iso := "mkf", value := .unrelated }
  , { walsCode := "mok", iso := "mkj", value := .unrelated }
  , { walsCode := "mud", iso := "mnf", value := .unrelated }
  , { walsCode := "mun", iso := "unr", value := .unrelated }
  , { walsCode := "mup", iso := "sur", value := .relatedForNonHumanReference }
  , { walsCode := "nma", iso := "nbi", value := .unrelated }
  , { walsCode := "nht", iso := "nhg", value := .relatedForAllDemonstratives }
  , { walsCode := "kho", iso := "naq", value := .unrelated }
  , { walsCode := "ndy", iso := "djk", value := .unrelated }
  , { walsCode := "nez", iso := "nez", value := .unrelated }
  , { walsCode := "nti", iso := "niy", value := .unrelated }
  , { walsCode := "ngi", iso := "wyb", value := .relatedForAllDemonstratives }
  , { walsCode := "niv", iso := "niv", value := .relatedForNonHumanReference }
  , { walsCode := "nko", iso := "cgg", value := .relatedByGenderMarkers }
  , { walsCode := "nku", iso := "xnz", value := .unrelated }
  , { walsCode := "nug", iso := "nuy", value := .unrelated }
  , { walsCode := "ond", iso := "one", value := .unrelated }
  , { walsCode := "orh", iso := "hae", value := .unrelated }
  , { walsCode := "pms", iso := "pma", value := .relatedForAllDemonstratives }
  , { walsCode := "pal", iso := "pau", value := .relatedForAllDemonstratives }
  , { walsCode := "pan", iso := "pan", value := .relatedForAllDemonstratives }
  , { walsCode := "psm", iso := "pqm", value := .unrelated }
  , { walsCode := "pau", iso := "pad", value := .relatedForAllDemonstratives }
  , { walsCode := "per", iso := "pip", value := .relatedByGenderMarkers }
  , { walsCode := "prs", iso := "pes", value := .relatedForNonHumanReference }
  , { walsCode := "pip", iso := "ppl", value := .relatedToRemoteDemonstratives }
  , { walsCode := "prh", iso := "myp", value := .relatedToRemoteDemonstratives }
  , { walsCode := "pit", iso := "pjt", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "ppi", iso := "pit", value := .relatedForAllDemonstratives }
  , { walsCode := "poh", iso := "pon", value := .unrelated }
  , { walsCode := "pme", iso := "peb", value := .unrelated }
  , { walsCode := "pso", iso := "pom", value := .relatedForAllDemonstratives }
  , { walsCode := "qim", iso := "qvi", value := .relatedForNonHumanReference }
  , { walsCode := "qta", iso := "qvn", value := .relatedForNonHumanReference }
  , { walsCode := "ram", iso := "rma", value := .relatedForAllDemonstratives }
  , { walsCode := "rap", iso := "rap", value := .relatedToRemoteDemonstratives }
  , { walsCode := "rej", iso := "rej", value := .unrelated }
  , { walsCode := "rem", iso := "bfw", value := .unrelated }
  , { walsCode := "ret", iso := "tnc", value := .relatedForAllDemonstratives }
  , { walsCode := "sam", iso := "smo", value := .relatedToRemoteDemonstratives }
  , { walsCode := "san", iso := "sag", value := .unrelated }
  , { walsCode := "saw", iso := "hvn", value := .unrelated }
  , { walsCode := "sml", iso := "sza", value := .unrelated }
  , { walsCode := "snt", iso := "set", value := .relatedForAllDemonstratives }
  , { walsCode := "scr", iso := "hbs", value := .unrelated }
  , { walsCode := "shn", iso := "sna", value := .relatedByGenderMarkers }
  , { walsCode := "snh", iso := "sin", value := .relatedForAllDemonstratives }
  , { walsCode := "sla", iso := "den", value := .relatedForNonHumanReference }
  , { walsCode := "spa", iso := "spa", value := .unrelated }
  , { walsCode := "sup", iso := "spp", value := .relatedForAllDemonstratives }
  , { walsCode := "tab", iso := "mky", value := .relatedForAllDemonstratives }
  , { walsCode := "tag", iso := "tgl", value := .unrelated }
  , { walsCode := "tau", iso := "tya", value := .unrelated }
  , { walsCode := "tha", iso := "tha", value := .unrelated }
  , { walsCode := "tib", iso := "bod", value := .unrelated }
  , { walsCode := "tid", iso := "tvo", value := .relatedForAllDemonstratives }
  , { walsCode := "tja", iso := "dih", value := .relatedForAllDemonstratives }
  , { walsCode := "ton", iso := "tqw", value := .unrelated }
  , { walsCode := "toq", iso := "mlu", value := .unrelated }
  , { walsCode := "tot", iso := "tlc", value := .unrelated }
  , { walsCode := "tru", iso := "tpy", value := .relatedByGenderMarkers }
  , { walsCode := "tuk", iso := "", value := .unrelated }
  , { walsCode := "tun", iso := "tun", value := .unrelated }
  , { walsCode := "tna", iso := "tuv", value := .unrelated }
  , { walsCode := "tur", iso := "tur", value := .relatedToRemoteDemonstratives }
  , { walsCode := "tte", iso := "tta", value := .unrelated }
  , { walsCode := "tvl", iso := "tvl", value := .relatedToRemoteDemonstratives }
  , { walsCode := "tzu", iso := "tzj", value := .relatedForAllDemonstratives }
  , { walsCode := "tsh", iso := "par", value := .relatedForAllDemonstratives }
  , { walsCode := "urk", iso := "urb", value := .unrelated }
  , { walsCode := "usa", iso := "wnu", value := .unrelated }
  , { walsCode := "ven", iso := "ven", value := .relatedByGenderMarkers }
  , { walsCode := "vie", iso := "vie", value := .relatedToRemoteDemonstratives }
  , { walsCode := "wam", iso := "wmb", value := .relatedForAllDemonstratives }
  , { walsCode := "wra", iso := "wba", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "wrd", iso := "wrr", value := .relatedForAllDemonstratives }
  , { walsCode := "war", iso := "pav", value := .unrelated }
  , { walsCode := "wic", iso := "wic", value := .unrelated }
  , { walsCode := "wik", iso := "yok", value := .unrelated }
  , { walsCode := "win", iso := "wnw", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "yag", iso := "yad", value := .relatedForNonHumanReference }
  , { walsCode := "yaq", iso := "yaq", value := .unrelated }
  , { walsCode := "yid", iso := "yii", value := .relatedForAllDemonstratives }
  , { walsCode := "yim", iso := "yee", value := .relatedForAllDemonstratives }
  , { walsCode := "yor", iso := "yor", value := .unrelated }
  , { walsCode := "yuc", iso := "yuc", value := .relatedByGenderMarkers }
  , { walsCode := "yko", iso := "yux", value := .unrelated }
  , { walsCode := "yuk", iso := "gcd", value := .relatedForAllDemonstratives }
  , { walsCode := "ypk", iso := "esu", value := .unrelated }
  , { walsCode := "yur", iso := "yur", value := .relatedForAllDemonstratives }
  , { walsCode := "zul", iso := "zul", value := .relatedByGenderMarkers }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F43A
