import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 137A: N-M Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 137A`.

Chapter 137, 230 languages.
-/

namespace Core.WALS.F137A

/-- WALS 137A values. -/
inductive NMPronouns where
  /-- No N-M pronouns (194 languages). -/
  | noNMPronouns
  /-- N-M pronouns, paradigmatic (25 languages). -/
  | nMPronounsParadigmatic
  /-- N-M pronouns, non-paradigmatic (11 languages). -/
  | nMPronounsNonParadigmatic
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 137A dataset (230 languages). -/
def allData : List (Datapoint NMPronouns) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noNMPronouns }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noNMPronouns }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noNMPronouns }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noNMPronouns }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noNMPronouns }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noNMPronouns }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noNMPronouns }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noNMPronouns }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noNMPronouns }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noNMPronouns }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noNMPronouns }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noNMPronouns }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .nMPronounsNonParadigmatic }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noNMPronouns }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noNMPronouns }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noNMPronouns }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .noNMPronouns }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noNMPronouns }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noNMPronouns }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noNMPronouns }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noNMPronouns }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .noNMPronouns }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nMPronounsNonParadigmatic }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .noNMPronouns }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noNMPronouns }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noNMPronouns }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noNMPronouns }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .nMPronounsParadigmatic }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noNMPronouns }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .nMPronounsParadigmatic }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noNMPronouns }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noNMPronouns }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .noNMPronouns }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .nMPronounsParadigmatic }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .nMPronounsParadigmatic }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noNMPronouns }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .nMPronounsParadigmatic }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noNMPronouns }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .noNMPronouns }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noNMPronouns }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noNMPronouns }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noNMPronouns }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noNMPronouns }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noNMPronouns }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .nMPronounsParadigmatic }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noNMPronouns }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noNMPronouns }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noNMPronouns }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noNMPronouns }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .nMPronounsParadigmatic }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noNMPronouns }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noNMPronouns }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noNMPronouns }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noNMPronouns }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noNMPronouns }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noNMPronouns }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noNMPronouns }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noNMPronouns }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noNMPronouns }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noNMPronouns }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .nMPronounsNonParadigmatic }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noNMPronouns }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nMPronounsNonParadigmatic }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noNMPronouns }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noNMPronouns }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noNMPronouns }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .nMPronounsNonParadigmatic }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noNMPronouns }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noNMPronouns }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noNMPronouns }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noNMPronouns }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noNMPronouns }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noNMPronouns }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noNMPronouns }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noNMPronouns }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noNMPronouns }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noNMPronouns }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .noNMPronouns }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noNMPronouns }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noNMPronouns }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noNMPronouns }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noNMPronouns }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noNMPronouns }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noNMPronouns }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .nMPronounsNonParadigmatic }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noNMPronouns }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noNMPronouns }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noNMPronouns }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nMPronounsNonParadigmatic }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .nMPronounsParadigmatic }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noNMPronouns }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noNMPronouns }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noNMPronouns }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noNMPronouns }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .nMPronounsParadigmatic }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noNMPronouns }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noNMPronouns }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .nMPronounsParadigmatic }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noNMPronouns }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noNMPronouns }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noNMPronouns }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noNMPronouns }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noNMPronouns }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noNMPronouns }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noNMPronouns }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noNMPronouns }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .nMPronounsNonParadigmatic }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noNMPronouns }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noNMPronouns }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noNMPronouns }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noNMPronouns }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .noNMPronouns }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noNMPronouns }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .nMPronounsParadigmatic }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noNMPronouns }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noNMPronouns }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .nMPronounsParadigmatic }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noNMPronouns }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noNMPronouns }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noNMPronouns }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noNMPronouns }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noNMPronouns }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .nMPronounsParadigmatic }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noNMPronouns }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noNMPronouns }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noNMPronouns }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noNMPronouns }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noNMPronouns }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .nMPronounsParadigmatic }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .nMPronounsNonParadigmatic }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .nMPronounsParadigmatic }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noNMPronouns }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .noNMPronouns }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noNMPronouns }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .noNMPronouns }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noNMPronouns }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noNMPronouns }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noNMPronouns }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noNMPronouns }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .noNMPronouns }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noNMPronouns }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .noNMPronouns }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noNMPronouns }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noNMPronouns }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noNMPronouns }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noNMPronouns }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noNMPronouns }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noNMPronouns }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noNMPronouns }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .nMPronounsParadigmatic }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noNMPronouns }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noNMPronouns }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noNMPronouns }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noNMPronouns }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noNMPronouns }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noNMPronouns }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noNMPronouns }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noNMPronouns }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .nMPronounsParadigmatic }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noNMPronouns }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noNMPronouns }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noNMPronouns }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noNMPronouns }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noNMPronouns }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nMPronounsParadigmatic }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noNMPronouns }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noNMPronouns }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noNMPronouns }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noNMPronouns }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noNMPronouns }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noNMPronouns }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noNMPronouns }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noNMPronouns }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noNMPronouns }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noNMPronouns }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noNMPronouns }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noNMPronouns }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noNMPronouns }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noNMPronouns }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .nMPronounsParadigmatic }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noNMPronouns }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noNMPronouns }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noNMPronouns }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noNMPronouns }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .noNMPronouns }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noNMPronouns }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noNMPronouns }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noNMPronouns }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noNMPronouns }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noNMPronouns }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noNMPronouns }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .noNMPronouns }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noNMPronouns }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noNMPronouns }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .nMPronounsNonParadigmatic }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noNMPronouns }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noNMPronouns }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noNMPronouns }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noNMPronouns }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noNMPronouns }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noNMPronouns }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noNMPronouns }
  , { walsCode := "wgl", language := "Waigali", iso := "wbk", value := .noNMPronouns }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noNMPronouns }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noNMPronouns }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noNMPronouns }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noNMPronouns }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .nMPronounsParadigmatic }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noNMPronouns }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noNMPronouns }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noNMPronouns }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noNMPronouns }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noNMPronouns }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .nMPronounsParadigmatic }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .nMPronounsParadigmatic }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noNMPronouns }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .nMPronounsParadigmatic }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noNMPronouns }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nMPronounsParadigmatic }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .nMPronounsParadigmatic }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noNMPronouns }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noNMPronouns }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noNMPronouns }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noNMPronouns }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noNMPronouns }
  , { walsCode := "yna", language := "Yupik (Naukan)", iso := "ynk", value := .noNMPronouns }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .nMPronounsNonParadigmatic }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noNMPronouns }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noNMPronouns }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noNMPronouns }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F137A
