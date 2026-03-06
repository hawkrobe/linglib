/-!
# WALS Feature 136B: M in First Person Singular
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 136B`.

Chapter 136, 230 languages.
-/

namespace Core.WALS.F136B

/-- WALS 136B values. -/
inductive MInFirstPersonSingular where
  | noMInFirstPersonSingular  -- No m in first person singular (177 languages)
  | mInFirstPersonSingular  -- m in first person singular (53 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 136B datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : MInFirstPersonSingular
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 136B dataset (230 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noMInFirstPersonSingular }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noMInFirstPersonSingular }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noMInFirstPersonSingular }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noMInFirstPersonSingular }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noMInFirstPersonSingular }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noMInFirstPersonSingular }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noMInFirstPersonSingular }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noMInFirstPersonSingular }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noMInFirstPersonSingular }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noMInFirstPersonSingular }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noMInFirstPersonSingular }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noMInFirstPersonSingular }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noMInFirstPersonSingular }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noMInFirstPersonSingular }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noMInFirstPersonSingular }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noMInFirstPersonSingular }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .noMInFirstPersonSingular }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .mInFirstPersonSingular }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noMInFirstPersonSingular }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noMInFirstPersonSingular }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noMInFirstPersonSingular }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .noMInFirstPersonSingular }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noMInFirstPersonSingular }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .noMInFirstPersonSingular }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .mInFirstPersonSingular }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noMInFirstPersonSingular }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noMInFirstPersonSingular }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noMInFirstPersonSingular }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .mInFirstPersonSingular }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .noMInFirstPersonSingular }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noMInFirstPersonSingular }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noMInFirstPersonSingular }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .noMInFirstPersonSingular }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noMInFirstPersonSingular }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .noMInFirstPersonSingular }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noMInFirstPersonSingular }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .noMInFirstPersonSingular }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .mInFirstPersonSingular }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .noMInFirstPersonSingular }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .mInFirstPersonSingular }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noMInFirstPersonSingular }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noMInFirstPersonSingular }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noMInFirstPersonSingular }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noMInFirstPersonSingular }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noMInFirstPersonSingular }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noMInFirstPersonSingular }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noMInFirstPersonSingular }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noMInFirstPersonSingular }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noMInFirstPersonSingular }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noMInFirstPersonSingular }
  , { walsCode := "eng", language := "English", iso := "eng", value := .mInFirstPersonSingular }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noMInFirstPersonSingular }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .mInFirstPersonSingular }
  , { walsCode := "fre", language := "French", iso := "fra", value := .mInFirstPersonSingular }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .mInFirstPersonSingular }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noMInFirstPersonSingular }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .mInFirstPersonSingular }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .mInFirstPersonSingular }
  , { walsCode := "ger", language := "German", iso := "deu", value := .mInFirstPersonSingular }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noMInFirstPersonSingular }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noMInFirstPersonSingular }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .mInFirstPersonSingular }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .mInFirstPersonSingular }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .mInFirstPersonSingular }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noMInFirstPersonSingular }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noMInFirstPersonSingular }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noMInFirstPersonSingular }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noMInFirstPersonSingular }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noMInFirstPersonSingular }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noMInFirstPersonSingular }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .mInFirstPersonSingular }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noMInFirstPersonSingular }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noMInFirstPersonSingular }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noMInFirstPersonSingular }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noMInFirstPersonSingular }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .mInFirstPersonSingular }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .mInFirstPersonSingular }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noMInFirstPersonSingular }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noMInFirstPersonSingular }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noMInFirstPersonSingular }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .mInFirstPersonSingular }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noMInFirstPersonSingular }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noMInFirstPersonSingular }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noMInFirstPersonSingular }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noMInFirstPersonSingular }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .mInFirstPersonSingular }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noMInFirstPersonSingular }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noMInFirstPersonSingular }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noMInFirstPersonSingular }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noMInFirstPersonSingular }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .mInFirstPersonSingular }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noMInFirstPersonSingular }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .mInFirstPersonSingular }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noMInFirstPersonSingular }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noMInFirstPersonSingular }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .mInFirstPersonSingular }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noMInFirstPersonSingular }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noMInFirstPersonSingular }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .mInFirstPersonSingular }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noMInFirstPersonSingular }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noMInFirstPersonSingular }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noMInFirstPersonSingular }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noMInFirstPersonSingular }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noMInFirstPersonSingular }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .noMInFirstPersonSingular }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .mInFirstPersonSingular }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .mInFirstPersonSingular }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noMInFirstPersonSingular }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noMInFirstPersonSingular }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noMInFirstPersonSingular }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .noMInFirstPersonSingular }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .mInFirstPersonSingular }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noMInFirstPersonSingular }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .mInFirstPersonSingular }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noMInFirstPersonSingular }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noMInFirstPersonSingular }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noMInFirstPersonSingular }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noMInFirstPersonSingular }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noMInFirstPersonSingular }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noMInFirstPersonSingular }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noMInFirstPersonSingular }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noMInFirstPersonSingular }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noMInFirstPersonSingular }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noMInFirstPersonSingular }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noMInFirstPersonSingular }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noMInFirstPersonSingular }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noMInFirstPersonSingular }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noMInFirstPersonSingular }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .mInFirstPersonSingular }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .noMInFirstPersonSingular }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noMInFirstPersonSingular }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .mInFirstPersonSingular }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noMInFirstPersonSingular }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .noMInFirstPersonSingular }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noMInFirstPersonSingular }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noMInFirstPersonSingular }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .mInFirstPersonSingular }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noMInFirstPersonSingular }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .noMInFirstPersonSingular }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .mInFirstPersonSingular }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noMInFirstPersonSingular }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noMInFirstPersonSingular }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noMInFirstPersonSingular }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noMInFirstPersonSingular }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noMInFirstPersonSingular }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noMInFirstPersonSingular }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noMInFirstPersonSingular }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noMInFirstPersonSingular }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noMInFirstPersonSingular }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noMInFirstPersonSingular }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .mInFirstPersonSingular }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .mInFirstPersonSingular }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noMInFirstPersonSingular }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noMInFirstPersonSingular }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .mInFirstPersonSingular }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noMInFirstPersonSingular }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noMInFirstPersonSingular }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noMInFirstPersonSingular }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noMInFirstPersonSingular }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noMInFirstPersonSingular }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noMInFirstPersonSingular }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noMInFirstPersonSingular }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noMInFirstPersonSingular }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noMInFirstPersonSingular }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .mInFirstPersonSingular }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .noMInFirstPersonSingular }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noMInFirstPersonSingular }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noMInFirstPersonSingular }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .mInFirstPersonSingular }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .mInFirstPersonSingular }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .mInFirstPersonSingular }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noMInFirstPersonSingular }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noMInFirstPersonSingular }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noMInFirstPersonSingular }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noMInFirstPersonSingular }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .mInFirstPersonSingular }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noMInFirstPersonSingular }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noMInFirstPersonSingular }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mInFirstPersonSingular }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .mInFirstPersonSingular }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noMInFirstPersonSingular }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noMInFirstPersonSingular }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noMInFirstPersonSingular }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .noMInFirstPersonSingular }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noMInFirstPersonSingular }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noMInFirstPersonSingular }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .noMInFirstPersonSingular }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noMInFirstPersonSingular }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noMInFirstPersonSingular }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noMInFirstPersonSingular }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noMInFirstPersonSingular }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .noMInFirstPersonSingular }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noMInFirstPersonSingular }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noMInFirstPersonSingular }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noMInFirstPersonSingular }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .mInFirstPersonSingular }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .mInFirstPersonSingular }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noMInFirstPersonSingular }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noMInFirstPersonSingular }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noMInFirstPersonSingular }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .mInFirstPersonSingular }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noMInFirstPersonSingular }
  , { walsCode := "wgl", language := "Waigali", iso := "wbk", value := .mInFirstPersonSingular }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .mInFirstPersonSingular }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noMInFirstPersonSingular }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .mInFirstPersonSingular }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noMInFirstPersonSingular }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noMInFirstPersonSingular }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noMInFirstPersonSingular }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noMInFirstPersonSingular }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .mInFirstPersonSingular }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noMInFirstPersonSingular }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noMInFirstPersonSingular }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noMInFirstPersonSingular }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noMInFirstPersonSingular }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noMInFirstPersonSingular }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .noMInFirstPersonSingular }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noMInFirstPersonSingular }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noMInFirstPersonSingular }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noMInFirstPersonSingular }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .mInFirstPersonSingular }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .mInFirstPersonSingular }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noMInFirstPersonSingular }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .mInFirstPersonSingular }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noMInFirstPersonSingular }
  , { walsCode := "yna", language := "Yupik (Naukan)", iso := "ynk", value := .noMInFirstPersonSingular }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noMInFirstPersonSingular }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noMInFirstPersonSingular }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .mInFirstPersonSingular }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noMInFirstPersonSingular }
  ]

-- Count verification
theorem total_count : allData.length = 230 := by native_decide

theorem count_noMInFirstPersonSingular :
    (allData.filter (·.value == .noMInFirstPersonSingular)).length = 177 := by native_decide
theorem count_mInFirstPersonSingular :
    (allData.filter (·.value == .mInFirstPersonSingular)).length = 53 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F136B
