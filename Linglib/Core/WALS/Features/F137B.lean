import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 137B: M in Second Person Singular
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 137B`.

Chapter 137, 230 languages.
-/

namespace Core.WALS.F137B

/-- WALS 137B values. -/
inductive MInSecondPersonSingular where
  | noMInSecondPersonSingular  -- No m in second person singular (152 languages)
  | mInSecondPersonSingular  -- m in second person singular (78 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 137B dataset (230 languages). -/
def allData : List (Datapoint MInSecondPersonSingular) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .mInSecondPersonSingular }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noMInSecondPersonSingular }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noMInSecondPersonSingular }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noMInSecondPersonSingular }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noMInSecondPersonSingular }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noMInSecondPersonSingular }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noMInSecondPersonSingular }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noMInSecondPersonSingular }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .mInSecondPersonSingular }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noMInSecondPersonSingular }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noMInSecondPersonSingular }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noMInSecondPersonSingular }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .mInSecondPersonSingular }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noMInSecondPersonSingular }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noMInSecondPersonSingular }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noMInSecondPersonSingular }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .mInSecondPersonSingular }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noMInSecondPersonSingular }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .mInSecondPersonSingular }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noMInSecondPersonSingular }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noMInSecondPersonSingular }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .noMInSecondPersonSingular }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .mInSecondPersonSingular }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .mInSecondPersonSingular }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noMInSecondPersonSingular }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noMInSecondPersonSingular }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .mInSecondPersonSingular }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .mInSecondPersonSingular }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noMInSecondPersonSingular }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .mInSecondPersonSingular }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noMInSecondPersonSingular }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .mInSecondPersonSingular }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .noMInSecondPersonSingular }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .mInSecondPersonSingular }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .mInSecondPersonSingular }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noMInSecondPersonSingular }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .mInSecondPersonSingular }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noMInSecondPersonSingular }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .mInSecondPersonSingular }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noMInSecondPersonSingular }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noMInSecondPersonSingular }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noMInSecondPersonSingular }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noMInSecondPersonSingular }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noMInSecondPersonSingular }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noMInSecondPersonSingular }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noMInSecondPersonSingular }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noMInSecondPersonSingular }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noMInSecondPersonSingular }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .mInSecondPersonSingular }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noMInSecondPersonSingular }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noMInSecondPersonSingular }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .mInSecondPersonSingular }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noMInSecondPersonSingular }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noMInSecondPersonSingular }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .mInSecondPersonSingular }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noMInSecondPersonSingular }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .mInSecondPersonSingular }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noMInSecondPersonSingular }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noMInSecondPersonSingular }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .mInSecondPersonSingular }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noMInSecondPersonSingular }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .mInSecondPersonSingular }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noMInSecondPersonSingular }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .mInSecondPersonSingular }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noMInSecondPersonSingular }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .mInSecondPersonSingular }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noMInSecondPersonSingular }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noMInSecondPersonSingular }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noMInSecondPersonSingular }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noMInSecondPersonSingular }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noMInSecondPersonSingular }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .mInSecondPersonSingular }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noMInSecondPersonSingular }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noMInSecondPersonSingular }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .mInSecondPersonSingular }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noMInSecondPersonSingular }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .noMInSecondPersonSingular }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noMInSecondPersonSingular }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .mInSecondPersonSingular }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noMInSecondPersonSingular }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noMInSecondPersonSingular }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noMInSecondPersonSingular }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .mInSecondPersonSingular }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .mInSecondPersonSingular }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .mInSecondPersonSingular }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noMInSecondPersonSingular }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .mInSecondPersonSingular }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .mInSecondPersonSingular }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .mInSecondPersonSingular }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noMInSecondPersonSingular }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noMInSecondPersonSingular }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noMInSecondPersonSingular }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noMInSecondPersonSingular }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .mInSecondPersonSingular }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noMInSecondPersonSingular }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noMInSecondPersonSingular }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noMInSecondPersonSingular }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noMInSecondPersonSingular }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noMInSecondPersonSingular }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noMInSecondPersonSingular }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noMInSecondPersonSingular }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noMInSecondPersonSingular }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noMInSecondPersonSingular }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noMInSecondPersonSingular }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .noMInSecondPersonSingular }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .mInSecondPersonSingular }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noMInSecondPersonSingular }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noMInSecondPersonSingular }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noMInSecondPersonSingular }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noMInSecondPersonSingular }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .noMInSecondPersonSingular }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .mInSecondPersonSingular }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .mInSecondPersonSingular }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .mInSecondPersonSingular }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noMInSecondPersonSingular }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .mInSecondPersonSingular }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noMInSecondPersonSingular }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noMInSecondPersonSingular }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noMInSecondPersonSingular }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noMInSecondPersonSingular }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noMInSecondPersonSingular }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .mInSecondPersonSingular }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .mInSecondPersonSingular }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noMInSecondPersonSingular }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noMInSecondPersonSingular }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noMInSecondPersonSingular }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noMInSecondPersonSingular }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .mInSecondPersonSingular }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .mInSecondPersonSingular }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .mInSecondPersonSingular }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noMInSecondPersonSingular }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .noMInSecondPersonSingular }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .mInSecondPersonSingular }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .noMInSecondPersonSingular }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noMInSecondPersonSingular }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noMInSecondPersonSingular }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noMInSecondPersonSingular }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noMInSecondPersonSingular }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .mInSecondPersonSingular }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noMInSecondPersonSingular }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noMInSecondPersonSingular }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noMInSecondPersonSingular }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .mInSecondPersonSingular }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .mInSecondPersonSingular }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noMInSecondPersonSingular }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noMInSecondPersonSingular }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .mInSecondPersonSingular }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noMInSecondPersonSingular }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noMInSecondPersonSingular }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noMInSecondPersonSingular }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noMInSecondPersonSingular }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noMInSecondPersonSingular }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noMInSecondPersonSingular }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noMInSecondPersonSingular }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noMInSecondPersonSingular }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .mInSecondPersonSingular }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noMInSecondPersonSingular }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noMInSecondPersonSingular }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .mInSecondPersonSingular }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noMInSecondPersonSingular }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noMInSecondPersonSingular }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noMInSecondPersonSingular }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .mInSecondPersonSingular }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noMInSecondPersonSingular }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noMInSecondPersonSingular }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .mInSecondPersonSingular }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noMInSecondPersonSingular }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .mInSecondPersonSingular }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noMInSecondPersonSingular }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .mInSecondPersonSingular }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noMInSecondPersonSingular }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noMInSecondPersonSingular }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noMInSecondPersonSingular }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .mInSecondPersonSingular }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noMInSecondPersonSingular }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noMInSecondPersonSingular }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noMInSecondPersonSingular }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noMInSecondPersonSingular }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mInSecondPersonSingular }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noMInSecondPersonSingular }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .mInSecondPersonSingular }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .mInSecondPersonSingular }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noMInSecondPersonSingular }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .mInSecondPersonSingular }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noMInSecondPersonSingular }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noMInSecondPersonSingular }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .mInSecondPersonSingular }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noMInSecondPersonSingular }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noMInSecondPersonSingular }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noMInSecondPersonSingular }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noMInSecondPersonSingular }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .mInSecondPersonSingular }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noMInSecondPersonSingular }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noMInSecondPersonSingular }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .mInSecondPersonSingular }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noMInSecondPersonSingular }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noMInSecondPersonSingular }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noMInSecondPersonSingular }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noMInSecondPersonSingular }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noMInSecondPersonSingular }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noMInSecondPersonSingular }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .mInSecondPersonSingular }
  , { walsCode := "wgl", language := "Waigali", iso := "wbk", value := .noMInSecondPersonSingular }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .mInSecondPersonSingular }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .mInSecondPersonSingular }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noMInSecondPersonSingular }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noMInSecondPersonSingular }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .mInSecondPersonSingular }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noMInSecondPersonSingular }
  , { walsCode := "was", language := "Washo", iso := "was", value := .mInSecondPersonSingular }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .mInSecondPersonSingular }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noMInSecondPersonSingular }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noMInSecondPersonSingular }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .mInSecondPersonSingular }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .mInSecondPersonSingular }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .mInSecondPersonSingular }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .mInSecondPersonSingular }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noMInSecondPersonSingular }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .mInSecondPersonSingular }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .mInSecondPersonSingular }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .mInSecondPersonSingular }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noMInSecondPersonSingular }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noMInSecondPersonSingular }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noMInSecondPersonSingular }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noMInSecondPersonSingular }
  , { walsCode := "yna", language := "Yupik (Naukan)", iso := "ynk", value := .mInSecondPersonSingular }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .mInSecondPersonSingular }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .mInSecondPersonSingular }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noMInSecondPersonSingular }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noMInSecondPersonSingular }
  ]

-- Count verification
theorem total_count : allData.length = 230 := by native_decide

theorem count_noMInSecondPersonSingular :
    (allData.filter (·.value == .noMInSecondPersonSingular)).length = 152 := by native_decide
theorem count_mInSecondPersonSingular :
    (allData.filter (·.value == .mInSecondPersonSingular)).length = 78 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F137B
