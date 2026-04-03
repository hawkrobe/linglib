import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 136A: M-T Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 136A`.

Chapter 136, 230 languages.
-/

namespace Core.WALS.F136A

/-- WALS 136A values. -/
inductive MTPronouns where
  | noMTPronouns  -- No M-T pronouns (200 languages)
  | mTPronounsParadigmatic  -- M-T pronouns, paradigmatic (27 languages)
  | mTPronounsNonParadigmatic  -- M-T pronouns, non-paradigmatic (3 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 136A dataset (230 languages). -/
def allData : List (Datapoint MTPronouns) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noMTPronouns }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noMTPronouns }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noMTPronouns }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noMTPronouns }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noMTPronouns }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noMTPronouns }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noMTPronouns }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noMTPronouns }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noMTPronouns }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noMTPronouns }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noMTPronouns }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noMTPronouns }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noMTPronouns }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noMTPronouns }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noMTPronouns }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noMTPronouns }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .noMTPronouns }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noMTPronouns }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noMTPronouns }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noMTPronouns }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noMTPronouns }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .noMTPronouns }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noMTPronouns }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .noMTPronouns }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noMTPronouns }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noMTPronouns }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noMTPronouns }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noMTPronouns }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noMTPronouns }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .noMTPronouns }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noMTPronouns }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noMTPronouns }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .noMTPronouns }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noMTPronouns }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .noMTPronouns }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noMTPronouns }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .noMTPronouns }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .mTPronounsParadigmatic }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .noMTPronouns }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .mTPronounsParadigmatic }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noMTPronouns }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noMTPronouns }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noMTPronouns }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noMTPronouns }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noMTPronouns }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noMTPronouns }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noMTPronouns }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noMTPronouns }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noMTPronouns }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noMTPronouns }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noMTPronouns }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noMTPronouns }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noMTPronouns }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .mTPronounsParadigmatic }
  , { walsCode := "fre", language := "French", iso := "fra", value := .mTPronounsParadigmatic }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .mTPronounsParadigmatic }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noMTPronouns }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noMTPronouns }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .mTPronounsParadigmatic }
  , { walsCode := "ger", language := "German", iso := "deu", value := .mTPronounsParadigmatic }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noMTPronouns }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noMTPronouns }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .mTPronounsParadigmatic }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .mTPronounsParadigmatic }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .mTPronounsNonParadigmatic }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noMTPronouns }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noMTPronouns }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noMTPronouns }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noMTPronouns }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noMTPronouns }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noMTPronouns }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .mTPronounsParadigmatic }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noMTPronouns }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noMTPronouns }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noMTPronouns }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noMTPronouns }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .mTPronounsParadigmatic }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .noMTPronouns }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noMTPronouns }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noMTPronouns }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noMTPronouns }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .mTPronounsParadigmatic }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noMTPronouns }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noMTPronouns }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noMTPronouns }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noMTPronouns }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noMTPronouns }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noMTPronouns }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noMTPronouns }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noMTPronouns }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noMTPronouns }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noMTPronouns }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noMTPronouns }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .mTPronounsParadigmatic }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noMTPronouns }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noMTPronouns }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noMTPronouns }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .noMTPronouns }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noMTPronouns }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noMTPronouns }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noMTPronouns }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noMTPronouns }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noMTPronouns }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noMTPronouns }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noMTPronouns }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noMTPronouns }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .noMTPronouns }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .mTPronounsParadigmatic }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noMTPronouns }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noMTPronouns }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noMTPronouns }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .noMTPronouns }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noMTPronouns }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noMTPronouns }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noMTPronouns }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noMTPronouns }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noMTPronouns }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noMTPronouns }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noMTPronouns }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noMTPronouns }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noMTPronouns }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noMTPronouns }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noMTPronouns }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noMTPronouns }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noMTPronouns }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noMTPronouns }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noMTPronouns }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noMTPronouns }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noMTPronouns }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .mTPronounsParadigmatic }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .noMTPronouns }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noMTPronouns }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .noMTPronouns }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noMTPronouns }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .noMTPronouns }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noMTPronouns }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noMTPronouns }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .mTPronounsParadigmatic }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noMTPronouns }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .noMTPronouns }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .mTPronounsParadigmatic }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .noMTPronouns }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noMTPronouns }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noMTPronouns }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noMTPronouns }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noMTPronouns }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noMTPronouns }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noMTPronouns }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noMTPronouns }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noMTPronouns }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noMTPronouns }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noMTPronouns }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noMTPronouns }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .mTPronounsParadigmatic }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noMTPronouns }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noMTPronouns }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noMTPronouns }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .mTPronounsParadigmatic }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noMTPronouns }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noMTPronouns }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noMTPronouns }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noMTPronouns }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noMTPronouns }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noMTPronouns }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noMTPronouns }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noMTPronouns }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .mTPronounsParadigmatic }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noMTPronouns }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noMTPronouns }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .mTPronounsParadigmatic }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noMTPronouns }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noMTPronouns }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noMTPronouns }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noMTPronouns }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noMTPronouns }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noMTPronouns }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .mTPronounsParadigmatic }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noMTPronouns }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noMTPronouns }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noMTPronouns }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noMTPronouns }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noMTPronouns }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noMTPronouns }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noMTPronouns }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .noMTPronouns }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noMTPronouns }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noMTPronouns }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noMTPronouns }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noMTPronouns }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noMTPronouns }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noMTPronouns }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .noMTPronouns }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noMTPronouns }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noMTPronouns }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noMTPronouns }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .mTPronounsParadigmatic }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .mTPronounsParadigmatic }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noMTPronouns }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noMTPronouns }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noMTPronouns }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .mTPronounsParadigmatic }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noMTPronouns }
  , { walsCode := "wgl", language := "Waigali", iso := "wbk", value := .mTPronounsParadigmatic }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noMTPronouns }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noMTPronouns }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noMTPronouns }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noMTPronouns }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noMTPronouns }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noMTPronouns }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noMTPronouns }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .mTPronounsNonParadigmatic }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noMTPronouns }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noMTPronouns }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noMTPronouns }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noMTPronouns }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noMTPronouns }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .noMTPronouns }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noMTPronouns }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noMTPronouns }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noMTPronouns }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .mTPronounsNonParadigmatic }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noMTPronouns }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noMTPronouns }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .mTPronounsParadigmatic }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noMTPronouns }
  , { walsCode := "yna", language := "Yupik (Naukan)", iso := "ynk", value := .noMTPronouns }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noMTPronouns }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noMTPronouns }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noMTPronouns }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noMTPronouns }
  ]

-- Count verification
theorem total_count : allData.length = 230 := by native_decide

theorem count_noMTPronouns :
    (allData.filter (·.value == .noMTPronouns)).length = 200 := by native_decide
theorem count_mTPronounsParadigmatic :
    (allData.filter (·.value == .mTPronounsParadigmatic)).length = 27 := by native_decide
theorem count_mTPronounsNonParadigmatic :
    (allData.filter (·.value == .mTPronounsNonParadigmatic)).length = 3 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F136A
