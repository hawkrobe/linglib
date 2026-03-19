import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 75A: Epistemic Possibility
@cite{vanbogaert-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 75A`.

Chapter 75, 240 languages.
-/

namespace Core.WALS.F75A

/-- WALS 75A values. -/
inductive EpistemicPossibility where
  | verbalConstructions  -- Verbal constructions (65 languages)
  | affixesOnVerbs  -- Affixes on verbs (84 languages)
  | other  -- Other (91 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 75A dataset (240 languages). -/
def allData : List (Datapoint EpistemicPossibility) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .verbalConstructions }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .verbalConstructions }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .affixesOnVerbs }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .other }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .other }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .verbalConstructions }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .other }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .verbalConstructions }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .affixesOnVerbs }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .verbalConstructions }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .verbalConstructions }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .verbalConstructions }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .affixesOnVerbs }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .other }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .affixesOnVerbs }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .affixesOnVerbs }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .other }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .other }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .other }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .verbalConstructions }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .other }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .affixesOnVerbs }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .other }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .other }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .other }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .affixesOnVerbs }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .affixesOnVerbs }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .other }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .affixesOnVerbs }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .verbalConstructions }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .other }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .other }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .other }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .verbalConstructions }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .affixesOnVerbs }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .other }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .other }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .affixesOnVerbs }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .affixesOnVerbs }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .other }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .affixesOnVerbs }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .affixesOnVerbs }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .affixesOnVerbs }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .verbalConstructions }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .affixesOnVerbs }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .other }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .verbalConstructions }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .affixesOnVerbs }
  , { walsCode := "eng", language := "English", iso := "eng", value := .verbalConstructions }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .affixesOnVerbs }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .affixesOnVerbs }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .verbalConstructions }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .verbalConstructions }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .other }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .verbalConstructions }
  , { walsCode := "fre", language := "French", iso := "fra", value := .verbalConstructions }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .affixesOnVerbs }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .affixesOnVerbs }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .affixesOnVerbs }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .other }
  , { walsCode := "ger", language := "German", iso := "deu", value := .verbalConstructions }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .affixesOnVerbs }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .verbalConstructions }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .verbalConstructions }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .affixesOnVerbs }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .affixesOnVerbs }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .affixesOnVerbs }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .verbalConstructions }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .other }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .verbalConstructions }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .verbalConstructions }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .other }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .verbalConstructions }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .other }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .verbalConstructions }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .verbalConstructions }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .affixesOnVerbs }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .affixesOnVerbs }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .other }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .other }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .verbalConstructions }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .verbalConstructions }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .other }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .other }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .other }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .verbalConstructions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .verbalConstructions }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .other }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .other }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .verbalConstructions }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .affixesOnVerbs }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .other }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .other }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .other }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .other }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .other }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .other }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .other }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .affixesOnVerbs }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .affixesOnVerbs }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .other }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .affixesOnVerbs }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .other }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .verbalConstructions }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .other }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .verbalConstructions }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .other }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .verbalConstructions }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .other }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .affixesOnVerbs }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .verbalConstructions }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .affixesOnVerbs }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .other }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .verbalConstructions }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .other }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .affixesOnVerbs }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .other }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .other }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .verbalConstructions }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .other }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .verbalConstructions }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .affixesOnVerbs }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .other }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .verbalConstructions }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .verbalConstructions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .verbalConstructions }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .affixesOnVerbs }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .affixesOnVerbs }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .other }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .affixesOnVerbs }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .other }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .verbalConstructions }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .affixesOnVerbs }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .other }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .other }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .verbalConstructions }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .verbalConstructions }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .other }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .affixesOnVerbs }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .affixesOnVerbs }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .verbalConstructions }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .other }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .verbalConstructions }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .other }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .affixesOnVerbs }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .affixesOnVerbs }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .other }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .other }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .affixesOnVerbs }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .other }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .other }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .other }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .affixesOnVerbs }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .other }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .other }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .affixesOnVerbs }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .verbalConstructions }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .other }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .affixesOnVerbs }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .affixesOnVerbs }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .verbalConstructions }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .affixesOnVerbs }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .other }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .other }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .affixesOnVerbs }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .affixesOnVerbs }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .other }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .verbalConstructions }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .affixesOnVerbs }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .verbalConstructions }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .other }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .affixesOnVerbs }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .other }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .verbalConstructions }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .verbalConstructions }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .verbalConstructions }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .verbalConstructions }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .other }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .other }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .other }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .affixesOnVerbs }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .affixesOnVerbs }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .other }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .verbalConstructions }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .affixesOnVerbs }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .other }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .other }
  , { walsCode := "so", language := "So", iso := "teu", value := .other }
  , { walsCode := "som", language := "Somali", iso := "som", value := .affixesOnVerbs }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .verbalConstructions }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .affixesOnVerbs }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .verbalConstructions }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .affixesOnVerbs }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .verbalConstructions }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .affixesOnVerbs }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .other }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .affixesOnVerbs }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .other }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .verbalConstructions }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .other }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .verbalConstructions }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .other }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .affixesOnVerbs }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .other }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .affixesOnVerbs }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .other }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .other }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .affixesOnVerbs }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .affixesOnVerbs }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .verbalConstructions }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .affixesOnVerbs }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .other }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .verbalConstructions }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .affixesOnVerbs }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .affixesOnVerbs }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .other }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .other }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .affixesOnVerbs }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .other }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .verbalConstructions }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .affixesOnVerbs }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .affixesOnVerbs }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .affixesOnVerbs }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .affixesOnVerbs }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .affixesOnVerbs }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .other }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .other }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .verbalConstructions }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .affixesOnVerbs }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .affixesOnVerbs }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .other }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .affixesOnVerbs }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .verbalConstructions }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .affixesOnVerbs }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .affixesOnVerbs }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .affixesOnVerbs }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .other }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .affixesOnVerbs }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .affixesOnVerbs }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .affixesOnVerbs }
  ]

-- Count verification
theorem total_count : allData.length = 240 := by native_decide

theorem count_verbalConstructions :
    (allData.filter (·.value == .verbalConstructions)).length = 65 := by native_decide
theorem count_affixesOnVerbs :
    (allData.filter (·.value == .affixesOnVerbs)).length = 84 := by native_decide
theorem count_other :
    (allData.filter (·.value == .other)).length = 91 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F75A
