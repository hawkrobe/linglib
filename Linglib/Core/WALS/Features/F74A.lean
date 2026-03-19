import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 74A: Situational Possibility
@cite{vanbogaert-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 74A`.

Chapter 74, 234 languages.
-/

namespace Core.WALS.F74A

/-- WALS 74A values. -/
inductive SituationalPossibility where
  | affixesOnVerbs  -- Affixes on verbs (63 languages)
  | verbalConstructions  -- Verbal constructions (158 languages)
  | otherKindsOfMarkers  -- Other kinds of markers (13 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 74A dataset (234 languages). -/
def allData : List (Datapoint SituationalPossibility) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .verbalConstructions }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .verbalConstructions }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .affixesOnVerbs }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .verbalConstructions }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .verbalConstructions }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .verbalConstructions }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .otherKindsOfMarkers }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .verbalConstructions }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .verbalConstructions }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .verbalConstructions }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .verbalConstructions }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .verbalConstructions }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .affixesOnVerbs }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .verbalConstructions }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .affixesOnVerbs }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .affixesOnVerbs }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .verbalConstructions }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .verbalConstructions }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .verbalConstructions }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .verbalConstructions }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .verbalConstructions }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .verbalConstructions }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .affixesOnVerbs }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .affixesOnVerbs }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .verbalConstructions }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .verbalConstructions }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .verbalConstructions }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .affixesOnVerbs }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .otherKindsOfMarkers }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .verbalConstructions }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .verbalConstructions }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .verbalConstructions }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .affixesOnVerbs }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .verbalConstructions }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .otherKindsOfMarkers }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .affixesOnVerbs }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .verbalConstructions }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .affixesOnVerbs }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .affixesOnVerbs }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .verbalConstructions }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .affixesOnVerbs }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .verbalConstructions }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .verbalConstructions }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .affixesOnVerbs }
  , { walsCode := "eng", language := "English", iso := "eng", value := .verbalConstructions }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .affixesOnVerbs }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .verbalConstructions }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .verbalConstructions }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .verbalConstructions }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .verbalConstructions }
  , { walsCode := "fre", language := "French", iso := "fra", value := .verbalConstructions }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .affixesOnVerbs }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .verbalConstructions }
  , { walsCode := "gdk", language := "Gadaba (Kondekor)", iso := "gdb", value := .affixesOnVerbs }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .affixesOnVerbs }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .verbalConstructions }
  , { walsCode := "ger", language := "German", iso := "deu", value := .verbalConstructions }
  , { walsCode := "goj", language := "Gojri", iso := "gju", value := .affixesOnVerbs }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .verbalConstructions }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .affixesOnVerbs }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .affixesOnVerbs }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .affixesOnVerbs }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .verbalConstructions }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .verbalConstructions }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .verbalConstructions }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .verbalConstructions }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .verbalConstructions }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .affixesOnVerbs }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .affixesOnVerbs }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .verbalConstructions }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .verbalConstructions }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .verbalConstructions }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .affixesOnVerbs }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .affixesOnVerbs }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .affixesOnVerbs }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .verbalConstructions }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .verbalConstructions }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .verbalConstructions }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .verbalConstructions }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .affixesOnVerbs }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .affixesOnVerbs }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .verbalConstructions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .verbalConstructions }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .verbalConstructions }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .verbalConstructions }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .otherKindsOfMarkers }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .affixesOnVerbs }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .verbalConstructions }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .verbalConstructions }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .verbalConstructions }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .verbalConstructions }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .verbalConstructions }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .verbalConstructions }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .verbalConstructions }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .affixesOnVerbs }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .affixesOnVerbs }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .verbalConstructions }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .affixesOnVerbs }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .affixesOnVerbs }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .verbalConstructions }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .verbalConstructions }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .otherKindsOfMarkers }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .verbalConstructions }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .verbalConstructions }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .verbalConstructions }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .verbalConstructions }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .verbalConstructions }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .otherKindsOfMarkers }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .affixesOnVerbs }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .verbalConstructions }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .verbalConstructions }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .verbalConstructions }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .verbalConstructions }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .affixesOnVerbs }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .verbalConstructions }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .verbalConstructions }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .verbalConstructions }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .verbalConstructions }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .verbalConstructions }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .verbalConstructions }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .verbalConstructions }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .verbalConstructions }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .verbalConstructions }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .verbalConstructions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .verbalConstructions }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .affixesOnVerbs }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .verbalConstructions }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .verbalConstructions }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .verbalConstructions }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .verbalConstructions }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .verbalConstructions }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .affixesOnVerbs }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .affixesOnVerbs }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .verbalConstructions }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .verbalConstructions }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .verbalConstructions }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .verbalConstructions }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .affixesOnVerbs }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .verbalConstructions }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .verbalConstructions }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .verbalConstructions }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .verbalConstructions }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .verbalConstructions }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .verbalConstructions }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .otherKindsOfMarkers }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .affixesOnVerbs }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .otherKindsOfMarkers }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .verbalConstructions }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .affixesOnVerbs }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .verbalConstructions }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .verbalConstructions }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .affixesOnVerbs }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .verbalConstructions }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .verbalConstructions }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .verbalConstructions }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .otherKindsOfMarkers }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .affixesOnVerbs }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .verbalConstructions }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .verbalConstructions }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .verbalConstructions }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .affixesOnVerbs }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .verbalConstructions }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .verbalConstructions }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .verbalConstructions }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .verbalConstructions }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .verbalConstructions }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .affixesOnVerbs }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .verbalConstructions }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .affixesOnVerbs }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .verbalConstructions }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .verbalConstructions }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .verbalConstructions }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .verbalConstructions }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .verbalConstructions }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .affixesOnVerbs }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .verbalConstructions }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .verbalConstructions }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .affixesOnVerbs }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .verbalConstructions }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .verbalConstructions }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .verbalConstructions }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .verbalConstructions }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .verbalConstructions }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .verbalConstructions }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .otherKindsOfMarkers }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .verbalConstructions }
  , { walsCode := "som", language := "Somali", iso := "som", value := .verbalConstructions }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .verbalConstructions }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .affixesOnVerbs }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .verbalConstructions }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .verbalConstructions }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .affixesOnVerbs }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .verbalConstructions }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .verbalConstructions }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .affixesOnVerbs }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .affixesOnVerbs }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .affixesOnVerbs }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .verbalConstructions }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .verbalConstructions }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .verbalConstructions }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .verbalConstructions }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .verbalConstructions }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .affixesOnVerbs }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .verbalConstructions }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .verbalConstructions }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .verbalConstructions }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .verbalConstructions }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .verbalConstructions }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .affixesOnVerbs }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .verbalConstructions }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .verbalConstructions }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .verbalConstructions }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .affixesOnVerbs }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .otherKindsOfMarkers }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .affixesOnVerbs }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .affixesOnVerbs }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .verbalConstructions }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .verbalConstructions }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .otherKindsOfMarkers }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .affixesOnVerbs }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .verbalConstructions }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .verbalConstructions }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .verbalConstructions }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .verbalConstructions }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .verbalConstructions }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .affixesOnVerbs }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .verbalConstructions }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .affixesOnVerbs }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .verbalConstructions }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .affixesOnVerbs }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .otherKindsOfMarkers }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .verbalConstructions }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .verbalConstructions }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .affixesOnVerbs }
  ]

-- Count verification
theorem total_count : allData.length = 234 := by native_decide

theorem count_affixesOnVerbs :
    (allData.filter (·.value == .affixesOnVerbs)).length = 63 := by native_decide
theorem count_verbalConstructions :
    (allData.filter (·.value == .verbalConstructions)).length = 158 := by native_decide
theorem count_otherKindsOfMarkers :
    (allData.filter (·.value == .otherKindsOfMarkers)).length = 13 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F74A
