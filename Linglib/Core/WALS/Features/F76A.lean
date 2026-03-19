import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 76A: Overlap between Situational and Epistemic Modal Marking
@cite{vanbogaert-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 76A`.

Chapter 76, 207 languages.
-/

namespace Core.WALS.F76A

/-- WALS 76A values. -/
inductive ModalOverlap where
  | overlapForBothPossibilityAndNecessity  -- Overlap for both possibility and necessity (36 languages)
  | overlapForEitherPossibilityOrNecessity  -- Overlap for either possibility or necessity (66 languages)
  | noOverlap  -- No overlap (105 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 76A dataset (207 languages). -/
def allData : List (Datapoint ModalOverlap) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noOverlap }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noOverlap }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noOverlap }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noOverlap }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noOverlap }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noOverlap }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noOverlap }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noOverlap }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noOverlap }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noOverlap }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noOverlap }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noOverlap }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noOverlap }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noOverlap }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noOverlap }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noOverlap }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noOverlap }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noOverlap }
  , { walsCode := "eng", language := "English", iso := "eng", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noOverlap }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noOverlap }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "fre", language := "French", iso := "fra", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noOverlap }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ger", language := "German", iso := "deu", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noOverlap }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noOverlap }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noOverlap }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noOverlap }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noOverlap }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noOverlap }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noOverlap }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noOverlap }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noOverlap }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noOverlap }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noOverlap }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noOverlap }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noOverlap }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noOverlap }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noOverlap }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noOverlap }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noOverlap }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noOverlap }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noOverlap }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .noOverlap }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noOverlap }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noOverlap }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noOverlap }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noOverlap }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noOverlap }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .noOverlap }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noOverlap }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noOverlap }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noOverlap }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noOverlap }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noOverlap }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noOverlap }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noOverlap }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .noOverlap }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noOverlap }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .noOverlap }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noOverlap }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noOverlap }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noOverlap }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noOverlap }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noOverlap }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noOverlap }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noOverlap }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noOverlap }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noOverlap }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noOverlap }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noOverlap }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noOverlap }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .noOverlap }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noOverlap }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noOverlap }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noOverlap }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .noOverlap }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .noOverlap }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noOverlap }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noOverlap }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noOverlap }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noOverlap }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noOverlap }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noOverlap }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noOverlap }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noOverlap }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noOverlap }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noOverlap }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noOverlap }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .noOverlap }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noOverlap }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noOverlap }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noOverlap }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noOverlap }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noOverlap }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noOverlap }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noOverlap }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .noOverlap }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noOverlap }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noOverlap }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noOverlap }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noOverlap }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noOverlap }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noOverlap }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noOverlap }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noOverlap }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .noOverlap }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noOverlap }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .overlapForEitherPossibilityOrNecessity }
  ]

-- Count verification
theorem total_count : allData.length = 207 := by native_decide

theorem count_overlapForBothPossibilityAndNecessity :
    (allData.filter (·.value == .overlapForBothPossibilityAndNecessity)).length = 36 := by native_decide
theorem count_overlapForEitherPossibilityOrNecessity :
    (allData.filter (·.value == .overlapForEitherPossibilityOrNecessity)).length = 66 := by native_decide
theorem count_noOverlap :
    (allData.filter (·.value == .noOverlap)).length = 105 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F76A
