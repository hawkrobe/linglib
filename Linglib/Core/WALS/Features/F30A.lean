/-!
# WALS Feature 30A: Number of Genders
@cite{corbett-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 30A`.

Chapter 30, 257 languages.
-/

namespace Core.WALS.F30A

/-- WALS 30A values. -/
inductive GenderCount where
  | none  -- None (145 languages)
  | two  -- Two (50 languages)
  | three  -- Three (26 languages)
  | four  -- Four (12 languages)
  | fiveOrMore  -- Five or more (24 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 30A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : GenderCount
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 30A dataset (257 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .three }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .none }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .none }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .two }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .two }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .none }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .none }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .two }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .two }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .two }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .two }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .two }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .fiveOrMore }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .two }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .four }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .none }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .none }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .none }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .fiveOrMore }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .none }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .three }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .none }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .none }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .none }
  , { walsCode := "bys", language := "Bayso", iso := "bsw", value := .two }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .two }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .two }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .four }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .none }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .none }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .four }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .none }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .two }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .none }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .none }
  , { walsCode := "car", language := "Carib", iso := "car", value := .none }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .none }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .fiveOrMore }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .none }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .two }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .none }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .none }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .none }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .none }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .none }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .two }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .none }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .none }
  , { walsCode := "def", language := "Defaka", iso := "afn", value := .three }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .fiveOrMore }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .two }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .two }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .none }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .none }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .four }
  , { walsCode := "eng", language := "English", iso := "eng", value := .three }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .none }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .none }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .none }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .none }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .none }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .none }
  , { walsCode := "fre", language := "French", iso := "fra", value := .two }
  , { walsCode := "fgu", language := "Fula (Guinean)", iso := "fuf", value := .fiveOrMore }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .two }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .none }
  , { walsCode := "ger", language := "German", iso := "deu", value := .three }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .four }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .three }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .three }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .three }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .none }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .none }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .none }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .none }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .none }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .two }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .none }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .none }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .two }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .two }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .two }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .none }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .none }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .fiveOrMore }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .none }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .three }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .none }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .none }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .none }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .none }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .fiveOrMore }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .two }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .none }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .none }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .fiveOrMore }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .none }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .three }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .none }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .none }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .two }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .three }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .none }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .none }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .none }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .none }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .two }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .none }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .two }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .none }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .none }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .fiveOrMore }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .none }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .none }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .two }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .fiveOrMore }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .three }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .none }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .none }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .none }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .four }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .none }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .two }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .three }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .two }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .none }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .none }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .fiveOrMore }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .fiveOrMore }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .two }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .two }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .none }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .three }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .none }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .none }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .none }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .three }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .none }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .none }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .four }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .fiveOrMore }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .two }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .none }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .fiveOrMore }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .two }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .none }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .two }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .two }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .none }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .none }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .three }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .none }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .none }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .none }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .fiveOrMore }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .none }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .three }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .none }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .fiveOrMore }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .none }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .fiveOrMore }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .fiveOrMore }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .fiveOrMore }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .two }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .three }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .none }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .two }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .none }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .none }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .none }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .two }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .two }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .two }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .four }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .none }
  , { walsCode := "pil", language := "Pileni", iso := "piv", value := .none }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .none }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .four }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .none }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .two }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .none }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .two }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .none }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .two }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .three }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .three }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .none }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .none }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .three }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .none }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .none }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .fiveOrMore }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .none }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .two }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .none }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .fiveOrMore }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .fiveOrMore }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .none }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .two }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .two }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .three }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .none }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .none }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .none }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .three }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .two }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .two }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .none }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .none }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .four }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .none }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .two }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .none }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .none }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .none }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .three }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .none }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .none }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .none }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .none }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .none }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .none }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .four }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .none }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .three }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .three }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .none }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .none }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .none }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .none }
  , { walsCode := "yaz", language := "Yazgulyam", iso := "yah", value := .two }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .none }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .none }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .fiveOrMore }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .none }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .none }
  , { walsCode := "ylb", language := "Yulparija", iso := "mpj", value := .none }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .none }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .none }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .four }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .none }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .fiveOrMore }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .none }
  ]

-- Count verification
theorem total_count : allData.length = 257 := by native_decide

theorem count_none :
    (allData.filter (·.value == .none)).length = 145 := by native_decide
theorem count_two :
    (allData.filter (·.value == .two)).length = 50 := by native_decide
theorem count_three :
    (allData.filter (·.value == .three)).length = 26 := by native_decide
theorem count_four :
    (allData.filter (·.value == .four)).length = 12 := by native_decide
theorem count_fiveOrMore :
    (allData.filter (·.value == .fiveOrMore)).length = 24 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F30A
