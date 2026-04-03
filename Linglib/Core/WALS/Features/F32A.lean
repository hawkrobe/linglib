import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 32A: Systems of Gender Assignment
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 32A`.

Chapter 32, 257 languages.
-/

namespace Core.WALS.F32A

/-- WALS 32A values. -/
inductive SystemsOfGenderAssignment where
  | noGender  -- No gender (145 languages)
  | semantic  -- Semantic (53 languages)
  | semanticAndFormal  -- Semantic and formal (59 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 32A dataset (257 languages). -/
def allData : List (Datapoint SystemsOfGenderAssignment) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .semantic }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noGender }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noGender }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .semanticAndFormal }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .semantic }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .noGender }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGender }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .semanticAndFormal }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .semanticAndFormal }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noGender }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .semanticAndFormal }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .semanticAndFormal }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .semanticAndFormal }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .semanticAndFormal }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .semanticAndFormal }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .semantic }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noGender }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noGender }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noGender }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .semanticAndFormal }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noGender }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .semantic }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noGender }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noGender }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noGender }
  , { walsCode := "bys", language := "Bayso", iso := "bsw", value := .semanticAndFormal }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .semanticAndFormal }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .semanticAndFormal }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .semantic }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noGender }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noGender }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .semantic }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noGender }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .semantic }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGender }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noGender }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noGender }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noGender }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noGender }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .semanticAndFormal }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noGender }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .semantic }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noGender }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noGender }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noGender }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noGender }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noGender }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .semantic }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGender }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noGender }
  , { walsCode := "def", language := "Defaka", iso := "afn", value := .semantic }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .semanticAndFormal }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .semantic }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .semantic }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noGender }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noGender }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .semantic }
  , { walsCode := "eng", language := "English", iso := "eng", value := .semantic }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noGender }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noGender }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noGender }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGender }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGender }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noGender }
  , { walsCode := "fre", language := "French", iso := "fra", value := .semanticAndFormal }
  , { walsCode := "fgu", language := "Fula (Guinean)", iso := "fuf", value := .semanticAndFormal }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .semanticAndFormal }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noGender }
  , { walsCode := "ger", language := "German", iso := "deu", value := .semanticAndFormal }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .semanticAndFormal }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .semantic }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noGender }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .semantic }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .semanticAndFormal }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noGender }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noGender }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noGender }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noGender }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noGender }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .semanticAndFormal }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noGender }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noGender }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .semanticAndFormal }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .semanticAndFormal }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .semantic }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGender }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGender }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .semantic }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noGender }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .semanticAndFormal }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noGender }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noGender }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noGender }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGender }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .semanticAndFormal }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .semanticAndFormal }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noGender }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noGender }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .semanticAndFormal }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noGender }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .semantic }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noGender }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noGender }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .semanticAndFormal }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noGender }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .semantic }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noGender }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .noGender }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noGender }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noGender }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .semantic }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noGender }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .semantic }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noGender }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noGender }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .semanticAndFormal }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noGender }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noGender }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .semantic }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .semanticAndFormal }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .semantic }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noGender }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noGender }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noGender }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noGender }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .semantic }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noGender }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .semanticAndFormal }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .semanticAndFormal }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .semanticAndFormal }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noGender }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noGender }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .semanticAndFormal }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .semanticAndFormal }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .semantic }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noGender }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noGender }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .semanticAndFormal }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noGender }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .semantic }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noGender }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGender }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGender }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .semanticAndFormal }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noGender }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noGender }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .semantic }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noGender }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .semantic }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .semantic }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noGender }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noGender }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .semantic }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .semanticAndFormal }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noGender }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .semanticAndFormal }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .semantic }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noGender }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noGender }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .semanticAndFormal }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noGender }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noGender }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noGender }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .semantic }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noGender }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .semantic }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noGender }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .semanticAndFormal }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noGender }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .semanticAndFormal }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .semanticAndFormal }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .semanticAndFormal }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .semantic }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .semantic }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .noGender }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .semanticAndFormal }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noGender }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noGender }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noGender }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .semanticAndFormal }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .semanticAndFormal }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .semantic }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .semantic }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noGender }
  , { walsCode := "pil", language := "Pileni", iso := "piv", value := .noGender }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noGender }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .semantic }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noGender }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .semantic }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .noGender }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .semanticAndFormal }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noGender }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGender }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGender }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .semanticAndFormal }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .semantic }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .semanticAndFormal }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .noGender }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noGender }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .noGender }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noGender }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .semantic }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noGender }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noGender }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .semanticAndFormal }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noGender }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .semanticAndFormal }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noGender }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .semanticAndFormal }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .semanticAndFormal }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noGender }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .semantic }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .semantic }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .semantic }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGender }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .noGender }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noGender }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .semantic }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .semanticAndFormal }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .semantic }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noGender }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noGender }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .semanticAndFormal }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noGender }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noGender }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .semantic }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noGender }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noGender }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noGender }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .semanticAndFormal }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noGender }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noGender }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noGender }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noGender }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noGender }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noGender }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .semantic }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noGender }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .semantic }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .semantic }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .noGender }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noGender }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noGender }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noGender }
  , { walsCode := "yaz", language := "Yazgulyam", iso := "yah", value := .semantic }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noGender }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noGender }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .semanticAndFormal }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGender }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noGender }
  , { walsCode := "ylb", language := "Yulparija", iso := "mpj", value := .noGender }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noGender }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noGender }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .semantic }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noGender }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .semanticAndFormal }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noGender }
  ]

-- Count verification
theorem total_count : allData.length = 257 := by native_decide

theorem count_noGender :
    (allData.filter (·.value == .noGender)).length = 145 := by native_decide
theorem count_semantic :
    (allData.filter (·.value == .semantic)).length = 53 := by native_decide
theorem count_semanticAndFormal :
    (allData.filter (·.value == .semanticAndFormal)).length = 59 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F32A
