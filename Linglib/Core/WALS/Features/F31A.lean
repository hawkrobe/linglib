import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 31A: Sex-based and Non-sex-based Gender Systems
@cite{corbett-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 31A`.

Chapter 31, 257 languages.
-/

namespace Core.WALS.F31A

/-- WALS 31A values. -/
inductive GenderBasis where
  | noGender  -- No gender (145 languages)
  | sexBased  -- Sex-based (84 languages)
  | nonSexBased  -- Non-sex-based (28 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 31A dataset (257 languages). -/
def allData : List (Datapoint GenderBasis) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .sexBased }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noGender }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noGender }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .sexBased }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .sexBased }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .noGender }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGender }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .sexBased }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .sexBased }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noGender }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .sexBased }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .sexBased }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .sexBased }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .sexBased }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .sexBased }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .sexBased }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noGender }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noGender }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noGender }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .nonSexBased }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noGender }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .sexBased }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noGender }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noGender }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noGender }
  , { walsCode := "bys", language := "Bayso", iso := "bsw", value := .sexBased }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .sexBased }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .sexBased }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .sexBased }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noGender }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noGender }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .sexBased }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noGender }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .sexBased }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGender }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noGender }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noGender }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noGender }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noGender }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nonSexBased }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noGender }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nonSexBased }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noGender }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noGender }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noGender }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noGender }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noGender }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .nonSexBased }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGender }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noGender }
  , { walsCode := "def", language := "Defaka", iso := "afn", value := .sexBased }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nonSexBased }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .sexBased }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .sexBased }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noGender }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noGender }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .sexBased }
  , { walsCode := "eng", language := "English", iso := "eng", value := .sexBased }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noGender }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noGender }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noGender }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGender }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGender }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noGender }
  , { walsCode := "fre", language := "French", iso := "fra", value := .sexBased }
  , { walsCode := "fgu", language := "Fula (Guinean)", iso := "fuf", value := .nonSexBased }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .sexBased }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noGender }
  , { walsCode := "ger", language := "German", iso := "deu", value := .sexBased }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .nonSexBased }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .sexBased }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noGender }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nonSexBased }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .sexBased }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noGender }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noGender }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noGender }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noGender }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noGender }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .sexBased }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noGender }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noGender }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .sexBased }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .sexBased }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nonSexBased }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGender }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGender }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .sexBased }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noGender }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .sexBased }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noGender }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noGender }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noGender }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGender }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .sexBased }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .sexBased }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noGender }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noGender }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nonSexBased }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noGender }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .sexBased }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noGender }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noGender }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .sexBased }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noGender }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .sexBased }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noGender }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .noGender }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noGender }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noGender }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .sexBased }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noGender }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .sexBased }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noGender }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noGender }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nonSexBased }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noGender }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noGender }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .sexBased }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .nonSexBased }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nonSexBased }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noGender }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noGender }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noGender }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noGender }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .sexBased }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noGender }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .sexBased }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .sexBased }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .sexBased }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noGender }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noGender }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .nonSexBased }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nonSexBased }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .nonSexBased }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noGender }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noGender }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .sexBased }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noGender }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .sexBased }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noGender }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGender }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGender }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .sexBased }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noGender }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noGender }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .sexBased }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noGender }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .sexBased }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .sexBased }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noGender }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noGender }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .sexBased }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .sexBased }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noGender }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .sexBased }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .nonSexBased }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noGender }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noGender }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .sexBased }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noGender }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noGender }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noGender }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .sexBased }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noGender }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .nonSexBased }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noGender }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nonSexBased }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noGender }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .sexBased }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .nonSexBased }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .nonSexBased }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .nonSexBased }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .sexBased }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .noGender }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .sexBased }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noGender }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noGender }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noGender }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .sexBased }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .sexBased }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .nonSexBased }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .sexBased }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noGender }
  , { walsCode := "pil", language := "Pileni", iso := "piv", value := .noGender }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noGender }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .sexBased }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noGender }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .sexBased }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .noGender }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .sexBased }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noGender }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGender }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGender }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .sexBased }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .sexBased }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .sexBased }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .noGender }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noGender }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .noGender }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noGender }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .sexBased }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noGender }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noGender }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .nonSexBased }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noGender }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .sexBased }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noGender }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .nonSexBased }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nonSexBased }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noGender }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .sexBased }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .sexBased }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .sexBased }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGender }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .noGender }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noGender }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .sexBased }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .sexBased }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .sexBased }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noGender }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noGender }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .sexBased }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noGender }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noGender }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .sexBased }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noGender }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noGender }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noGender }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .sexBased }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noGender }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noGender }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noGender }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noGender }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noGender }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noGender }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .sexBased }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noGender }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .nonSexBased }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .sexBased }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .noGender }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noGender }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noGender }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noGender }
  , { walsCode := "yaz", language := "Yazgulyam", iso := "yah", value := .sexBased }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noGender }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noGender }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .sexBased }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGender }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noGender }
  , { walsCode := "ylb", language := "Yulparija", iso := "mpj", value := .noGender }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noGender }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noGender }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .sexBased }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noGender }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .nonSexBased }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noGender }
  ]

-- Count verification
theorem total_count : allData.length = 257 := by native_decide

theorem count_noGender :
    (allData.filter (·.value == .noGender)).length = 145 := by native_decide
theorem count_sexBased :
    (allData.filter (·.value == .sexBased)).length = 84 := by native_decide
theorem count_nonSexBased :
    (allData.filter (·.value == .nonSexBased)).length = 28 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F31A
