/-!
# WALS Feature 17A: Rhythm Types
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 17A`.

Chapter 17, 323 languages.
-/

namespace Core.WALS.F17A

/-- WALS 17A values. -/
inductive RhythmTypes where
  | trochaic  -- Trochaic (153 languages)
  | iambic  -- Iambic (31 languages)
  | dualBothTrochaicAndIambic  -- Dual: both trochaic and iambic (4 languages)
  | undetermined  -- Undetermined (37 languages)
  | noRhythmicStress  -- No rhythmic stress (98 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 17A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : RhythmTypes
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 17A dataset (323 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ace", language := "Acehnese", iso := "ace", value := .trochaic }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .noRhythmicStress }
  , { walsCode := "akl", language := "Aklanon", iso := "akl", value := .iambic }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noRhythmicStress }
  , { walsCode := "atq", language := "Alutiiq", iso := "ems", value := .undetermined }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .trochaic }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noRhythmicStress }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .trochaic }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .trochaic }
  , { walsCode := "abe", language := "Arabic (Beirut)", iso := "apc", value := .trochaic }
  , { walsCode := "ael", language := "Arabic (Eastern Libyan)", iso := "ayl", value := .iambic }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .trochaic }
  , { walsCode := "arv", language := "Arabic (Negev)", iso := "ajp", value := .trochaic }
  , { walsCode := "apa", language := "Arabic (Palestinian)", iso := "ajp", value := .trochaic }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .trochaic }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noRhythmicStress }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .undetermined }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .trochaic }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .iambic }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .noRhythmicStress }
  , { walsCode := "awd", language := "Awadhi", iso := "awa", value := .noRhythmicStress }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .trochaic }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .trochaic }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .noRhythmicStress }
  , { walsCode := "blk", language := "Balantak", iso := "blz", value := .trochaic }
  , { walsCode := "bbm", language := "Bambam", iso := "ptu", value := .noRhythmicStress }
  , { walsCode := "bna", language := "Banawá", iso := "jaa", value := .trochaic }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .undetermined }
  , { walsCode := "bgg", language := "Banggai", iso := "bgz", value := .undetermined }
  , { walsCode := "bnt", language := "Bantik", iso := "bnq", value := .noRhythmicStress }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noRhythmicStress }
  , { walsCode := "bqi", language := "Basque (Basaburua and Imoz)", iso := "eus", value := .undetermined }
  , { walsCode := "bqb", language := "Basque (Bidasoa Valley)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqg", language := "Basque (Gernica)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqh", language := "Basque (Hondarribia)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bql", language := "Basque (Lekeitio)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqn", language := "Basque (Northern High Navarrese)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqo", language := "Basque (Oñati)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqr", language := "Basque (Roncalese)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqs", language := "Basque (Sakana)", iso := "eus", value := .undetermined }
  , { walsCode := "bso", language := "Basque (Souletin)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqz", language := "Basque (Zeberio)", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .trochaic }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noRhythmicStress }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .undetermined }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .trochaic }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noRhythmicStress }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noRhythmicStress }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .trochaic }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .trochaic }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .trochaic }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noRhythmicStress }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .trochaic }
  , { walsCode := "cyg", language := "Cayuga", iso := "cay", value := .iambic }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .trochaic }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .iambic }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .undetermined }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .noRhythmicStress }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .iambic }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noRhythmicStress }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .trochaic }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noRhythmicStress }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .trochaic }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .trochaic }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .iambic }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noRhythmicStress }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .trochaic }
  , { walsCode := "dak", language := "Dakota", iso := "dak", value := .noRhythmicStress }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .trochaic }
  , { walsCode := "dri", language := "Dari", iso := "prs", value := .trochaic }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .noRhythmicStress }
  , { walsCode := "dhu", language := "Dhurga", iso := "dhu", value := .noRhythmicStress }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .undetermined }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .trochaic }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noRhythmicStress }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .trochaic }
  , { walsCode := "dob", language := "Dobel", iso := "kvo", value := .noRhythmicStress }
  , { walsCode := "dou", language := "Doutai", iso := "tds", value := .noRhythmicStress }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .trochaic }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .trochaic }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .trochaic }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noRhythmicStress }
  , { walsCode := "eng", language := "English", iso := "eng", value := .trochaic }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .trochaic }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .trochaic }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .iambic }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .undetermined }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .trochaic }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .trochaic }
  , { walsCode := "for", language := "Fore", iso := "for", value := .noRhythmicStress }
  , { walsCode := "fre", language := "French", iso := "fra", value := .undetermined }
  , { walsCode := "glp", language := "Gaalpu", iso := "dhg", value := .undetermined }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .undetermined }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .noRhythmicStress }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .trochaic }
  , { walsCode := "gay", language := "Gayo", iso := "gay", value := .trochaic }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .trochaic }
  , { walsCode := "ger", language := "German", iso := "deu", value := .trochaic }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .undetermined }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noRhythmicStress }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .trochaic }
  , { walsCode := "gor", language := "Gorowa", iso := "gow", value := .noRhythmicStress }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noRhythmicStress }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .trochaic }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .undetermined }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .trochaic }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .trochaic }
  , { walsCode := "hno", language := "Haida (Northern)", iso := "hdn", value := .iambic }
  , { walsCode := "hnn", language := "Hanunóo", iso := "hnn", value := .undetermined }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .trochaic }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .trochaic }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .iambic }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .undetermined }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noRhythmicStress }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .trochaic }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .trochaic }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .trochaic }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .trochaic }
  , { walsCode := "iga", language := "Inga", iso := "inb", value := .trochaic }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noRhythmicStress }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noRhythmicStress }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .undetermined }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .undetermined }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .trochaic }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .undetermined }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .noRhythmicStress }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .trochaic }
  , { walsCode := "kra", language := "Kara (in Papua New Guinea)", iso := "leu", value := .undetermined }
  , { walsCode := "krl", language := "Karelian", iso := "krl", value := .trochaic }
  , { walsCode := "kaj", language := "Kaure", iso := "bpp", value := .trochaic }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .trochaic }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .trochaic }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noRhythmicStress }
  , { walsCode := "ktn", language := "Ketengban", iso := "xte", value := .noRhythmicStress }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noRhythmicStress }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noRhythmicStress }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .undetermined }
  , { walsCode := "ksr", language := "Kisar", iso := "kje", value := .trochaic }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .trochaic }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noRhythmicStress }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .noRhythmicStress }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .trochaic }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .trochaic }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noRhythmicStress }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .undetermined }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .undetermined }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .trochaic }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .undetermined }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .trochaic }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .trochaic }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .trochaic }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .dualBothTrochaicAndIambic }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noRhythmicStress }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .trochaic }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .trochaic }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .trochaic }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .undetermined }
  , { walsCode := "liv", language := "Liv", iso := "liv", value := .trochaic }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .trochaic }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .trochaic }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .noRhythmicStress }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .iambic }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .trochaic }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .trochaic }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .trochaic }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .trochaic }
  , { walsCode := "mlc", language := "Malacca Creole", iso := "mcm", value := .trochaic }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noRhythmicStress }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .trochaic }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .undetermined }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .undetermined }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .trochaic }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .trochaic }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .trochaic }
  , { walsCode := "mnj", language := "Mantjiltjara", iso := "mpj", value := .trochaic }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .iambic }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .trochaic }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .trochaic }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .noRhythmicStress }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .noRhythmicStress }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noRhythmicStress }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .iambic }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .trochaic }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .trochaic }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .trochaic }
  , { walsCode := "myy", language := "Mayi-Yapi", iso := "xyj", value := .trochaic }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .iambic }
  , { walsCode := "mta", language := "Mentuh Tapuh", iso := "sdo", value := .trochaic }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noRhythmicStress }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .iambic }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .trochaic }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noRhythmicStress }
  , { walsCode := "mmo", language := "Mordvin (Moksha)", iso := "mdf", value := .noRhythmicStress }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .trochaic }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .iambic }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .trochaic }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .iambic }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .trochaic }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .trochaic }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .trochaic }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .trochaic }
  , { walsCode := "ngr", language := "Ngarinyeri", iso := "nay", value := .trochaic }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .trochaic }
  , { walsCode := "nin", language := "Ningil", iso := "niz", value := .trochaic }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .undetermined }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .trochaic }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .undetermined }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .trochaic }
  , { walsCode := "nbo", language := "Nyambo", iso := "now", value := .noRhythmicStress }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .trochaic }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .trochaic }
  , { walsCode := "obk", language := "Obokuitai", iso := "afz", value := .noRhythmicStress }
  , { walsCode := "olm", language := "Oloh Mangtangai", iso := "nij", value := .noRhythmicStress }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noRhythmicStress }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .trochaic }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noRhythmicStress }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .trochaic }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .iambic }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noRhythmicStress }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noRhythmicStress }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .iambic }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .trochaic }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .trochaic }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .trochaic }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .trochaic }
  , { walsCode := "pkm", language := "Pokomchí", iso := "poh", value := .noRhythmicStress }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .trochaic }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .iambic }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .undetermined }
  , { walsCode := "que", language := "Quechan", iso := "yum", value := .noRhythmicStress }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .trochaic }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .undetermined }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .noRhythmicStress }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .trochaic }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .noRhythmicStress }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noRhythmicStress }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .trochaic }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .trochaic }
  , { walsCode := "swi", language := "Sawai", iso := "szw", value := .noRhythmicStress }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noRhythmicStress }
  , { walsCode := "sru", language := "Selaru", iso := "slu", value := .trochaic }
  , { walsCode := "sly", language := "Selayar", iso := "sly", value := .noRhythmicStress }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .trochaic }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .trochaic }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noRhythmicStress }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .iambic }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .trochaic }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noRhythmicStress }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .undetermined }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .iambic }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .noRhythmicStress }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noRhythmicStress }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noRhythmicStress }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .trochaic }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .noRhythmicStress }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .trochaic }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .noRhythmicStress }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .trochaic }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noRhythmicStress }
  , { walsCode := "sto", language := "Stoney", iso := "sto", value := .noRhythmicStress }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noRhythmicStress }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .trochaic }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .trochaic }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .trochaic }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noRhythmicStress }
  , { walsCode := "tns", language := "Tanna (Southwest)", iso := "nwi", value := .trochaic }
  , { walsCode := "tgw", language := "Tarangan (West)", iso := "txn", value := .trochaic }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noRhythmicStress }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .trochaic }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .trochaic }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noRhythmicStress }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .trochaic }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .trochaic }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .trochaic }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .trochaic }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .noRhythmicStress }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .noRhythmicStress }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .trochaic }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noRhythmicStress }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noRhythmicStress }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .trochaic }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .trochaic }
  , { walsCode := "unm", language := "Unami", iso := "unm", value := .iambic }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .undetermined }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .iambic }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .trochaic }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .trochaic }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .iambic }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .trochaic }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .trochaic }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .trochaic }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .trochaic }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .trochaic }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .trochaic }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noRhythmicStress }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .trochaic }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .trochaic }
  , { walsCode := "wer", language := "Weri", iso := "wer", value := .iambic }
  , { walsCode := "wet", language := "Wetan", iso := "lex", value := .undetermined }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .dualBothTrochaicAndIambic }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .trochaic }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .iambic }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noRhythmicStress }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .noRhythmicStress }
  , { walsCode := "ymd", language := "Yamdena", iso := "jmd", value := .noRhythmicStress }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .noRhythmicStress }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .trochaic }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .undetermined }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .trochaic }
  , { walsCode := "yzv", language := "Yazva", iso := "kpv", value := .noRhythmicStress }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .trochaic }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .dualBothTrochaicAndIambic }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .trochaic }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .trochaic }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .noRhythmicStress }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .undetermined }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .iambic }
  , { walsCode := "ych", language := "Yup'ik (Chevak)", iso := "esu", value := .iambic }
  , { walsCode := "yun", language := "Yup'ik (Norton Sound)", iso := "esu", value := .iambic }
  , { walsCode := "ysl", language := "Yupik (St. Lawrence Island)", iso := "ess", value := .iambic }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .dualBothTrochaicAndIambic }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .trochaic }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .trochaic }
  ]

-- Count verification
theorem total_count : allData.length = 323 := by native_decide

theorem count_trochaic :
    (allData.filter (·.value == .trochaic)).length = 153 := by native_decide
theorem count_iambic :
    (allData.filter (·.value == .iambic)).length = 31 := by native_decide
theorem count_dualBothTrochaicAndIambic :
    (allData.filter (·.value == .dualBothTrochaicAndIambic)).length = 4 := by native_decide
theorem count_undetermined :
    (allData.filter (·.value == .undetermined)).length = 37 := by native_decide
theorem count_noRhythmicStress :
    (allData.filter (·.value == .noRhythmicStress)).length = 98 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F17A
