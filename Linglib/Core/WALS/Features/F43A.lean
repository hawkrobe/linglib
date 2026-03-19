/-!
# WALS Feature 43A: Third Person Pronouns and Demonstratives
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 43A`.

Chapter 43, 225 languages.
-/

namespace Core.WALS.F43A

/-- WALS 43A values. -/
inductive ThirdPersonPronounsAndDemonstratives where
  | unrelated  -- Unrelated (100 languages)
  | relatedForAllDemonstratives  -- Related for all demonstratives (52 languages)
  | relatedToRemoteDemonstratives  -- Related to remote demonstratives (18 languages)
  | relatedToNonRemoteDemonstratives  -- Related to non-remote demonstratives (14 languages)
  | relatedByGenderMarkers  -- Related by gender markers (24 languages)
  | relatedForNonHumanReference  -- Related for non-human reference (17 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 43A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ThirdPersonPronounsAndDemonstratives
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 43A dataset (225 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ain", language := "Ainu", iso := "ain", value := .unrelated }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .relatedByGenderMarkers }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .relatedForAllDemonstratives }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .relatedForAllDemonstratives }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .unrelated }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .unrelated }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .relatedByGenderMarkers }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .relatedByGenderMarkers }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .relatedToRemoteDemonstratives }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .unrelated }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .relatedToRemoteDemonstratives }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .relatedForNonHumanReference }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .relatedByGenderMarkers }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .unrelated }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .relatedToRemoteDemonstratives }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .relatedForAllDemonstratives }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .unrelated }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .unrelated }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .relatedForAllDemonstratives }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .unrelated }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .relatedToRemoteDemonstratives }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .relatedForAllDemonstratives }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .unrelated }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .unrelated }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .relatedForAllDemonstratives }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .relatedForAllDemonstratives }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .unrelated }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .relatedForAllDemonstratives }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .unrelated }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .unrelated }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .relatedForAllDemonstratives }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .relatedToRemoteDemonstratives }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .relatedForAllDemonstratives }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .relatedByGenderMarkers }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .unrelated }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .unrelated }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .relatedForNonHumanReference }
  , { walsCode := "eng", language := "English", iso := "eng", value := .relatedForAllDemonstratives }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .unrelated }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .unrelated }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .unrelated }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .unrelated }
  , { walsCode := "fre", language := "French", iso := "fra", value := .relatedByGenderMarkers }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .unrelated }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .relatedForNonHumanReference }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .relatedToRemoteDemonstratives }
  , { walsCode := "ger", language := "German", iso := "deu", value := .relatedByGenderMarkers }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .relatedForNonHumanReference }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .relatedByGenderMarkers }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .unrelated }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .relatedByGenderMarkers }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .unrelated }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .relatedForNonHumanReference }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .unrelated }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .relatedToRemoteDemonstratives }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .relatedForAllDemonstratives }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .relatedForAllDemonstratives }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .relatedForAllDemonstratives }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .relatedForNonHumanReference }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .relatedForAllDemonstratives }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .unrelated }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .relatedByGenderMarkers }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .unrelated }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .unrelated }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .unrelated }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .unrelated }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .relatedToRemoteDemonstratives }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .unrelated }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .unrelated }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .relatedForNonHumanReference }
  , { walsCode := "jun", language := "Juang", iso := "jun", value := .unrelated }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .relatedByGenderMarkers }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .relatedForAllDemonstratives }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .relatedToRemoteDemonstratives }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .unrelated }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .relatedForAllDemonstratives }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .unrelated }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .relatedForNonHumanReference }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .unrelated }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .relatedForAllDemonstratives }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .relatedForAllDemonstratives }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .relatedForAllDemonstratives }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .unrelated }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .unrelated }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .relatedByGenderMarkers }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .unrelated }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .unrelated }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .unrelated }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .unrelated }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .unrelated }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .unrelated }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .unrelated }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .unrelated }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .unrelated }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .unrelated }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .unrelated }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .relatedForNonHumanReference }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .unrelated }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .relatedByGenderMarkers }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .relatedForAllDemonstratives }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .unrelated }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .unrelated }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .relatedToRemoteDemonstratives }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .relatedByGenderMarkers }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .relatedForAllDemonstratives }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .relatedForAllDemonstratives }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .relatedByGenderMarkers }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .relatedForNonHumanReference }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .relatedForAllDemonstratives }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .relatedToRemoteDemonstratives }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .relatedForAllDemonstratives }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .unrelated }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .relatedForAllDemonstratives }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .unrelated }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .relatedByGenderMarkers }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .relatedByGenderMarkers }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .unrelated }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .relatedForAllDemonstratives }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .unrelated }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .relatedForAllDemonstratives }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .unrelated }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .unrelated }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .unrelated }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .unrelated }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .unrelated }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .unrelated }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .unrelated }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .relatedForNonHumanReference }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .unrelated }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .relatedForAllDemonstratives }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .unrelated }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .unrelated }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .unrelated }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .unrelated }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .relatedForAllDemonstratives }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .relatedForNonHumanReference }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .relatedByGenderMarkers }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .unrelated }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .unrelated }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .unrelated }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .unrelated }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .relatedForAllDemonstratives }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .relatedForAllDemonstratives }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .relatedForAllDemonstratives }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .unrelated }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .relatedForAllDemonstratives }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .relatedByGenderMarkers }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .relatedForNonHumanReference }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .relatedToRemoteDemonstratives }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .relatedToRemoteDemonstratives }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .relatedForAllDemonstratives }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .unrelated }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .unrelated }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .relatedForAllDemonstratives }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .relatedForNonHumanReference }
  , { walsCode := "qta", language := "Quechua (Tarma)", iso := "qvn", value := .relatedForNonHumanReference }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .relatedForAllDemonstratives }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .relatedToRemoteDemonstratives }
  , { walsCode := "rej", language := "Rejang", iso := "rej", value := .unrelated }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .unrelated }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .relatedForAllDemonstratives }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .relatedToRemoteDemonstratives }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .unrelated }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .unrelated }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .unrelated }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .relatedForAllDemonstratives }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .unrelated }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .relatedByGenderMarkers }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .relatedForAllDemonstratives }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .relatedForNonHumanReference }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .unrelated }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .relatedForAllDemonstratives }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .relatedForAllDemonstratives }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .unrelated }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .unrelated }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .unrelated }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .unrelated }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .relatedForAllDemonstratives }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .relatedForAllDemonstratives }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .unrelated }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .unrelated }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .unrelated }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .relatedByGenderMarkers }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .unrelated }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .unrelated }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .unrelated }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .relatedToRemoteDemonstratives }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .unrelated }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .relatedToRemoteDemonstratives }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .relatedForAllDemonstratives }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .relatedForAllDemonstratives }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .unrelated }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .unrelated }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .relatedByGenderMarkers }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .relatedToRemoteDemonstratives }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .relatedForAllDemonstratives }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .relatedForAllDemonstratives }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .unrelated }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .unrelated }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .unrelated }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .relatedToNonRemoteDemonstratives }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .relatedForNonHumanReference }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .unrelated }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .relatedForAllDemonstratives }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .relatedForAllDemonstratives }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .unrelated }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .relatedByGenderMarkers }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .unrelated }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .relatedForAllDemonstratives }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .unrelated }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .relatedForAllDemonstratives }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .relatedByGenderMarkers }
  ]

-- Count verification
theorem total_count : allData.length = 225 := by native_decide

theorem count_unrelated :
    (allData.filter (·.value == .unrelated)).length = 100 := by native_decide
theorem count_relatedForAllDemonstratives :
    (allData.filter (·.value == .relatedForAllDemonstratives)).length = 52 := by native_decide
theorem count_relatedToRemoteDemonstratives :
    (allData.filter (·.value == .relatedToRemoteDemonstratives)).length = 18 := by native_decide
theorem count_relatedToNonRemoteDemonstratives :
    (allData.filter (·.value == .relatedToNonRemoteDemonstratives)).length = 14 := by native_decide
theorem count_relatedByGenderMarkers :
    (allData.filter (·.value == .relatedByGenderMarkers)).length = 24 := by native_decide
theorem count_relatedForNonHumanReference :
    (allData.filter (·.value == .relatedForNonHumanReference)).length = 17 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F43A
