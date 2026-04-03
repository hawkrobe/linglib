import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 111A: Nonperiphrastic Causative Constructions
@cite{song-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 111A`.

Chapter 111, 310 languages.
-/

namespace Core.WALS.F111A

/-- WALS 111A values. -/
inductive NonperiphrCausativeType where
  | neither  -- Neither (23 languages)
  | morphologicalOnly  -- Morphological but no compound (254 languages)
  | compoundOnly  -- Compound but no morphological (9 languages)
  | both  -- Both (24 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 111A dataset (310 languages). -/
def allData : List (Datapoint NonperiphrCausativeType) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .morphologicalOnly }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .morphologicalOnly }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .morphologicalOnly }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .morphologicalOnly }
  , { walsCode := "aji", language := "Ajië", iso := "aji", value := .morphologicalOnly }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .both }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .morphologicalOnly }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .morphologicalOnly }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .morphologicalOnly }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .morphologicalOnly }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .morphologicalOnly }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .morphologicalOnly }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .morphologicalOnly }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .morphologicalOnly }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .morphologicalOnly }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .morphologicalOnly }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .morphologicalOnly }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .morphologicalOnly }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .morphologicalOnly }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .morphologicalOnly }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .neither }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .morphologicalOnly }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .morphologicalOnly }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .morphologicalOnly }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .morphologicalOnly }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .morphologicalOnly }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .morphologicalOnly }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .both }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .morphologicalOnly }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .morphologicalOnly }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .both }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .morphologicalOnly }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .morphologicalOnly }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .morphologicalOnly }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .morphologicalOnly }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .both }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .morphologicalOnly }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .morphologicalOnly }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .morphologicalOnly }
  , { walsCode := "car", language := "Carib", iso := "car", value := .morphologicalOnly }
  , { walsCode := "crq", language := "Carrier", iso := "crx", value := .both }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .morphologicalOnly }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .morphologicalOnly }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .morphologicalOnly }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .morphologicalOnly }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .morphologicalOnly }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .morphologicalOnly }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .morphologicalOnly }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .morphologicalOnly }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .morphologicalOnly }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .morphologicalOnly }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .morphologicalOnly }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .morphologicalOnly }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .morphologicalOnly }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .morphologicalOnly }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .morphologicalOnly }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .morphologicalOnly }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .morphologicalOnly }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .neither }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .morphologicalOnly }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .morphologicalOnly }
  , { walsCode := "eng", language := "English", iso := "eng", value := .morphologicalOnly }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .morphologicalOnly }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .morphologicalOnly }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .neither }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .morphologicalOnly }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .morphologicalOnly }
  , { walsCode := "fre", language := "French", iso := "fra", value := .both }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .morphologicalOnly }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .morphologicalOnly }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .morphologicalOnly }
  , { walsCode := "ger", language := "German", iso := "deu", value := .morphologicalOnly }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .neither }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .morphologicalOnly }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .neither }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .morphologicalOnly }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .morphologicalOnly }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .morphologicalOnly }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .morphologicalOnly }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .morphologicalOnly }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .morphologicalOnly }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .morphologicalOnly }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .morphologicalOnly }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .morphologicalOnly }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .morphologicalOnly }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .neither }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .morphologicalOnly }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .morphologicalOnly }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .morphologicalOnly }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .morphologicalOnly }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .morphologicalOnly }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .morphologicalOnly }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .morphologicalOnly }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .morphologicalOnly }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .morphologicalOnly }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .morphologicalOnly }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .neither }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .morphologicalOnly }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .morphologicalOnly }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .morphologicalOnly }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .compoundOnly }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .morphologicalOnly }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .morphologicalOnly }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .morphologicalOnly }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .morphologicalOnly }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .morphologicalOnly }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .morphologicalOnly }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .morphologicalOnly }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .morphologicalOnly }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .morphologicalOnly }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .compoundOnly }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .morphologicalOnly }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .morphologicalOnly }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .morphologicalOnly }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .morphologicalOnly }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .morphologicalOnly }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .morphologicalOnly }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .morphologicalOnly }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .both }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .neither }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .morphologicalOnly }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .morphologicalOnly }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .morphologicalOnly }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .morphologicalOnly }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .morphologicalOnly }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .both }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .compoundOnly }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .morphologicalOnly }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .morphologicalOnly }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .morphologicalOnly }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .morphologicalOnly }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .morphologicalOnly }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .morphologicalOnly }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .both }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .neither }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .morphologicalOnly }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .morphologicalOnly }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .morphologicalOnly }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .morphologicalOnly }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .both }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .both }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .both }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .morphologicalOnly }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .morphologicalOnly }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .morphologicalOnly }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .morphologicalOnly }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .morphologicalOnly }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .morphologicalOnly }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .morphologicalOnly }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .morphologicalOnly }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .morphologicalOnly }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .morphologicalOnly }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .morphologicalOnly }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .morphologicalOnly }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .morphologicalOnly }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .morphologicalOnly }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .morphologicalOnly }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .morphologicalOnly }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .compoundOnly }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .both }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .morphologicalOnly }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .morphologicalOnly }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .morphologicalOnly }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .morphologicalOnly }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .morphologicalOnly }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .morphologicalOnly }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .both }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .morphologicalOnly }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .morphologicalOnly }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .neither }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .morphologicalOnly }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .morphologicalOnly }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .morphologicalOnly }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .morphologicalOnly }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .neither }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .morphologicalOnly }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .both }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .morphologicalOnly }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .morphologicalOnly }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .both }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .neither }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .morphologicalOnly }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .neither }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .morphologicalOnly }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .morphologicalOnly }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .morphologicalOnly }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .morphologicalOnly }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .morphologicalOnly }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .morphologicalOnly }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .morphologicalOnly }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .morphologicalOnly }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .morphologicalOnly }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .morphologicalOnly }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .morphologicalOnly }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .morphologicalOnly }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .morphologicalOnly }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .morphologicalOnly }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .morphologicalOnly }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .morphologicalOnly }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .morphologicalOnly }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .neither }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .morphologicalOnly }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .neither }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .morphologicalOnly }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .morphologicalOnly }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .morphologicalOnly }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .morphologicalOnly }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .morphologicalOnly }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .morphologicalOnly }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .morphologicalOnly }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .morphologicalOnly }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .morphologicalOnly }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .morphologicalOnly }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .morphologicalOnly }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .both }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .morphologicalOnly }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .morphologicalOnly }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .morphologicalOnly }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .morphologicalOnly }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .both }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .morphologicalOnly }
  , { walsCode := "rej", language := "Rejang", iso := "rej", value := .neither }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .morphologicalOnly }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .morphologicalOnly }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .morphologicalOnly }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .morphologicalOnly }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .morphologicalOnly }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .morphologicalOnly }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .neither }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .morphologicalOnly }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .morphologicalOnly }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .morphologicalOnly }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .both }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .morphologicalOnly }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .morphologicalOnly }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .morphologicalOnly }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .morphologicalOnly }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .morphologicalOnly }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .morphologicalOnly }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .morphologicalOnly }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .both }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .morphologicalOnly }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .morphologicalOnly }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .morphologicalOnly }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .morphologicalOnly }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .morphologicalOnly }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .morphologicalOnly }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .morphologicalOnly }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .morphologicalOnly }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .morphologicalOnly }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .morphologicalOnly }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .morphologicalOnly }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .morphologicalOnly }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .neither }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .neither }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .both }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .morphologicalOnly }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .morphologicalOnly }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .morphologicalOnly }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .morphologicalOnly }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .morphologicalOnly }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .morphologicalOnly }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .compoundOnly }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .morphologicalOnly }
  , { walsCode := "tsw", language := "Tswana", iso := "tsn", value := .morphologicalOnly }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .morphologicalOnly }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .both }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .morphologicalOnly }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .morphologicalOnly }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .morphologicalOnly }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .morphologicalOnly }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .morphologicalOnly }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .both }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .morphologicalOnly }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .morphologicalOnly }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .neither }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .morphologicalOnly }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .morphologicalOnly }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .morphologicalOnly }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .morphologicalOnly }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .morphologicalOnly }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .neither }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .compoundOnly }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .morphologicalOnly }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .morphologicalOnly }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .compoundOnly }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .compoundOnly }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .morphologicalOnly }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .morphologicalOnly }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .morphologicalOnly }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .morphologicalOnly }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .morphologicalOnly }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .morphologicalOnly }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .morphologicalOnly }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .morphologicalOnly }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .morphologicalOnly }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .morphologicalOnly }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .morphologicalOnly }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .neither }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .morphologicalOnly }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .morphologicalOnly }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .both }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .neither }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .compoundOnly }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .morphologicalOnly }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .morphologicalOnly }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .morphologicalOnly }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .morphologicalOnly }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .morphologicalOnly }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .morphologicalOnly }
  ]

-- Count verification
theorem total_count : allData.length = 310 := by native_decide

theorem count_neither :
    (allData.filter (·.value == .neither)).length = 23 := by native_decide
theorem count_morphologicalOnly :
    (allData.filter (·.value == .morphologicalOnly)).length = 254 := by native_decide
theorem count_compoundOnly :
    (allData.filter (·.value == .compoundOnly)).length = 9 := by native_decide
theorem count_both :
    (allData.filter (·.value == .both)).length = 24 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F111A
