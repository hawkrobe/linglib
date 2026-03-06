/-!
# WALS Feature 35A: Plurality in Independent Personal Pronouns
@cite{haspelmath-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 35A`.

Chapter 35, 261 languages.
-/

namespace Core.WALS.F35A

/-- WALS 35A values. -/
inductive PronounPlurality where
  | noIndependentSubjectPronouns  -- No independent subject pronouns (2 languages)
  | numberIndifferentPronouns  -- Number-indifferent pronouns (9 languages)
  | personNumberAffixes  -- Person-number affixes (25 languages)
  | personNumberStem  -- Person-number stem (114 languages)
  | personNumberStemPronominalPluralAffix  -- Person-number stem + pronominal plural affix (47 languages)
  | personNumberStemNominalPluralAffix  -- Person-number stem + nominal plural affix (22 languages)
  | personStemPronominalPluralAffix  -- Person stem + pronominal plural affix (23 languages)
  | personStemNominalPluralAffix  -- Person stem + nominal plural affix (19 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 35A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PronounPlurality
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 35A dataset (261 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .personNumberStem }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .personNumberStem }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noIndependentSubjectPronouns }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .personNumberAffixes }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .personNumberAffixes }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .personNumberStem }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .personNumberAffixes }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .personNumberStem }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .personNumberStem }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .personStemPronominalPluralAffix }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .personStemPronominalPluralAffix }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .personNumberStem }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .personNumberStem }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .personStemNominalPluralAffix }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .personNumberStem }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .personNumberStem }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .personNumberStem }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .personNumberStem }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .personNumberStem }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .personStemNominalPluralAffix }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .numberIndifferentPronouns }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .personNumberStem }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .numberIndifferentPronouns }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .personStemNominalPluralAffix }
  , { walsCode := "car", language := "Carib", iso := "car", value := .personNumberStem }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .personNumberAffixes }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .personNumberStem }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .personNumberAffixes }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .personNumberStem }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .personStemPronominalPluralAffix }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .personStemPronominalPluralAffix }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .numberIndifferentPronouns }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .personStemPronominalPluralAffix }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .personNumberAffixes }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .personNumberAffixes }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .personNumberStem }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .personStemPronominalPluralAffix }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .personStemPronominalPluralAffix }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .personStemPronominalPluralAffix }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .personNumberStem }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .personStemPronominalPluralAffix }
  , { walsCode := "eng", language := "English", iso := "eng", value := .personNumberStem }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .personNumberStem }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .personNumberStem }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .personStemPronominalPluralAffix }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .personNumberStem }
  , { walsCode := "fre", language := "French", iso := "fra", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .personNumberStem }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .personNumberStem }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ger", language := "German", iso := "deu", value := .personNumberStem }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .personNumberStem }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .personNumberStem }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .personNumberStem }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .personNumberStem }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .personNumberStem }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .personNumberStem }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .personNumberStem }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .personNumberStem }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .personNumberStem }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .personNumberStem }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .personNumberStem }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .personNumberStem }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .personNumberStem }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .numberIndifferentPronouns }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .personNumberStem }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .personNumberStem }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .personNumberStem }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .personNumberStem }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .personNumberAffixes }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .personStemNominalPluralAffix }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .personStemPronominalPluralAffix }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .personNumberAffixes }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .personStemPronominalPluralAffix }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .personNumberStem }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .personNumberStem }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .personNumberStem }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .personNumberStem }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .personStemNominalPluralAffix }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .personStemPronominalPluralAffix }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .personNumberStem }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .personNumberStem }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .personNumberStem }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .numberIndifferentPronouns }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .personNumberStem }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .personNumberAffixes }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .personNumberStem }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .personNumberStem }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .personNumberAffixes }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .personNumberStem }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .personNumberStem }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .personNumberStem }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .personNumberStem }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .personNumberStem }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .personStemNominalPluralAffix }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .personStemNominalPluralAffix }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .personNumberStem }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .personNumberAffixes }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .personNumberAffixes }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .personNumberStem }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .personNumberStem }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .personNumberStem }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .personNumberStem }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .personNumberStem }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .personNumberStem }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .personNumberStem }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .personStemNominalPluralAffix }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .personNumberStem }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .personNumberStem }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .numberIndifferentPronouns }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .personStemNominalPluralAffix }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .personNumberStem }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .personNumberStem }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .personStemNominalPluralAffix }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .personNumberStem }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .personStemNominalPluralAffix }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .personNumberStem }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .personNumberAffixes }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .personStemPronominalPluralAffix }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .personNumberAffixes }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .personNumberStem }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .personStemNominalPluralAffix }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .personNumberStem }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .personStemPronominalPluralAffix }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .personNumberStem }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "nic", language := "Nicobarese", iso := "ncb", value := .personNumberStem }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .personStemNominalPluralAffix }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .personNumberStem }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .personNumberStem }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .personNumberAffixes }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .numberIndifferentPronouns }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .personStemPronominalPluralAffix }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .personNumberStem }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .personNumberAffixes }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .personNumberStem }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .personNumberAffixes }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .personNumberAffixes }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .personNumberStem }
  , { walsCode := "pil", language := "Pileni", iso := "piv", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .numberIndifferentPronouns }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .personNumberAffixes }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .personNumberStem }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .numberIndifferentPronouns }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .personStemNominalPluralAffix }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .personNumberStem }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .personStemPronominalPluralAffix }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .personNumberStem }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .personStemPronominalPluralAffix }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .personStemPronominalPluralAffix }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .personNumberStem }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .personNumberStem }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .personNumberStem }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .personNumberStem }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .personStemPronominalPluralAffix }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .personNumberStem }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .personNumberStem }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .personNumberStem }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .personNumberStem }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .personNumberStem }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .personNumberAffixes }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .personNumberStem }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .personStemNominalPluralAffix }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .personNumberStem }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .personNumberStem }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .personNumberStem }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .personNumberStem }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .personStemNominalPluralAffix }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .personNumberAffixes }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .personNumberStem }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .personNumberAffixes }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .personStemNominalPluralAffix }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .personStemNominalPluralAffix }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .personNumberStem }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .personNumberStem }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .personNumberStem }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .personStemPronominalPluralAffix }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .personNumberStem }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .personNumberStemNominalPluralAffix }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noIndependentSubjectPronouns }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .personNumberStem }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .personNumberAffixes }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .personStemNominalPluralAffix }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .personNumberStem }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .personNumberStem }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .personNumberStemPronominalPluralAffix }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .personNumberStem }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .personNumberStem }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .personNumberStem }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .personNumberStem }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .personNumberStem }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .personNumberAffixes }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .personStemPronominalPluralAffix }
  , { walsCode := "yna", language := "Yupik (Naukan)", iso := "ynk", value := .personNumberStem }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .personNumberStem }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .personNumberStem }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .personNumberStem }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .personStemPronominalPluralAffix }
  ]

-- Count verification
theorem total_count : allData.length = 261 := by native_decide

theorem count_noIndependentSubjectPronouns :
    (allData.filter (·.value == .noIndependentSubjectPronouns)).length = 2 := by native_decide
theorem count_numberIndifferentPronouns :
    (allData.filter (·.value == .numberIndifferentPronouns)).length = 9 := by native_decide
theorem count_personNumberAffixes :
    (allData.filter (·.value == .personNumberAffixes)).length = 25 := by native_decide
theorem count_personNumberStem :
    (allData.filter (·.value == .personNumberStem)).length = 114 := by native_decide
theorem count_personNumberStemPronominalPluralAffix :
    (allData.filter (·.value == .personNumberStemPronominalPluralAffix)).length = 47 := by native_decide
theorem count_personNumberStemNominalPluralAffix :
    (allData.filter (·.value == .personNumberStemNominalPluralAffix)).length = 22 := by native_decide
theorem count_personStemPronominalPluralAffix :
    (allData.filter (·.value == .personStemPronominalPluralAffix)).length = 23 := by native_decide
theorem count_personStemNominalPluralAffix :
    (allData.filter (·.value == .personStemNominalPluralAffix)).length = 19 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F35A
