/-!
# WALS Feature 72A: Imperative-Hortative Systems
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 72A`.

Chapter 72, 375 languages.
-/

namespace Core.WALS.F72A

/-- WALS 72A values. -/
inductive ImperativeHortativeSystems where
  | maximalSystem  -- Maximal system (133 languages)
  | minimalSystem  -- Minimal system (20 languages)
  | bothTypesOfSystem  -- Both types of system (21 languages)
  | neitherTypeOfSystem  -- Neither type of system (201 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 72A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ImperativeHortativeSystems
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 72A dataset (375 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .neitherTypeOfSystem }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .maximalSystem }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .neitherTypeOfSystem }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .neitherTypeOfSystem }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .maximalSystem }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .maximalSystem }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .maximalSystem }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .maximalSystem }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .neitherTypeOfSystem }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .minimalSystem }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .neitherTypeOfSystem }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .neitherTypeOfSystem }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .neitherTypeOfSystem }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .neitherTypeOfSystem }
  , { walsCode := "anl", language := "Arabic (North Levantine Spoken)", iso := "apc", value := .maximalSystem }
  , { walsCode := "ark", language := "Araki", iso := "akr", value := .maximalSystem }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .neitherTypeOfSystem }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .neitherTypeOfSystem }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .neitherTypeOfSystem }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .neitherTypeOfSystem }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .maximalSystem }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .neitherTypeOfSystem }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .neitherTypeOfSystem }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .maximalSystem }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .maximalSystem }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .neitherTypeOfSystem }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .neitherTypeOfSystem }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .bothTypesOfSystem }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .maximalSystem }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .maximalSystem }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .neitherTypeOfSystem }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .maximalSystem }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .minimalSystem }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .neitherTypeOfSystem }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .neitherTypeOfSystem }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .neitherTypeOfSystem }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .bothTypesOfSystem }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .neitherTypeOfSystem }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .neitherTypeOfSystem }
  , { walsCode := "buk", language := "Bukusu", iso := "bxk", value := .bothTypesOfSystem }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .maximalSystem }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .neitherTypeOfSystem }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .neitherTypeOfSystem }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .neitherTypeOfSystem }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .maximalSystem }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .neitherTypeOfSystem }
  , { walsCode := "car", language := "Carib", iso := "car", value := .neitherTypeOfSystem }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .neitherTypeOfSystem }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .neitherTypeOfSystem }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .neitherTypeOfSystem }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .bothTypesOfSystem }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .neitherTypeOfSystem }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .neitherTypeOfSystem }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .minimalSystem }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .neitherTypeOfSystem }
  , { walsCode := "coi", language := "Chortí", iso := "caa", value := .neitherTypeOfSystem }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .neitherTypeOfSystem }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .maximalSystem }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .neitherTypeOfSystem }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .neitherTypeOfSystem }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .minimalSystem }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .neitherTypeOfSystem }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .maximalSystem }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .neitherTypeOfSystem }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .neitherTypeOfSystem }
  , { walsCode := "dbd", language := "Dabida", iso := "dav", value := .maximalSystem }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .maximalSystem }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .maximalSystem }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .neitherTypeOfSystem }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .neitherTypeOfSystem }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .neitherTypeOfSystem }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .maximalSystem }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .neitherTypeOfSystem }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .neitherTypeOfSystem }
  , { walsCode := "dyu", language := "Dyula", iso := "dyu", value := .minimalSystem }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .neitherTypeOfSystem }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .neitherTypeOfSystem }
  , { walsCode := "eng", language := "English", iso := "eng", value := .neitherTypeOfSystem }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .neitherTypeOfSystem }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .neitherTypeOfSystem }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .maximalSystem }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .maximalSystem }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .maximalSystem }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .neitherTypeOfSystem }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .neitherTypeOfSystem }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .bothTypesOfSystem }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .maximalSystem }
  , { walsCode := "fre", language := "French", iso := "fra", value := .neitherTypeOfSystem }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .maximalSystem }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .neitherTypeOfSystem }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .neitherTypeOfSystem }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .maximalSystem }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .neitherTypeOfSystem }
  , { walsCode := "gbk", language := "Gbaya (Northwest)", iso := "gya", value := .maximalSystem }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .neitherTypeOfSystem }
  , { walsCode := "ger", language := "German", iso := "deu", value := .neitherTypeOfSystem }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .maximalSystem }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .minimalSystem }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .maximalSystem }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .neitherTypeOfSystem }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .maximalSystem }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .neitherTypeOfSystem }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .maximalSystem }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .minimalSystem }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .neitherTypeOfSystem }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .neitherTypeOfSystem }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .maximalSystem }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .bothTypesOfSystem }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .maximalSystem }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .neitherTypeOfSystem }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .maximalSystem }
  , { walsCode := "her", language := "Herero", iso := "her", value := .maximalSystem }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .neitherTypeOfSystem }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .maximalSystem }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .neitherTypeOfSystem }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .neitherTypeOfSystem }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .neitherTypeOfSystem }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .maximalSystem }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .maximalSystem }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .neitherTypeOfSystem }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .neitherTypeOfSystem }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .minimalSystem }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .neitherTypeOfSystem }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .minimalSystem }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .neitherTypeOfSystem }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .neitherTypeOfSystem }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .neitherTypeOfSystem }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .maximalSystem }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .minimalSystem }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .maximalSystem }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .maximalSystem }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .neitherTypeOfSystem }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .maximalSystem }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .neitherTypeOfSystem }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .maximalSystem }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .neitherTypeOfSystem }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .maximalSystem }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .maximalSystem }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .neitherTypeOfSystem }
  , { walsCode := "kgm", language := "Kagoma", iso := "kdm", value := .neitherTypeOfSystem }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .maximalSystem }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .maximalSystem }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .neitherTypeOfSystem }
  , { walsCode := "krt", language := "Karata", iso := "kpt", value := .neitherTypeOfSystem }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .maximalSystem }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .neitherTypeOfSystem }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .maximalSystem }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .neitherTypeOfSystem }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .bothTypesOfSystem }
  , { walsCode := "krq", language := "Kerek", iso := "krk", value := .maximalSystem }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .neitherTypeOfSystem }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .maximalSystem }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .neitherTypeOfSystem }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .maximalSystem }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .neitherTypeOfSystem }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .maximalSystem }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .maximalSystem }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .maximalSystem }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .neitherTypeOfSystem }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .neitherTypeOfSystem }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .neitherTypeOfSystem }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .maximalSystem }
  , { walsCode := "kow", language := "Ko (Winye)", iso := "kst", value := .minimalSystem }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .maximalSystem }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .maximalSystem }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .neitherTypeOfSystem }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .maximalSystem }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .neitherTypeOfSystem }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .maximalSystem }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .neitherTypeOfSystem }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .bothTypesOfSystem }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .bothTypesOfSystem }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .bothTypesOfSystem }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .maximalSystem }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .maximalSystem }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .maximalSystem }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .neitherTypeOfSystem }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .neitherTypeOfSystem }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .neitherTypeOfSystem }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .minimalSystem }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .neitherTypeOfSystem }
  , { walsCode := "lno", language := "Ladino", iso := "lad", value := .neitherTypeOfSystem }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .maximalSystem }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .neitherTypeOfSystem }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .neitherTypeOfSystem }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .neitherTypeOfSystem }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .neitherTypeOfSystem }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .neitherTypeOfSystem }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .maximalSystem }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .neitherTypeOfSystem }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .neitherTypeOfSystem }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .bothTypesOfSystem }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .neitherTypeOfSystem }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .maximalSystem }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .maximalSystem }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .maximalSystem }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .neitherTypeOfSystem }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .maximalSystem }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .neitherTypeOfSystem }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .neitherTypeOfSystem }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .maximalSystem }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .neitherTypeOfSystem }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .maximalSystem }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .neitherTypeOfSystem }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .maximalSystem }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .neitherTypeOfSystem }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .neitherTypeOfSystem }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .neitherTypeOfSystem }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .maximalSystem }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .neitherTypeOfSystem }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .maximalSystem }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .neitherTypeOfSystem }
  , { walsCode := "mkn", language := "Mankanya", iso := "knf", value := .neitherTypeOfSystem }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .minimalSystem }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .maximalSystem }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .neitherTypeOfSystem }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .neitherTypeOfSystem }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .maximalSystem }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .maximalSystem }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .neitherTypeOfSystem }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .neitherTypeOfSystem }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .neitherTypeOfSystem }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .neitherTypeOfSystem }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .neitherTypeOfSystem }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .neitherTypeOfSystem }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .maximalSystem }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .bothTypesOfSystem }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .neitherTypeOfSystem }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .neitherTypeOfSystem }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .maximalSystem }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .neitherTypeOfSystem }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .neitherTypeOfSystem }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .maximalSystem }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .neitherTypeOfSystem }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .maximalSystem }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .bothTypesOfSystem }
  , { walsCode := "mop", language := "Mopan", iso := "mop", value := .neitherTypeOfSystem }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .neitherTypeOfSystem }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .neitherTypeOfSystem }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .bothTypesOfSystem }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .neitherTypeOfSystem }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .neitherTypeOfSystem }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .neitherTypeOfSystem }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .maximalSystem }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .bothTypesOfSystem }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .maximalSystem }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .maximalSystem }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .maximalSystem }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .neitherTypeOfSystem }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .maximalSystem }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .maximalSystem }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .maximalSystem }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .neitherTypeOfSystem }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .maximalSystem }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .maximalSystem }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .maximalSystem }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .neitherTypeOfSystem }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .maximalSystem }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .bothTypesOfSystem }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .maximalSystem }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .neitherTypeOfSystem }
  , { walsCode := "nub", language := "Nubi", iso := "kcn", value := .maximalSystem }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .neitherTypeOfSystem }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .neitherTypeOfSystem }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .maximalSystem }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .bothTypesOfSystem }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .neitherTypeOfSystem }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .maximalSystem }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .neitherTypeOfSystem }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .neitherTypeOfSystem }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .maximalSystem }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .neitherTypeOfSystem }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .neitherTypeOfSystem }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .neitherTypeOfSystem }
  , { walsCode := "pta", language := "Paita", iso := "duf", value := .neitherTypeOfSystem }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .neitherTypeOfSystem }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .maximalSystem }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .maximalSystem }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .maximalSystem }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .neitherTypeOfSystem }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .neitherTypeOfSystem }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .minimalSystem }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .neitherTypeOfSystem }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .maximalSystem }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .neitherTypeOfSystem }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .neitherTypeOfSystem }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .neitherTypeOfSystem }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .neitherTypeOfSystem }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .neitherTypeOfSystem }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .neitherTypeOfSystem }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .neitherTypeOfSystem }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .minimalSystem }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .maximalSystem }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .maximalSystem }
  , { walsCode := "rav", language := "Romani (Ajia Varvara)", iso := "rmn", value := .maximalSystem }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .maximalSystem }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .neitherTypeOfSystem }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .maximalSystem }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .neitherTypeOfSystem }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .bothTypesOfSystem }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .neitherTypeOfSystem }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .neitherTypeOfSystem }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .neitherTypeOfSystem }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .maximalSystem }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .neitherTypeOfSystem }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .neitherTypeOfSystem }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .neitherTypeOfSystem }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .maximalSystem }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .neitherTypeOfSystem }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .neitherTypeOfSystem }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .maximalSystem }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .neitherTypeOfSystem }
  , { walsCode := "so", language := "So", iso := "teu", value := .neitherTypeOfSystem }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .minimalSystem }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .neitherTypeOfSystem }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .neitherTypeOfSystem }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .neitherTypeOfSystem }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .neitherTypeOfSystem }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .neitherTypeOfSystem }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .minimalSystem }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .bothTypesOfSystem }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .maximalSystem }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .neitherTypeOfSystem }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .neitherTypeOfSystem }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .minimalSystem }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .maximalSystem }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .maximalSystem }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .maximalSystem }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .bothTypesOfSystem }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .neitherTypeOfSystem }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .neitherTypeOfSystem }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .neitherTypeOfSystem }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .neitherTypeOfSystem }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .neitherTypeOfSystem }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .neitherTypeOfSystem }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .neitherTypeOfSystem }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .maximalSystem }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .maximalSystem }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .neitherTypeOfSystem }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .neitherTypeOfSystem }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .maximalSystem }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .neitherTypeOfSystem }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .maximalSystem }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .maximalSystem }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .maximalSystem }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .maximalSystem }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .neitherTypeOfSystem }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .neitherTypeOfSystem }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .neitherTypeOfSystem }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .neitherTypeOfSystem }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .maximalSystem }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .minimalSystem }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .minimalSystem }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .neitherTypeOfSystem }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .maximalSystem }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .maximalSystem }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .neitherTypeOfSystem }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .neitherTypeOfSystem }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .neitherTypeOfSystem }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .neitherTypeOfSystem }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .maximalSystem }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .neitherTypeOfSystem }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .maximalSystem }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .neitherTypeOfSystem }
  , { walsCode := "ykm", language := "Yakoma", iso := "yky", value := .bothTypesOfSystem }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .neitherTypeOfSystem }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .maximalSystem }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .maximalSystem }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .maximalSystem }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .maximalSystem }
  , { walsCode := "ysi", language := "Yupik (Sirenik)", iso := "ysr", value := .maximalSystem }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .neitherTypeOfSystem }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .neitherTypeOfSystem }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .maximalSystem }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .maximalSystem }
  ]

-- Count verification
theorem total_count : allData.length = 375 := by native_decide

theorem count_maximalSystem :
    (allData.filter (·.value == .maximalSystem)).length = 133 := by native_decide
theorem count_minimalSystem :
    (allData.filter (·.value == .minimalSystem)).length = 20 := by native_decide
theorem count_bothTypesOfSystem :
    (allData.filter (·.value == .bothTypesOfSystem)).length = 21 := by native_decide
theorem count_neitherTypeOfSystem :
    (allData.filter (·.value == .neitherTypeOfSystem)).length = 201 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F72A
