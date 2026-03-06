/-!
# WALS Feature 53A: Ordinal Numerals
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 53A`.

Chapter 53, 321 languages.
-/

namespace Core.WALS.F53A

/-- WALS 53A values. -/
inductive OrdinalNumerals where
  | none  -- None (33 languages)
  | oneTwoThree  -- One, two, three (3 languages)
  | firstTwoThree  -- First, two, three (12 languages)
  | oneThTwoThThreeTh  -- One-th, two-th, three-th (41 languages)
  | firstOneThTwoThThreeTh  -- First/one-th, two-th, three-th (54 languages)
  | firstTwoThThreeTh  -- First, two-th, three-th (110 languages)
  | firstSecondThreeTh  -- First, second, three-th (61 languages)
  | various  -- Various (7 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 53A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : OrdinalNumerals
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 53A dataset (321 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .none }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .firstOneThTwoThThreeTh }
  , { walsCode := "aci", language := "Achí", iso := "acr", value := .firstTwoThThreeTh }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .firstOneThTwoThThreeTh }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .firstTwoThThreeTh }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .none }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .firstTwoThThreeTh }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .firstTwoThThreeTh }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .firstTwoThThreeTh }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ago", language := "Angolar", iso := "aoa", value := .firstTwoThree }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .none }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .firstTwoThThreeTh }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .firstTwoThThreeTh }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .firstSecondThreeTh }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .none }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .firstTwoThThreeTh }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .firstTwoThThreeTh }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .oneThTwoThThreeTh }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .none }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .none }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .firstTwoThree }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .firstOneThTwoThThreeTh }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .firstTwoThThreeTh }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .firstTwoThThreeTh }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .firstTwoThThreeTh }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .none }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .oneThTwoThThreeTh }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .firstTwoThThreeTh }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .firstSecondThreeTh }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .firstTwoThThreeTh }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .firstTwoThThreeTh }
  , { walsCode := "bsm", language := "Bislama", iso := "bis", value := .firstOneThTwoThThreeTh }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .firstTwoThThreeTh }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .firstOneThTwoThThreeTh }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .firstSecondThreeTh }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .firstTwoThree }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .firstSecondThreeTh }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .various }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .firstTwoThThreeTh }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .firstOneThTwoThThreeTh }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .firstTwoThThreeTh }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .none }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .oneThTwoThThreeTh }
  , { walsCode := "car", language := "Carib", iso := "car", value := .oneThTwoThThreeTh }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .firstSecondThreeTh }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .firstTwoThThreeTh }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .firstTwoThThreeTh }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .none }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .firstSecondThreeTh }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .firstTwoThThreeTh }
  , { walsCode := "col", language := "Chol", iso := "ctu", value := .firstTwoThThreeTh }
  , { walsCode := "coi", language := "Chortí", iso := "caa", value := .firstSecondThreeTh }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .firstOneThTwoThThreeTh }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .oneThTwoThThreeTh }
  , { walsCode := "cog", language := "Cogui", iso := "kog", value := .various }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .firstTwoThThreeTh }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .oneThTwoThThreeTh }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .firstSecondThreeTh }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .oneThTwoThThreeTh }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .firstSecondThreeTh }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .firstTwoThThreeTh }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .firstTwoThThreeTh }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .firstTwoThThreeTh }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .none }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .firstTwoThThreeTh }
  , { walsCode := "eng", language := "English", iso := "eng", value := .firstSecondThreeTh }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .firstSecondThreeTh }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .firstOneThTwoThThreeTh }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .firstSecondThreeTh }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .firstTwoThThreeTh }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .firstTwoThThreeTh }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .firstSecondThreeTh }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .firstTwoThThreeTh }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .firstSecondThreeTh }
  , { walsCode := "fre", language := "French", iso := "fra", value := .firstSecondThreeTh }
  , { walsCode := "fea", language := "Frisian (Eastern)", iso := "frs", value := .firstTwoThThreeTh }
  , { walsCode := "fno", language := "Frisian (North)", iso := "frr", value := .firstSecondThreeTh }
  , { walsCode := "frw", language := "Frisian (Western)", iso := "fry", value := .firstTwoThThreeTh }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .firstTwoThThreeTh }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .firstTwoThThreeTh }
  , { walsCode := "glc", language := "Galician", iso := "glg", value := .firstSecondThreeTh }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .firstOneThTwoThThreeTh }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .firstTwoThThreeTh }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .firstTwoThThreeTh }
  , { walsCode := "ger", language := "German", iso := "deu", value := .firstTwoThThreeTh }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .firstTwoThree }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .firstTwoThThreeTh }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .firstTwoThThreeTh }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .firstSecondThreeTh }
  , { walsCode := "gre", language := "Greenlandic (East)", iso := "kal", value := .firstSecondThreeTh }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .firstSecondThreeTh }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .firstOneThTwoThThreeTh }
  , { walsCode := "gbc", language := "Guinea Bissau Crioulo", iso := "pov", value := .firstSecondThreeTh }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .firstTwoThThreeTh }
  , { walsCode := "grn", language := "Gurenne", iso := "gur", value := .firstTwoThThreeTh }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .firstTwoThThreeTh }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .firstTwoThThreeTh }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .firstOneThTwoThThreeTh }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .firstTwoThThreeTh }
  , { walsCode := "her", language := "Herero", iso := "her", value := .firstTwoThThreeTh }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .firstTwoThThreeTh }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .none }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .oneThTwoThThreeTh }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .firstSecondThreeTh }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .oneThTwoThThreeTh }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .firstSecondThreeTh }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .firstTwoThThreeTh }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .none }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .none }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .firstTwoThThreeTh }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .firstTwoThree }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .firstSecondThreeTh }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .firstSecondThreeTh }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .firstSecondThreeTh }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .firstTwoThThreeTh }
  , { walsCode := "izh", language := "Izhor", iso := "izh", value := .firstSecondThreeTh }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .firstOneThTwoThThreeTh }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .oneThTwoThThreeTh }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .firstTwoThThreeTh }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .oneThTwoThThreeTh }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .firstTwoThThreeTh }
  , { walsCode := "kwe", language := "Kanjobal (Western)", iso := "knj", value := .firstTwoThThreeTh }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .firstOneThTwoThThreeTh }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .firstOneThTwoThThreeTh }
  , { walsCode := "krl", language := "Karelian", iso := "krl", value := .firstSecondThreeTh }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ksu", language := "Kashubian", iso := "csb", value := .firstSecondThreeTh }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .oneThTwoThThreeTh }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .firstTwoThThreeTh }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .various }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .firstSecondThreeTh }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .firstTwoThThreeTh }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .oneThTwoThThreeTh }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .various }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .oneThTwoThThreeTh }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .firstTwoThThreeTh }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .firstTwoThThreeTh }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .none }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .oneThTwoThThreeTh }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .none }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .firstSecondThreeTh }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .oneThTwoThThreeTh }
  , { walsCode := "ktt", language := "Kott", iso := "", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .oneTwoThree }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .oneTwoThree }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .firstTwoThThreeTh }
  , { walsCode := "kug", language := "Kunming", iso := "cmn", value := .oneThTwoThThreeTh }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .firstTwoThThreeTh }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .firstOneThTwoThThreeTh }
  , { walsCode := "kwr", language := "Kwamera", iso := "tnk", value := .oneThTwoThThreeTh }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .firstOneThTwoThThreeTh }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ldn", language := "Ladin", iso := "lld", value := .firstSecondThreeTh }
  , { walsCode := "lno", language := "Ladino", iso := "lad", value := .firstSecondThreeTh }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .firstTwoThThreeTh }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .firstTwoThree }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .firstSecondThreeTh }
  , { walsCode := "les", language := "Lese", iso := "les", value := .firstTwoThThreeTh }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .oneThTwoThThreeTh }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .none }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .firstSecondThreeTh }
  , { walsCode := "liv", language := "Liv", iso := "liv", value := .firstSecondThreeTh }
  , { walsCode := "lge", language := "Low German", iso := "nds", value := .firstTwoThThreeTh }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .firstOneThTwoThThreeTh }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .firstTwoThThreeTh }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .firstSecondThreeTh }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mlc", language := "Malacca Creole", iso := "mcm", value := .oneThTwoThThreeTh }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .firstTwoThThreeTh }
  , { walsCode := "mly", language := "Malay", iso := "zsm", value := .firstTwoThThreeTh }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .firstTwoThThreeTh }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .firstTwoThThreeTh }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .firstTwoThThreeTh }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .oneThTwoThThreeTh }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .none }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mjk", language := "Manjaku", iso := "mfv", value := .firstTwoThThreeTh }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .oneThTwoThThreeTh }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .none }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .none }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .oneThTwoThThreeTh }
  , { walsCode := "mqc", language := "Martinique Creole", iso := "gcf", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .firstTwoThThreeTh }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .firstTwoThThreeTh }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .firstSecondThreeTh }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .firstOneThTwoThThreeTh }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .none }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .firstTwoThree }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .oneThTwoThThreeTh }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .firstTwoThThreeTh }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .firstTwoThThreeTh }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .firstTwoThThreeTh }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .firstSecondThreeTh }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .firstTwoThThreeTh }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .firstTwoThThreeTh }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .none }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .firstTwoThree }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .firstTwoThThreeTh }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .firstOneThTwoThThreeTh }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .firstSecondThreeTh }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .none }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .firstTwoThThreeTh }
  , { walsCode := "occ", language := "Occitan", iso := "oci", value := .firstSecondThreeTh }
  , { walsCode := "orb", language := "Oromo (Boraana)", iso := "gax", value := .firstTwoThThreeTh }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .firstTwoThThreeTh }
  , { walsCode := "owc", language := "Oromo (West-Central)", iso := "gaz", value := .firstOneThTwoThThreeTh }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .firstTwoThThreeTh }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .firstTwoThThreeTh }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .oneThTwoThThreeTh }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .oneThTwoThThreeTh }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .firstTwoThThreeTh }
  , { walsCode := "pap", language := "Papiamentu", iso := "pap", value := .firstTwoThThreeTh }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .firstTwoThThreeTh }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .firstTwoThThreeTh }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .oneThTwoThThreeTh }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .firstOneThTwoThThreeTh }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .various }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .firstSecondThreeTh }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .firstTwoThThreeTh }
  , { walsCode := "pcm", language := "Poqomam", iso := "poc", value := .firstTwoThThreeTh }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .firstSecondThreeTh }
  , { walsCode := "pri", language := "Príncipense", iso := "pre", value := .firstTwoThree }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .firstOneThTwoThThreeTh }
  , { walsCode := "qec", language := "Quechua (Ecuadorean)", iso := "qug", value := .firstOneThTwoThThreeTh }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .firstOneThTwoThThreeTh }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .firstTwoThThreeTh }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .firstOneThTwoThThreeTh }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .firstTwoThThreeTh }
  , { walsCode := "rmc", language := "Romansch", iso := "roh", value := .firstSecondThreeTh }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .firstSecondThreeTh }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .firstSecondThreeTh }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .firstTwoThThreeTh }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .firstTwoThree }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .oneTwoThree }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .oneThTwoThThreeTh }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .none }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .firstSecondThreeTh }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .firstTwoThThreeTh }
  , { walsCode := "sey", language := "Seychelles Creole", iso := "crs", value := .firstTwoThThreeTh }
  , { walsCode := "ssh", language := "Shinassha", iso := "bwo", value := .firstOneThTwoThThreeTh }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .firstTwoThThreeTh }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .firstTwoThThreeTh }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .firstTwoThThreeTh }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .firstSecondThreeTh }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .firstSecondThreeTh }
  , { walsCode := "so", language := "So", iso := "teu", value := .firstSecondThreeTh }
  , { walsCode := "som", language := "Somali", iso := "som", value := .oneThTwoThThreeTh }
  , { walsCode := "srl", language := "Sorbian (Lower)", iso := "dsb", value := .firstSecondThreeTh }
  , { walsCode := "sou", language := "Sorbian (Upper)", iso := "hsb", value := .firstSecondThreeTh }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .firstSecondThreeTh }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .firstSecondThreeTh }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .firstTwoThThreeTh }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .firstTwoThThreeTh }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .firstSecondThreeTh }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .firstSecondThreeTh }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .firstTwoThThreeTh }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .firstTwoThThreeTh }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .firstTwoThThreeTh }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .oneThTwoThThreeTh }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .none }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .oneThTwoThThreeTh }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .none }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .oneThTwoThThreeTh }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .firstTwoThThreeTh }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .oneThTwoThThreeTh }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .none }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .oneThTwoThThreeTh }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .firstTwoThree }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .firstTwoThThreeTh }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .firstOneThTwoThThreeTh }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .oneThTwoThThreeTh }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .oneThTwoThThreeTh }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .firstTwoThThreeTh }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .firstOneThTwoThThreeTh }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .firstSecondThreeTh }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .oneThTwoThThreeTh }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .various }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .firstSecondThreeTh }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .oneThTwoThThreeTh }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .oneThTwoThThreeTh }
  , { walsCode := "vep", language := "Veps", iso := "vep", value := .firstSecondThreeTh }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .various }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .firstSecondThreeTh }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .firstTwoThree }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .none }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .firstSecondThreeTh }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .firstTwoThThreeTh }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .firstTwoThThreeTh }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .firstTwoThThreeTh }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .oneThTwoThThreeTh }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .firstTwoThThreeTh }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .oneThTwoThThreeTh }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .firstTwoThThreeTh }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .firstOneThTwoThThreeTh }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .firstOneThTwoThThreeTh }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .firstTwoThThreeTh }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .firstTwoThThreeTh }
  ]

-- Count verification
theorem total_count : allData.length = 321 := by native_decide

theorem count_none :
    (allData.filter (·.value == .none)).length = 33 := by native_decide
theorem count_oneTwoThree :
    (allData.filter (·.value == .oneTwoThree)).length = 3 := by native_decide
theorem count_firstTwoThree :
    (allData.filter (·.value == .firstTwoThree)).length = 12 := by native_decide
theorem count_oneThTwoThThreeTh :
    (allData.filter (·.value == .oneThTwoThThreeTh)).length = 41 := by native_decide
theorem count_firstOneThTwoThThreeTh :
    (allData.filter (·.value == .firstOneThTwoThThreeTh)).length = 54 := by native_decide
theorem count_firstTwoThThreeTh :
    (allData.filter (·.value == .firstTwoThThreeTh)).length = 110 := by native_decide
theorem count_firstSecondThreeTh :
    (allData.filter (·.value == .firstSecondThreeTh)).length = 61 := by native_decide
theorem count_various :
    (allData.filter (·.value == .various)).length = 7 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F53A
