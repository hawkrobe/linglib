/-!
# WALS Feature 16A: Weight Factors in Weight-Sensitive Stress Systems
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 16A`.

Chapter 16, 500 languages.
-/

namespace Core.WALS.F16A

/-- WALS 16A values. -/
inductive WeightFactorsInWeightSensitiveStressSystems where
  | noWeight  -- No weight (261 languages)
  | longVowel  -- Long vowel (65 languages)
  | codaConsonant  -- Coda consonant (18 languages)
  | longVowelOrCodaConsonant  -- Long vowel or coda consonant (35 languages)
  | prominence  -- Prominence (41 languages)
  | lexicalStress  -- Lexical stress (38 languages)
  | combined  -- Combined (42 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 16A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : WeightFactorsInWeightSensitiveStressSystems
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 16A dataset (500 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .lexicalStress }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .prominence }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .noWeight }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .longVowel }
  , { walsCode := "akl", language := "Aklanon", iso := "akl", value := .codaConsonant }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .prominence }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noWeight }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noWeight }
  , { walsCode := "atq", language := "Alutiiq", iso := "ems", value := .combined }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .noWeight }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .codaConsonant }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .noWeight }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .longVowel }
  , { walsCode := "ahs", language := "Arabic (Bani-Hassan)", iso := "mey", value := .combined }
  , { walsCode := "abe", language := "Arabic (Beirut)", iso := "apc", value := .longVowelOrCodaConsonant }
  , { walsCode := "ael", language := "Arabic (Eastern Libyan)", iso := "ayl", value := .combined }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .combined }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .longVowel }
  , { walsCode := "arh", language := "Arabic (Hijazi)", iso := "acw", value := .longVowelOrCodaConsonant }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .longVowelOrCodaConsonant }
  , { walsCode := "arv", language := "Arabic (Negev)", iso := "ajp", value := .combined }
  , { walsCode := "apa", language := "Arabic (Palestinian)", iso := "ajp", value := .combined }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .longVowelOrCodaConsonant }
  , { walsCode := "atb", language := "Aralle-Tabulahan", iso := "atq", value := .noWeight }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noWeight }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noWeight }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .prominence }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .prominence }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .noWeight }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .noWeight }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .lexicalStress }
  , { walsCode := "au", language := "Au", iso := "avt", value := .prominence }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .combined }
  , { walsCode := "awd", language := "Awadhi", iso := "awa", value := .longVowelOrCodaConsonant }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noWeight }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noWeight }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .noWeight }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noWeight }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .combined }
  , { walsCode := "blk", language := "Balantak", iso := "blz", value := .noWeight }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .noWeight }
  , { walsCode := "bbm", language := "Bambam", iso := "ptu", value := .noWeight }
  , { walsCode := "bna", language := "Banawá", iso := "jaa", value := .noWeight }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .longVowel }
  , { walsCode := "bgg", language := "Banggai", iso := "bgz", value := .longVowel }
  , { walsCode := "bnl", language := "Banggarla", iso := "bjb", value := .noWeight }
  , { walsCode := "bnt", language := "Bantik", iso := "bnq", value := .noWeight }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noWeight }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noWeight }
  , { walsCode := "bqi", language := "Basque (Basaburua and Imoz)", iso := "eus", value := .lexicalStress }
  , { walsCode := "bqb", language := "Basque (Bidasoa Valley)", iso := "eus", value := .noWeight }
  , { walsCode := "bqg", language := "Basque (Gernica)", iso := "eus", value := .lexicalStress }
  , { walsCode := "bqh", language := "Basque (Hondarribia)", iso := "eus", value := .codaConsonant }
  , { walsCode := "bql", language := "Basque (Lekeitio)", iso := "eus", value := .noWeight }
  , { walsCode := "bqn", language := "Basque (Northern High Navarrese)", iso := "eus", value := .noWeight }
  , { walsCode := "bqo", language := "Basque (Oñati)", iso := "eus", value := .noWeight }
  , { walsCode := "bqr", language := "Basque (Roncalese)", iso := "eus", value := .noWeight }
  , { walsCode := "bqs", language := "Basque (Sakana)", iso := "eus", value := .noWeight }
  , { walsCode := "bso", language := "Basque (Souletin)", iso := "eus", value := .lexicalStress }
  , { walsCode := "bqz", language := "Basque (Zeberio)", iso := "eus", value := .lexicalStress }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .combined }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noWeight }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noWeight }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noWeight }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noWeight }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noWeight }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .combined }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noWeight }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .lexicalStress }
  , { walsCode := "bim", language := "Bima", iso := "bhp", value := .noWeight }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noWeight }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noWeight }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .noWeight }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .longVowel }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noWeight }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .noWeight }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .lexicalStress }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .combined }
  , { walsCode := "cpa", language := "Campa Pajonal Asheninca", iso := "cjo", value := .noWeight }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noWeight }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .combined }
  , { walsCode := "car", language := "Carib", iso := "car", value := .longVowelOrCodaConsonant }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .lexicalStress }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noWeight }
  , { walsCode := "cyg", language := "Cayuga", iso := "cay", value := .combined }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noWeight }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .longVowelOrCodaConsonant }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .codaConsonant }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .noWeight }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noWeight }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noWeight }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .longVowelOrCodaConsonant }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noWeight }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .prominence }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noWeight }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noWeight }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .noWeight }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noWeight }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .combined }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .prominence }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .noWeight }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noWeight }
  , { walsCode := "daa", language := "Da'a", iso := "kzf", value := .noWeight }
  , { walsCode := "dak", language := "Dakota", iso := "dak", value := .noWeight }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noWeight }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .longVowelOrCodaConsonant }
  , { walsCode := "dri", language := "Dari", iso := "prs", value := .noWeight }
  , { walsCode := "des", language := "Desano", iso := "des", value := .lexicalStress }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .longVowel }
  , { walsCode := "dhu", language := "Dhurga", iso := "dhu", value := .longVowel }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .combined }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noWeight }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noWeight }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .longVowel }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noWeight }
  , { walsCode := "dob", language := "Dobel", iso := "kvo", value := .lexicalStress }
  , { walsCode := "dou", language := "Doutai", iso := "tds", value := .noWeight }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noWeight }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .codaConsonant }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noWeight }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .lexicalStress }
  , { walsCode := "emc", language := "Embera Chami", iso := "cmi", value := .combined }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .noWeight }
  , { walsCode := "eng", language := "English", iso := "eng", value := .longVowelOrCodaConsonant }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .longVowel }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .noWeight }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .longVowel }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .longVowel }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .noWeight }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .longVowel }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noWeight }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .noWeight }
  , { walsCode := "for", language := "Fore", iso := "for", value := .prominence }
  , { walsCode := "fre", language := "French", iso := "fra", value := .prominence }
  , { walsCode := "glp", language := "Gaalpu", iso := "dhg", value := .noWeight }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noWeight }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .noWeight }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noWeight }
  , { walsCode := "gay", language := "Gayo", iso := "gay", value := .prominence }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noWeight }
  , { walsCode := "ger", language := "German", iso := "deu", value := .codaConsonant }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .longVowel }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .prominence }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .longVowelOrCodaConsonant }
  , { walsCode := "gor", language := "Gorowa", iso := "gow", value := .longVowelOrCodaConsonant }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .lexicalStress }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .lexicalStress }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .longVowelOrCodaConsonant }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noWeight }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .noWeight }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .prominence }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noWeight }
  , { walsCode := "hno", language := "Haida (Northern)", iso := "hdn", value := .prominence }
  , { walsCode := "hln", language := "Halang", iso := "hal", value := .noWeight }
  , { walsCode := "hnn", language := "Hanunóo", iso := "hnn", value := .lexicalStress }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .longVowel }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noWeight }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .longVowelOrCodaConsonant }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .longVowelOrCodaConsonant }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .longVowelOrCodaConsonant }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .longVowel }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .noWeight }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .longVowel }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .longVowel }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noWeight }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noWeight }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noWeight }
  , { walsCode := "iga", language := "Inga", iso := "inb", value := .combined }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noWeight }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .combined }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noWeight }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .longVowel }
  , { walsCode := "irm", language := "Irish (Munster)", iso := "gle", value := .longVowel }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .lexicalStress }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noWeight }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noWeight }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .prominence }
  , { walsCode := "jum", language := "Júma", iso := "jua", value := .noWeight }
  , { walsCode := "kli", language := "Kaili", iso := "lew", value := .noWeight }
  , { walsCode := "kaw", language := "Kaiwá", iso := "kgk", value := .noWeight }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .noWeight }
  , { walsCode := "klp", language := "Kalapuya", iso := "kyl", value := .noWeight }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noWeight }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noWeight }
  , { walsCode := "kra", language := "Kara (in Papua New Guinea)", iso := "leu", value := .combined }
  , { walsCode := "krl", language := "Karelian", iso := "krl", value := .longVowelOrCodaConsonant }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .longVowel }
  , { walsCode := "ksh", language := "Kashaya", iso := "kju", value := .longVowelOrCodaConsonant }
  , { walsCode := "kaj", language := "Kaure", iso := "bpp", value := .prominence }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .longVowel }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .combined }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .noWeight }
  , { walsCode := "kap", language := "Kela (Apoze)", iso := "kcl", value := .noWeight }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .combined }
  , { walsCode := "ktn", language := "Ketengban", iso := "xte", value := .lexicalStress }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .lexicalStress }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .longVowel }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noWeight }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .prominence }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noWeight }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .longVowelOrCodaConsonant }
  , { walsCode := "ksr", language := "Kisar", iso := "kje", value := .noWeight }
  , { walsCode := "kit", language := "Kitsai", iso := "kii", value := .noWeight }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .longVowelOrCodaConsonant }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .longVowel }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noWeight }
  , { walsCode := "koo", language := "Kola", iso := "kvv", value := .lexicalStress }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .longVowel }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noWeight }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .noWeight }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noWeight }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .longVowelOrCodaConsonant }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .prominence }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noWeight }
  , { walsCode := "kuz", language := "Kulamanen", iso := "mbt", value := .prominence }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .lexicalStress }
  , { walsCode := "kjn", language := "Kunjen", iso := "kjn", value := .noWeight }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .lexicalStress }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .longVowel }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noWeight }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .combined }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .prominence }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noWeight }
  , { walsCode := "lla", language := "Lamu-Lamu", iso := "lby", value := .noWeight }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noWeight }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .longVowel }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .noWeight }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noWeight }
  , { walsCode := "lje", language := "Lauje", iso := "law", value := .noWeight }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noWeight }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noWeight }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .longVowel }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .codaConsonant }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .lexicalStress }
  , { walsCode := "liv", language := "Liv", iso := "liv", value := .noWeight }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noWeight }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .longVowel }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noWeight }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .noWeight }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .noWeight }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .longVowelOrCodaConsonant }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .prominence }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .noWeight }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .codaConsonant }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .longVowel }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .longVowel }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .longVowel }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .noWeight }
  , { walsCode := "mlc", language := "Malacca Creole", iso := "mcm", value := .codaConsonant }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noWeight }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .prominence }
  , { walsCode := "mly", language := "Malay", iso := "zsm", value := .combined }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .longVowel }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .combined }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .combined }
  , { walsCode := "mms", language := "Mamasa", iso := "mqj", value := .noWeight }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .codaConsonant }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .lexicalStress }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noWeight }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .prominence }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noWeight }
  , { walsCode := "mnj", language := "Mantjiltjara", iso := "mpj", value := .noWeight }
  , { walsCode := "mnx", language := "Manx", iso := "glv", value := .noWeight }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .longVowel }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noWeight }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noWeight }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noWeight }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .longVowel }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .longVowel }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noWeight }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noWeight }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .longVowel }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noWeight }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noWeight }
  , { walsCode := "myy", language := "Mayi-Yapi", iso := "xyj", value := .noWeight }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .noWeight }
  , { walsCode := "meb", language := "Melayu Betawi", iso := "bew", value := .prominence }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .longVowel }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .noWeight }
  , { walsCode := "mta", language := "Mentuh Tapuh", iso := "sdo", value := .noWeight }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noWeight }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noWeight }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noWeight }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .longVowelOrCodaConsonant }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .longVowelOrCodaConsonant }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .longVowelOrCodaConsonant }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noWeight }
  , { walsCode := "mgd", language := "Mongondow", iso := "mog", value := .longVowelOrCodaConsonant }
  , { walsCode := "mmo", language := "Mordvin (Moksha)", iso := "mdf", value := .prominence }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noWeight }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .codaConsonant }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .combined }
  , { walsCode := "mrk", language := "Murik", iso := "mtf", value := .longVowel }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .longVowel }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .longVowel }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noWeight }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .noWeight }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noWeight }
  , { walsCode := "npu", language := "Napu", iso := "npy", value := .noWeight }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .longVowelOrCodaConsonant }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .codaConsonant }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .noWeight }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .noWeight }
  , { walsCode := "nsy", language := "Neo-Aramaic (Assyrian)", iso := "aii", value := .noWeight }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .longVowel }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .lexicalStress }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .prominence }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noWeight }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .noWeight }
  , { walsCode := "ngr", language := "Ngarinyeri", iso := "nay", value := .noWeight }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .longVowel }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .noWeight }
  , { walsCode := "nin", language := "Ningil", iso := "niz", value := .noWeight }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noWeight }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .longVowelOrCodaConsonant }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noWeight }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .longVowelOrCodaConsonant }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noWeight }
  , { walsCode := "nbo", language := "Nyambo", iso := "now", value := .noWeight }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .combined }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .noWeight }
  , { walsCode := "obk", language := "Obokuitai", iso := "afz", value := .prominence }
  , { walsCode := "occ", language := "Occitan", iso := "oci", value := .combined }
  , { walsCode := "olm", language := "Oloh Mangtangai", iso := "nij", value := .noWeight }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noWeight }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .noWeight }
  , { walsCode := "orc", language := "Oroch", iso := "oac", value := .noWeight }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .longVowel }
  , { walsCode := "oto", language := "Oto", iso := "iow", value := .longVowel }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noWeight }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noWeight }
  , { walsCode := "pad", language := "Padoe", iso := "pdo", value := .noWeight }
  , { walsCode := "pag", language := "Pagu", iso := "pgu", value := .noWeight }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .noWeight }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noWeight }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .noWeight }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noWeight }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .combined }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .noWeight }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noWeight }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noWeight }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .noWeight }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .combined }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .noWeight }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noWeight }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noWeight }
  , { walsCode := "pkm", language := "Pokomchí", iso := "poh", value := .noWeight }
  , { walsCode := "plb", language := "Polabian", iso := "pox", value := .longVowel }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noWeight }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noWeight }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .lexicalStress }
  , { walsCode := "plp", language := "Pulopetak", iso := "nij", value := .noWeight }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .prominence }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .lexicalStress }
  , { walsCode := "que", language := "Quechan", iso := "yum", value := .noWeight }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .noWeight }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noWeight }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .noWeight }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .longVowelOrCodaConsonant }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noWeight }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .noWeight }
  , { walsCode := "rnr", language := "Romani (North Russian)", iso := "rml", value := .noWeight }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .lexicalStress }
  , { walsCode := "rsm", language := "Romansch (Surmeiran)", iso := "roh", value := .combined }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .longVowel }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .noWeight }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .longVowel }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .lexicalStress }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .noWeight }
  , { walsCode := "sao", language := "Saho", iso := "ssy", value := .lexicalStress }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noWeight }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .prominence }
  , { walsCode := "sps", language := "Salish (Southern Puget Sound)", iso := "slh", value := .lexicalStress }
  , { walsCode := "sbg", language := "Sama (Balangingi)", iso := "sse", value := .noWeight }
  , { walsCode := "sgr", language := "Sangir", iso := "sxn", value := .noWeight }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noWeight }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .noWeight }
  , { walsCode := "swi", language := "Sawai", iso := "szw", value := .prominence }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noWeight }
  , { walsCode := "sru", language := "Selaru", iso := "slu", value := .codaConsonant }
  , { walsCode := "sly", language := "Selayar", iso := "sly", value := .noWeight }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noWeight }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .longVowel }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noWeight }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .prominence }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .codaConsonant }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .prominence }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .longVowel }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .codaConsonant }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .prominence }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .prominence }
  , { walsCode := "skl", language := "Sikule", iso := "skh", value := .noWeight }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .noWeight }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .longVowel }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noWeight }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .lexicalStress }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .noWeight }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .prominence }
  , { walsCode := "svc", language := "Slovincian", iso := "csb", value := .combined }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .noWeight }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .longVowel }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .combined }
  , { walsCode := "spo", language := "Spokane", iso := "spo", value := .lexicalStress }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .prominence }
  , { walsCode := "sto", language := "Stoney", iso := "sto", value := .codaConsonant }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .prominence }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noWeight }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noWeight }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .longVowelOrCodaConsonant }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noWeight }
  , { walsCode := "tbr", language := "Tabaru", iso := "tby", value := .noWeight }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .prominence }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noWeight }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .lexicalStress }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .longVowel }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .noWeight }
  , { walsCode := "tld", language := "Talaud", iso := "tld", value := .noWeight }
  , { walsCode := "tns", language := "Tanna (Southwest)", iso := "nwi", value := .longVowelOrCodaConsonant }
  , { walsCode := "tgw", language := "Tarangan (West)", iso := "txn", value := .codaConsonant }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noWeight }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noWeight }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .noWeight }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .longVowelOrCodaConsonant }
  , { walsCode := "thp", language := "Thaypan", iso := "typ", value := .noWeight }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .longVowel }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noWeight }
  , { walsCode := "tse", language := "Timorese", iso := "aoz", value := .noWeight }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noWeight }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .noWeight }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noWeight }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .longVowel }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .codaConsonant }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noWeight }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .combined }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .longVowel }
  , { walsCode := "tnt", language := "Tontemboan", iso := "tnt", value := .combined }
  , { walsCode := "trd", language := "Toraja", iso := "sda", value := .noWeight }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .noWeight }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noWeight }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .prominence }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noWeight }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .noWeight }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noWeight }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noWeight }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .lexicalStress }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .noWeight }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .longVowel }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .longVowel }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noWeight }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .noWeight }
  , { walsCode := "unm", language := "Unami", iso := "unm", value := .combined }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .longVowel }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noWeight }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noWeight }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .lexicalStress }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .noWeight }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .noWeight }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .noWeight }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .noWeight }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .longVowel }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noWeight }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .noWeight }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noWeight }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noWeight }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noWeight }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noWeight }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noWeight }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .combined }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noWeight }
  , { walsCode := "wer", language := "Weri", iso := "wer", value := .noWeight }
  , { walsCode := "wet", language := "Wetan", iso := "lex", value := .noWeight }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .prominence }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noWeight }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .noWeight }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .lexicalStress }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .lexicalStress }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .longVowel }
  , { walsCode := "ymd", language := "Yamdena", iso := "jmd", value := .noWeight }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .longVowelOrCodaConsonant }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .noWeight }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .combined }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .combined }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noWeight }
  , { walsCode := "yzv", language := "Yazva", iso := "kpv", value := .prominence }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noWeight }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .longVowel }
  , { walsCode := "yil", language := "Yil", iso := "yll", value := .prominence }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noWeight }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .longVowel }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .noWeight }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .lexicalStress }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .longVowelOrCodaConsonant }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .combined }
  , { walsCode := "ych", language := "Yup'ik (Chevak)", iso := "esu", value := .combined }
  , { walsCode := "yun", language := "Yup'ik (Norton Sound)", iso := "esu", value := .combined }
  , { walsCode := "ysl", language := "Yupik (St. Lawrence Island)", iso := "ess", value := .longVowel }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .longVowel }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noWeight }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noWeight }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noWeight }
  ]

-- Count verification
theorem total_count : allData.length = 500 := by native_decide

theorem count_noWeight :
    (allData.filter (·.value == .noWeight)).length = 261 := by native_decide
theorem count_longVowel :
    (allData.filter (·.value == .longVowel)).length = 65 := by native_decide
theorem count_codaConsonant :
    (allData.filter (·.value == .codaConsonant)).length = 18 := by native_decide
theorem count_longVowelOrCodaConsonant :
    (allData.filter (·.value == .longVowelOrCodaConsonant)).length = 35 := by native_decide
theorem count_prominence :
    (allData.filter (·.value == .prominence)).length = 41 := by native_decide
theorem count_lexicalStress :
    (allData.filter (·.value == .lexicalStress)).length = 38 := by native_decide
theorem count_combined :
    (allData.filter (·.value == .combined)).length = 42 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F16A
