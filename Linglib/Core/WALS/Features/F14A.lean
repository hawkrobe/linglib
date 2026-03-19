/-!
# WALS Feature 14A: Fixed Stress Locations
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 14A`.

Chapter 14, 502 languages.
-/

namespace Core.WALS.F14A

/-- WALS 14A values. -/
inductive FixedStressLocations where
  | noFixedStress  -- No fixed stress (220 languages)
  | initial  -- Initial (92 languages)
  | second  -- Second (16 languages)
  | third  -- Third (1 languages)
  | antepenultimate  -- Antepenultimate (12 languages)
  | penultimate  -- Penultimate (110 languages)
  | ultimate  -- Ultimate (51 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 14A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : FixedStressLocations
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noFixedStress }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .ultimate }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .initial }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .noFixedStress }
  , { walsCode := "akl", language := "Aklanon", iso := "akl", value := .noFixedStress }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noFixedStress }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .penultimate }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .penultimate }
  , { walsCode := "atq", language := "Alutiiq", iso := "ems", value := .noFixedStress }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .second }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noFixedStress }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .initial }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noFixedStress }
  , { walsCode := "ahs", language := "Arabic (Bani-Hassan)", iso := "mey", value := .noFixedStress }
  , { walsCode := "abe", language := "Arabic (Beirut)", iso := "apc", value := .noFixedStress }
  , { walsCode := "ael", language := "Arabic (Eastern Libyan)", iso := "ayl", value := .noFixedStress }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noFixedStress }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noFixedStress }
  , { walsCode := "arh", language := "Arabic (Hijazi)", iso := "acw", value := .noFixedStress }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .noFixedStress }
  , { walsCode := "arv", language := "Arabic (Negev)", iso := "ajp", value := .noFixedStress }
  , { walsCode := "apa", language := "Arabic (Palestinian)", iso := "ajp", value := .noFixedStress }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noFixedStress }
  , { walsCode := "atb", language := "Aralle-Tabulahan", iso := "atq", value := .penultimate }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .second }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .penultimate }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noFixedStress }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noFixedStress }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .initial }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .second }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .ultimate }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noFixedStress }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .noFixedStress }
  , { walsCode := "awd", language := "Awadhi", iso := "awa", value := .noFixedStress }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .penultimate }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .penultimate }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .initial }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .ultimate }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .noFixedStress }
  , { walsCode := "blk", language := "Balantak", iso := "blz", value := .penultimate }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .ultimate }
  , { walsCode := "bbm", language := "Bambam", iso := "ptu", value := .penultimate }
  , { walsCode := "bna", language := "Banawá", iso := "jaa", value := .noFixedStress }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .noFixedStress }
  , { walsCode := "bgg", language := "Banggai", iso := "bgz", value := .noFixedStress }
  , { walsCode := "bnl", language := "Banggarla", iso := "bjb", value := .antepenultimate }
  , { walsCode := "bnt", language := "Bantik", iso := "bnq", value := .penultimate }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .penultimate }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .ultimate }
  , { walsCode := "bqi", language := "Basque (Basaburua and Imoz)", iso := "eus", value := .noFixedStress }
  , { walsCode := "bqb", language := "Basque (Bidasoa Valley)", iso := "eus", value := .second }
  , { walsCode := "bqg", language := "Basque (Gernica)", iso := "eus", value := .noFixedStress }
  , { walsCode := "bqh", language := "Basque (Hondarribia)", iso := "eus", value := .noFixedStress }
  , { walsCode := "bql", language := "Basque (Lekeitio)", iso := "eus", value := .penultimate }
  , { walsCode := "bqn", language := "Basque (Northern High Navarrese)", iso := "eus", value := .penultimate }
  , { walsCode := "bqo", language := "Basque (Oñati)", iso := "eus", value := .second }
  , { walsCode := "bqr", language := "Basque (Roncalese)", iso := "eus", value := .penultimate }
  , { walsCode := "bqs", language := "Basque (Sakana)", iso := "eus", value := .initial }
  , { walsCode := "bso", language := "Basque (Souletin)", iso := "eus", value := .noFixedStress }
  , { walsCode := "bqz", language := "Basque (Zeberio)", iso := "eus", value := .noFixedStress }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noFixedStress }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .penultimate }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .ultimate }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noFixedStress }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .initial }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .ultimate }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .noFixedStress }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .penultimate }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .noFixedStress }
  , { walsCode := "bim", language := "Bima", iso := "bhp", value := .penultimate }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .initial }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .penultimate }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .penultimate }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .noFixedStress }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .initial }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .penultimate }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noFixedStress }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .initial }
  , { walsCode := "cpa", language := "Campa Pajonal Asheninca", iso := "cjo", value := .noFixedStress }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .ultimate }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .noFixedStress }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noFixedStress }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noFixedStress }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .penultimate }
  , { walsCode := "cyg", language := "Cayuga", iso := "cay", value := .noFixedStress }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .antepenultimate }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .noFixedStress }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noFixedStress }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .ultimate }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .initial }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noFixedStress }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .noFixedStress }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .initial }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noFixedStress }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .ultimate }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .initial }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noFixedStress }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .penultimate }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .antepenultimate }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .noFixedStress }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noFixedStress }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .initial }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .initial }
  , { walsCode := "daa", language := "Da'a", iso := "kzf", value := .penultimate }
  , { walsCode := "dak", language := "Dakota", iso := "dak", value := .second }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .ultimate }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .noFixedStress }
  , { walsCode := "dri", language := "Dari", iso := "prs", value := .ultimate }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noFixedStress }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .noFixedStress }
  , { walsCode := "dhu", language := "Dhurga", iso := "dhu", value := .noFixedStress }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noFixedStress }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .initial }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .initial }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noFixedStress }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .penultimate }
  , { walsCode := "dob", language := "Dobel", iso := "kvo", value := .penultimate }
  , { walsCode := "dou", language := "Doutai", iso := "tds", value := .initial }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .initial }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noFixedStress }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .initial }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noFixedStress }
  , { walsCode := "emc", language := "Embera Chami", iso := "cmi", value := .noFixedStress }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .penultimate }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noFixedStress }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noFixedStress }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .penultimate }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .initial }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noFixedStress }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .initial }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noFixedStress }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .initial }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .penultimate }
  , { walsCode := "for", language := "Fore", iso := "for", value := .noFixedStress }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noFixedStress }
  , { walsCode := "glp", language := "Gaalpu", iso := "dhg", value := .initial }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .initial }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .penultimate }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .initial }
  , { walsCode := "gay", language := "Gayo", iso := "gay", value := .noFixedStress }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .antepenultimate }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noFixedStress }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .initial }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noFixedStress }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .initial }
  , { walsCode := "gor", language := "Gorowa", iso := "gow", value := .noFixedStress }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noFixedStress }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .antepenultimate }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .ultimate }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .ultimate }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .initial }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .noFixedStress }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .initial }
  , { walsCode := "hno", language := "Haida (Northern)", iso := "hdn", value := .noFixedStress }
  , { walsCode := "hln", language := "Halang", iso := "hal", value := .ultimate }
  , { walsCode := "hnn", language := "Hanunóo", iso := "hnn", value := .penultimate }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .penultimate }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .ultimate }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noFixedStress }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noFixedStress }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .noFixedStress }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noFixedStress }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .initial }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .initial }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noFixedStress }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .initial }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .initial }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .penultimate }
  , { walsCode := "iga", language := "Inga", iso := "inb", value := .noFixedStress }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .initial }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noFixedStress }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .ultimate }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .initial }
  , { walsCode := "irm", language := "Irish (Munster)", iso := "gle", value := .noFixedStress }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noFixedStress }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .initial }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .penultimate }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noFixedStress }
  , { walsCode := "jum", language := "Júma", iso := "jua", value := .penultimate }
  , { walsCode := "kli", language := "Kaili", iso := "lew", value := .penultimate }
  , { walsCode := "kaw", language := "Kaiwá", iso := "kgk", value := .ultimate }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .ultimate }
  , { walsCode := "klp", language := "Kalapuya", iso := "kyl", value := .initial }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .initial }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .penultimate }
  , { walsCode := "kra", language := "Kara (in Papua New Guinea)", iso := "leu", value := .noFixedStress }
  , { walsCode := "krl", language := "Karelian", iso := "krl", value := .initial }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noFixedStress }
  , { walsCode := "ksh", language := "Kashaya", iso := "kju", value := .noFixedStress }
  , { walsCode := "kaj", language := "Kaure", iso := "bpp", value := .noFixedStress }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noFixedStress }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .initial }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .ultimate }
  , { walsCode := "kap", language := "Kela (Apoze)", iso := "kcl", value := .antepenultimate }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noFixedStress }
  , { walsCode := "ktn", language := "Ketengban", iso := "xte", value := .noFixedStress }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noFixedStress }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noFixedStress }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .ultimate }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .ultimate }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .ultimate }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noFixedStress }
  , { walsCode := "ksr", language := "Kisar", iso := "kje", value := .penultimate }
  , { walsCode := "kit", language := "Kitsai", iso := "kii", value := .noFixedStress }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noFixedStress }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noFixedStress }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .penultimate }
  , { walsCode := "koo", language := "Kola", iso := "kvv", value := .penultimate }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .noFixedStress }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .initial }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .penultimate }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .initial }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .initial }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noFixedStress }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .initial }
  , { walsCode := "kuz", language := "Kulamanen", iso := "mbt", value := .noFixedStress }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noFixedStress }
  , { walsCode := "kjn", language := "Kunjen", iso := "kjn", value := .ultimate }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .penultimate }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .noFixedStress }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .penultimate }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .noFixedStress }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noFixedStress }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .ultimate }
  , { walsCode := "lla", language := "Lamu-Lamu", iso := "lby", value := .second }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .initial }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .noFixedStress }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .penultimate }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .initial }
  , { walsCode := "lje", language := "Lauje", iso := "law", value := .penultimate }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .initial }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .penultimate }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .noFixedStress }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noFixedStress }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noFixedStress }
  , { walsCode := "liv", language := "Liv", iso := "liv", value := .initial }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .initial }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noFixedStress }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .penultimate }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .penultimate }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .antepenultimate }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .ultimate }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .noFixedStress }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .antepenultimate }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noFixedStress }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .noFixedStress }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .noFixedStress }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noFixedStress }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .penultimate }
  , { walsCode := "mlc", language := "Malacca Creole", iso := "mcm", value := .noFixedStress }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .penultimate }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noFixedStress }
  , { walsCode := "mly", language := "Malay", iso := "zsm", value := .noFixedStress }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .noFixedStress }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .noFixedStress }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noFixedStress }
  , { walsCode := "mms", language := "Mamasa", iso := "mqj", value := .penultimate }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noFixedStress }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noFixedStress }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .penultimate }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .noFixedStress }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .initial }
  , { walsCode := "mnj", language := "Mantjiltjara", iso := "mpj", value := .initial }
  , { walsCode := "mnx", language := "Manx", iso := "glv", value := .initial }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noFixedStress }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .second }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .initial }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .initial }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .noFixedStress }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .noFixedStress }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .ultimate }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .ultimate }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .initial }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .penultimate }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .initial }
  , { walsCode := "myy", language := "Mayi-Yapi", iso := "xyj", value := .initial }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .second }
  , { walsCode := "meb", language := "Melayu Betawi", iso := "bew", value := .noFixedStress }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noFixedStress }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .penultimate }
  , { walsCode := "mta", language := "Mentuh Tapuh", iso := "sdo", value := .ultimate }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noFixedStress }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .penultimate }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .initial }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .noFixedStress }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .noFixedStress }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noFixedStress }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .penultimate }
  , { walsCode := "mgd", language := "Mongondow", iso := "mog", value := .penultimate }
  , { walsCode := "mmo", language := "Mordvin (Moksha)", iso := "mdf", value := .noFixedStress }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .penultimate }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noFixedStress }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .noFixedStress }
  , { walsCode := "mrk", language := "Murik", iso := "mtf", value := .noFixedStress }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noFixedStress }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .noFixedStress }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .penultimate }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .penultimate }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .ultimate }
  , { walsCode := "npu", language := "Napu", iso := "npy", value := .penultimate }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noFixedStress }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noFixedStress }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .initial }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .penultimate }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .penultimate }
  , { walsCode := "nsy", language := "Neo-Aramaic (Assyrian)", iso := "aii", value := .penultimate }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noFixedStress }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noFixedStress }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noFixedStress }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .penultimate }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .penultimate }
  , { walsCode := "ngr", language := "Ngarinyeri", iso := "nay", value := .initial }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noFixedStress }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .penultimate }
  , { walsCode := "nin", language := "Ningil", iso := "niz", value := .initial }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .initial }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noFixedStress }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .penultimate }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noFixedStress }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .penultimate }
  , { walsCode := "nbo", language := "Nyambo", iso := "now", value := .initial }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .noFixedStress }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .initial }
  , { walsCode := "obk", language := "Obokuitai", iso := "afz", value := .noFixedStress }
  , { walsCode := "occ", language := "Occitan", iso := "oci", value := .noFixedStress }
  , { walsCode := "olm", language := "Oloh Mangtangai", iso := "nij", value := .penultimate }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .penultimate }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .initial }
  , { walsCode := "orc", language := "Oroch", iso := "oac", value := .ultimate }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noFixedStress }
  , { walsCode := "oto", language := "Oto", iso := "iow", value := .noFixedStress }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .initial }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .antepenultimate }
  , { walsCode := "pad", language := "Padoe", iso := "pdo", value := .penultimate }
  , { walsCode := "pag", language := "Pagu", iso := "pgu", value := .penultimate }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .second }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .penultimate }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .penultimate }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noFixedStress }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noFixedStress }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .penultimate }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .antepenultimate }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .ultimate }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .initial }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noFixedStress }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .penultimate }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .initial }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .initial }
  , { walsCode := "pkm", language := "Pokomchí", iso := "poh", value := .ultimate }
  , { walsCode := "plb", language := "Polabian", iso := "pox", value := .noFixedStress }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .penultimate }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .second }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noFixedStress }
  , { walsCode := "plp", language := "Pulopetak", iso := "nij", value := .penultimate }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noFixedStress }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .initial }
  , { walsCode := "que", language := "Quechan", iso := "yum", value := .ultimate }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .penultimate }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .penultimate }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .ultimate }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noFixedStress }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .penultimate }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .initial }
  , { walsCode := "rnr", language := "Romani (North Russian)", iso := "rml", value := .ultimate }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noFixedStress }
  , { walsCode := "rsm", language := "Romansch (Surmeiran)", iso := "roh", value := .noFixedStress }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .noFixedStress }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .penultimate }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .noFixedStress }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noFixedStress }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .initial }
  , { walsCode := "sao", language := "Saho", iso := "ssy", value := .noFixedStress }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .antepenultimate }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .noFixedStress }
  , { walsCode := "sps", language := "Salish (Southern Puget Sound)", iso := "slh", value := .noFixedStress }
  , { walsCode := "sbg", language := "Sama (Balangingi)", iso := "sse", value := .penultimate }
  , { walsCode := "sgr", language := "Sangir", iso := "sxn", value := .penultimate }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .penultimate }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .noFixedStress }
  , { walsCode := "swi", language := "Sawai", iso := "szw", value := .noFixedStress }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .ultimate }
  , { walsCode := "sru", language := "Selaru", iso := "slu", value := .noFixedStress }
  , { walsCode := "sly", language := "Selayar", iso := "sly", value := .penultimate }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .initial }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .noFixedStress }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .ultimate }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noFixedStress }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noFixedStress }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noFixedStress }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .noFixedStress }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noFixedStress }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .ultimate }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .noFixedStress }
  , { walsCode := "skl", language := "Sikule", iso := "skh", value := .ultimate }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .noFixedStress }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noFixedStress }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .second }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noFixedStress }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .initial }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .noFixedStress }
  , { walsCode := "svc", language := "Slovincian", iso := "csb", value := .noFixedStress }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .initial }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .noFixedStress }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noFixedStress }
  , { walsCode := "spo", language := "Spokane", iso := "spo", value := .noFixedStress }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .penultimate }
  , { walsCode := "sto", language := "Stoney", iso := "sto", value := .second }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noFixedStress }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .initial }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .penultimate }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noFixedStress }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .penultimate }
  , { walsCode := "tbr", language := "Tabaru", iso := "tby", value := .penultimate }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .noFixedStress }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .penultimate }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .penultimate }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noFixedStress }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .ultimate }
  , { walsCode := "tld", language := "Talaud", iso := "tld", value := .penultimate }
  , { walsCode := "tns", language := "Tanna (Southwest)", iso := "nwi", value := .noFixedStress }
  , { walsCode := "tgw", language := "Tarangan (West)", iso := "txn", value := .noFixedStress }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .ultimate }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .penultimate }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .initial }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .noFixedStress }
  , { walsCode := "thp", language := "Thaypan", iso := "typ", value := .second }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noFixedStress }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .initial }
  , { walsCode := "tse", language := "Timorese", iso := "aoz", value := .penultimate }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .initial }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .antepenultimate }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .penultimate }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .noFixedStress }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noFixedStress }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .second }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .noFixedStress }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noFixedStress }
  , { walsCode := "tnt", language := "Tontemboan", iso := "tnt", value := .noFixedStress }
  , { walsCode := "trd", language := "Toraja", iso := "sda", value := .penultimate }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .penultimate }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .ultimate }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .ultimate }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .ultimate }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .penultimate }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .penultimate }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .initial }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noFixedStress }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .initial }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .ultimate }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noFixedStress }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noFixedStress }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .penultimate }
  , { walsCode := "unm", language := "Unami", iso := "unm", value := .noFixedStress }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noFixedStress }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .second }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .ultimate }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noFixedStress }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .ultimate }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .initial }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .ultimate }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .initial }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noFixedStress }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .penultimate }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .initial }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .initial }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .penultimate }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .penultimate }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .ultimate }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .initial }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noFixedStress }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .penultimate }
  , { walsCode := "wer", language := "Weri", iso := "wer", value := .ultimate }
  , { walsCode := "wet", language := "Wetan", iso := "lex", value := .penultimate }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noFixedStress }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .initial }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .third }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noFixedStress }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .noFixedStress }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .noFixedStress }
  , { walsCode := "ymd", language := "Yamdena", iso := "jmd", value := .penultimate }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .noFixedStress }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .penultimate }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noFixedStress }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .initial }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .penultimate }
  , { walsCode := "yzv", language := "Yazva", iso := "kpv", value := .noFixedStress }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .initial }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noFixedStress }
  , { walsCode := "yil", language := "Yil", iso := "yll", value := .noFixedStress }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .initial }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noFixedStress }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .initial }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noFixedStress }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noFixedStress }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noFixedStress }
  , { walsCode := "ych", language := "Yup'ik (Chevak)", iso := "esu", value := .noFixedStress }
  , { walsCode := "yun", language := "Yup'ik (Norton Sound)", iso := "esu", value := .noFixedStress }
  , { walsCode := "ysl", language := "Yupik (St. Lawrence Island)", iso := "ess", value := .noFixedStress }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noFixedStress }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .penultimate }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "zul", language := "Zulu", iso := "zul", value := .penultimate }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .initial }
  ]

/-- Complete WALS 14A dataset (502 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 502 := by native_decide

theorem count_noFixedStress :
    (allData.filter (·.value == .noFixedStress)).length = 220 := by native_decide
theorem count_initial :
    (allData.filter (·.value == .initial)).length = 92 := by native_decide
theorem count_second :
    (allData.filter (·.value == .second)).length = 16 := by native_decide
theorem count_third :
    (allData.filter (·.value == .third)).length = 1 := by native_decide
theorem count_antepenultimate :
    (allData.filter (·.value == .antepenultimate)).length = 12 := by native_decide
theorem count_penultimate :
    (allData.filter (·.value == .penultimate)).length = 110 := by native_decide
theorem count_ultimate :
    (allData.filter (·.value == .ultimate)).length = 51 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F14A
