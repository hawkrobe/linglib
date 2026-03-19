/-!
# WALS Feature 15A: Weight-Sensitive Stress
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 15A`.

Chapter 15, 500 languages.
-/

namespace Core.WALS.F15A

/-- WALS 15A values. -/
inductive WeightSensitiveStress where
  | leftEdgeFirstOrSecond  -- Left-edge: First or second (37 languages)
  | leftOrientedOneOfTheFirstThree  -- Left-oriented: One of the first three (2 languages)
  | rightEdgeUltimateOrPenultimate  -- Right-edge: Ultimate or penultimate (65 languages)
  | rightOrientedOneOfTheLastThree  -- Right-oriented: One of the last three (27 languages)
  | unboundedStressCanBeAnywhere  -- Unbounded: Stress can be anywhere (54 languages)
  | combinedRightEdgeAndUnbounded  -- Combined: Right-edge and unbounded (8 languages)
  | notPredictable  -- Not predictable (26 languages)
  | fixedStress  -- Fixed stress (no weight-sensitivity) (281 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 15A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : WeightSensitiveStress
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 15A dataset (500 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .notPredictable }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .fixedStress }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .fixedStress }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "akl", language := "Aklanon", iso := "akl", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .fixedStress }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .fixedStress }
  , { walsCode := "atq", language := "Alutiiq", iso := "ems", value := .leftEdgeFirstOrSecond }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .fixedStress }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .fixedStress }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ahs", language := "Arabic (Bani-Hassan)", iso := "mey", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "abe", language := "Arabic (Beirut)", iso := "apc", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "ael", language := "Arabic (Eastern Libyan)", iso := "ayl", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "arh", language := "Arabic (Hijazi)", iso := "acw", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "arv", language := "Arabic (Negev)", iso := "ajp", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "apa", language := "Arabic (Palestinian)", iso := "ajp", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "atb", language := "Aralle-Tabulahan", iso := "atq", value := .fixedStress }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .fixedStress }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .fixedStress }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .leftEdgeFirstOrSecond }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .fixedStress }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .fixedStress }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .fixedStress }
  , { walsCode := "au", language := "Au", iso := "avt", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .leftEdgeFirstOrSecond }
  , { walsCode := "awd", language := "Awadhi", iso := "awa", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .fixedStress }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .fixedStress }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .fixedStress }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .fixedStress }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "blk", language := "Balantak", iso := "blz", value := .fixedStress }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .fixedStress }
  , { walsCode := "bbm", language := "Bambam", iso := "ptu", value := .fixedStress }
  , { walsCode := "bna", language := "Banawá", iso := "jaa", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .leftEdgeFirstOrSecond }
  , { walsCode := "bgg", language := "Banggai", iso := "bgz", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bnl", language := "Banggarla", iso := "bjb", value := .fixedStress }
  , { walsCode := "bnt", language := "Bantik", iso := "bnq", value := .fixedStress }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .fixedStress }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .fixedStress }
  , { walsCode := "bqi", language := "Basque (Basaburua and Imoz)", iso := "eus", value := .leftEdgeFirstOrSecond }
  , { walsCode := "bqb", language := "Basque (Bidasoa Valley)", iso := "eus", value := .fixedStress }
  , { walsCode := "bqg", language := "Basque (Gernica)", iso := "eus", value := .notPredictable }
  , { walsCode := "bqh", language := "Basque (Hondarribia)", iso := "eus", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bql", language := "Basque (Lekeitio)", iso := "eus", value := .fixedStress }
  , { walsCode := "bqn", language := "Basque (Northern High Navarrese)", iso := "eus", value := .fixedStress }
  , { walsCode := "bqo", language := "Basque (Oñati)", iso := "eus", value := .fixedStress }
  , { walsCode := "bqr", language := "Basque (Roncalese)", iso := "eus", value := .fixedStress }
  , { walsCode := "bqs", language := "Basque (Sakana)", iso := "eus", value := .fixedStress }
  , { walsCode := "bso", language := "Basque (Souletin)", iso := "eus", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bqz", language := "Basque (Zeberio)", iso := "eus", value := .notPredictable }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .fixedStress }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .fixedStress }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .fixedStress }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .fixedStress }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .fixedStress }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bim", language := "Bima", iso := "bhp", value := .fixedStress }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .fixedStress }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .fixedStress }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .fixedStress }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .fixedStress }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .fixedStress }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .notPredictable }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .fixedStress }
  , { walsCode := "cpa", language := "Campa Pajonal Asheninca", iso := "cjo", value := .notPredictable }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .fixedStress }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .leftEdgeFirstOrSecond }
  , { walsCode := "car", language := "Carib", iso := "car", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .fixedStress }
  , { walsCode := "cyg", language := "Cayuga", iso := "cay", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .fixedStress }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .fixedStress }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .fixedStress }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .notPredictable }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .fixedStress }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .fixedStress }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .fixedStress }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .fixedStress }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .fixedStress }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .fixedStress }
  , { walsCode := "daa", language := "Da'a", iso := "kzf", value := .fixedStress }
  , { walsCode := "dak", language := "Dakota", iso := "dak", value := .fixedStress }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .fixedStress }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "dri", language := "Dari", iso := "prs", value := .fixedStress }
  , { walsCode := "des", language := "Desano", iso := "des", value := .notPredictable }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .leftEdgeFirstOrSecond }
  , { walsCode := "dhu", language := "Dhurga", iso := "dhu", value := .leftEdgeFirstOrSecond }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .fixedStress }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .fixedStress }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .fixedStress }
  , { walsCode := "dob", language := "Dobel", iso := "kvo", value := .fixedStress }
  , { walsCode := "dou", language := "Doutai", iso := "tds", value := .fixedStress }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .fixedStress }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .fixedStress }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .leftEdgeFirstOrSecond }
  , { walsCode := "emc", language := "Embera Chami", iso := "cmi", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .fixedStress }
  , { walsCode := "eng", language := "English", iso := "eng", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .fixedStress }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .fixedStress }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .fixedStress }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .fixedStress }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .fixedStress }
  , { walsCode := "for", language := "Fore", iso := "for", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "fre", language := "French", iso := "fra", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "glp", language := "Gaalpu", iso := "dhg", value := .fixedStress }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .fixedStress }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .fixedStress }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .fixedStress }
  , { walsCode := "gay", language := "Gayo", iso := "gay", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .fixedStress }
  , { walsCode := "ger", language := "German", iso := "deu", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .fixedStress }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .fixedStress }
  , { walsCode := "gor", language := "Gorowa", iso := "gow", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .notPredictable }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .fixedStress }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .fixedStress }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .fixedStress }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .fixedStress }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .fixedStress }
  , { walsCode := "hno", language := "Haida (Northern)", iso := "hdn", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "hln", language := "Halang", iso := "hal", value := .fixedStress }
  , { walsCode := "hnn", language := "Hanunóo", iso := "hnn", value := .fixedStress }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .fixedStress }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .fixedStress }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .notPredictable }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .leftEdgeFirstOrSecond }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .fixedStress }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .fixedStress }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .fixedStress }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .fixedStress }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .fixedStress }
  , { walsCode := "iga", language := "Inga", iso := "inb", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .fixedStress }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .fixedStress }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .fixedStress }
  , { walsCode := "irm", language := "Irish (Munster)", iso := "gle", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .fixedStress }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .fixedStress }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "jum", language := "Júma", iso := "jua", value := .fixedStress }
  , { walsCode := "kli", language := "Kaili", iso := "lew", value := .fixedStress }
  , { walsCode := "kaw", language := "Kaiwá", iso := "kgk", value := .fixedStress }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .fixedStress }
  , { walsCode := "klp", language := "Kalapuya", iso := "kyl", value := .fixedStress }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .fixedStress }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .fixedStress }
  , { walsCode := "kra", language := "Kara (in Papua New Guinea)", iso := "leu", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "krl", language := "Karelian", iso := "krl", value := .fixedStress }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ksh", language := "Kashaya", iso := "kju", value := .leftOrientedOneOfTheFirstThree }
  , { walsCode := "kaj", language := "Kaure", iso := "bpp", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .fixedStress }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .fixedStress }
  , { walsCode := "kap", language := "Kela (Apoze)", iso := "kcl", value := .fixedStress }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ktn", language := "Ketengban", iso := "xte", value := .notPredictable }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .notPredictable }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .fixedStress }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .fixedStress }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .fixedStress }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ksr", language := "Kisar", iso := "kje", value := .fixedStress }
  , { walsCode := "kit", language := "Kitsai", iso := "kii", value := .notPredictable }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .fixedStress }
  , { walsCode := "koo", language := "Kola", iso := "kvv", value := .fixedStress }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .fixedStress }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .fixedStress }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .fixedStress }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .fixedStress }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .fixedStress }
  , { walsCode := "kuz", language := "Kulamanen", iso := "mbt", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "kjn", language := "Kunjen", iso := "kjn", value := .fixedStress }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .fixedStress }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .fixedStress }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .fixedStress }
  , { walsCode := "lla", language := "Lamu-Lamu", iso := "lby", value := .fixedStress }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .fixedStress }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .leftOrientedOneOfTheFirstThree }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .fixedStress }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .fixedStress }
  , { walsCode := "lje", language := "Lauje", iso := "law", value := .fixedStress }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .fixedStress }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .fixedStress }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .leftEdgeFirstOrSecond }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "liv", language := "Liv", iso := "liv", value := .fixedStress }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .fixedStress }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .leftEdgeFirstOrSecond }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .fixedStress }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .fixedStress }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .fixedStress }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .fixedStress }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .fixedStress }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .fixedStress }
  , { walsCode := "mlc", language := "Malacca Creole", iso := "mcm", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .fixedStress }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mly", language := "Malay", iso := "zsm", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "mms", language := "Mamasa", iso := "mqj", value := .fixedStress }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .notPredictable }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .fixedStress }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .fixedStress }
  , { walsCode := "mnj", language := "Mantjiltjara", iso := "mpj", value := .fixedStress }
  , { walsCode := "mnx", language := "Manx", iso := "glv", value := .fixedStress }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .fixedStress }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .fixedStress }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .fixedStress }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .fixedStress }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .fixedStress }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .fixedStress }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .fixedStress }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .fixedStress }
  , { walsCode := "myy", language := "Mayi-Yapi", iso := "xyj", value := .fixedStress }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .fixedStress }
  , { walsCode := "meb", language := "Melayu Betawi", iso := "bew", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .fixedStress }
  , { walsCode := "mta", language := "Mentuh Tapuh", iso := "sdo", value := .fixedStress }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .notPredictable }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .fixedStress }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .fixedStress }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .leftEdgeFirstOrSecond }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .leftEdgeFirstOrSecond }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .fixedStress }
  , { walsCode := "mgd", language := "Mongondow", iso := "mog", value := .fixedStress }
  , { walsCode := "mmo", language := "Mordvin (Moksha)", iso := "mdf", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .fixedStress }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "mrk", language := "Murik", iso := "mtf", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .fixedStress }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .fixedStress }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .fixedStress }
  , { walsCode := "npu", language := "Napu", iso := "npy", value := .fixedStress }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .fixedStress }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .fixedStress }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .fixedStress }
  , { walsCode := "nsy", language := "Neo-Aramaic (Assyrian)", iso := "aii", value := .fixedStress }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .leftEdgeFirstOrSecond }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .notPredictable }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .fixedStress }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .fixedStress }
  , { walsCode := "ngr", language := "Ngarinyeri", iso := "nay", value := .fixedStress }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .fixedStress }
  , { walsCode := "nin", language := "Ningil", iso := "niz", value := .fixedStress }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .fixedStress }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .fixedStress }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .fixedStress }
  , { walsCode := "nbo", language := "Nyambo", iso := "now", value := .fixedStress }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .leftEdgeFirstOrSecond }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .fixedStress }
  , { walsCode := "obk", language := "Obokuitai", iso := "afz", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "occ", language := "Occitan", iso := "oci", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "olm", language := "Oloh Mangtangai", iso := "nij", value := .fixedStress }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .fixedStress }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .fixedStress }
  , { walsCode := "orc", language := "Oroch", iso := "oac", value := .fixedStress }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .leftEdgeFirstOrSecond }
  , { walsCode := "oto", language := "Oto", iso := "iow", value := .leftEdgeFirstOrSecond }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .fixedStress }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .fixedStress }
  , { walsCode := "pad", language := "Padoe", iso := "pdo", value := .fixedStress }
  , { walsCode := "pag", language := "Pagu", iso := "pgu", value := .fixedStress }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .fixedStress }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .fixedStress }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .fixedStress }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .notPredictable }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .fixedStress }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .fixedStress }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .fixedStress }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .fixedStress }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .fixedStress }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .fixedStress }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .fixedStress }
  , { walsCode := "pkm", language := "Pokomchí", iso := "poh", value := .fixedStress }
  , { walsCode := "plb", language := "Polabian", iso := "pox", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .fixedStress }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .fixedStress }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "plp", language := "Pulopetak", iso := "nij", value := .fixedStress }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .fixedStress }
  , { walsCode := "que", language := "Quechan", iso := "yum", value := .fixedStress }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .fixedStress }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .fixedStress }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .fixedStress }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .notPredictable }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .fixedStress }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .fixedStress }
  , { walsCode := "rnr", language := "Romani (North Russian)", iso := "rml", value := .fixedStress }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "rsm", language := "Romansch (Surmeiran)", iso := "roh", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .leftEdgeFirstOrSecond }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .fixedStress }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .fixedStress }
  , { walsCode := "sao", language := "Saho", iso := "ssy", value := .notPredictable }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .fixedStress }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "sps", language := "Salish (Southern Puget Sound)", iso := "slh", value := .notPredictable }
  , { walsCode := "sbg", language := "Sama (Balangingi)", iso := "sse", value := .fixedStress }
  , { walsCode := "sgr", language := "Sangir", iso := "sxn", value := .fixedStress }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .fixedStress }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "swi", language := "Sawai", iso := "szw", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .fixedStress }
  , { walsCode := "sru", language := "Selaru", iso := "slu", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "sly", language := "Selayar", iso := "sly", value := .fixedStress }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .fixedStress }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .leftEdgeFirstOrSecond }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .fixedStress }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .leftEdgeFirstOrSecond }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .fixedStress }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "skl", language := "Sikule", iso := "skh", value := .fixedStress }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .combinedRightEdgeAndUnbounded }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .fixedStress }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .notPredictable }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .fixedStress }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "svc", language := "Slovincian", iso := "csb", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .fixedStress }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "spo", language := "Spokane", iso := "spo", value := .notPredictable }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .fixedStress }
  , { walsCode := "sto", language := "Stoney", iso := "sto", value := .fixedStress }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .fixedStress }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .fixedStress }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .fixedStress }
  , { walsCode := "tbr", language := "Tabaru", iso := "tby", value := .fixedStress }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .fixedStress }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .fixedStress }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .fixedStress }
  , { walsCode := "tld", language := "Talaud", iso := "tld", value := .fixedStress }
  , { walsCode := "tns", language := "Tanna (Southwest)", iso := "nwi", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "tgw", language := "Tarangan (West)", iso := "txn", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .fixedStress }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .fixedStress }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .fixedStress }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .leftEdgeFirstOrSecond }
  , { walsCode := "thp", language := "Thaypan", iso := "typ", value := .fixedStress }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .fixedStress }
  , { walsCode := "tse", language := "Timorese", iso := "aoz", value := .fixedStress }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .fixedStress }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .fixedStress }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .fixedStress }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .fixedStress }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "tnt", language := "Tontemboan", iso := "tnt", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "trd", language := "Toraja", iso := "sda", value := .fixedStress }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .fixedStress }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .fixedStress }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .fixedStress }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .fixedStress }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .fixedStress }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .fixedStress }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .fixedStress }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .fixedStress }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .fixedStress }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .leftEdgeFirstOrSecond }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .notPredictable }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .fixedStress }
  , { walsCode := "unm", language := "Unami", iso := "unm", value := .rightOrientedOneOfTheLastThree }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .leftEdgeFirstOrSecond }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .fixedStress }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .fixedStress }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .notPredictable }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .fixedStress }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .fixedStress }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .fixedStress }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .fixedStress }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .leftEdgeFirstOrSecond }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .fixedStress }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .fixedStress }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .fixedStress }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .fixedStress }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .fixedStress }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .fixedStress }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .fixedStress }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .leftEdgeFirstOrSecond }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .fixedStress }
  , { walsCode := "wer", language := "Weri", iso := "wer", value := .fixedStress }
  , { walsCode := "wet", language := "Wetan", iso := "lex", value := .fixedStress }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .fixedStress }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .fixedStress }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .notPredictable }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "ymd", language := "Yamdena", iso := "jmd", value := .fixedStress }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .fixedStress }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .rightEdgeUltimateOrPenultimate }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .fixedStress }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .fixedStress }
  , { walsCode := "yzv", language := "Yazva", iso := "kpv", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .fixedStress }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "yil", language := "Yil", iso := "yll", value := .leftEdgeFirstOrSecond }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .fixedStress }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .leftEdgeFirstOrSecond }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .fixedStress }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .notPredictable }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .leftEdgeFirstOrSecond }
  , { walsCode := "ych", language := "Yup'ik (Chevak)", iso := "esu", value := .leftEdgeFirstOrSecond }
  , { walsCode := "yun", language := "Yup'ik (Norton Sound)", iso := "esu", value := .leftEdgeFirstOrSecond }
  , { walsCode := "ysl", language := "Yupik (St. Lawrence Island)", iso := "ess", value := .notPredictable }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .unboundedStressCanBeAnywhere }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .fixedStress }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .fixedStress }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .fixedStress }
  ]

-- Count verification
theorem total_count : allData.length = 500 := by native_decide

theorem count_leftEdgeFirstOrSecond :
    (allData.filter (·.value == .leftEdgeFirstOrSecond)).length = 37 := by native_decide
theorem count_leftOrientedOneOfTheFirstThree :
    (allData.filter (·.value == .leftOrientedOneOfTheFirstThree)).length = 2 := by native_decide
theorem count_rightEdgeUltimateOrPenultimate :
    (allData.filter (·.value == .rightEdgeUltimateOrPenultimate)).length = 65 := by native_decide
theorem count_rightOrientedOneOfTheLastThree :
    (allData.filter (·.value == .rightOrientedOneOfTheLastThree)).length = 27 := by native_decide
theorem count_unboundedStressCanBeAnywhere :
    (allData.filter (·.value == .unboundedStressCanBeAnywhere)).length = 54 := by native_decide
theorem count_combinedRightEdgeAndUnbounded :
    (allData.filter (·.value == .combinedRightEdgeAndUnbounded)).length = 8 := by native_decide
theorem count_notPredictable :
    (allData.filter (·.value == .notPredictable)).length = 26 := by native_decide
theorem count_fixedStress :
    (allData.filter (·.value == .fixedStress)).length = 281 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F15A
