import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 27A: Reduplication
@cite{rubino-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 27A`.

Chapter 27, 368 languages.
-/

namespace Core.WALS.F27A

/-- WALS 27A values. -/
inductive ReduplicationType where
  | productiveFullAndPartialReduplication  -- Productive full and partial reduplication (278 languages)
  | fullReduplicationOnly  -- Full reduplication only (35 languages)
  | noProductiveReduplication  -- No productive reduplication (55 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 27A dataset (368 languages). -/
def allData : List (Datapoint ReduplicationType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "agl", language := "Aghul", iso := "agx", value := .noProductiveReduplication }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .fullReduplicationOnly }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .productiveFullAndPartialReduplication }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .productiveFullAndPartialReduplication }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .productiveFullAndPartialReduplication }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .noProductiveReduplication }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .productiveFullAndPartialReduplication }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noProductiveReduplication }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .productiveFullAndPartialReduplication }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .fullReduplicationOnly }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .fullReduplicationOnly }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .productiveFullAndPartialReduplication }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .productiveFullAndPartialReduplication }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noProductiveReduplication }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .fullReduplicationOnly }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bnw", language := "Baniwa", iso := "bwi", value := .noProductiveReduplication }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noProductiveReduplication }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bsm", language := "Bislama", iso := "bis", value := .productiveFullAndPartialReduplication }
  , { walsCode := "blq", language := "Bole", iso := "bol", value := .productiveFullAndPartialReduplication }
  , { walsCode := "buw", language := "Bulu", iso := "bum", value := .productiveFullAndPartialReduplication }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .fullReduplicationOnly }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .fullReduplicationOnly }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .productiveFullAndPartialReduplication }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noProductiveReduplication }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noProductiveReduplication }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cvc", language := "Chavacano", iso := "cbk", value := .fullReduplicationOnly }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cmk", language := "Chemakum", iso := "xch", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .fullReduplicationOnly }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .productiveFullAndPartialReduplication }
  , { walsCode := "col", language := "Chol", iso := "ctu", value := .productiveFullAndPartialReduplication }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cla", language := "Clallam", iso := "clm", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .fullReduplicationOnly }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cwe", language := "Columbia-Wenatchi", iso := "col", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dri", language := "Dari", iso := "prs", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .productiveFullAndPartialReduplication }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .productiveFullAndPartialReduplication }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .productiveFullAndPartialReduplication }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .productiveFullAndPartialReduplication }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noProductiveReduplication }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .productiveFullAndPartialReduplication }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .fullReduplicationOnly }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noProductiveReduplication }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .productiveFullAndPartialReduplication }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .fullReduplicationOnly }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noProductiveReduplication }
  , { walsCode := "fox", language := "Fox", iso := "sac", value := .productiveFullAndPartialReduplication }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noProductiveReduplication }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .productiveFullAndPartialReduplication }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noProductiveReduplication }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .productiveFullAndPartialReduplication }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noProductiveReduplication }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .productiveFullAndPartialReduplication }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noProductiveReduplication }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noProductiveReduplication }
  , { walsCode := "gmt", language := "Gumatj", iso := "gnn", value := .fullReduplicationOnly }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hrr", language := "Harari", iso := "har", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .productiveFullAndPartialReduplication }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noProductiveReduplication }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .productiveFullAndPartialReduplication }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .fullReduplicationOnly }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .productiveFullAndPartialReduplication }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .productiveFullAndPartialReduplication }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noProductiveReduplication }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .fullReduplicationOnly }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noProductiveReduplication }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noProductiveReduplication }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .productiveFullAndPartialReduplication }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .fullReduplicationOnly }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .productiveFullAndPartialReduplication }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .productiveFullAndPartialReduplication }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .productiveFullAndPartialReduplication }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .fullReduplicationOnly }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .productiveFullAndPartialReduplication }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .productiveFullAndPartialReduplication }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noProductiveReduplication }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .productiveFullAndPartialReduplication }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .productiveFullAndPartialReduplication }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .productiveFullAndPartialReduplication }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .productiveFullAndPartialReduplication }
  , { walsCode := "koo", language := "Kola", iso := "kvv", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noProductiveReduplication }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .productiveFullAndPartialReduplication }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noProductiveReduplication }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kjn", language := "Kunjen", iso := "kjn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noProductiveReduplication }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noProductiveReduplication }
  , { walsCode := "lrd", language := "Lardil", iso := "lbz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noProductiveReduplication }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .productiveFullAndPartialReduplication }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .productiveFullAndPartialReduplication }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .fullReduplicationOnly }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noProductiveReduplication }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .fullReduplicationOnly }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noProductiveReduplication }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .productiveFullAndPartialReduplication }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .fullReduplicationOnly }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .fullReduplicationOnly }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .noProductiveReduplication }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .productiveFullAndPartialReduplication }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .fullReduplicationOnly }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .productiveFullAndPartialReduplication }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .productiveFullAndPartialReduplication }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .productiveFullAndPartialReduplication }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mxl", language := "Mixtec (Alacatlatzala)", iso := "mim", value := .fullReduplicationOnly }
  , { walsCode := "mja", language := "Mixtec (Jamiltepec)", iso := "mxt", value := .noProductiveReduplication }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .productiveFullAndPartialReduplication }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .noProductiveReduplication }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .productiveFullAndPartialReduplication }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .productiveFullAndPartialReduplication }
  , { walsCode := "muh", language := "Muher", iso := "sgw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .productiveFullAndPartialReduplication }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .fullReduplicationOnly }
  , { walsCode := "nhc", language := "Nahuatl (Central)", iso := "nhn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .productiveFullAndPartialReduplication }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noProductiveReduplication }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noProductiveReduplication }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noProductiveReduplication }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .fullReduplicationOnly }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .noProductiveReduplication }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .fullReduplicationOnly }
  , { walsCode := "nkr", language := "Nukuoro", iso := "nkr", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ojs", language := "Ojibwa (Severn)", iso := "ojs", value := .productiveFullAndPartialReduplication }
  , { walsCode := "oka", language := "Okanagan", iso := "oka", value := .productiveFullAndPartialReduplication }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noProductiveReduplication }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .productiveFullAndPartialReduplication }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .fullReduplicationOnly }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .productiveFullAndPartialReduplication }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .productiveFullAndPartialReduplication }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .noProductiveReduplication }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pgl", language := "Pingilapese", iso := "pif", value := .productiveFullAndPartialReduplication }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noProductiveReduplication }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .fullReduplicationOnly }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .productiveFullAndPartialReduplication }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noProductiveReduplication }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .productiveFullAndPartialReduplication }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .fullReduplicationOnly }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .productiveFullAndPartialReduplication }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .fullReduplicationOnly }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .productiveFullAndPartialReduplication }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .productiveFullAndPartialReduplication }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .productiveFullAndPartialReduplication }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .productiveFullAndPartialReduplication }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .productiveFullAndPartialReduplication }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .productiveFullAndPartialReduplication }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noProductiveReduplication }
  , { walsCode := "sst", language := "Salish (Straits)", iso := "str", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .productiveFullAndPartialReduplication }
  , { walsCode := "swi", language := "Sawai", iso := "szw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .noProductiveReduplication }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .productiveFullAndPartialReduplication }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sry", language := "Siraya", iso := "fos", value := .productiveFullAndPartialReduplication }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .productiveFullAndPartialReduplication }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noProductiveReduplication }
  , { walsCode := "som", language := "Somali", iso := "som", value := .productiveFullAndPartialReduplication }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noProductiveReduplication }
  , { walsCode := "spo", language := "Spokane", iso := "spo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .productiveFullAndPartialReduplication }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .productiveFullAndPartialReduplication }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .noProductiveReduplication }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .fullReduplicationOnly }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .productiveFullAndPartialReduplication }
  , { walsCode := "thw", language := "Thao", iso := "ssf", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .productiveFullAndPartialReduplication }
  , { walsCode := "til", language := "Tillamook", iso := "til", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .productiveFullAndPartialReduplication }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noProductiveReduplication }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tsw", language := "Tswana", iso := "tsn", value := .fullReduplicationOnly }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .productiveFullAndPartialReduplication }
  , { walsCode := "twa", language := "Twana", iso := "twa", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tze", language := "Tzeltal", iso := "tzh", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .productiveFullAndPartialReduplication }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .productiveFullAndPartialReduplication }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .productiveFullAndPartialReduplication }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .productiveFullAndPartialReduplication }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noProductiveReduplication }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wwy", language := "Waray-Waray", iso := "war", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .productiveFullAndPartialReduplication }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .productiveFullAndPartialReduplication }
  , { walsCode := "was", language := "Washo", iso := "was", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noProductiveReduplication }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noProductiveReduplication }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noProductiveReduplication }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .productiveFullAndPartialReduplication }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .fullReduplicationOnly }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .noProductiveReduplication }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noProductiveReduplication }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .noProductiveReduplication }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .fullReduplicationOnly }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .productiveFullAndPartialReduplication }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noProductiveReduplication }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .productiveFullAndPartialReduplication }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noProductiveReduplication }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .productiveFullAndPartialReduplication }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .fullReduplicationOnly }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .fullReduplicationOnly }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noProductiveReduplication }
  ]

-- Count verification
theorem total_count : allData.length = 368 := by native_decide

theorem count_productiveFullAndPartialReduplication :
    (allData.filter (·.value == .productiveFullAndPartialReduplication)).length = 278 := by native_decide
theorem count_fullReduplicationOnly :
    (allData.filter (·.value == .fullReduplicationOnly)).length = 35 := by native_decide
theorem count_noProductiveReduplication :
    (allData.filter (·.value == .noProductiveReduplication)).length = 55 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F27A
