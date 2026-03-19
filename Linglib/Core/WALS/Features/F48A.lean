/-!
# WALS Feature 48A: Person Marking on Adpositions
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 48A`.

Chapter 48, 378 languages.
-/

namespace Core.WALS.F48A

/-- WALS 48A values. -/
inductive PersonMarkingOnAdpositions where
  | noAdpositions  -- No adpositions (63 languages)
  | noPersonMarking  -- No person marking (209 languages)
  | pronounsOnly  -- Pronouns only (83 languages)
  | pronounsAndNouns  -- Pronouns and nouns (23 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 48A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PersonMarkingOnAdpositions
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 48A dataset (378 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noPersonMarking }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noPersonMarking }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .pronounsAndNouns }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noPersonMarking }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noPersonMarking }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noAdpositions }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noPersonMarking }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noPersonMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .pronounsOnly }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noPersonMarking }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noPersonMarking }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noPersonMarking }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .pronounsOnly }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .noPersonMarking }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .pronounsOnly }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .pronounsOnly }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noAdpositions }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noAdpositions }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .pronounsOnly }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPersonMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noAdpositions }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noPersonMarking }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noPersonMarking }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noPersonMarking }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noPersonMarking }
  , { walsCode := "au", language := "Au", iso := "avt", value := .pronounsOnly }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noPersonMarking }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noAdpositions }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .pronounsOnly }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noPersonMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .pronounsOnly }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noPersonMarking }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .noAdpositions }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noPersonMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noPersonMarking }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noPersonMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noPersonMarking }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noPersonMarking }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noPersonMarking }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noPersonMarking }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .pronounsOnly }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .pronounsOnly }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .noPersonMarking }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .pronounsAndNouns }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noPersonMarking }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noPersonMarking }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .noPersonMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noPersonMarking }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noPersonMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .pronounsOnly }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .noPersonMarking }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noPersonMarking }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noPersonMarking }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .pronounsOnly }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .pronounsOnly }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .noPersonMarking }
  , { walsCode := "car", language := "Carib", iso := "car", value := .pronounsAndNouns }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noPersonMarking }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noAdpositions }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .pronounsOnly }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noPersonMarking }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .pronounsOnly }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .noPersonMarking }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noPersonMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noPersonMarking }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noAdpositions }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .pronounsOnly }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noPersonMarking }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .noPersonMarking }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noAdpositions }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .pronounsOnly }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .pronounsAndNouns }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noAdpositions }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .noPersonMarking }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noPersonMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noPersonMarking }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noPersonMarking }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noPersonMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .pronounsOnly }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noPersonMarking }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noPersonMarking }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noPersonMarking }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noPersonMarking }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noPersonMarking }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noPersonMarking }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noPersonMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noPersonMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noPersonMarking }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noPersonMarking }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .pronounsOnly }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .pronounsOnly }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .pronounsOnly }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .pronounsAndNouns }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .pronounsOnly }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noPersonMarking }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noPersonMarking }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .pronounsOnly }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noAdpositions }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noPersonMarking }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noPersonMarking }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noPersonMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noPersonMarking }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPersonMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noPersonMarking }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .pronounsOnly }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .pronounsOnly }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noPersonMarking }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noPersonMarking }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noAdpositions }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noPersonMarking }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .noAdpositions }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .noAdpositions }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noAdpositions }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noPersonMarking }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .pronounsOnly }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .pronounsOnly }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noPersonMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .pronounsOnly }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPersonMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noPersonMarking }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .pronounsOnly }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .pronounsOnly }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noPersonMarking }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noPersonMarking }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .pronounsOnly }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noPersonMarking }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPersonMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noPersonMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noPersonMarking }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .pronounsOnly }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noPersonMarking }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .pronounsOnly }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noPersonMarking }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .pronounsAndNouns }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPersonMarking }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noAdpositions }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPersonMarking }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noAdpositions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noPersonMarking }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noPersonMarking }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .noPersonMarking }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .pronounsOnly }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noPersonMarking }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noPersonMarking }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .pronounsAndNouns }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPersonMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noAdpositions }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noPersonMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .pronounsAndNouns }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noPersonMarking }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noPersonMarking }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noPersonMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noPersonMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPersonMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .pronounsOnly }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noAdpositions }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .pronounsAndNouns }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noPersonMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .pronounsOnly }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noPersonMarking }
  , { walsCode := "klk", language := "Koh", iso := "xuo", value := .noPersonMarking }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noPersonMarking }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noPersonMarking }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .noPersonMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noPersonMarking }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .pronounsOnly }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .pronounsOnly }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noPersonMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPersonMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noPersonMarking }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .noPersonMarking }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noPersonMarking }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .pronounsOnly }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noAdpositions }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noAdpositions }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noPersonMarking }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noPersonMarking }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noPersonMarking }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .pronounsOnly }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .pronounsOnly }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .pronounsOnly }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noPersonMarking }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .pronounsAndNouns }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noPersonMarking }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noPersonMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPersonMarking }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .noPersonMarking }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .pronounsOnly }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noPersonMarking }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .noAdpositions }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .pronounsOnly }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .pronounsOnly }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noAdpositions }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .noPersonMarking }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noAdpositions }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .pronounsOnly }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noAdpositions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPersonMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noAdpositions }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPersonMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noPersonMarking }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noPersonMarking }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noAdpositions }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noPersonMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noAdpositions }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noAdpositions }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noPersonMarking }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .noPersonMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .pronounsAndNouns }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .pronounsOnly }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPersonMarking }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noPersonMarking }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noPersonMarking }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noAdpositions }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .pronounsOnly }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noPersonMarking }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .noPersonMarking }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noAdpositions }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noPersonMarking }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noPersonMarking }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noPersonMarking }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noPersonMarking }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .pronounsOnly }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .pronounsOnly }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .noPersonMarking }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .pronounsAndNouns }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noPersonMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noPersonMarking }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noAdpositions }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noAdpositions }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noPersonMarking }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noPersonMarking }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .pronounsAndNouns }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .noPersonMarking }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noPersonMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .pronounsOnly }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noAdpositions }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noAdpositions }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noAdpositions }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .pronounsOnly }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noAdpositions }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noPersonMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .pronounsOnly }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .pronounsOnly }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .pronounsOnly }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .pronounsOnly }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noAdpositions }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noPersonMarking }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noAdpositions }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .noPersonMarking }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noAdpositions }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noPersonMarking }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noPersonMarking }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noPersonMarking }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .pronounsOnly }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPersonMarking }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noPersonMarking }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .pronounsAndNouns }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noAdpositions }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noAdpositions }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noPersonMarking }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .noAdpositions }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .pronounsOnly }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .pronounsAndNouns }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPersonMarking }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noPersonMarking }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noPersonMarking }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noPersonMarking }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .noPersonMarking }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noPersonMarking }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .noPersonMarking }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noPersonMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noPersonMarking }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noAdpositions }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .pronounsOnly }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noPersonMarking }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .noPersonMarking }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .pronounsOnly }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noPersonMarking }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noPersonMarking }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .pronounsOnly }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noPersonMarking }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noPersonMarking }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPersonMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPersonMarking }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .noPersonMarking }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .noPersonMarking }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noPersonMarking }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .pronounsOnly }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .noPersonMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noPersonMarking }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noPersonMarking }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noPersonMarking }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noAdpositions }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .pronounsOnly }
  , { walsCode := "so", language := "So", iso := "teu", value := .pronounsOnly }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noPersonMarking }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noAdpositions }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noPersonMarking }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noPersonMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPersonMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noPersonMarking }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noPersonMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noAdpositions }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .noAdpositions }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .pronounsAndNouns }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noAdpositions }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .pronounsOnly }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .pronounsOnly }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .pronounsOnly }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noPersonMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPersonMarking }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noPersonMarking }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .pronounsOnly }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .noAdpositions }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noPersonMarking }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .pronounsOnly }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noPersonMarking }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .pronounsAndNouns }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noPersonMarking }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noPersonMarking }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .noPersonMarking }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noPersonMarking }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noPersonMarking }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .pronounsOnly }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noPersonMarking }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noPersonMarking }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .noPersonMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noPersonMarking }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noPersonMarking }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .noPersonMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noPersonMarking }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .pronounsAndNouns }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .pronounsAndNouns }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .pronounsOnly }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noPersonMarking }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noAdpositions }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .pronounsOnly }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noAdpositions }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .pronounsOnly }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .pronounsOnly }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPersonMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noAdpositions }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noPersonMarking }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noPersonMarking }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noPersonMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noPersonMarking }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noAdpositions }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .pronounsOnly }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .pronounsAndNouns }
  , { walsCode := "was", language := "Washo", iso := "was", value := .pronounsOnly }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .pronounsAndNouns }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .pronounsOnly }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noPersonMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noAdpositions }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noAdpositions }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noAdpositions }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noAdpositions }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .noPersonMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .pronounsAndNouns }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .pronounsOnly }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPersonMarking }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .pronounsOnly }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .pronounsAndNouns }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .pronounsOnly }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noAdpositions }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .pronounsOnly }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPersonMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .pronounsOnly }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noPersonMarking }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noAdpositions }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noAdpositions }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noPersonMarking }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noPersonMarking }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .pronounsOnly }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noAdpositions }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noPersonMarking }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noAdpositions }
  ]

-- Count verification
theorem total_count : allData.length = 378 := by native_decide

theorem count_noAdpositions :
    (allData.filter (·.value == .noAdpositions)).length = 63 := by native_decide
theorem count_noPersonMarking :
    (allData.filter (·.value == .noPersonMarking)).length = 209 := by native_decide
theorem count_pronounsOnly :
    (allData.filter (·.value == .pronounsOnly)).length = 83 := by native_decide
theorem count_pronounsAndNouns :
    (allData.filter (·.value == .pronounsAndNouns)).length = 23 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F48A
