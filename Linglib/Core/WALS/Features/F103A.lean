/-!
# WALS Feature 103A: Third Person Zero of Verbal Person Marking
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 103A`.

Chapter 103, 380 languages.
-/

namespace Core.WALS.F103A

/-- WALS 103A values. -/
inductive ThirdPersonZeroOfVerbalPersonMarking where
  | noPersonMarking  -- No person marking (96 languages)
  | noZeroRealization  -- No zero realization (181 languages)
  | zeroInSome3sgForms  -- Zero in some 3sg forms (21 languages)
  | zeroInAll3sgForms  -- Zero in all 3sg forms (45 languages)
  | zeroInAll3rdPersonForms  -- Zero in all 3rd person forms (36 languages)
  | zeroOnlyIn3rdNonsingular  -- Zero only in 3rd nonsingular (1 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 103A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ThirdPersonZeroOfVerbalPersonMarking
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 103A dataset (380 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noPersonMarking }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .zeroInSome3sgForms }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noZeroRealization }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noPersonMarking }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .zeroInAll3rdPersonForms }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noZeroRealization }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noZeroRealization }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noPersonMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noZeroRealization }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noZeroRealization }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noZeroRealization }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noZeroRealization }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .zeroInAll3rdPersonForms }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .noZeroRealization }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noZeroRealization }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noZeroRealization }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noPersonMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .zeroInAll3sgForms }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPersonMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noZeroRealization }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .zeroInAll3sgForms }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .zeroInAll3sgForms }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .zeroInAll3sgForms }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .zeroInAll3sgForms }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noZeroRealization }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noZeroRealization }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noPersonMarking }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .zeroInAll3sgForms }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noPersonMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noZeroRealization }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noPersonMarking }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .noPersonMarking }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noZeroRealization }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .zeroOnlyIn3rdNonsingular }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noPersonMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noZeroRealization }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noZeroRealization }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noZeroRealization }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noZeroRealization }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noZeroRealization }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .noZeroRealization }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .noZeroRealization }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .zeroInSome3sgForms }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .zeroInSome3sgForms }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noPersonMarking }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .noPersonMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noPersonMarking }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noZeroRealization }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noZeroRealization }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .zeroInAll3sgForms }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .zeroInAll3sgForms }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noZeroRealization }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noZeroRealization }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noZeroRealization }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .noZeroRealization }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noZeroRealization }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noZeroRealization }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .zeroInSome3sgForms }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noZeroRealization }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .zeroInAll3sgForms }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noZeroRealization }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .noZeroRealization }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noPersonMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noZeroRealization }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noZeroRealization }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noZeroRealization }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noZeroRealization }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .zeroInAll3sgForms }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .zeroInAll3rdPersonForms }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .noZeroRealization }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .zeroInAll3sgForms }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .zeroInAll3rdPersonForms }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .zeroInAll3sgForms }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noZeroRealization }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noZeroRealization }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noPersonMarking }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noZeroRealization }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noZeroRealization }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noZeroRealization }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noZeroRealization }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noPersonMarking }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .zeroInAll3sgForms }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noPersonMarking }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noZeroRealization }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noZeroRealization }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noZeroRealization }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noZeroRealization }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noPersonMarking }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noZeroRealization }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noZeroRealization }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noZeroRealization }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noZeroRealization }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .zeroInAll3sgForms }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noZeroRealization }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noZeroRealization }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noZeroRealization }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noPersonMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noZeroRealization }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noZeroRealization }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noPersonMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .zeroInAll3sgForms }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPersonMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noZeroRealization }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noZeroRealization }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .zeroInAll3rdPersonForms }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noPersonMarking }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noZeroRealization }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noPersonMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noPersonMarking }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .zeroInAll3rdPersonForms }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .noPersonMarking }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noZeroRealization }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noZeroRealization }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPersonMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .zeroInAll3sgForms }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noZeroRealization }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noZeroRealization }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPersonMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noZeroRealization }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .zeroInAll3rdPersonForms }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noZeroRealization }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noPersonMarking }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noPersonMarking }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noPersonMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .zeroInAll3sgForms }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPersonMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noZeroRealization }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noPersonMarking }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .noZeroRealization }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noZeroRealization }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noZeroRealization }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noZeroRealization }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .zeroInAll3sgForms }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPersonMarking }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .zeroInAll3rdPersonForms }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPersonMarking }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .zeroInAll3sgForms }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noZeroRealization }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noZeroRealization }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .noZeroRealization }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .noZeroRealization }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noZeroRealization }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .zeroInAll3rdPersonForms }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noZeroRealization }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPersonMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPersonMarking }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noPersonMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noZeroRealization }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noZeroRealization }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noPersonMarking }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noZeroRealization }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noPersonMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPersonMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noZeroRealization }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .zeroInAll3sgForms }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noZeroRealization }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noPersonMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .zeroInAll3rdPersonForms }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .zeroInAll3sgForms }
  , { walsCode := "klk", language := "Koh", iso := "xuo", value := .noPersonMarking }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noZeroRealization }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noZeroRealization }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .noZeroRealization }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noPersonMarking }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noZeroRealization }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noZeroRealization }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noPersonMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPersonMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noPersonMarking }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .noPersonMarking }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .zeroInAll3sgForms }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .zeroInSome3sgForms }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .zeroInAll3rdPersonForms }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .zeroInAll3rdPersonForms }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noPersonMarking }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noPersonMarking }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noZeroRealization }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .zeroInAll3rdPersonForms }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .zeroInSome3sgForms }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .noZeroRealization }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .zeroInAll3sgForms }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noZeroRealization }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noZeroRealization }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noPersonMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPersonMarking }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noZeroRealization }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noZeroRealization }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noZeroRealization }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .noPersonMarking }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noZeroRealization }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .zeroInSome3sgForms }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noZeroRealization }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .noZeroRealization }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .zeroInSome3sgForms }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPersonMarking }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noZeroRealization }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPersonMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .zeroInAll3sgForms }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPersonMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noZeroRealization }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .zeroInAll3sgForms }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .zeroInAll3rdPersonForms }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noZeroRealization }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noPersonMarking }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noZeroRealization }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noZeroRealization }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .noPersonMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noZeroRealization }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .zeroInAll3rdPersonForms }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPersonMarking }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noPersonMarking }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noZeroRealization }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noZeroRealization }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noZeroRealization }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noZeroRealization }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .noPersonMarking }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noZeroRealization }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noZeroRealization }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noPersonMarking }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noZeroRealization }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noZeroRealization }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noPersonMarking }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noZeroRealization }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .zeroInAll3rdPersonForms }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .zeroInAll3rdPersonForms }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noZeroRealization }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noPersonMarking }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .zeroInAll3sgForms }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noZeroRealization }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .zeroInAll3rdPersonForms }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .zeroInSome3sgForms }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .noZeroRealization }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noPersonMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .zeroInAll3sgForms }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noZeroRealization }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .zeroInAll3sgForms }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noZeroRealization }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noZeroRealization }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noZeroRealization }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noPersonMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noPersonMarking }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noZeroRealization }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noPersonMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noZeroRealization }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .zeroInAll3rdPersonForms }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noPersonMarking }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .zeroInAll3rdPersonForms }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .noZeroRealization }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noZeroRealization }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .zeroInSome3sgForms }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noZeroRealization }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .zeroInAll3sgForms }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .zeroInAll3sgForms }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPersonMarking }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noZeroRealization }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noZeroRealization }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noPersonMarking }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .zeroInAll3sgForms }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .zeroInAll3sgForms }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .zeroInAll3sgForms }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .zeroInAll3sgForms }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .zeroInAll3rdPersonForms }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noZeroRealization }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .zeroInAll3sgForms }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noZeroRealization }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noPersonMarking }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .zeroInAll3rdPersonForms }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .zeroInAll3sgForms }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .noZeroRealization }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noPersonMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .zeroInSome3sgForms }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noZeroRealization }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noZeroRealization }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noPersonMarking }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .noZeroRealization }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noZeroRealization }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noZeroRealization }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noZeroRealization }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noZeroRealization }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noPersonMarking }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPersonMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPersonMarking }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .noPersonMarking }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .noPersonMarking }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noZeroRealization }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noPersonMarking }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .noPersonMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noZeroRealization }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noZeroRealization }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noPersonMarking }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .zeroInAll3sgForms }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .zeroInAll3sgForms }
  , { walsCode := "so", language := "So", iso := "teu", value := .zeroInAll3rdPersonForms }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noZeroRealization }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .zeroInAll3rdPersonForms }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noZeroRealization }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noPersonMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPersonMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noZeroRealization }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noZeroRealization }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noPersonMarking }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .noZeroRealization }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .zeroInSome3sgForms }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noZeroRealization }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noZeroRealization }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noZeroRealization }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .zeroInAll3rdPersonForms }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .zeroInSome3sgForms }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPersonMarking }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noZeroRealization }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noPersonMarking }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .zeroInSome3sgForms }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noZeroRealization }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .noZeroRealization }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noZeroRealization }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .zeroInAll3rdPersonForms }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .zeroInSome3sgForms }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noZeroRealization }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .zeroInAll3sgForms }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .zeroInAll3sgForms }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noZeroRealization }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noZeroRealization }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noZeroRealization }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .noZeroRealization }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noZeroRealization }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noZeroRealization }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .noZeroRealization }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .zeroInAll3sgForms }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .zeroInAll3sgForms }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .zeroInSome3sgForms }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .noZeroRealization }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noZeroRealization }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noZeroRealization }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .noZeroRealization }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noPersonMarking }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .zeroInSome3sgForms }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noZeroRealization }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPersonMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noZeroRealization }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .zeroInAll3sgForms }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .zeroInSome3sgForms }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noPersonMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noPersonMarking }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .zeroInAll3sgForms }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .zeroInAll3sgForms }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noZeroRealization }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noZeroRealization }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noZeroRealization }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noZeroRealization }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noZeroRealization }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .zeroInAll3rdPersonForms }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .zeroInAll3rdPersonForms }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noPersonMarking }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .zeroInAll3rdPersonForms }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .noZeroRealization }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noZeroRealization }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .zeroInSome3sgForms }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPersonMarking }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .zeroInSome3sgForms }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .zeroInSome3sgForms }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noPersonMarking }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noPersonMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noZeroRealization }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPersonMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noZeroRealization }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noZeroRealization }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .zeroInAll3rdPersonForms }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noZeroRealization }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noZeroRealization }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noZeroRealization }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .noZeroRealization }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noZeroRealization }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noZeroRealization }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noPersonMarking }
  ]

-- Count verification
theorem total_count : allData.length = 380 := by native_decide

theorem count_noPersonMarking :
    (allData.filter (·.value == .noPersonMarking)).length = 96 := by native_decide
theorem count_noZeroRealization :
    (allData.filter (·.value == .noZeroRealization)).length = 181 := by native_decide
theorem count_zeroInSome3sgForms :
    (allData.filter (·.value == .zeroInSome3sgForms)).length = 21 := by native_decide
theorem count_zeroInAll3sgForms :
    (allData.filter (·.value == .zeroInAll3sgForms)).length = 45 := by native_decide
theorem count_zeroInAll3rdPersonForms :
    (allData.filter (·.value == .zeroInAll3rdPersonForms)).length = 36 := by native_decide
theorem count_zeroOnlyIn3rdNonsingular :
    (allData.filter (·.value == .zeroOnlyIn3rdNonsingular)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F103A
