import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 102A: Verbal Person Marking
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 102A`.

Chapter 102, 378 languages.
-/

namespace Core.WALS.F102A

/-- WALS 102A values. -/
inductive VerbalPersonMarking where
  | noPersonMarking  -- No person marking (82 languages)
  | onlyTheAArgument  -- Only the A argument (73 languages)
  | onlyThePArgument  -- Only the P argument (24 languages)
  | aOrPArgument  -- A or P argument (6 languages)
  | bothTheAAndPArguments  -- Both the A and P arguments (193 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 102A dataset (378 languages). -/
def allData : List (Datapoint VerbalPersonMarking) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .onlyThePArgument }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .bothTheAAndPArguments }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .bothTheAAndPArguments }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noPersonMarking }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .bothTheAAndPArguments }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .bothTheAAndPArguments }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .bothTheAAndPArguments }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noPersonMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .bothTheAAndPArguments }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .bothTheAAndPArguments }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .bothTheAAndPArguments }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .bothTheAAndPArguments }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .bothTheAAndPArguments }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .bothTheAAndPArguments }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .onlyThePArgument }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .bothTheAAndPArguments }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .bothTheAAndPArguments }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noPersonMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .bothTheAAndPArguments }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPersonMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .bothTheAAndPArguments }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .onlyTheAArgument }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .bothTheAAndPArguments }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .bothTheAAndPArguments }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .onlyTheAArgument }
  , { walsCode := "au", language := "Au", iso := "avt", value := .bothTheAAndPArguments }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .aOrPArgument }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noPersonMarking }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .bothTheAAndPArguments }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noPersonMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .bothTheAAndPArguments }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noPersonMarking }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .noPersonMarking }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .bothTheAAndPArguments }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .onlyTheAArgument }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noPersonMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .bothTheAAndPArguments }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .onlyThePArgument }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .bothTheAAndPArguments }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .bothTheAAndPArguments }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .bothTheAAndPArguments }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .bothTheAAndPArguments }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .bothTheAAndPArguments }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .bothTheAAndPArguments }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .onlyTheAArgument }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noPersonMarking }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .noPersonMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noPersonMarking }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .onlyTheAArgument }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .bothTheAAndPArguments }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .onlyTheAArgument }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .bothTheAAndPArguments }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .bothTheAAndPArguments }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .bothTheAAndPArguments }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .onlyThePArgument }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .onlyTheAArgument }
  , { walsCode := "car", language := "Carib", iso := "car", value := .bothTheAAndPArguments }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .onlyThePArgument }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .bothTheAAndPArguments }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .onlyTheAArgument }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .aOrPArgument }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .onlyTheAArgument }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .bothTheAAndPArguments }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noPersonMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .bothTheAAndPArguments }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .bothTheAAndPArguments }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .bothTheAAndPArguments }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .bothTheAAndPArguments }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .bothTheAAndPArguments }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .bothTheAAndPArguments }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .onlyTheAArgument }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .bothTheAAndPArguments }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .bothTheAAndPArguments }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .onlyTheAArgument }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .onlyTheAArgument }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .bothTheAAndPArguments }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noPersonMarking }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .onlyTheAArgument }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .bothTheAAndPArguments }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .bothTheAAndPArguments }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .onlyTheAArgument }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .bothTheAAndPArguments }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noPersonMarking }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .onlyTheAArgument }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .onlyTheAArgument }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .bothTheAAndPArguments }
  , { walsCode := "eng", language := "English", iso := "eng", value := .onlyTheAArgument }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noPersonMarking }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .bothTheAAndPArguments }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .onlyTheAArgument }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .bothTheAAndPArguments }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .bothTheAAndPArguments }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .onlyTheAArgument }
  , { walsCode := "fre", language := "French", iso := "fra", value := .onlyTheAArgument }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .bothTheAAndPArguments }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .onlyTheAArgument }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noPersonMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .bothTheAAndPArguments }
  , { walsCode := "ger", language := "German", iso := "deu", value := .onlyTheAArgument }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noPersonMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .bothTheAAndPArguments }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPersonMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .bothTheAAndPArguments }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .bothTheAAndPArguments }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .bothTheAAndPArguments }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noPersonMarking }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .bothTheAAndPArguments }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noPersonMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noPersonMarking }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .bothTheAAndPArguments }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .noPersonMarking }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .bothTheAAndPArguments }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .onlyTheAArgument }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPersonMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .onlyTheAArgument }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .onlyTheAArgument }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .bothTheAAndPArguments }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPersonMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .bothTheAAndPArguments }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .onlyTheAArgument }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .bothTheAAndPArguments }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .onlyTheAArgument }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noPersonMarking }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .onlyThePArgument }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .bothTheAAndPArguments }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPersonMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .onlyThePArgument }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noPersonMarking }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .aOrPArgument }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .onlyTheAArgument }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .onlyTheAArgument }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .onlyTheAArgument }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .bothTheAAndPArguments }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPersonMarking }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .bothTheAAndPArguments }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPersonMarking }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .aOrPArgument }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .onlyTheAArgument }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .bothTheAAndPArguments }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .bothTheAAndPArguments }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .onlyThePArgument }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .bothTheAAndPArguments }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .bothTheAAndPArguments }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .bothTheAAndPArguments }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .bothTheAAndPArguments }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPersonMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPersonMarking }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .onlyThePArgument }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .bothTheAAndPArguments }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .onlyTheAArgument }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noPersonMarking }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .onlyTheAArgument }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noPersonMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPersonMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .bothTheAAndPArguments }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .aOrPArgument }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .bothTheAAndPArguments }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .onlyThePArgument }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .bothTheAAndPArguments }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .onlyTheAArgument }
  , { walsCode := "klk", language := "Koh", iso := "xuo", value := .noPersonMarking }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .bothTheAAndPArguments }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .bothTheAAndPArguments }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .bothTheAAndPArguments }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noPersonMarking }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .bothTheAAndPArguments }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .bothTheAAndPArguments }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noPersonMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPersonMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noPersonMarking }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .noPersonMarking }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .bothTheAAndPArguments }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .bothTheAAndPArguments }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .bothTheAAndPArguments }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .bothTheAAndPArguments }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noPersonMarking }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noPersonMarking }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .onlyThePArgument }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .bothTheAAndPArguments }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .bothTheAAndPArguments }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .bothTheAAndPArguments }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .onlyTheAArgument }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .bothTheAAndPArguments }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .bothTheAAndPArguments }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noPersonMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPersonMarking }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .bothTheAAndPArguments }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .bothTheAAndPArguments }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .bothTheAAndPArguments }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .bothTheAAndPArguments }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .bothTheAAndPArguments }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .bothTheAAndPArguments }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .onlyTheAArgument }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .bothTheAAndPArguments }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .bothTheAAndPArguments }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPersonMarking }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .bothTheAAndPArguments }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPersonMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .bothTheAAndPArguments }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPersonMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .bothTheAAndPArguments }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .bothTheAAndPArguments }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .bothTheAAndPArguments }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .bothTheAAndPArguments }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noPersonMarking }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .bothTheAAndPArguments }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .bothTheAAndPArguments }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .noPersonMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .onlyTheAArgument }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .bothTheAAndPArguments }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPersonMarking }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noPersonMarking }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .onlyTheAArgument }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .bothTheAAndPArguments }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .onlyTheAArgument }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .bothTheAAndPArguments }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .noPersonMarking }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .bothTheAAndPArguments }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .bothTheAAndPArguments }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noPersonMarking }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .bothTheAAndPArguments }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .bothTheAAndPArguments }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .onlyThePArgument }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .bothTheAAndPArguments }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .onlyTheAArgument }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .bothTheAAndPArguments }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .onlyThePArgument }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .onlyThePArgument }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .bothTheAAndPArguments }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .onlyTheAArgument }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .bothTheAAndPArguments }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .bothTheAAndPArguments }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .bothTheAAndPArguments }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .bothTheAAndPArguments }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noPersonMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .onlyTheAArgument }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .bothTheAAndPArguments }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .bothTheAAndPArguments }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .bothTheAAndPArguments }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .bothTheAAndPArguments }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .bothTheAAndPArguments }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noPersonMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noPersonMarking }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .bothTheAAndPArguments }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .onlyThePArgument }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .onlyTheAArgument }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .bothTheAAndPArguments }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noPersonMarking }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .onlyTheAArgument }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .bothTheAAndPArguments }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .bothTheAAndPArguments }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .onlyTheAArgument }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .bothTheAAndPArguments }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .bothTheAAndPArguments }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .bothTheAAndPArguments }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPersonMarking }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .bothTheAAndPArguments }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .onlyThePArgument }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .onlyThePArgument }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .bothTheAAndPArguments }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .onlyTheAArgument }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .bothTheAAndPArguments }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .bothTheAAndPArguments }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .bothTheAAndPArguments }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .bothTheAAndPArguments }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .bothTheAAndPArguments }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .onlyTheAArgument }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noPersonMarking }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .bothTheAAndPArguments }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .bothTheAAndPArguments }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .bothTheAAndPArguments }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noPersonMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .bothTheAAndPArguments }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .bothTheAAndPArguments }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .onlyTheAArgument }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noPersonMarking }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .onlyTheAArgument }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .bothTheAAndPArguments }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .onlyTheAArgument }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .bothTheAAndPArguments }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .bothTheAAndPArguments }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .onlyTheAArgument }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noPersonMarking }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPersonMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPersonMarking }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .noPersonMarking }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .noPersonMarking }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .bothTheAAndPArguments }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .onlyThePArgument }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .onlyThePArgument }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .onlyTheAArgument }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .bothTheAAndPArguments }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noPersonMarking }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .bothTheAAndPArguments }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .bothTheAAndPArguments }
  , { walsCode := "so", language := "So", iso := "teu", value := .onlyTheAArgument }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .bothTheAAndPArguments }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .bothTheAAndPArguments }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .onlyTheAArgument }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noPersonMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPersonMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .bothTheAAndPArguments }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .onlyTheAArgument }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noPersonMarking }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .bothTheAAndPArguments }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .bothTheAAndPArguments }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .bothTheAAndPArguments }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .bothTheAAndPArguments }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .onlyTheAArgument }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .bothTheAAndPArguments }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .onlyTheAArgument }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPersonMarking }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .onlyTheAArgument }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .onlyThePArgument }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .bothTheAAndPArguments }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .onlyTheAArgument }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .aOrPArgument }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .bothTheAAndPArguments }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .bothTheAAndPArguments }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .bothTheAAndPArguments }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .onlyTheAArgument }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .onlyTheAArgument }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .bothTheAAndPArguments }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .bothTheAAndPArguments }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .onlyTheAArgument }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .onlyThePArgument }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .bothTheAAndPArguments }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .onlyTheAArgument }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .bothTheAAndPArguments }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .bothTheAAndPArguments }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .bothTheAAndPArguments }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .onlyTheAArgument }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .bothTheAAndPArguments }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .onlyTheAArgument }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .bothTheAAndPArguments }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .bothTheAAndPArguments }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .bothTheAAndPArguments }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .bothTheAAndPArguments }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noPersonMarking }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .onlyTheAArgument }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .bothTheAAndPArguments }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPersonMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .bothTheAAndPArguments }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .onlyTheAArgument }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .onlyTheAArgument }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noPersonMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .onlyThePArgument }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .bothTheAAndPArguments }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .bothTheAAndPArguments }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .bothTheAAndPArguments }
  , { walsCode := "was", language := "Washo", iso := "was", value := .bothTheAAndPArguments }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .onlyTheAArgument }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .onlyTheAArgument }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .onlyTheAArgument }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .bothTheAAndPArguments }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .bothTheAAndPArguments }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noPersonMarking }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .onlyTheAArgument }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .noPersonMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .bothTheAAndPArguments }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .onlyThePArgument }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPersonMarking }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .onlyThePArgument }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .bothTheAAndPArguments }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noPersonMarking }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noPersonMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .bothTheAAndPArguments }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPersonMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .bothTheAAndPArguments }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .onlyTheAArgument }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .bothTheAAndPArguments }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .bothTheAAndPArguments }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .bothTheAAndPArguments }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .bothTheAAndPArguments }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .bothTheAAndPArguments }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .bothTheAAndPArguments }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .bothTheAAndPArguments }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noPersonMarking }
  ]

-- Count verification
theorem total_count : allData.length = 378 := by native_decide

theorem count_noPersonMarking :
    (allData.filter (·.value == .noPersonMarking)).length = 82 := by native_decide
theorem count_onlyTheAArgument :
    (allData.filter (·.value == .onlyTheAArgument)).length = 73 := by native_decide
theorem count_onlyThePArgument :
    (allData.filter (·.value == .onlyThePArgument)).length = 24 := by native_decide
theorem count_aOrPArgument :
    (allData.filter (·.value == .aOrPArgument)).length = 6 := by native_decide
theorem count_bothTheAAndPArguments :
    (allData.filter (·.value == .bothTheAAndPArguments)).length = 193 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F102A
