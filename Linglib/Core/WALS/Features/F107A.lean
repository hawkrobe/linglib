/-!
# WALS Feature 107A: Passive Constructions
@cite{siewierska-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 107A`.

Chapter 107, 373 languages.
-/

namespace Core.WALS.F107A

/-- WALS 107A values. -/
inductive PassiveType where
  | present  -- Present (162 languages)
  | absent  -- Absent (211 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 107A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PassiveType
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 107A dataset (373 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .present }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .absent }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .absent }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .absent }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .absent }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .absent }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .absent }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .absent }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .present }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .absent }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .present }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .absent }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .present }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .present }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .absent }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .absent }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .present }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .absent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .present }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .present }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .absent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .present }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .absent }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .absent }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .absent }
  , { walsCode := "au", language := "Au", iso := "avt", value := .absent }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .absent }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .absent }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .present }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .absent }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .absent }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .absent }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .absent }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .absent }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .absent }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .present }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .present }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .absent }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .absent }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .present }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .present }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .present }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .present }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .present }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .absent }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .absent }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .absent }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .absent }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .absent }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .present }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .absent }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .absent }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .absent }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .absent }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .absent }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .absent }
  , { walsCode := "car", language := "Carib", iso := "car", value := .present }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .absent }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .present }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .present }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .absent }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .present }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .absent }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .absent }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .absent }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .absent }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .absent }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .present }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .present }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .present }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .present }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .present }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .absent }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .present }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .present }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .absent }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .absent }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .present }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .absent }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .present }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .present }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .present }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .present }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .present }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .absent }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .present }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .absent }
  , { walsCode := "eng", language := "English", iso := "eng", value := .present }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .absent }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .absent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .present }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .absent }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .present }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .present }
  , { walsCode := "fre", language := "French", iso := "fra", value := .present }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .present }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .present }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .absent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .present }
  , { walsCode := "ger", language := "German", iso := "deu", value := .present }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .absent }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .absent }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .present }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .present }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .present }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .absent }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .absent }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .absent }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .absent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .absent }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .present }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .present }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .absent }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .absent }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .present }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .present }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .present }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .present }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .present }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .absent }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .present }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .present }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .absent }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .absent }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .present }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .absent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .absent }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .present }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .absent }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .absent }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .present }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .present }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .present }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .present }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .present }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .absent }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .absent }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .absent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .present }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .present }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .absent }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .present }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .present }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .present }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .present }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .absent }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .present }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .absent }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .present }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .absent }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .present }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .absent }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .absent }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .absent }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .absent }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .absent }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .present }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .present }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .present }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .absent }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .absent }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .present }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .absent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .present }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .absent }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .present }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .present }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .present }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .present }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .present }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .present }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .present }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .present }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .absent }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .absent }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .absent }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .absent }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .absent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .absent }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .present }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .absent }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .absent }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .present }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .absent }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .present }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .present }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .absent }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .absent }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .present }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .present }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .present }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .absent }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .absent }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .absent }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .present }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .absent }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .present }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .absent }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .present }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .present }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .absent }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .present }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .absent }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .present }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .present }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .absent }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .absent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .absent }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .absent }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .absent }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .absent }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .absent }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .present }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .absent }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .absent }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .absent }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .absent }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .absent }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .absent }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .absent }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .present }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .absent }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .present }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .present }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .present }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .absent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .present }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .present }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .absent }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .absent }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .present }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .present }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .absent }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .present }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .present }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .absent }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .absent }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .absent }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .absent }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .present }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .absent }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .present }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .present }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .present }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .absent }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .absent }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .present }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .absent }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .absent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .absent }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .present }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .absent }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .absent }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .absent }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .present }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .present }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .present }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .present }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .present }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .absent }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .present }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .present }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .absent }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .absent }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .present }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .absent }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .present }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .absent }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .present }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .absent }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .present }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .present }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .absent }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .absent }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .absent }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .absent }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .present }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .absent }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .absent }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .absent }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .absent }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .absent }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .present }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .absent }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .absent }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .absent }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .absent }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .absent }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .present }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .absent }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .absent }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .present }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .present }
  , { walsCode := "so", language := "So", iso := "teu", value := .present }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .present }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .present }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .absent }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .present }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .absent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .present }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .present }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .absent }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .absent }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .present }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .absent }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .absent }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .absent }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .present }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .absent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .present }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .absent }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .absent }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .absent }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .present }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .absent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .absent }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .absent }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .absent }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .absent }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .absent }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .absent }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .absent }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .absent }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .absent }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .absent }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .absent }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .present }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .absent }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .present }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .present }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .present }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .present }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .absent }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .absent }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .absent }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .absent }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .absent }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .absent }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .absent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .present }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .absent }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .absent }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .absent }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .present }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .present }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .absent }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .absent }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .present }
  , { walsCode := "was", language := "Washo", iso := "was", value := .absent }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .absent }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .present }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .absent }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .absent }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .absent }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .present }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .present }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .absent }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .absent }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .present }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .absent }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .absent }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .absent }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .absent }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .absent }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .absent }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .absent }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .present }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .absent }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .present }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .present }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .absent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .present }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .present }
  ]

-- Count verification
theorem total_count : allData.length = 373 := by native_decide

theorem count_present :
    (allData.filter (·.value == .present)).length = 162 := by native_decide
theorem count_absent :
    (allData.filter (·.value == .absent)).length = 211 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F107A
