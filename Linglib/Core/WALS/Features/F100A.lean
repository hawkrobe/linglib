import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 100A: Alignment of Verbal Person Marking
@cite{siewierska-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 100A`.

Chapter 100, 380 languages.
-/

namespace Core.WALS.F100A

/-- WALS 100A values. -/
inductive VerbalPersonAlignment where
  | neutral  -- Neutral (84 languages)
  | accusative  -- Accusative (212 languages)
  | ergative  -- Ergative (19 languages)
  | active  -- Active (26 languages)
  | hierarchical  -- Hierarchical (11 languages)
  | split  -- Split (28 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 100A dataset (380 languages). -/
def allData : List (Datapoint VerbalPersonAlignment) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .accusative }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .accusative }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ergative }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .neutral }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .active }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .accusative }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .active }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .neutral }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .split }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .accusative }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .accusative }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .accusative }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .accusative }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .active }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .accusative }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .accusative }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .active }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .neutral }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .accusative }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .neutral }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .active }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .accusative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .accusative }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .split }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .ergative }
  , { walsCode := "au", language := "Au", iso := "avt", value := .accusative }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .hierarchical }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .neutral }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .hierarchical }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .neutral }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .accusative }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .neutral }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .neutral }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .accusative }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .accusative }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .neutral }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .ergative }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .accusative }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .accusative }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .accusative }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .accusative }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .accusative }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .accusative }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .accusative }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .accusative }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .neutral }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .neutral }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .neutral }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .accusative }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .split }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .accusative }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .accusative }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .active }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .accusative }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .ergative }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .accusative }
  , { walsCode := "car", language := "Carib", iso := "car", value := .ergative }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .ergative }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .split }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .ergative }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .hierarchical }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .accusative }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .split }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .neutral }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .split }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .accusative }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .accusative }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .accusative }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .accusative }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .accusative }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .accusative }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .accusative }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .hierarchical }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .accusative }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .accusative }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .accusative }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .neutral }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .accusative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .accusative }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .accusative }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .accusative }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .neutral }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .accusative }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .neutral }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .accusative }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .accusative }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .accusative }
  , { walsCode := "eng", language := "English", iso := "eng", value := .accusative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .neutral }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .accusative }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .accusative }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .accusative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .accusative }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .accusative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .accusative }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .accusative }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .accusative }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .neutral }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .accusative }
  , { walsCode := "ger", language := "German", iso := "deu", value := .accusative }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .neutral }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .accusative }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .neutral }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .accusative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .accusative }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .active }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .neutral }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .accusative }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .neutral }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .neutral }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .split }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .neutral }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .accusative }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .accusative }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .neutral }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .accusative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .accusative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .split }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .neutral }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .accusative }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .accusative }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .accusative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .accusative }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .neutral }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .accusative }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .active }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .neutral }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .accusative }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .neutral }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .accusative }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .accusative }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .accusative }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .accusative }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .ergative }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .neutral }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .accusative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .neutral }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .accusative }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .accusative }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .accusative }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .ergative }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .ergative }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .hierarchical }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .split }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .accusative }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .hierarchical }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .neutral }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .neutral }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .accusative }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .active }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .active }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .neutral }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .accusative }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .neutral }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .neutral }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .accusative }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .hierarchical }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .accusative }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .accusative }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .active }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .accusative }
  , { walsCode := "klk", language := "Koh", iso := "xuo", value := .neutral }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .accusative }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .accusative }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .ergative }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .neutral }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .accusative }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .accusative }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .neutral }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .neutral }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .neutral }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .neutral }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .accusative }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .accusative }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .accusative }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .accusative }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .neutral }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .neutral }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .ergative }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .active }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .accusative }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .active }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .accusative }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .accusative }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .accusative }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .neutral }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .neutral }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .hierarchical }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .active }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .accusative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .accusative }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .neutral }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .accusative }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .ergative }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .accusative }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .accusative }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .accusative }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .neutral }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .accusative }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .neutral }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .accusative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .neutral }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .hierarchical }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .accusative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .accusative }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .accusative }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .neutral }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .accusative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .accusative }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .neutral }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .accusative }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .accusative }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .neutral }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .neutral }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .accusative }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .accusative }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .accusative }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .split }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .neutral }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .active }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .accusative }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .neutral }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .accusative }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .accusative }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .accusative }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .accusative }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .ergative }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .accusative }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .accusative }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .accusative }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .accusative }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .accusative }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .accusative }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .active }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .accusative }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .accusative }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .neutral }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .accusative }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .split }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .split }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .accusative }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .accusative }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .split }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .neutral }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .neutral }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .accusative }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .accusative }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .accusative }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .hierarchical }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .neutral }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .accusative }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .accusative }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .active }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .accusative }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .accusative }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .accusative }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .accusative }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .neutral }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .accusative }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .accusative }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .accusative }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .hierarchical }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .split }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .accusative }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .accusative }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .accusative }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .accusative }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .accusative }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .accusative }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .neutral }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .split }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .accusative }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ergative }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .neutral }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .accusative }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .accusative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .accusative }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .neutral }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .accusative }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .accusative }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .accusative }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .accusative }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .accusative }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .accusative }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .neutral }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .neutral }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .neutral }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .neutral }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .neutral }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .accusative }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .accusative }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .accusative }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .split }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .accusative }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .neutral }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .accusative }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .accusative }
  , { walsCode := "so", language := "So", iso := "teu", value := .accusative }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .accusative }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .accusative }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .accusative }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .neutral }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .neutral }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .accusative }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .active }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .neutral }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .split }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .accusative }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .accusative }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .accusative }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .accusative }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .accusative }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .split }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .neutral }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .accusative }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .accusative }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .accusative }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .accusative }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .split }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .accusative }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .active }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .accusative }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .accusative }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .accusative }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .active }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .accusative }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .accusative }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .ergative }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .split }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .active }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .accusative }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .active }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .split }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .accusative }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .ergative }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .accusative }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .ergative }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .accusative }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .split }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .accusative }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .neutral }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .accusative }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .accusative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .neutral }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .split }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .accusative }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .accusative }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .neutral }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .accusative }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .accusative }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .active }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .accusative }
  , { walsCode := "was", language := "Washo", iso := "was", value := .split }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .accusative }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .accusative }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .accusative }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .active }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .accusative }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .neutral }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .accusative }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .neutral }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .active }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .accusative }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .neutral }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .split }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .split }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .neutral }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .neutral }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .split }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .neutral }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .active }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .accusative }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .split }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .ergative }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .accusative }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .accusative }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .accusative }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .accusative }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .accusative }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .neutral }
  ]

-- Count verification
theorem total_count : allData.length = 380 := by native_decide

theorem count_neutral :
    (allData.filter (·.value == .neutral)).length = 84 := by native_decide
theorem count_accusative :
    (allData.filter (·.value == .accusative)).length = 212 := by native_decide
theorem count_ergative :
    (allData.filter (·.value == .ergative)).length = 19 := by native_decide
theorem count_active :
    (allData.filter (·.value == .active)).length = 26 := by native_decide
theorem count_hierarchical :
    (allData.filter (·.value == .hierarchical)).length = 11 := by native_decide
theorem count_split :
    (allData.filter (·.value == .split)).length = 28 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F100A
