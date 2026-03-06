/-!
# WALS Feature 104A: Order of Person Markers on the Verb
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 104A`.

Chapter 104, 379 languages.
-/

namespace Core.WALS.F104A

/-- WALS 104A values. -/
inductive OrderOfPersonMarkersOnTheVerb where
  | aAndPDoNotOrDoNotBothOccurOnTheVerb  -- A and P do not or do not both occur on the verb (187 languages)
  | aPrecedesP  -- A precedes P (96 languages)
  | pPrecedesA  -- P precedes A (57 languages)
  | bothOrdersOfAAndPOccur  -- Both orders of A and P occur (19 languages)
  | aAndPAreFused  -- A and P are fused (20 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 104A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : OrderOfPersonMarkersOnTheVerb
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 104A dataset (379 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .aPrecedesP }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .pPrecedesA }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .aPrecedesP }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .aAndPAreFused }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .aAndPAreFused }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .aPrecedesP }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .aPrecedesP }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .pPrecedesA }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .pPrecedesA }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .aPrecedesP }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .aPrecedesP }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .aPrecedesP }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .aPrecedesP }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .aPrecedesP }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .aPrecedesP }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .pPrecedesA }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .pPrecedesA }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "au", language := "Au", iso := "avt", value := .aPrecedesP }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .aAndPAreFused }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .aPrecedesP }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .pPrecedesA }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .pPrecedesA }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .aPrecedesP }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .aPrecedesP }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .aPrecedesP }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .aPrecedesP }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .aPrecedesP }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .aPrecedesP }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .pPrecedesA }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .pPrecedesA }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .aPrecedesP }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "car", language := "Carib", iso := "car", value := .aAndPAreFused }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .aPrecedesP }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .aPrecedesP }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .aPrecedesP }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .aPrecedesP }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .aPrecedesP }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .pPrecedesA }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .pPrecedesA }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .aAndPAreFused }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .aPrecedesP }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .pPrecedesA }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .pPrecedesA }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .pPrecedesA }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .aPrecedesP }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .aPrecedesP }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .aPrecedesP }
  , { walsCode := "eng", language := "English", iso := "eng", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .aPrecedesP }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .aPrecedesP }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .aPrecedesP }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "fre", language := "French", iso := "fra", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .pPrecedesA }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .pPrecedesA }
  , { walsCode := "ger", language := "German", iso := "deu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .aAndPAreFused }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .pPrecedesA }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .aPrecedesP }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .aAndPAreFused }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .aPrecedesP }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .pPrecedesA }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .aPrecedesP }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .aPrecedesP }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .pPrecedesA }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .aAndPAreFused }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .aPrecedesP }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .pPrecedesA }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .aAndPAreFused }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .aPrecedesP }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .aAndPAreFused }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .aPrecedesP }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .aPrecedesP }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .aPrecedesP }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .aPrecedesP }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .aPrecedesP }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .pPrecedesA }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "klk", language := "Koh", iso := "xuo", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .aPrecedesP }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .aPrecedesP }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .aPrecedesP }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .aPrecedesP }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .aPrecedesP }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .aAndPAreFused }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .aPrecedesP }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .aPrecedesP }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .pPrecedesA }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .aPrecedesP }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .aPrecedesP }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .pPrecedesA }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .aPrecedesP }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .aPrecedesP }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .aPrecedesP }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .aAndPAreFused }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .pPrecedesA }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .aPrecedesP }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .aAndPAreFused }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .aPrecedesP }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .aPrecedesP }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .aPrecedesP }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .aAndPAreFused }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .aPrecedesP }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .pPrecedesA }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .aPrecedesP }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .aPrecedesP }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .aPrecedesP }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .aPrecedesP }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .pPrecedesA }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .aPrecedesP }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .aPrecedesP }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .pPrecedesA }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .aPrecedesP }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .pPrecedesA }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .pPrecedesA }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .aPrecedesP }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .aPrecedesP }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .aPrecedesP }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .pPrecedesA }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .aPrecedesP }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .aAndPAreFused }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .aPrecedesP }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .aPrecedesP }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .aPrecedesP }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .aPrecedesP }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .aPrecedesP }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .aPrecedesP }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .pPrecedesA }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .aPrecedesP }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .aPrecedesP }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .aPrecedesP }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .aPrecedesP }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .pPrecedesA }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .pPrecedesA }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .pPrecedesA }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .pPrecedesA }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .pPrecedesA }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .aPrecedesP }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .pPrecedesA }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .pPrecedesA }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .aPrecedesP }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .pPrecedesA }
  , { walsCode := "so", language := "So", iso := "teu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .pPrecedesA }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .pPrecedesA }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .aPrecedesP }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .pPrecedesA }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .pPrecedesA }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .pPrecedesA }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .aPrecedesP }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .pPrecedesA }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .aAndPAreFused }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .pPrecedesA }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .pPrecedesA }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .pPrecedesA }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .pPrecedesA }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .aPrecedesP }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .pPrecedesA }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .pPrecedesA }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .pPrecedesA }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .aPrecedesP }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .pPrecedesA }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .pPrecedesA }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .aPrecedesP }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .pPrecedesA }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .aPrecedesP }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .aAndPAreFused }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .aPrecedesP }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .aPrecedesP }
  , { walsCode := "was", language := "Washo", iso := "was", value := .pPrecedesA }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .aPrecedesP }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .aPrecedesP }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .aPrecedesP }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .pPrecedesA }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .bothOrdersOfAAndPOccur }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .aAndPAreFused }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .aAndPAreFused }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .aPrecedesP }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .aPrecedesP }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .aAndPAreFused }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .aPrecedesP }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .aAndPDoNotOrDoNotBothOccurOnTheVerb }
  ]

-- Count verification
theorem total_count : allData.length = 379 := by native_decide

theorem count_aAndPDoNotOrDoNotBothOccurOnTheVerb :
    (allData.filter (·.value == .aAndPDoNotOrDoNotBothOccurOnTheVerb)).length = 187 := by native_decide
theorem count_aPrecedesP :
    (allData.filter (·.value == .aPrecedesP)).length = 96 := by native_decide
theorem count_pPrecedesA :
    (allData.filter (·.value == .pPrecedesA)).length = 57 := by native_decide
theorem count_bothOrdersOfAAndPOccur :
    (allData.filter (·.value == .bothOrdersOfAAndPOccur)).length = 19 := by native_decide
theorem count_aAndPAreFused :
    (allData.filter (·.value == .aAndPAreFused)).length = 20 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F104A
