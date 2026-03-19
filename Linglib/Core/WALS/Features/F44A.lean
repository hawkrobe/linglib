/-!
# WALS Feature 44A: Gender Distinctions in Independent Personal Pronouns
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 44A`.

Chapter 44, 378 languages.
-/

namespace Core.WALS.F44A

/-- WALS 44A values. -/
inductive GenderDistinctionsInIndependentPersonalPronouns where
  | in3rdPerson1stAndOr2ndPerson  -- In 3rd person + 1st and/or 2nd person (18 languages)
  | v3rdPersonOnlyButAlsoNonSingular  -- 3rd person only, but also non-singular (42 languages)
  | v3rdPersonSingularOnly  -- 3rd person singular only (61 languages)
  | v1stOr2ndPersonButNot3rd  -- 1st or 2nd person but not 3rd (2 languages)
  | v3rdPersonNonSingularOnly  -- 3rd person non-singular only (1 languages)
  | noGenderDistinctions  -- No gender distinctions (254 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 44A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : GenderDistinctionsInIndependentPersonalPronouns
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 44A dataset (378 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noGenderDistinctions }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .v3rdPersonSingularOnly }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noGenderDistinctions }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noGenderDistinctions }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noGenderDistinctions }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noGenderDistinctions }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .v3rdPersonSingularOnly }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGenderDistinctions }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .noGenderDistinctions }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .noGenderDistinctions }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .v3rdPersonSingularOnly }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .v3rdPersonSingularOnly }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noGenderDistinctions }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noGenderDistinctions }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noGenderDistinctions }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noGenderDistinctions }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noGenderDistinctions }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noGenderDistinctions }
  , { walsCode := "au", language := "Au", iso := "avt", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noGenderDistinctions }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .v3rdPersonSingularOnly }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noGenderDistinctions }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noGenderDistinctions }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noGenderDistinctions }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .v3rdPersonSingularOnly }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noGenderDistinctions }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .v3rdPersonSingularOnly }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noGenderDistinctions }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noGenderDistinctions }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noGenderDistinctions }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noGenderDistinctions }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .noGenderDistinctions }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .v3rdPersonSingularOnly }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noGenderDistinctions }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noGenderDistinctions }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noGenderDistinctions }
  , { walsCode := "bro", language := "Broken", iso := "tcs", value := .noGenderDistinctions }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .v3rdPersonSingularOnly }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .v1stOr2ndPersonButNot3rd }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .v3rdPersonSingularOnly }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .noGenderDistinctions }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noGenderDistinctions }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noGenderDistinctions }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGenderDistinctions }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .noGenderDistinctions }
  , { walsCode := "car", language := "Carib", iso := "car", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noGenderDistinctions }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noGenderDistinctions }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noGenderDistinctions }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noGenderDistinctions }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noGenderDistinctions }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .v3rdPersonSingularOnly }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noGenderDistinctions }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noGenderDistinctions }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noGenderDistinctions }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noGenderDistinctions }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noGenderDistinctions }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .noGenderDistinctions }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noGenderDistinctions }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .noGenderDistinctions }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .v3rdPersonSingularOnly }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .noGenderDistinctions }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .v3rdPersonSingularOnly }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGenderDistinctions }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .v3rdPersonNonSingularOnly }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noGenderDistinctions }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noGenderDistinctions }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .v3rdPersonSingularOnly }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noGenderDistinctions }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noGenderDistinctions }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .v3rdPersonSingularOnly }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noGenderDistinctions }
  , { walsCode := "eng", language := "English", iso := "eng", value := .v3rdPersonSingularOnly }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noGenderDistinctions }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noGenderDistinctions }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noGenderDistinctions }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGenderDistinctions }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGenderDistinctions }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noGenderDistinctions }
  , { walsCode := "fre", language := "French", iso := "fra", value := .v3rdPersonSingularOnly }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noGenderDistinctions }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noGenderDistinctions }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noGenderDistinctions }
  , { walsCode := "ger", language := "German", iso := "deu", value := .v3rdPersonSingularOnly }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noGenderDistinctions }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .v3rdPersonSingularOnly }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noGenderDistinctions }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noGenderDistinctions }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .v3rdPersonSingularOnly }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noGenderDistinctions }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noGenderDistinctions }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noGenderDistinctions }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .noGenderDistinctions }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noGenderDistinctions }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noGenderDistinctions }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGenderDistinctions }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noGenderDistinctions }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGenderDistinctions }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noGenderDistinctions }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noGenderDistinctions }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .v3rdPersonSingularOnly }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noGenderDistinctions }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noGenderDistinctions }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGenderDistinctions }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noGenderDistinctions }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .noGenderDistinctions }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .v1stOr2ndPersonButNot3rd }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .v3rdPersonSingularOnly }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .v3rdPersonSingularOnly }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noGenderDistinctions }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noGenderDistinctions }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noGenderDistinctions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noGenderDistinctions }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .noGenderDistinctions }
  , { walsCode := "kna", language := "Karitiâna", iso := "ktn", value := .noGenderDistinctions }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noGenderDistinctions }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .noGenderDistinctions }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noGenderDistinctions }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noGenderDistinctions }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noGenderDistinctions }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noGenderDistinctions }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noGenderDistinctions }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .v3rdPersonSingularOnly }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noGenderDistinctions }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .v3rdPersonSingularOnly }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noGenderDistinctions }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noGenderDistinctions }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noGenderDistinctions }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noGenderDistinctions }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noGenderDistinctions }
  , { walsCode := "klk", language := "Koh", iso := "xuo", value := .noGenderDistinctions }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .v3rdPersonSingularOnly }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "kjo", language := "Konjo", iso := "kjc", value := .noGenderDistinctions }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .v3rdPersonSingularOnly }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noGenderDistinctions }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noGenderDistinctions }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noGenderDistinctions }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .v3rdPersonSingularOnly }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .noGenderDistinctions }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noGenderDistinctions }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noGenderDistinctions }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noGenderDistinctions }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noGenderDistinctions }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noGenderDistinctions }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noGenderDistinctions }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noGenderDistinctions }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noGenderDistinctions }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noGenderDistinctions }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .noGenderDistinctions }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noGenderDistinctions }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noGenderDistinctions }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .noGenderDistinctions }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .v3rdPersonSingularOnly }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noGenderDistinctions }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .v3rdPersonSingularOnly }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noGenderDistinctions }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noGenderDistinctions }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noGenderDistinctions }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .noGenderDistinctions }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noGenderDistinctions }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noGenderDistinctions }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .v3rdPersonSingularOnly }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .v3rdPersonSingularOnly }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noGenderDistinctions }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGenderDistinctions }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGenderDistinctions }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .v3rdPersonSingularOnly }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noGenderDistinctions }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .v3rdPersonSingularOnly }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noGenderDistinctions }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noGenderDistinctions }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .noGenderDistinctions }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .v3rdPersonSingularOnly }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noGenderDistinctions }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noGenderDistinctions }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noGenderDistinctions }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noGenderDistinctions }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noGenderDistinctions }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noGenderDistinctions }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .noGenderDistinctions }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .v3rdPersonSingularOnly }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noGenderDistinctions }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noGenderDistinctions }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noGenderDistinctions }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .v3rdPersonSingularOnly }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noGenderDistinctions }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .noGenderDistinctions }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noGenderDistinctions }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noGenderDistinctions }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .v3rdPersonSingularOnly }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noGenderDistinctions }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noGenderDistinctions }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .v3rdPersonSingularOnly }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .v3rdPersonSingularOnly }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noGenderDistinctions }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noGenderDistinctions }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noGenderDistinctions }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .v3rdPersonSingularOnly }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .v3rdPersonSingularOnly }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noGenderDistinctions }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noGenderDistinctions }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noGenderDistinctions }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noGenderDistinctions }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noGenderDistinctions }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noGenderDistinctions }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noGenderDistinctions }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .noGenderDistinctions }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noGenderDistinctions }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .v3rdPersonSingularOnly }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noGenderDistinctions }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noGenderDistinctions }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noGenderDistinctions }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noGenderDistinctions }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noGenderDistinctions }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noGenderDistinctions }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .v3rdPersonSingularOnly }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .v3rdPersonSingularOnly }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .noGenderDistinctions }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .v3rdPersonSingularOnly }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noGenderDistinctions }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noGenderDistinctions }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .v3rdPersonSingularOnly }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .v3rdPersonSingularOnly }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noGenderDistinctions }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .noGenderDistinctions }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noGenderDistinctions }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noGenderDistinctions }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGenderDistinctions }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGenderDistinctions }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .noGenderDistinctions }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .v3rdPersonSingularOnly }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .v3rdPersonSingularOnly }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noGenderDistinctions }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noGenderDistinctions }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noGenderDistinctions }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noGenderDistinctions }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noGenderDistinctions }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .noGenderDistinctions }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .noGenderDistinctions }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noGenderDistinctions }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noGenderDistinctions }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .v3rdPersonSingularOnly }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noGenderDistinctions }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noGenderDistinctions }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noGenderDistinctions }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noGenderDistinctions }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noGenderDistinctions }
  , { walsCode := "so", language := "So", iso := "teu", value := .noGenderDistinctions }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noGenderDistinctions }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noGenderDistinctions }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noGenderDistinctions }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noGenderDistinctions }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noGenderDistinctions }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .v3rdPersonSingularOnly }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noGenderDistinctions }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noGenderDistinctions }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noGenderDistinctions }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noGenderDistinctions }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .noGenderDistinctions }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noGenderDistinctions }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGenderDistinctions }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noGenderDistinctions }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .noGenderDistinctions }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noGenderDistinctions }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .v3rdPersonSingularOnly }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noGenderDistinctions }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noGenderDistinctions }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noGenderDistinctions }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .noGenderDistinctions }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noGenderDistinctions }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noGenderDistinctions }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noGenderDistinctions }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .v3rdPersonSingularOnly }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noGenderDistinctions }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .noGenderDistinctions }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noGenderDistinctions }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .in3rdPerson1stAndOr2ndPerson }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .noGenderDistinctions }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noGenderDistinctions }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noGenderDistinctions }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .noGenderDistinctions }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .noGenderDistinctions }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noGenderDistinctions }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .v3rdPersonSingularOnly }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .noGenderDistinctions }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noGenderDistinctions }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noGenderDistinctions }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noGenderDistinctions }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noGenderDistinctions }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noGenderDistinctions }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noGenderDistinctions }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noGenderDistinctions }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noGenderDistinctions }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noGenderDistinctions }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .v3rdPersonSingularOnly }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noGenderDistinctions }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noGenderDistinctions }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .v3rdPersonSingularOnly }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noGenderDistinctions }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noGenderDistinctions }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noGenderDistinctions }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noGenderDistinctions }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noGenderDistinctions }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .v3rdPersonSingularOnly }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noGenderDistinctions }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noGenderDistinctions }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noGenderDistinctions }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .v3rdPersonSingularOnly }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noGenderDistinctions }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .v3rdPersonSingularOnly }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noGenderDistinctions }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noGenderDistinctions }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGenderDistinctions }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noGenderDistinctions }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noGenderDistinctions }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noGenderDistinctions }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noGenderDistinctions }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .v3rdPersonSingularOnly }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .noGenderDistinctions }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noGenderDistinctions }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .v3rdPersonOnlyButAlsoNonSingular }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noGenderDistinctions }
  ]

-- Count verification
theorem total_count : allData.length = 378 := by native_decide

theorem count_in3rdPerson1stAndOr2ndPerson :
    (allData.filter (·.value == .in3rdPerson1stAndOr2ndPerson)).length = 18 := by native_decide
theorem count_v3rdPersonOnlyButAlsoNonSingular :
    (allData.filter (·.value == .v3rdPersonOnlyButAlsoNonSingular)).length = 42 := by native_decide
theorem count_v3rdPersonSingularOnly :
    (allData.filter (·.value == .v3rdPersonSingularOnly)).length = 61 := by native_decide
theorem count_v1stOr2ndPersonButNot3rd :
    (allData.filter (·.value == .v1stOr2ndPersonButNot3rd)).length = 2 := by native_decide
theorem count_v3rdPersonNonSingularOnly :
    (allData.filter (·.value == .v3rdPersonNonSingularOnly)).length = 1 := by native_decide
theorem count_noGenderDistinctions :
    (allData.filter (·.value == .noGenderDistinctions)).length = 254 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F44A
