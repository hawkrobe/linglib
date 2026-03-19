import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 73A: The Optative
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 73A`.

Chapter 73, 319 languages.
-/

namespace Core.WALS.F73A

/-- WALS 73A values. -/
inductive Optative where
  | inflectionalOptativePresent  -- Inflectional optative present (48 languages)
  | inflectionalOptativeAbsent  -- Inflectional optative absent (271 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 73A dataset (319 languages). -/
def allData : List (Datapoint Optative) :=
  [ { walsCode := "abz", language := "Abaza", iso := "abq", value := .inflectionalOptativePresent }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .inflectionalOptativePresent }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .inflectionalOptativeAbsent }
  , { walsCode := "adt", language := "Adyghe (Temirgoy)", iso := "ady", value := .inflectionalOptativePresent }
  , { walsCode := "agl", language := "Aghul", iso := "agx", value := .inflectionalOptativePresent }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .inflectionalOptativeAbsent }
  , { walsCode := "awk", language := "Akwa", iso := "akw", value := .inflectionalOptativeAbsent }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .inflectionalOptativeAbsent }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .inflectionalOptativePresent }
  , { walsCode := "aso", language := "Altai (Southern)", iso := "alt", value := .inflectionalOptativeAbsent }
  , { walsCode := "alu", language := "Alutor", iso := "alr", value := .inflectionalOptativeAbsent }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .inflectionalOptativeAbsent }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .inflectionalOptativeAbsent }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .inflectionalOptativeAbsent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .inflectionalOptativeAbsent }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .inflectionalOptativeAbsent }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .inflectionalOptativeAbsent }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .inflectionalOptativeAbsent }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .inflectionalOptativePresent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .inflectionalOptativeAbsent }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .inflectionalOptativeAbsent }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .inflectionalOptativePresent }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .inflectionalOptativeAbsent }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .inflectionalOptativePresent }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .inflectionalOptativePresent }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .inflectionalOptativeAbsent }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .inflectionalOptativePresent }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .inflectionalOptativeAbsent }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .inflectionalOptativeAbsent }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .inflectionalOptativeAbsent }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .inflectionalOptativeAbsent }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .inflectionalOptativeAbsent }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .inflectionalOptativeAbsent }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .inflectionalOptativeAbsent }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .inflectionalOptativeAbsent }
  , { walsCode := "bez", language := "Bezhta", iso := "kap", value := .inflectionalOptativePresent }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .inflectionalOptativeAbsent }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .inflectionalOptativeAbsent }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .inflectionalOptativeAbsent }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .inflectionalOptativePresent }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .inflectionalOptativeAbsent }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .inflectionalOptativeAbsent }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .inflectionalOptativeAbsent }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .inflectionalOptativeAbsent }
  , { walsCode := "car", language := "Carib", iso := "car", value := .inflectionalOptativeAbsent }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .inflectionalOptativeAbsent }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .inflectionalOptativeAbsent }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .inflectionalOptativeAbsent }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .inflectionalOptativePresent }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .inflectionalOptativePresent }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .inflectionalOptativeAbsent }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .inflectionalOptativeAbsent }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .inflectionalOptativeAbsent }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .inflectionalOptativeAbsent }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .inflectionalOptativeAbsent }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .inflectionalOptativeAbsent }
  , { walsCode := "dbd", language := "Dabida", iso := "dav", value := .inflectionalOptativeAbsent }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .inflectionalOptativeAbsent }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .inflectionalOptativeAbsent }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .inflectionalOptativeAbsent }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .inflectionalOptativePresent }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .inflectionalOptativeAbsent }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .inflectionalOptativeAbsent }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .inflectionalOptativePresent }
  , { walsCode := "eng", language := "English", iso := "eng", value := .inflectionalOptativeAbsent }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .inflectionalOptativeAbsent }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .inflectionalOptativeAbsent }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .inflectionalOptativeAbsent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .inflectionalOptativePresent }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .inflectionalOptativeAbsent }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .inflectionalOptativeAbsent }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .inflectionalOptativeAbsent }
  , { walsCode := "fre", language := "French", iso := "fra", value := .inflectionalOptativeAbsent }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .inflectionalOptativeAbsent }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .inflectionalOptativeAbsent }
  , { walsCode := "gbk", language := "Gbaya (Northwest)", iso := "gya", value := .inflectionalOptativeAbsent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .inflectionalOptativePresent }
  , { walsCode := "ger", language := "German", iso := "deu", value := .inflectionalOptativeAbsent }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .inflectionalOptativePresent }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inflectionalOptativeAbsent }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .inflectionalOptativeAbsent }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .inflectionalOptativeAbsent }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .inflectionalOptativeAbsent }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .inflectionalOptativePresent }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .inflectionalOptativeAbsent }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .inflectionalOptativeAbsent }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .inflectionalOptativeAbsent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .inflectionalOptativeAbsent }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .inflectionalOptativeAbsent }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .inflectionalOptativeAbsent }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .inflectionalOptativePresent }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .inflectionalOptativeAbsent }
  , { walsCode := "her", language := "Herero", iso := "her", value := .inflectionalOptativeAbsent }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .inflectionalOptativeAbsent }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .inflectionalOptativeAbsent }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .inflectionalOptativeAbsent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .inflectionalOptativeAbsent }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .inflectionalOptativePresent }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .inflectionalOptativeAbsent }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .inflectionalOptativeAbsent }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .inflectionalOptativeAbsent }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .inflectionalOptativeAbsent }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .inflectionalOptativeAbsent }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .inflectionalOptativeAbsent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .inflectionalOptativeAbsent }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .inflectionalOptativeAbsent }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .inflectionalOptativePresent }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .inflectionalOptativeAbsent }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .inflectionalOptativeAbsent }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .inflectionalOptativeAbsent }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .inflectionalOptativeAbsent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .inflectionalOptativeAbsent }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .inflectionalOptativePresent }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .inflectionalOptativeAbsent }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .inflectionalOptativePresent }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .inflectionalOptativeAbsent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .inflectionalOptativeAbsent }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .inflectionalOptativeAbsent }
  , { walsCode := "krm", language := "Karaim", iso := "kdr", value := .inflectionalOptativePresent }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .inflectionalOptativeAbsent }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .inflectionalOptativeAbsent }
  , { walsCode := "ktz", language := "Kati (in Afghanistan)", iso := "bsh", value := .inflectionalOptativeAbsent }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .inflectionalOptativeAbsent }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .inflectionalOptativeAbsent }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .inflectionalOptativeAbsent }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .inflectionalOptativeAbsent }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .inflectionalOptativeAbsent }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .inflectionalOptativeAbsent }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .inflectionalOptativeAbsent }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .inflectionalOptativeAbsent }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .inflectionalOptativePresent }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .inflectionalOptativeAbsent }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .inflectionalOptativeAbsent }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .inflectionalOptativeAbsent }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .inflectionalOptativeAbsent }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .inflectionalOptativeAbsent }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .inflectionalOptativeAbsent }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .inflectionalOptativeAbsent }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .inflectionalOptativeAbsent }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .inflectionalOptativeAbsent }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .inflectionalOptativeAbsent }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .inflectionalOptativeAbsent }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .inflectionalOptativeAbsent }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .inflectionalOptativeAbsent }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .inflectionalOptativeAbsent }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .inflectionalOptativeAbsent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .inflectionalOptativeAbsent }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .inflectionalOptativeAbsent }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .inflectionalOptativeAbsent }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .inflectionalOptativeAbsent }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .inflectionalOptativeAbsent }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .inflectionalOptativeAbsent }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .inflectionalOptativePresent }
  , { walsCode := "kuq", language := "Kumyk", iso := "kum", value := .inflectionalOptativePresent }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .inflectionalOptativeAbsent }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .inflectionalOptativeAbsent }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .inflectionalOptativeAbsent }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .inflectionalOptativeAbsent }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .inflectionalOptativePresent }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .inflectionalOptativeAbsent }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .inflectionalOptativeAbsent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .inflectionalOptativeAbsent }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .inflectionalOptativeAbsent }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .inflectionalOptativeAbsent }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .inflectionalOptativeAbsent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .inflectionalOptativePresent }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .inflectionalOptativePresent }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .inflectionalOptativeAbsent }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .inflectionalOptativeAbsent }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .inflectionalOptativeAbsent }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .inflectionalOptativeAbsent }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .inflectionalOptativeAbsent }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .inflectionalOptativeAbsent }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .inflectionalOptativeAbsent }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .inflectionalOptativeAbsent }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .inflectionalOptativeAbsent }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .inflectionalOptativeAbsent }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .inflectionalOptativeAbsent }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .inflectionalOptativeAbsent }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .inflectionalOptativeAbsent }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .inflectionalOptativeAbsent }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .inflectionalOptativeAbsent }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .inflectionalOptativeAbsent }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .inflectionalOptativeAbsent }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .inflectionalOptativeAbsent }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .inflectionalOptativeAbsent }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .inflectionalOptativeAbsent }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .inflectionalOptativeAbsent }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .inflectionalOptativePresent }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .inflectionalOptativePresent }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .inflectionalOptativeAbsent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .inflectionalOptativeAbsent }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .inflectionalOptativePresent }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .inflectionalOptativeAbsent }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .inflectionalOptativeAbsent }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .inflectionalOptativeAbsent }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .inflectionalOptativeAbsent }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .inflectionalOptativeAbsent }
  , { walsCode := "mop", language := "Mopan", iso := "mop", value := .inflectionalOptativeAbsent }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .inflectionalOptativeAbsent }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .inflectionalOptativePresent }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .inflectionalOptativeAbsent }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .inflectionalOptativeAbsent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .inflectionalOptativeAbsent }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .inflectionalOptativeAbsent }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .inflectionalOptativeAbsent }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .inflectionalOptativeAbsent }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .inflectionalOptativeAbsent }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .inflectionalOptativePresent }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .inflectionalOptativeAbsent }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .inflectionalOptativeAbsent }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .inflectionalOptativeAbsent }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .inflectionalOptativeAbsent }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .inflectionalOptativeAbsent }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .inflectionalOptativeAbsent }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .inflectionalOptativeAbsent }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .inflectionalOptativeAbsent }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .inflectionalOptativeAbsent }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .inflectionalOptativePresent }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .inflectionalOptativeAbsent }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .inflectionalOptativeAbsent }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .inflectionalOptativeAbsent }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .inflectionalOptativeAbsent }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .inflectionalOptativeAbsent }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .inflectionalOptativeAbsent }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .inflectionalOptativeAbsent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .inflectionalOptativeAbsent }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .inflectionalOptativeAbsent }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .inflectionalOptativeAbsent }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .inflectionalOptativeAbsent }
  , { walsCode := "pta", language := "Paita", iso := "duf", value := .inflectionalOptativeAbsent }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .inflectionalOptativeAbsent }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .inflectionalOptativeAbsent }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .inflectionalOptativeAbsent }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .inflectionalOptativeAbsent }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .inflectionalOptativeAbsent }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .inflectionalOptativeAbsent }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .inflectionalOptativeAbsent }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .inflectionalOptativeAbsent }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .inflectionalOptativeAbsent }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .inflectionalOptativeAbsent }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .inflectionalOptativeAbsent }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .inflectionalOptativePresent }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .inflectionalOptativeAbsent }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .inflectionalOptativeAbsent }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .inflectionalOptativeAbsent }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .inflectionalOptativeAbsent }
  , { walsCode := "rav", language := "Romani (Ajia Varvara)", iso := "rmn", value := .inflectionalOptativeAbsent }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .inflectionalOptativeAbsent }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .inflectionalOptativePresent }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .inflectionalOptativePresent }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .inflectionalOptativeAbsent }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .inflectionalOptativeAbsent }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .inflectionalOptativeAbsent }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .inflectionalOptativeAbsent }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .inflectionalOptativeAbsent }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .inflectionalOptativeAbsent }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .inflectionalOptativeAbsent }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .inflectionalOptativeAbsent }
  , { walsCode := "shr", language := "Shor", iso := "cjs", value := .inflectionalOptativeAbsent }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .inflectionalOptativeAbsent }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .inflectionalOptativeAbsent }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .inflectionalOptativeAbsent }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .inflectionalOptativeAbsent }
  , { walsCode := "som", language := "Somali", iso := "som", value := .inflectionalOptativeAbsent }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .inflectionalOptativeAbsent }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .inflectionalOptativeAbsent }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .inflectionalOptativeAbsent }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .inflectionalOptativeAbsent }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .inflectionalOptativeAbsent }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .inflectionalOptativeAbsent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .inflectionalOptativeAbsent }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .inflectionalOptativeAbsent }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .inflectionalOptativeAbsent }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .inflectionalOptativePresent }
  , { walsCode := "taz", language := "Talysh (Azerbaijan)", iso := "tly", value := .inflectionalOptativePresent }
  , { walsCode := "tsp", language := "Tamil (Spoken)", iso := "tam", value := .inflectionalOptativeAbsent }
  , { walsCode := "tmi", language := "Tatar (Mishar)", iso := "tat", value := .inflectionalOptativeAbsent }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .inflectionalOptativeAbsent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .inflectionalOptativeAbsent }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .inflectionalOptativeAbsent }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .inflectionalOptativeAbsent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .inflectionalOptativeAbsent }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .inflectionalOptativeAbsent }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .inflectionalOptativeAbsent }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .inflectionalOptativeAbsent }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .inflectionalOptativePresent }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .inflectionalOptativePresent }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .inflectionalOptativeAbsent }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .inflectionalOptativeAbsent }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .inflectionalOptativeAbsent }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .inflectionalOptativeAbsent }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .inflectionalOptativeAbsent }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .inflectionalOptativeAbsent }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .inflectionalOptativeAbsent }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .inflectionalOptativeAbsent }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .inflectionalOptativeAbsent }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .inflectionalOptativeAbsent }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .inflectionalOptativeAbsent }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .inflectionalOptativeAbsent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .inflectionalOptativeAbsent }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .inflectionalOptativeAbsent }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .inflectionalOptativeAbsent }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .inflectionalOptativeAbsent }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .inflectionalOptativeAbsent }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .inflectionalOptativeAbsent }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .inflectionalOptativePresent }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .inflectionalOptativeAbsent }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .inflectionalOptativePresent }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .inflectionalOptativeAbsent }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .inflectionalOptativeAbsent }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .inflectionalOptativeAbsent }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .inflectionalOptativeAbsent }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .inflectionalOptativeAbsent }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .inflectionalOptativeAbsent }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .inflectionalOptativeAbsent }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .inflectionalOptativeAbsent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .inflectionalOptativeAbsent }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .inflectionalOptativePresent }
  ]

-- Count verification
theorem total_count : allData.length = 319 := by native_decide

theorem count_inflectionalOptativePresent :
    (allData.filter (·.value == .inflectionalOptativePresent)).length = 48 := by native_decide
theorem count_inflectionalOptativeAbsent :
    (allData.filter (·.value == .inflectionalOptativeAbsent)).length = 271 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F73A
