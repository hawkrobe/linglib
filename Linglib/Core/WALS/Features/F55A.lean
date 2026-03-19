/-!
# WALS Feature 55A: Numeral Classifiers
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 55A`.

Chapter 55, 400 languages.
-/

namespace Core.WALS.F55A

/-- WALS 55A values. -/
inductive NumeralClassifiers where
  | absent  -- Absent (260 languages)
  | optional  -- Optional (62 languages)
  | obligatory  -- Obligatory (78 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 55A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NumeralClassifiers
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 55A dataset (400 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .absent }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .absent }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .absent }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .obligatory }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .absent }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .optional }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .absent }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .absent }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .absent }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .obligatory }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .absent }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .absent }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .absent }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .absent }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .absent }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .absent }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .absent }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .absent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .absent }
  , { walsCode := "ako", language := "Arabic (Kormakiti)", iso := "acy", value := .absent }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .absent }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .absent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .absent }
  , { walsCode := "arz", language := "Armenian (Iranian)", iso := "hye", value := .optional }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .absent }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .obligatory }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .absent }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .absent }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .obligatory }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .absent }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .absent }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .optional }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .absent }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .optional }
  , { walsCode := "bnv", language := "Baniva", iso := "bvv", value := .obligatory }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .absent }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .absent }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .absent }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .optional }
  , { walsCode := "beg", language := "Begak-Ida'an", iso := "dbj", value := .optional }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .obligatory }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .obligatory }
  , { walsCode := "bit", language := "Biatah", iso := "bth", value := .optional }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .obligatory }
  , { walsCode := "bor", language := "Bora", iso := "boa", value := .optional }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .absent }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .absent }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .absent }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .obligatory }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .absent }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .absent }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .obligatory }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .absent }
  , { walsCode := "crq", language := "Carrier", iso := "crx", value := .obligatory }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .absent }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .obligatory }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .obligatory }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .absent }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .optional }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .optional }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .absent }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .absent }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .absent }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .absent }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .absent }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .absent }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .absent }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .obligatory }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .absent }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .absent }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .absent }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .obligatory }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .absent }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .absent }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .absent }
  , { walsCode := "cul", language := "Culina", iso := "cul", value := .absent }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .absent }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .absent }
  , { walsCode := "dat", language := "Datooga", iso := "tcc", value := .absent }
  , { walsCode := "den", language := "Dení", iso := "dny", value := .absent }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .absent }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .absent }
  , { walsCode := "dob", language := "Dobel", iso := "kvo", value := .optional }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .absent }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .absent }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .absent }
  , { walsCode := "eng", language := "English", iso := "eng", value := .absent }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .absent }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .absent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .absent }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .obligatory }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .absent }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .absent }
  , { walsCode := "fre", language := "French", iso := "fra", value := .absent }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .absent }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .absent }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .absent }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .obligatory }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .absent }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .absent }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .absent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .absent }
  , { walsCode := "ger", language := "German", iso := "deu", value := .absent }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .optional }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .absent }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .absent }
  , { walsCode := "gdf", language := "Guduf", iso := "gdf", value := .absent }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .absent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .optional }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .optional }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .absent }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .absent }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .absent }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .absent }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .absent }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .obligatory }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .absent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .optional }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .absent }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .absent }
  , { walsCode := "hyo", language := "Hyow", iso := "csh", value := .obligatory }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .absent }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .absent }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .absent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .absent }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .optional }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .absent }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .absent }
  , { walsCode := "jah", language := "Jahai", iso := "jhi", value := .optional }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .obligatory }
  , { walsCode := "jmm", language := "Jamamadi", iso := "jaa", value := .absent }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .absent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .obligatory }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .absent }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .optional }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .absent }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .absent }
  , { walsCode := "klp", language := "Kalapuya", iso := "kyl", value := .obligatory }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .obligatory }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .obligatory }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .absent }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .absent }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .absent }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .obligatory }
  , { walsCode := "kbr", language := "Kayan (Baram)", iso := "kys", value := .optional }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .obligatory }
  , { walsCode := "klt", language := "Kelabit", iso := "kzi", value := .absent }
  , { walsCode := "keu", language := "Kenyah (Uma' Lung)", iso := "keu", value := .optional }
  , { walsCode := "keo", language := "Keo", iso := "xxk", value := .obligatory }
  , { walsCode := "ktp", language := "Ketapang", iso := "xdy", value := .obligatory }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .absent }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .absent }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .obligatory }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .optional }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .optional }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .obligatory }
  , { walsCode := "khu", language := "Khumi", iso := "cnk", value := .obligatory }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .obligatory }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .absent }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .obligatory }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .absent }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .absent }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .absent }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .absent }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .absent }
  , { walsCode := "kag", language := "Komering", iso := "kge", value := .optional }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .absent }
  , { walsCode := "knu", language := "Konua", iso := "kyx", value := .absent }
  , { walsCode := "krf", language := "Korafe", iso := "kpr", value := .absent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .obligatory }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .absent }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .absent }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .obligatory }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .absent }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .absent }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .absent }
  , { walsCode := "kua", language := "Kualan", iso := "sdm", value := .obligatory }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .absent }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .obligatory }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .absent }
  , { walsCode := "lch", language := "Lachi", iso := "lbt", value := .obligatory }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .obligatory }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .obligatory }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .absent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .absent }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .obligatory }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .absent }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .absent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .absent }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .absent }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .absent }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .obligatory }
  , { walsCode := "lov", language := "Loven", iso := "lbo", value := .obligatory }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .absent }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .absent }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .absent }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .absent }
  , { walsCode := "lud", language := "Lun Dayeh", iso := "lnd", value := .optional }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .absent }
  , { walsCode := "lur", language := "Luri", iso := "lrc", value := .optional }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .absent }
  , { walsCode := "msy", language := "Magar (Syangja)", iso := "mrd", value := .absent }
  , { walsCode := "mhm", language := "Mah Meri", iso := "mhe", value := .optional }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .absent }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .optional }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .absent }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .absent }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .absent }
  , { walsCode := "mli", language := "Mali", iso := "gcc", value := .absent }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .absent }
  , { walsCode := "mnr", language := "Mandar", iso := "mdr", value := .optional }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .obligatory }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .absent }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .absent }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .absent }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .absent }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .absent }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .absent }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .absent }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .absent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .optional }
  , { walsCode := "mzn", language := "Mazanderani", iso := "mzn", value := .optional }
  , { walsCode := "mbg", language := "Mbugu", iso := "mhd", value := .absent }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .absent }
  , { walsCode := "mel", language := "Melanau", iso := "mel", value := .optional }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .absent }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .optional }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .optional }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .absent }
  , { walsCode := "mit", language := "Mituku", iso := "zmq", value := .absent }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .absent }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .absent }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .absent }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .obligatory }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .obligatory }
  , { walsCode := "mll", language := "Molala", iso := "mbe", value := .absent }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .absent }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .absent }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .absent }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .absent }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .absent }
  , { walsCode := "mkw", language := "Máku", iso := "xak", value := .absent }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .absent }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .absent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .absent }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .absent }
  , { walsCode := "npu", language := "Napu", iso := "npy", value := .optional }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .absent }
  , { walsCode := "nrm", language := "Narom", iso := "nrm", value := .optional }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .absent }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .obligatory }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .absent }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .absent }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .obligatory }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .absent }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .absent }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .obligatory }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .obligatory }
  , { walsCode := "ngy", language := "Ngarinyman", iso := "nbj", value := .absent }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .absent }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .absent }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .optional }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .obligatory }
  , { walsCode := "nvs", language := "Nivkh (South Sakhalin)", iso := "niv", value := .obligatory }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .absent }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .absent }
  , { walsCode := "nyl", language := "Nyelâyu", iso := "yly", value := .obligatory }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .absent }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .absent }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .optional }
  , { walsCode := "ore", language := "Orejón", iso := "ore", value := .optional }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .absent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .absent }
  , { walsCode := "pad", language := "Padoe", iso := "pdo", value := .optional }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .absent }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .absent }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .obligatory }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .absent }
  , { walsCode := "prc", language := "Paresi", iso := "pab", value := .absent }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .absent }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .absent }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .optional }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .optional }
  , { walsCode := "pil", language := "Pileni", iso := "piv", value := .optional }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .absent }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .absent }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .absent }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .absent }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .obligatory }
  , { walsCode := "fma", language := "Pulaar", iso := "fuc", value := .absent }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .obligatory }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .absent }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .absent }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .absent }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .absent }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .absent }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .obligatory }
  , { walsCode := "rse", language := "Romani (Sepecides)", iso := "rmn", value := .optional }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .absent }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .absent }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .absent }
  , { walsCode := "rcp", language := "Russian-Chinese Pidgin (Birobidjan)", iso := "", value := .absent }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .absent }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .absent }
  , { walsCode := "bjs", language := "Sama (Southern)", iso := "ssb", value := .optional }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .optional }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .absent }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .optional }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .optional }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .obligatory }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .absent }
  , { walsCode := "smd", language := "Semandang", iso := "sdm", value := .obligatory }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .obligatory }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .absent }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .absent }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .absent }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .absent }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .absent }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .obligatory }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .absent }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .optional }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .absent }
  , { walsCode := "so", language := "So", iso := "teu", value := .obligatory }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .obligatory }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .absent }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .absent }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .absent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .absent }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .absent }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .obligatory }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .absent }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .absent }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .optional }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .optional }
  , { walsCode := "tll", language := "Taulil", iso := "tuh", value := .absent }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .absent }
  , { walsCode := "tht", language := "Tehit", iso := "kps", value := .obligatory }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .absent }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .absent }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .absent }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .obligatory }
  , { walsCode := "trn", language := "Terêna", iso := "ter", value := .absent }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .optional }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .obligatory }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .optional }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .optional }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .absent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .absent }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .obligatory }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .absent }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .absent }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .absent }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .optional }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .absent }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .optional }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .obligatory }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .obligatory }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .absent }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .absent }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .optional }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .optional }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .absent }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .absent }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .optional }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .optional }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .absent }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .obligatory }
  , { walsCode := "tze", language := "Tzeltal", iso := "tzh", value := .obligatory }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .obligatory }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .absent }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .absent }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .absent }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .optional }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .obligatory }
  , { walsCode := "wgl", language := "Waigali", iso := "wbk", value := .absent }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .obligatory }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .absent }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .obligatory }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .absent }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .absent }
  , { walsCode := "was", language := "Washo", iso := "was", value := .absent }
  , { walsCode := "wur", language := "Waurá", iso := "wau", value := .optional }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .absent }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .absent }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .absent }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .obligatory }
  , { walsCode := "ymi", language := "Yami", iso := "tao", value := .absent }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .optional }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .absent }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .absent }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .absent }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .absent }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .absent }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .absent }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .obligatory }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .absent }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .absent }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .absent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .absent }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .absent }
  ]

-- Count verification
theorem total_count : allData.length = 400 := by native_decide

theorem count_absent :
    (allData.filter (·.value == .absent)).length = 260 := by native_decide
theorem count_optional :
    (allData.filter (·.value == .optional)).length = 62 := by native_decide
theorem count_obligatory :
    (allData.filter (·.value == .obligatory)).length = 78 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F55A
