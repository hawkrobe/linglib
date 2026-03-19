/-!
# WALS Feature 46A: Indefinite Pronouns
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 46A`.

Chapter 46, 326 languages.
-/

namespace Core.WALS.F46A

/-- WALS 46A values. -/
inductive IndefinitePronouns where
  | interrogativeBased  -- Interrogative-based (194 languages)
  | genericNounBased  -- Generic-noun-based (85 languages)
  | special  -- Special (22 languages)
  | mixed  -- Mixed (23 languages)
  | existentialConstruction  -- Existential construction (2 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 46A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : IndefinitePronouns
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 46A dataset (326 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .special }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .genericNounBased }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .interrogativeBased }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .interrogativeBased }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .interrogativeBased }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .interrogativeBased }
  , { walsCode := "aso", language := "Altai (Southern)", iso := "alt", value := .interrogativeBased }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .interrogativeBased }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .genericNounBased }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .genericNounBased }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .interrogativeBased }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .interrogativeBased }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .genericNounBased }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .genericNounBased }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .interrogativeBased }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .genericNounBased }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .interrogativeBased }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .interrogativeBased }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .interrogativeBased }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .interrogativeBased }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .genericNounBased }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .interrogativeBased }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .genericNounBased }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .genericNounBased }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .genericNounBased }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .interrogativeBased }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .interrogativeBased }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .interrogativeBased }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .interrogativeBased }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .interrogativeBased }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .mixed }
  , { walsCode := "boz", language := "Bozo (Tigemaxo)", iso := "boz", value := .mixed }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .special }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .genericNounBased }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .interrogativeBased }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .interrogativeBased }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .interrogativeBased }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .interrogativeBased }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .interrogativeBased }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .interrogativeBased }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .special }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .interrogativeBased }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .genericNounBased }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .interrogativeBased }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .interrogativeBased }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .interrogativeBased }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .interrogativeBased }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .interrogativeBased }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .interrogativeBased }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .interrogativeBased }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .mixed }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .genericNounBased }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .interrogativeBased }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .interrogativeBased }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .interrogativeBased }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .interrogativeBased }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .interrogativeBased }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .genericNounBased }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .special }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .interrogativeBased }
  , { walsCode := "ene", language := "Enets", iso := "", value := .interrogativeBased }
  , { walsCode := "eng", language := "English", iso := "eng", value := .genericNounBased }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .genericNounBased }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .interrogativeBased }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .interrogativeBased }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .interrogativeBased }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .genericNounBased }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .special }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .genericNounBased }
  , { walsCode := "fre", language := "French", iso := "fra", value := .genericNounBased }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .interrogativeBased }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .genericNounBased }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .interrogativeBased }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .interrogativeBased }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .genericNounBased }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .interrogativeBased }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .genericNounBased }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .interrogativeBased }
  , { walsCode := "ger", language := "German", iso := "deu", value := .mixed }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .interrogativeBased }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .genericNounBased }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .interrogativeBased }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .interrogativeBased }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .interrogativeBased }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .mixed }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .interrogativeBased }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .interrogativeBased }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .interrogativeBased }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .genericNounBased }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .interrogativeBased }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .interrogativeBased }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .special }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .interrogativeBased }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .interrogativeBased }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .interrogativeBased }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .interrogativeBased }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .interrogativeBased }
  , { walsCode := "ibi", language := "Ibibio", iso := "ibb", value := .genericNounBased }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .interrogativeBased }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .genericNounBased }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .genericNounBased }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .genericNounBased }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .genericNounBased }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .genericNounBased }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .interrogativeBased }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .interrogativeBased }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .interrogativeBased }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .interrogativeBased }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .interrogativeBased }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .interrogativeBased }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .genericNounBased }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .special }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .interrogativeBased }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .genericNounBased }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .interrogativeBased }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .interrogativeBased }
  , { walsCode := "krm", language := "Karaim", iso := "kdr", value := .interrogativeBased }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .special }
  , { walsCode := "krl", language := "Karelian", iso := "krl", value := .interrogativeBased }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .interrogativeBased }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .special }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .interrogativeBased }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .mixed }
  , { walsCode := "krq", language := "Kerek", iso := "krk", value := .special }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .interrogativeBased }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .interrogativeBased }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .interrogativeBased }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .interrogativeBased }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .interrogativeBased }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .mixed }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .special }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .mixed }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .interrogativeBased }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .interrogativeBased }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .interrogativeBased }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .genericNounBased }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .interrogativeBased }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .interrogativeBased }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .interrogativeBased }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .interrogativeBased }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .interrogativeBased }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .genericNounBased }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .interrogativeBased }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .genericNounBased }
  , { walsCode := "ksi", language := "Ksingmul", iso := "puo", value := .interrogativeBased }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .interrogativeBased }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .genericNounBased }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .genericNounBased }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .interrogativeBased }
  , { walsCode := "kwr", language := "Kwamera", iso := "tnk", value := .genericNounBased }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .genericNounBased }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .genericNounBased }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .interrogativeBased }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .interrogativeBased }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .genericNounBased }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .interrogativeBased }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .genericNounBased }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .genericNounBased }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .interrogativeBased }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .interrogativeBased }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .interrogativeBased }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .interrogativeBased }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .genericNounBased }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .genericNounBased }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .genericNounBased }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .interrogativeBased }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .interrogativeBased }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .special }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .genericNounBased }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .interrogativeBased }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .interrogativeBased }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .mixed }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .genericNounBased }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .mixed }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .interrogativeBased }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .special }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .mixed }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .interrogativeBased }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .interrogativeBased }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .genericNounBased }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .interrogativeBased }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .interrogativeBased }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .interrogativeBased }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .interrogativeBased }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .genericNounBased }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .interrogativeBased }
  , { walsCode := "sum", language := "Mayangna", iso := "yan", value := .genericNounBased }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .genericNounBased }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .genericNounBased }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .genericNounBased }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .interrogativeBased }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .genericNounBased }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .interrogativeBased }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .genericNounBased }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .interrogativeBased }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .existentialConstruction }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .interrogativeBased }
  , { walsCode := "mmo", language := "Mordvin (Moksha)", iso := "mdf", value := .interrogativeBased }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .mixed }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .interrogativeBased }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .interrogativeBased }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .genericNounBased }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .interrogativeBased }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .interrogativeBased }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .interrogativeBased }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .genericNounBased }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .interrogativeBased }
  , { walsCode := "neg", language := "Negidal", iso := "neg", value := .interrogativeBased }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .special }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .interrogativeBased }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .interrogativeBased }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .interrogativeBased }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .interrogativeBased }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .interrogativeBased }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .interrogativeBased }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .genericNounBased }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .interrogativeBased }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .interrogativeBased }
  , { walsCode := "nro", language := "Nharo", iso := "nhr", value := .mixed }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .mixed }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .interrogativeBased }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .genericNounBased }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .interrogativeBased }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .genericNounBased }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .mixed }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .genericNounBased }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .genericNounBased }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .interrogativeBased }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .special }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .special }
  , { walsCode := "orl", language := "Orokolo", iso := "oro", value := .genericNounBased }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .genericNounBased }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .interrogativeBased }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .interrogativeBased }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .genericNounBased }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .interrogativeBased }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .genericNounBased }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .special }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .interrogativeBased }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .interrogativeBased }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .interrogativeBased }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .genericNounBased }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .mixed }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .interrogativeBased }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .interrogativeBased }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .mixed }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .interrogativeBased }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .interrogativeBased }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .genericNounBased }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .interrogativeBased }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .interrogativeBased }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .interrogativeBased }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .interrogativeBased }
  , { walsCode := "ski", language := "Saami (Kildin)", iso := "sjd", value := .interrogativeBased }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .interrogativeBased }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .genericNounBased }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .genericNounBased }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .interrogativeBased }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .genericNounBased }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .interrogativeBased }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .mixed }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .interrogativeBased }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .interrogativeBased }
  , { walsCode := "shr", language := "Shor", iso := "cjs", value := .interrogativeBased }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .interrogativeBased }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .interrogativeBased }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .genericNounBased }
  , { walsCode := "som", language := "Somali", iso := "som", value := .genericNounBased }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .special }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .interrogativeBased }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .genericNounBased }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .special }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .interrogativeBased }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .existentialConstruction }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .interrogativeBased }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .interrogativeBased }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .interrogativeBased }
  , { walsCode := "tmu", language := "Tat (Muslim)", iso := "ttt", value := .genericNounBased }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .interrogativeBased }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .mixed }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .interrogativeBased }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .interrogativeBased }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .genericNounBased }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .genericNounBased }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .interrogativeBased }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .interrogativeBased }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .genericNounBased }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .interrogativeBased }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .interrogativeBased }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .genericNounBased }
  , { walsCode := "tst", language := "Tsat", iso := "huq", value := .interrogativeBased }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .interrogativeBased }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .genericNounBased }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .mixed }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .genericNounBased }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .interrogativeBased }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .interrogativeBased }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .interrogativeBased }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .interrogativeBased }
  , { walsCode := "uku", language := "Upper Kuskokwim", iso := "kuu", value := .interrogativeBased }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .mixed }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .genericNounBased }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .interrogativeBased }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .interrogativeBased }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .interrogativeBased }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .mixed }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .interrogativeBased }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .interrogativeBased }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .interrogativeBased }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .interrogativeBased }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .interrogativeBased }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .special }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .interrogativeBased }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .mixed }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .genericNounBased }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .interrogativeBased }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .special }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .interrogativeBased }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .interrogativeBased }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .interrogativeBased }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .genericNounBased }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .interrogativeBased }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .interrogativeBased }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .interrogativeBased }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .special }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .interrogativeBased }
  ]

-- Count verification
theorem total_count : allData.length = 326 := by native_decide

theorem count_interrogativeBased :
    (allData.filter (·.value == .interrogativeBased)).length = 194 := by native_decide
theorem count_genericNounBased :
    (allData.filter (·.value == .genericNounBased)).length = 85 := by native_decide
theorem count_special :
    (allData.filter (·.value == .special)).length = 22 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 23 := by native_decide
theorem count_existentialConstruction :
    (allData.filter (·.value == .existentialConstruction)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F46A
