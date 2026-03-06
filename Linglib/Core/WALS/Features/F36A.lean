/-!
# WALS Feature 36A: The Associative Plural
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 36A`.

Chapter 36, 236 languages.
-/

namespace Core.WALS.F36A

/-- WALS 36A values. -/
inductive AssociativePlural where
  | associativeSameAsAdditivePlural  -- Associative same as additive plural (104 languages)
  | uniqueAffixalAssociativePlural  -- Unique affixal associative plural (48 languages)
  | uniquePeriphrasticAssociativePlural  -- Unique periphrastic associative plural (47 languages)
  | noAssociativePlural  -- No associative plural (37 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 36A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : AssociativePlural
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 36A dataset (236 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noAssociativePlural }
  , { walsCode := "adt", language := "Adyghe (Temirgoy)", iso := "ady", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "agl", language := "Aghul", iso := "agx", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .associativeSameAsAdditivePlural }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noAssociativePlural }
  , { walsCode := "alu", language := "Alutor", iso := "alr", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noAssociativePlural }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .associativeSameAsAdditivePlural }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noAssociativePlural }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noAssociativePlural }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .associativeSameAsAdditivePlural }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noAssociativePlural }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bnd", language := "Bandi", iso := "bza", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bnw", language := "Baniwa", iso := "bwi", value := .noAssociativePlural }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noAssociativePlural }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .associativeSameAsAdditivePlural }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "bdc", language := "Berbice Dutch Creole", iso := "brc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .associativeSameAsAdditivePlural }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "chm", language := "Chamalal", iso := "cji", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .associativeSameAsAdditivePlural }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .associativeSameAsAdditivePlural }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .associativeSameAsAdditivePlural }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .associativeSameAsAdditivePlural }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .associativeSameAsAdditivePlural }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "des", language := "Desano", iso := "des", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noAssociativePlural }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noAssociativePlural }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .noAssociativePlural }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noAssociativePlural }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noAssociativePlural }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .associativeSameAsAdditivePlural }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .associativeSameAsAdditivePlural }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .associativeSameAsAdditivePlural }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ger", language := "German", iso := "deu", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .associativeSameAsAdditivePlural }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noAssociativePlural }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noAssociativePlural }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "gji", language := "Gurindji", iso := "gue", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "hwc", language := "Hawaiian Creole", iso := "hwc", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .associativeSameAsAdditivePlural }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noAssociativePlural }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noAssociativePlural }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .associativeSameAsAdditivePlural }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "iir", language := "Indonesian (Papuan)", iso := "pmy", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noAssociativePlural }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noAssociativePlural }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noAssociativePlural }
  , { walsCode := "jcr", language := "Jamaican Creole", iso := "jam", value := .associativeSameAsAdditivePlural }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .associativeSameAsAdditivePlural }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ktz", language := "Kati (in Afghanistan)", iso := "bsh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .associativeSameAsAdditivePlural }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kfc", language := "Kriol (Fitzroy Crossing)", iso := "rop", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "knq", language := "Kriol (Ngukurr)", iso := "rop", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .associativeSameAsAdditivePlural }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kuq", language := "Kumyk", iso := "kum", value := .associativeSameAsAdditivePlural }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noAssociativePlural }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noAssociativePlural }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noAssociativePlural }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noAssociativePlural }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lcr", language := "Lesser Antillean French Creole", iso := "", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lok", language := "Loko", iso := "lok", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lma", language := "Loma", iso := "lom", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .associativeSameAsAdditivePlural }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .associativeSameAsAdditivePlural }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mbu", language := "Manambu", iso := "mle", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .associativeSameAsAdditivePlural }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noAssociativePlural }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mcr", language := "Mauritian Creole", iso := "mfe", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noAssociativePlural }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .associativeSameAsAdditivePlural }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "mce", language := "Mískito Coast English Creole", iso := "bzk", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .associativeSameAsAdditivePlural }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .associativeSameAsAdditivePlural }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .associativeSameAsAdditivePlural }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noAssociativePlural }
  , { walsCode := "orc", language := "Oroch", iso := "oac", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .associativeSameAsAdditivePlural }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noAssociativePlural }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noAssociativePlural }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .associativeSameAsAdditivePlural }
  , { walsCode := "pap", language := "Papiamentu", iso := "pap", value := .associativeSameAsAdditivePlural }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .associativeSameAsAdditivePlural }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noAssociativePlural }
  , { walsCode := "fma", language := "Pulaar", iso := "fuc", value := .associativeSameAsAdditivePlural }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noAssociativePlural }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noAssociativePlural }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .associativeSameAsAdditivePlural }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .associativeSameAsAdditivePlural }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .associativeSameAsAdditivePlural }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "rsh", language := "Shughni", iso := "sgh", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .associativeSameAsAdditivePlural }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noAssociativePlural }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tbs", language := "Tabassaran", iso := "tab", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tmu", language := "Tat (Muslim)", iso := "ttt", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noAssociativePlural }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tof", language := "Tofa", iso := "kim", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .associativeSameAsAdditivePlural }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .associativeSameAsAdditivePlural }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .uniquePeriphrasticAssociativePlural }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .associativeSameAsAdditivePlural }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .associativeSameAsAdditivePlural }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .associativeSameAsAdditivePlural }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .associativeSameAsAdditivePlural }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .associativeSameAsAdditivePlural }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noAssociativePlural }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .noAssociativePlural }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noAssociativePlural }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .associativeSameAsAdditivePlural }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .associativeSameAsAdditivePlural }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .uniqueAffixalAssociativePlural }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .associativeSameAsAdditivePlural }
  ]

-- Count verification
theorem total_count : allData.length = 236 := by native_decide

theorem count_associativeSameAsAdditivePlural :
    (allData.filter (·.value == .associativeSameAsAdditivePlural)).length = 104 := by native_decide
theorem count_uniqueAffixalAssociativePlural :
    (allData.filter (·.value == .uniqueAffixalAssociativePlural)).length = 48 := by native_decide
theorem count_uniquePeriphrasticAssociativePlural :
    (allData.filter (·.value == .uniquePeriphrasticAssociativePlural)).length = 47 := by native_decide
theorem count_noAssociativePlural :
    (allData.filter (·.value == .noAssociativePlural)).length = 37 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F36A
