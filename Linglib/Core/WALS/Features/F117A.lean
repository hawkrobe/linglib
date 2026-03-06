/-!
# WALS Feature 117A: Predicative Possession
@cite{stassen-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 117A`.

Chapter 117, 240 languages.
-/

namespace Core.WALS.F117A

/-- WALS 117A values. -/
inductive PredicativePossession where
  | locational  -- Locational (48 languages)
  | genitive  -- Genitive (22 languages)
  | topic  -- Topic (48 languages)
  | conjunctional  -- Conjunctional (59 languages)
  | have  -- 'Have' (63 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 117A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PredicativePossession
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 117A dataset (240 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .have }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .topic }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .conjunctional }
  , { walsCode := "ahu", language := "Aghu", iso := "ahh", value := .topic }
  , { walsCode := "agl", language := "Aghul", iso := "agx", value := .locational }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .have }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .topic }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .locational }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .conjunctional }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .have }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .conjunctional }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .locational }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .conjunctional }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .locational }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .genitive }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .genitive }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .locational }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .topic }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .genitive }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .topic }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .have }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .locational }
  , { walsCode := "bgg", language := "Banggai", iso := "bgz", value := .topic }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .conjunctional }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .have }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .topic }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .genitive }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .genitive }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .locational }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .have }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .topic }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .locational }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .conjunctional }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .locational }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .genitive }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .locational }
  , { walsCode := "car", language := "Carib", iso := "car", value := .conjunctional }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .topic }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .genitive }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .have }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .topic }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .conjunctional }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .conjunctional }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .conjunctional }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .locational }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .have }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .conjunctional }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .have }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .have }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .conjunctional }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .locational }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .conjunctional }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .have }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .conjunctional }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .conjunctional }
  , { walsCode := "eng", language := "English", iso := "eng", value := .have }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .genitive }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .locational }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .locational }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .locational }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .topic }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .locational }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .conjunctional }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .have }
  , { walsCode := "nbh", language := "Ghulfan", iso := "ghl", value := .locational }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .conjunctional }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .conjunctional }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .have }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .have }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .topic }
  , { walsCode := "gno", language := "Guanano", iso := "gvc", value := .have }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .have }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .genitive }
  , { walsCode := "grn", language := "Gurenne", iso := "gur", value := .have }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .have }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .conjunctional }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .locational }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .locational }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .conjunctional }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .locational }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .have }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .topic }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .locational }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .locational }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .have }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .locational }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .topic }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .locational }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .conjunctional }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .topic }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .conjunctional }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .locational }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .locational }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .have }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .topic }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .topic }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .topic }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .topic }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .topic }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .locational }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .locational }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .have }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .locational }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .have }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .have }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .have }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .locational }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .topic }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .have }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .conjunctional }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .locational }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .genitive }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .genitive }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .have }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .genitive }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .conjunctional }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .topic }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .topic }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .conjunctional }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .topic }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .have }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .have }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .locational }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .conjunctional }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .locational }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .topic }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .conjunctional }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .conjunctional }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .have }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .genitive }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .have }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .conjunctional }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .genitive }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .have }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .conjunctional }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .locational }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .have }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .topic }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .conjunctional }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .conjunctional }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .have }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .genitive }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .conjunctional }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .locational }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .conjunctional }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .topic }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .topic }
  , { walsCode := "nhp", language := "Nahuatl (Pochutla)", iso := "xpo", value := .have }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .have }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .conjunctional }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .genitive }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .genitive }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .conjunctional }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .conjunctional }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .conjunctional }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .conjunctional }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .have }
  , { walsCode := "ojs", language := "Ojibwa (Severn)", iso := "ojs", value := .have }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .genitive }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .have }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .topic }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .topic }
  , { walsCode := "plr", language := "Palor", iso := "fap", value := .have }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .topic }
  , { walsCode := "pap", language := "Papiamentu", iso := "pap", value := .have }
  , { walsCode := "prd", language := "Parji (Dravidian)", iso := "pci", value := .locational }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .conjunctional }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .have }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .have }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .conjunctional }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .have }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .have }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .genitive }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .have }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .topic }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .have }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .conjunctional }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .locational }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .topic }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .locational }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .conjunctional }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .conjunctional }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .topic }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .topic }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .locational }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .have }
  , { walsCode := "srr", language := "Serrano", iso := "ser", value := .have }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .locational }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .conjunctional }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .have }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .locational }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .topic }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .conjunctional }
  , { walsCode := "so", language := "So", iso := "teu", value := .conjunctional }
  , { walsCode := "som", language := "Somali", iso := "som", value := .conjunctional }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .have }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .have }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .conjunctional }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .conjunctional }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .have }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .topic }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .genitive }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .have }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .locational }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .locational }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .topic }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .conjunctional }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .topic }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .have }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .genitive }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .topic }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .topic }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .topic }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .have }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .locational }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .have }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .topic }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .topic }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .genitive }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .topic }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .have }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .topic }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .topic }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .locational }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .topic }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .have }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .conjunctional }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .locational }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .locational }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .locational }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .have }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .have }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .conjunctional }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .conjunctional }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .have }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .conjunctional }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .conjunctional }
  , { walsCode := "zpi", language := "Zapotec (Ixtlan)", iso := "zpd", value := .conjunctional }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .conjunctional }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .conjunctional }
  ]

-- Count verification
theorem total_count : allData.length = 240 := by native_decide

theorem count_locational :
    (allData.filter (·.value == .locational)).length = 48 := by native_decide
theorem count_genitive :
    (allData.filter (·.value == .genitive)).length = 22 := by native_decide
theorem count_topic :
    (allData.filter (·.value == .topic)).length = 48 := by native_decide
theorem count_conjunctional :
    (allData.filter (·.value == .conjunctional)).length = 59 := by native_decide
theorem count_have :
    (allData.filter (·.value == .have)).length = 63 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F117A
