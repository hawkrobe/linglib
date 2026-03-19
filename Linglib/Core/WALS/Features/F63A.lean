/-!
# WALS Feature 63A: Noun Phrase Conjunction
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 63A`.

Chapter 63, 234 languages.
-/

namespace Core.WALS.F63A

/-- WALS 63A values. -/
inductive NounPhraseConjunction where
  | andDifferentFromWith  -- 'And' different from 'with' (131 languages)
  | andIdenticalToWith  -- 'And' identical to 'with' (103 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 63A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NounPhraseConjunction
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 63A dataset (234 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .andDifferentFromWith }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .andIdenticalToWith }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .andIdenticalToWith }
  , { walsCode := "ahu", language := "Aghu", iso := "ahh", value := .andDifferentFromWith }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .andDifferentFromWith }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .andIdenticalToWith }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .andDifferentFromWith }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .andDifferentFromWith }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .andDifferentFromWith }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .andDifferentFromWith }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .andIdenticalToWith }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .andDifferentFromWith }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .andDifferentFromWith }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .andIdenticalToWith }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .andDifferentFromWith }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .andDifferentFromWith }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .andDifferentFromWith }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .andDifferentFromWith }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .andDifferentFromWith }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .andDifferentFromWith }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .andDifferentFromWith }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .andIdenticalToWith }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .andDifferentFromWith }
  , { walsCode := "bgg", language := "Banggai", iso := "bgz", value := .andIdenticalToWith }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .andIdenticalToWith }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .andDifferentFromWith }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .andIdenticalToWith }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .andDifferentFromWith }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .andIdenticalToWith }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .andIdenticalToWith }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .andIdenticalToWith }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .andDifferentFromWith }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .andDifferentFromWith }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .andDifferentFromWith }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .andDifferentFromWith }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .andIdenticalToWith }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .andIdenticalToWith }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .andDifferentFromWith }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .andIdenticalToWith }
  , { walsCode := "car", language := "Carib", iso := "car", value := .andIdenticalToWith }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .andIdenticalToWith }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .andIdenticalToWith }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .andIdenticalToWith }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .andDifferentFromWith }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .andDifferentFromWith }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .andDifferentFromWith }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .andIdenticalToWith }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .andIdenticalToWith }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .andDifferentFromWith }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .andIdenticalToWith }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .andDifferentFromWith }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .andDifferentFromWith }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .andIdenticalToWith }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .andDifferentFromWith }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .andIdenticalToWith }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .andDifferentFromWith }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .andDifferentFromWith }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .andIdenticalToWith }
  , { walsCode := "eng", language := "English", iso := "eng", value := .andDifferentFromWith }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .andDifferentFromWith }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .andIdenticalToWith }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .andIdenticalToWith }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .andIdenticalToWith }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .andDifferentFromWith }
  , { walsCode := "fre", language := "French", iso := "fra", value := .andDifferentFromWith }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .andIdenticalToWith }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .andDifferentFromWith }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .andIdenticalToWith }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .andDifferentFromWith }
  , { walsCode := "nbh", language := "Ghulfan", iso := "ghl", value := .andIdenticalToWith }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .andDifferentFromWith }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .andIdenticalToWith }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .andDifferentFromWith }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .andIdenticalToWith }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .andDifferentFromWith }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .andDifferentFromWith }
  , { walsCode := "grn", language := "Gurenne", iso := "gur", value := .andIdenticalToWith }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .andIdenticalToWith }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .andIdenticalToWith }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .andDifferentFromWith }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .andDifferentFromWith }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .andDifferentFromWith }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .andDifferentFromWith }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .andDifferentFromWith }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .andDifferentFromWith }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .andIdenticalToWith }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .andDifferentFromWith }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .andDifferentFromWith }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .andIdenticalToWith }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .andIdenticalToWith }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .andIdenticalToWith }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .andDifferentFromWith }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .andIdenticalToWith }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .andIdenticalToWith }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .andDifferentFromWith }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .andIdenticalToWith }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .andIdenticalToWith }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .andDifferentFromWith }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .andDifferentFromWith }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .andDifferentFromWith }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .andIdenticalToWith }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .andDifferentFromWith }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .andDifferentFromWith }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .andIdenticalToWith }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .andDifferentFromWith }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .andDifferentFromWith }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .andIdenticalToWith }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .andIdenticalToWith }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .andDifferentFromWith }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .andIdenticalToWith }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .andDifferentFromWith }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .andDifferentFromWith }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .andDifferentFromWith }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .andDifferentFromWith }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .andDifferentFromWith }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .andDifferentFromWith }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .andDifferentFromWith }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .andIdenticalToWith }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .andIdenticalToWith }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .andIdenticalToWith }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .andDifferentFromWith }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .andIdenticalToWith }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .andIdenticalToWith }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .andDifferentFromWith }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .andDifferentFromWith }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .andDifferentFromWith }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .andIdenticalToWith }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .andIdenticalToWith }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .andDifferentFromWith }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .andIdenticalToWith }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .andDifferentFromWith }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .andIdenticalToWith }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .andIdenticalToWith }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .andDifferentFromWith }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .andIdenticalToWith }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .andDifferentFromWith }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .andDifferentFromWith }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .andDifferentFromWith }
  , { walsCode := "mcf", language := "Michif", iso := "crg", value := .andDifferentFromWith }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .andIdenticalToWith }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .andIdenticalToWith }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .andIdenticalToWith }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .andIdenticalToWith }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .andDifferentFromWith }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .andIdenticalToWith }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .andDifferentFromWith }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .andIdenticalToWith }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .andDifferentFromWith }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .andDifferentFromWith }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .andDifferentFromWith }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .andDifferentFromWith }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .andIdenticalToWith }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .andIdenticalToWith }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .andDifferentFromWith }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .andIdenticalToWith }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .andIdenticalToWith }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .andDifferentFromWith }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .andIdenticalToWith }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .andIdenticalToWith }
  , { walsCode := "ojs", language := "Ojibwa (Severn)", iso := "ojs", value := .andDifferentFromWith }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .andDifferentFromWith }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .andDifferentFromWith }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .andIdenticalToWith }
  , { walsCode := "plr", language := "Palor", iso := "fap", value := .andIdenticalToWith }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .andIdenticalToWith }
  , { walsCode := "prd", language := "Parji (Dravidian)", iso := "pci", value := .andDifferentFromWith }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .andDifferentFromWith }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .andDifferentFromWith }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .andIdenticalToWith }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .andIdenticalToWith }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .andDifferentFromWith }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .andDifferentFromWith }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .andDifferentFromWith }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .andDifferentFromWith }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .andDifferentFromWith }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .andIdenticalToWith }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .andIdenticalToWith }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .andDifferentFromWith }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .andIdenticalToWith }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .andIdenticalToWith }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .andIdenticalToWith }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .andDifferentFromWith }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .andDifferentFromWith }
  , { walsCode := "srr", language := "Serrano", iso := "ser", value := .andDifferentFromWith }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .andIdenticalToWith }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .andIdenticalToWith }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .andDifferentFromWith }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .andDifferentFromWith }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .andDifferentFromWith }
  , { walsCode := "som", language := "Somali", iso := "som", value := .andDifferentFromWith }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .andDifferentFromWith }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .andDifferentFromWith }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .andIdenticalToWith }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .andIdenticalToWith }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .andDifferentFromWith }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .andDifferentFromWith }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .andIdenticalToWith }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .andDifferentFromWith }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .andIdenticalToWith }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .andIdenticalToWith }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .andDifferentFromWith }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .andDifferentFromWith }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .andDifferentFromWith }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .andDifferentFromWith }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .andDifferentFromWith }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .andDifferentFromWith }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .andIdenticalToWith }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .andIdenticalToWith }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .andDifferentFromWith }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .andDifferentFromWith }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .andIdenticalToWith }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .andIdenticalToWith }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .andDifferentFromWith }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .andDifferentFromWith }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .andIdenticalToWith }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .andIdenticalToWith }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .andDifferentFromWith }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .andDifferentFromWith }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .andDifferentFromWith }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .andDifferentFromWith }
  , { walsCode := "wrp", language := "Waropen", iso := "wrp", value := .andDifferentFromWith }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .andIdenticalToWith }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .andIdenticalToWith }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .andIdenticalToWith }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .andDifferentFromWith }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .andIdenticalToWith }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .andDifferentFromWith }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .andIdenticalToWith }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .andDifferentFromWith }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .andDifferentFromWith }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .andIdenticalToWith }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .andIdenticalToWith }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .andDifferentFromWith }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .andIdenticalToWith }
  ]

-- Count verification
theorem total_count : allData.length = 234 := by native_decide

theorem count_andDifferentFromWith :
    (allData.filter (·.value == .andDifferentFromWith)).length = 131 := by native_decide
theorem count_andIdenticalToWith :
    (allData.filter (·.value == .andIdenticalToWith)).length = 103 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F63A
