/-!
# WALS Feature 58A: Obligatory Possessive Inflection
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 58A`.

Chapter 58, 244 languages.
-/

namespace Core.WALS.F58A

/-- WALS 58A values. -/
inductive ObligatoryPossessiveInflection where
  | exists  -- Exists (43 languages)
  | absent  -- Absent (201 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 58A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ObligatoryPossessiveInflection
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 58A dataset (244 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .absent }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .exists }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .absent }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .absent }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .absent }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .absent }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .absent }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .absent }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .absent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .absent }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .absent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .absent }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .absent }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .exists }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .absent }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .absent }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .absent }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .absent }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .absent }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .exists }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .absent }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .absent }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .absent }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .exists }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .absent }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .absent }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .absent }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .absent }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .absent }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .absent }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .absent }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .exists }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .exists }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .exists }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .absent }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .absent }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .absent }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .exists }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .absent }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .exists }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .exists }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .absent }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .exists }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .exists }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .absent }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .exists }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .exists }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .absent }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .absent }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .absent }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .absent }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .absent }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .absent }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .absent }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .exists }
  , { walsCode := "eng", language := "English", iso := "eng", value := .absent }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .exists }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .exists }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .absent }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .absent }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .absent }
  , { walsCode := "fre", language := "French", iso := "fra", value := .absent }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .absent }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .absent }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .absent }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .absent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .absent }
  , { walsCode := "ger", language := "German", iso := "deu", value := .absent }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .absent }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .absent }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .absent }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .absent }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .absent }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .absent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .exists }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .exists }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .absent }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .absent }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .absent }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .exists }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .absent }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .absent }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .absent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .absent }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .absent }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .absent }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .absent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .absent }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .absent }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .absent }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .absent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .absent }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .absent }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .absent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .absent }
  , { walsCode := "knp", language := "Kanum (Ngkâlmpw)", iso := "kcd", value := .absent }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .absent }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .exists }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .absent }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .absent }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .absent }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .absent }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .absent }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .absent }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .absent }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .absent }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .exists }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .absent }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .exists }
  , { walsCode := "kln", language := "Kolana", iso := "kvw", value := .absent }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .absent }
  , { walsCode := "knu", language := "Konua", iso := "kyx", value := .absent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .absent }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .absent }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .absent }
  , { walsCode := "kiu", language := "Kui (in Indonesia)", iso := "kvd", value := .exists }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .absent }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .exists }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .absent }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .absent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .absent }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .absent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .absent }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .exists }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .absent }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .absent }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .absent }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .absent }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .exists }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .absent }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .absent }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .absent }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .absent }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .absent }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .absent }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .absent }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .absent }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .absent }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .absent }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .absent }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .absent }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .absent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .absent }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .absent }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .absent }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .absent }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .absent }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .absent }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .absent }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .absent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .exists }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .absent }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .absent }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .absent }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .absent }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .exists }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .absent }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .absent }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .absent }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .absent }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .absent }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .absent }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .absent }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .absent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .absent }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .exists }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .absent }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .exists }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .absent }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .absent }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .absent }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .exists }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .absent }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .absent }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .absent }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .absent }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .absent }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .exists }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .absent }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .absent }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .exists }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .absent }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .absent }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .exists }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .absent }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .absent }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .absent }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .absent }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .absent }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .absent }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .absent }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .absent }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .absent }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .absent }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .absent }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .absent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .absent }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .absent }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .absent }
  , { walsCode := "tgp", language := "Tanglapui", iso := "tpg", value := .exists }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .absent }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .absent }
  , { walsCode := "tht", language := "Tehit", iso := "kps", value := .absent }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .absent }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .absent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .absent }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .absent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .exists }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .absent }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .absent }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .exists }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .absent }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .absent }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .exists }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .absent }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .absent }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .exists }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .absent }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .absent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .absent }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .exists }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .absent }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .absent }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .absent }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .absent }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .absent }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .absent }
  , { walsCode := "was", language := "Washo", iso := "was", value := .absent }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .absent }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .absent }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .absent }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .exists }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .exists }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .absent }
  , { walsCode := "yli", language := "Yali", iso := "yli", value := .absent }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .absent }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .absent }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .absent }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .absent }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .absent }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .absent }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .absent }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .absent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .absent }
  ]

-- Count verification
theorem total_count : allData.length = 244 := by native_decide

theorem count_exists :
    (allData.filter (·.value == .exists)).length = 43 := by native_decide
theorem count_absent :
    (allData.filter (·.value == .absent)).length = 201 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F58A
