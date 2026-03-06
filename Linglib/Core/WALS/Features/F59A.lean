/-!
# WALS Feature 59A: Possessive Classification
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 59A`.

Chapter 59, 243 languages.
-/

namespace Core.WALS.F59A

/-- WALS 59A values. -/
inductive PossessiveClassification where
  | noPossessiveClassification  -- No possessive classification (125 languages)
  | twoClasses  -- Two classes (94 languages)
  | threeToFiveClasses  -- Three to five classes (20 languages)
  | moreThanFiveClasses  -- More than five classes (4 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 59A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PossessiveClassification
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 59A dataset (243 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noPossessiveClassification }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noPossessiveClassification }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noPossessiveClassification }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noPossessiveClassification }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .twoClasses }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .moreThanFiveClasses }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noPossessiveClassification }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .moreThanFiveClasses }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noPossessiveClassification }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noPossessiveClassification }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noPossessiveClassification }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noPossessiveClassification }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .twoClasses }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .twoClasses }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noPossessiveClassification }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noPossessiveClassification }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noPossessiveClassification }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noPossessiveClassification }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noPossessiveClassification }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .twoClasses }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noPossessiveClassification }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .noPossessiveClassification }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noPossessiveClassification }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .noPossessiveClassification }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .twoClasses }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .noPossessiveClassification }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .twoClasses }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .threeToFiveClasses }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noPossessiveClassification }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noPossessiveClassification }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .twoClasses }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .threeToFiveClasses }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noPossessiveClassification }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noPossessiveClassification }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .moreThanFiveClasses }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noPossessiveClassification }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .twoClasses }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .moreThanFiveClasses }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .twoClasses }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noPossessiveClassification }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .noPossessiveClassification }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noPossessiveClassification }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .noPossessiveClassification }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noPossessiveClassification }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .twoClasses }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .twoClasses }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .twoClasses }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .noPossessiveClassification }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .twoClasses }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .twoClasses }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noPossessiveClassification }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .twoClasses }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .twoClasses }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .twoClasses }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .twoClasses }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noPossessiveClassification }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noPossessiveClassification }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noPossessiveClassification }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .twoClasses }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noPossessiveClassification }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noPossessiveClassification }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noPossessiveClassification }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .twoClasses }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noPossessiveClassification }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .twoClasses }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .twoClasses }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noPossessiveClassification }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noPossessiveClassification }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .twoClasses }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPossessiveClassification }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noPossessiveClassification }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noPossessiveClassification }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noPossessiveClassification }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noPossessiveClassification }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .twoClasses }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .twoClasses }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPossessiveClassification }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noPossessiveClassification }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noPossessiveClassification }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noPossessiveClassification }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPossessiveClassification }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .threeToFiveClasses }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .twoClasses }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noPossessiveClassification }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .twoClasses }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .twoClasses }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .noPossessiveClassification }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .twoClasses }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noPossessiveClassification }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noPossessiveClassification }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noPossessiveClassification }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPossessiveClassification }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .threeToFiveClasses }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .twoClasses }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noPossessiveClassification }
  , { walsCode := "knp", language := "Kanum (Ngkâlmpw)", iso := "kcd", value := .noPossessiveClassification }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noPossessiveClassification }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noPossessiveClassification }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .twoClasses }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noPossessiveClassification }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noPossessiveClassification }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noPossessiveClassification }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noPossessiveClassification }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .twoClasses }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .twoClasses }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .threeToFiveClasses }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .twoClasses }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .twoClasses }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .twoClasses }
  , { walsCode := "kln", language := "Kolana", iso := "kvw", value := .noPossessiveClassification }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noPossessiveClassification }
  , { walsCode := "knu", language := "Konua", iso := "kyx", value := .twoClasses }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noPossessiveClassification }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .twoClasses }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .twoClasses }
  , { walsCode := "kiu", language := "Kui (in Indonesia)", iso := "kvd", value := .twoClasses }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .twoClasses }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noPossessiveClassification }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .twoClasses }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .twoClasses }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .twoClasses }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noPossessiveClassification }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPossessiveClassification }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .threeToFiveClasses }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .twoClasses }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .twoClasses }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .twoClasses }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .twoClasses }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .twoClasses }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPossessiveClassification }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .twoClasses }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .noPossessiveClassification }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPossessiveClassification }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noPossessiveClassification }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .twoClasses }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPossessiveClassification }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noPossessiveClassification }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .twoClasses }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .threeToFiveClasses }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .twoClasses }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .twoClasses }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .twoClasses }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .twoClasses }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPossessiveClassification }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noPossessiveClassification }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noPossessiveClassification }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .twoClasses }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noPossessiveClassification }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .noPossessiveClassification }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .threeToFiveClasses }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .twoClasses }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .twoClasses }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noPossessiveClassification }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noPossessiveClassification }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noPossessiveClassification }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noPossessiveClassification }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .twoClasses }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noPossessiveClassification }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .twoClasses }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .twoClasses }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .twoClasses }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .twoClasses }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noPossessiveClassification }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noPossessiveClassification }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .twoClasses }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .twoClasses }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noPossessiveClassification }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .threeToFiveClasses }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPossessiveClassification }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .twoClasses }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .twoClasses }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noPossessiveClassification }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPossessiveClassification }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .twoClasses }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .threeToFiveClasses }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noPossessiveClassification }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .twoClasses }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .twoClasses }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .twoClasses }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noPossessiveClassification }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noPossessiveClassification }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noPossessiveClassification }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .twoClasses }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .threeToFiveClasses }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noPossessiveClassification }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPossessiveClassification }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .twoClasses }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .threeToFiveClasses }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .threeToFiveClasses }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .threeToFiveClasses }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noPossessiveClassification }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noPossessiveClassification }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noPossessiveClassification }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .twoClasses }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPossessiveClassification }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noPossessiveClassification }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noPossessiveClassification }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .twoClasses }
  , { walsCode := "tgp", language := "Tanglapui", iso := "tpg", value := .twoClasses }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .twoClasses }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .twoClasses }
  , { walsCode := "tht", language := "Tehit", iso := "kps", value := .twoClasses }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .noPossessiveClassification }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .twoClasses }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPossessiveClassification }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noPossessiveClassification }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .twoClasses }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .twoClasses }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .twoClasses }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noPossessiveClassification }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .threeToFiveClasses }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .twoClasses }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .twoClasses }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noPossessiveClassification }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noPossessiveClassification }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .threeToFiveClasses }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .threeToFiveClasses }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .twoClasses }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPossessiveClassification }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noPossessiveClassification }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noPossessiveClassification }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noPossessiveClassification }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .threeToFiveClasses }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .noPossessiveClassification }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noPossessiveClassification }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .twoClasses }
  , { walsCode := "was", language := "Washo", iso := "was", value := .twoClasses }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .twoClasses }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .twoClasses }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noPossessiveClassification }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .threeToFiveClasses }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .twoClasses }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noPossessiveClassification }
  , { walsCode := "yli", language := "Yali", iso := "yli", value := .noPossessiveClassification }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPossessiveClassification }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noPossessiveClassification }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noPossessiveClassification }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPossessiveClassification }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .threeToFiveClasses }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .twoClasses }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .twoClasses }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noPossessiveClassification }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noPossessiveClassification }
  ]

-- Count verification
theorem total_count : allData.length = 243 := by native_decide

theorem count_noPossessiveClassification :
    (allData.filter (·.value == .noPossessiveClassification)).length = 125 := by native_decide
theorem count_twoClasses :
    (allData.filter (·.value == .twoClasses)).length = 94 := by native_decide
theorem count_threeToFiveClasses :
    (allData.filter (·.value == .threeToFiveClasses)).length = 20 := by native_decide
theorem count_moreThanFiveClasses :
    (allData.filter (·.value == .moreThanFiveClasses)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F59A
