import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 58B: Number of Possessive Nouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 58B`.

Chapter 58, 243 languages.
-/

namespace Core.WALS.F58B

/-- WALS 58B values. -/
inductive NumberOfPossessiveNouns where
  | noneReported  -- None reported (233 languages)
  | one  -- One (3 languages)
  | twoToFour  -- Two to four (4 languages)
  | fiveOrMore  -- Five or more (3 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 58B dataset (243 languages). -/
def allData : List (Datapoint NumberOfPossessiveNouns) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noneReported }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noneReported }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noneReported }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noneReported }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noneReported }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noneReported }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noneReported }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noneReported }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noneReported }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noneReported }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noneReported }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noneReported }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noneReported }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noneReported }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noneReported }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noneReported }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noneReported }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noneReported }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noneReported }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noneReported }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noneReported }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .noneReported }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noneReported }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .noneReported }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noneReported }
  , { walsCode := "brk", language := "Berik", iso := "bkl", value := .noneReported }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .noneReported }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noneReported }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noneReported }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noneReported }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .noneReported }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noneReported }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noneReported }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noneReported }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noneReported }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .twoToFour }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .noneReported }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .twoToFour }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noneReported }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noneReported }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .noneReported }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noneReported }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .noneReported }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noneReported }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noneReported }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noneReported }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noneReported }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .noneReported }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noneReported }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .noneReported }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noneReported }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noneReported }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noneReported }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noneReported }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noneReported }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noneReported }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noneReported }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noneReported }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noneReported }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .twoToFour }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noneReported }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noneReported }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noneReported }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noneReported }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noneReported }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noneReported }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noneReported }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noneReported }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noneReported }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noneReported }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noneReported }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noneReported }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .one }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noneReported }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noneReported }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noneReported }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noneReported }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noneReported }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noneReported }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noneReported }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noneReported }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noneReported }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noneReported }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noneReported }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .noneReported }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noneReported }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .noneReported }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noneReported }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noneReported }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noneReported }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noneReported }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noneReported }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noneReported }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noneReported }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noneReported }
  , { walsCode := "knp", language := "Kanum (Ngkâlmpw)", iso := "kcd", value := .noneReported }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noneReported }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noneReported }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noneReported }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noneReported }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noneReported }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noneReported }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noneReported }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .noneReported }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noneReported }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .fiveOrMore }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noneReported }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noneReported }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .noneReported }
  , { walsCode := "kln", language := "Kolana", iso := "kvw", value := .noneReported }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noneReported }
  , { walsCode := "knu", language := "Konua", iso := "kyx", value := .noneReported }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noneReported }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noneReported }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noneReported }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .noneReported }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noneReported }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noneReported }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .noneReported }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noneReported }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noneReported }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noneReported }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noneReported }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .noneReported }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .noneReported }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noneReported }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noneReported }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noneReported }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noneReported }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noneReported }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noneReported }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .noneReported }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noneReported }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noneReported }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noneReported }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noneReported }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noneReported }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noneReported }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noneReported }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .noneReported }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noneReported }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noneReported }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noneReported }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noneReported }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noneReported }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noneReported }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .noneReported }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noneReported }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .noneReported }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .noneReported }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noneReported }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noneReported }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noneReported }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noneReported }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noneReported }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noneReported }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noneReported }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noneReported }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noneReported }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noneReported }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noneReported }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .noneReported }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noneReported }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noneReported }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noneReported }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noneReported }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noneReported }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .twoToFour }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noneReported }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .fiveOrMore }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noneReported }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .noneReported }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noneReported }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noneReported }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .fiveOrMore }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noneReported }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noneReported }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noneReported }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noneReported }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noneReported }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noneReported }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noneReported }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noneReported }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noneReported }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noneReported }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noneReported }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noneReported }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noneReported }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noneReported }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noneReported }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noneReported }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noneReported }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noneReported }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noneReported }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noneReported }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noneReported }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noneReported }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noneReported }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noneReported }
  , { walsCode := "tgp", language := "Tanglapui", iso := "tpg", value := .noneReported }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noneReported }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noneReported }
  , { walsCode := "tht", language := "Tehit", iso := "kps", value := .noneReported }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .noneReported }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noneReported }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noneReported }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noneReported }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noneReported }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noneReported }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noneReported }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noneReported }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .one }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noneReported }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noneReported }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noneReported }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noneReported }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noneReported }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noneReported }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noneReported }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noneReported }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noneReported }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noneReported }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noneReported }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .noneReported }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noneReported }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noneReported }
  , { walsCode := "was", language := "Washo", iso := "was", value := .one }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noneReported }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noneReported }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noneReported }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noneReported }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noneReported }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noneReported }
  , { walsCode := "yli", language := "Yali", iso := "yli", value := .noneReported }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noneReported }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noneReported }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noneReported }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noneReported }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noneReported }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noneReported }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noneReported }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noneReported }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noneReported }
  ]

-- Count verification
theorem total_count : allData.length = 243 := by native_decide

theorem count_noneReported :
    (allData.filter (·.value == .noneReported)).length = 233 := by native_decide
theorem count_one :
    (allData.filter (·.value == .one)).length = 3 := by native_decide
theorem count_twoToFour :
    (allData.filter (·.value == .twoToFour)).length = 4 := by native_decide
theorem count_fiveOrMore :
    (allData.filter (·.value == .fiveOrMore)).length = 3 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F58B
