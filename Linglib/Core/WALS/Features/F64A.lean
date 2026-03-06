/-!
# WALS Feature 64A: Nominal and Verbal Conjunction
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 64A`.

Chapter 64, 301 languages.
-/

namespace Core.WALS.F64A

/-- WALS 64A values. -/
inductive NominalAndVerbalConjunction where
  | identity  -- Identity (161 languages)
  | differentiation  -- Differentiation (125 languages)
  | bothExpressedByJuxtaposition  -- Both expressed by juxtaposition (15 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 64A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NominalAndVerbalConjunction
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 64A dataset (301 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .identity }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .identity }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .identity }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .identity }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .differentiation }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .differentiation }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .differentiation }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .differentiation }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .identity }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .differentiation }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .bothExpressedByJuxtaposition }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .identity }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .bothExpressedByJuxtaposition }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .identity }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .bothExpressedByJuxtaposition }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .differentiation }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .differentiation }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .differentiation }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .differentiation }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .differentiation }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .differentiation }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .identity }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .identity }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .identity }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .differentiation }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .identity }
  , { walsCode := "boz", language := "Bozo (Tigemaxo)", iso := "boz", value := .identity }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .identity }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .differentiation }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .differentiation }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .identity }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .identity }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .differentiation }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .identity }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .differentiation }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .differentiation }
  , { walsCode := "cyg", language := "Cayuga", iso := "cay", value := .differentiation }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .identity }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .identity }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .differentiation }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .identity }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .differentiation }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .identity }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .identity }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .identity }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .differentiation }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .differentiation }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .identity }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .differentiation }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .differentiation }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .differentiation }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .differentiation }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .differentiation }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .differentiation }
  , { walsCode := "dug", language := "Dullay (Gollango)", iso := "gwd", value := .identity }
  , { walsCode := "eng", language := "English", iso := "eng", value := .identity }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .identity }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .identity }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .differentiation }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .differentiation }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .identity }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .differentiation }
  , { walsCode := "fre", language := "French", iso := "fra", value := .identity }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .identity }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .identity }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .identity }
  , { walsCode := "ger", language := "German", iso := "deu", value := .identity }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .identity }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .bothExpressedByJuxtaposition }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .identity }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .identity }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .identity }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .identity }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .identity }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .identity }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .differentiation }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .differentiation }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .differentiation }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .differentiation }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .identity }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .identity }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .identity }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .bothExpressedByJuxtaposition }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .identity }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .differentiation }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .identity }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .identity }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .differentiation }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .differentiation }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .identity }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .identity }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .identity }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .identity }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .identity }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .differentiation }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .bothExpressedByJuxtaposition }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .differentiation }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .differentiation }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .differentiation }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .identity }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .differentiation }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .identity }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .differentiation }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .differentiation }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .differentiation }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .identity }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .differentiation }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .identity }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .identity }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .identity }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .identity }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .differentiation }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .identity }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .differentiation }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .differentiation }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .differentiation }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .differentiation }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .identity }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .differentiation }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .differentiation }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .identity }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .differentiation }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .identity }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .differentiation }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .differentiation }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .bothExpressedByJuxtaposition }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .identity }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .identity }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .identity }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .identity }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .identity }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .differentiation }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .identity }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .identity }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .differentiation }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .differentiation }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .identity }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .identity }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .identity }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .differentiation }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .differentiation }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .identity }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .differentiation }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .identity }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .identity }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .differentiation }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .differentiation }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .differentiation }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .differentiation }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .identity }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .identity }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .identity }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .identity }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .differentiation }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .differentiation }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .differentiation }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .differentiation }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .identity }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .identity }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .differentiation }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .differentiation }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .bothExpressedByJuxtaposition }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .identity }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .differentiation }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .differentiation }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .differentiation }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .differentiation }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .identity }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .differentiation }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .identity }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .identity }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .identity }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .identity }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .identity }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .differentiation }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .differentiation }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .identity }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .identity }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .differentiation }
  , { walsCode := "nmi", language := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", value := .identity }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .identity }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .identity }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .identity }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .identity }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .identity }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .identity }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .identity }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .identity }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .differentiation }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .differentiation }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .identity }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .bothExpressedByJuxtaposition }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .identity }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .differentiation }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .identity }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .identity }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .differentiation }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .differentiation }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .differentiation }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .identity }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .identity }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .identity }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .identity }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .differentiation }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .identity }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .differentiation }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .differentiation }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .differentiation }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .identity }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .identity }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .differentiation }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .differentiation }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .identity }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .identity }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .identity }
  , { walsCode := "pop", language := "Popoloca (Metzontla)", iso := "pbe", value := .identity }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .identity }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .identity }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .differentiation }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .differentiation }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .identity }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .bothExpressedByJuxtaposition }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .identity }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .differentiation }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .identity }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .identity }
  , { walsCode := "ski", language := "Saami (Kildin)", iso := "sjd", value := .identity }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .identity }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .differentiation }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .identity }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .differentiation }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .bothExpressedByJuxtaposition }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .identity }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .differentiation }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .differentiation }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .identity }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .identity }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .differentiation }
  , { walsCode := "so", language := "So", iso := "teu", value := .differentiation }
  , { walsCode := "som", language := "Somali", iso := "som", value := .differentiation }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .differentiation }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .identity }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .identity }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .identity }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .identity }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .identity }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .differentiation }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .identity }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .identity }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .identity }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .differentiation }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .differentiation }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .differentiation }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .differentiation }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .identity }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .differentiation }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .identity }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .identity }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .identity }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .identity }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .identity }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .differentiation }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .identity }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .identity }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .bothExpressedByJuxtaposition }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .identity }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .differentiation }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .identity }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .differentiation }
  , { walsCode := "tst", language := "Tsat", iso := "huq", value := .differentiation }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .identity }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .identity }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .identity }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .differentiation }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .identity }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .identity }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .identity }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .identity }
  , { walsCode := "uku", language := "Upper Kuskokwim", iso := "kuu", value := .differentiation }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .differentiation }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .identity }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .identity }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .identity }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .identity }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .bothExpressedByJuxtaposition }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .differentiation }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .identity }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .differentiation }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .differentiation }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .bothExpressedByJuxtaposition }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .identity }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .identity }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .identity }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .differentiation }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .bothExpressedByJuxtaposition }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .differentiation }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .differentiation }
  , { walsCode := "zaq", language := "Zapotec (Quiegolani)", iso := "zpi", value := .identity }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .identity }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .differentiation }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .differentiation }
  ]

-- Count verification
theorem total_count : allData.length = 301 := by native_decide

theorem count_identity :
    (allData.filter (·.value == .identity)).length = 161 := by native_decide
theorem count_differentiation :
    (allData.filter (·.value == .differentiation)).length = 125 := by native_decide
theorem count_bothExpressedByJuxtaposition :
    (allData.filter (·.value == .bothExpressedByJuxtaposition)).length = 15 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F64A
