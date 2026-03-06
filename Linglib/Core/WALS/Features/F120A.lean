/-!
# WALS Feature 120A: Zero Copula for Predicate Nominals
@cite{stassen-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 120A`.

Chapter 120, 386 languages.
-/

namespace Core.WALS.F120A

/-- WALS 120A values. -/
inductive ZeroCopulaType where
  | impossible  -- Impossible (211 languages)
  | possible  -- Possible (175 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 120A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ZeroCopulaType
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 120A dataset (386 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abz", language := "Abaza", iso := "abq", value := .impossible }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .impossible }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .possible }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .possible }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .impossible }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .impossible }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .impossible }
  , { walsCode := "ahu", language := "Aghu", iso := "ahh", value := .possible }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .impossible }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .impossible }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .possible }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .impossible }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .impossible }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .possible }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .impossible }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .possible }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .impossible }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .possible }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .possible }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .possible }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .impossible }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .impossible }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .possible }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .possible }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .possible }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .impossible }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .impossible }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .possible }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .impossible }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .possible }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .impossible }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .impossible }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .possible }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .impossible }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .impossible }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .impossible }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .impossible }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .impossible }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .possible }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .possible }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .impossible }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .impossible }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .impossible }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .impossible }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .possible }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .possible }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .possible }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .impossible }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .impossible }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .impossible }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .possible }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .impossible }
  , { walsCode := "brj", language := "Burji", iso := "bji", value := .possible }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .possible }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .impossible }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .impossible }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .possible }
  , { walsCode := "car", language := "Carib", iso := "car", value := .possible }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .impossible }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .impossible }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .impossible }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .impossible }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .possible }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .impossible }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .impossible }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .impossible }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .impossible }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .possible }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .impossible }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .possible }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .possible }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .impossible }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .impossible }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .possible }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .impossible }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .impossible }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .possible }
  , { walsCode := "dab", language := "Daba", iso := "dbq", value := .possible }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .impossible }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .impossible }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .impossible }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .possible }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .possible }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .possible }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .possible }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .impossible }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .possible }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .possible }
  , { walsCode := "eng", language := "English", iso := "eng", value := .impossible }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .possible }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .impossible }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .possible }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .possible }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .impossible }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .impossible }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .impossible }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .possible }
  , { walsCode := "for", language := "Fore", iso := "for", value := .possible }
  , { walsCode := "fre", language := "French", iso := "fra", value := .impossible }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .possible }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .impossible }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .possible }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .impossible }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .impossible }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .impossible }
  , { walsCode := "nbh", language := "Ghulfan", iso := "ghl", value := .impossible }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .possible }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .impossible }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .impossible }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .impossible }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .impossible }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .impossible }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .impossible }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .possible }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .possible }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .possible }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .possible }
  , { walsCode := "grn", language := "Gurenne", iso := "gur", value := .impossible }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .possible }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .impossible }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .impossible }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .impossible }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .possible }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .impossible }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .impossible }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .possible }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .possible }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .impossible }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .possible }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .impossible }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .impossible }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .impossible }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .impossible }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .impossible }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .possible }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .impossible }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .possible }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .possible }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .possible }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .impossible }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .possible }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .possible }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .impossible }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .impossible }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .possible }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .impossible }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .impossible }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .impossible }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .impossible }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .possible }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .impossible }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .possible }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .possible }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .impossible }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .impossible }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .impossible }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .possible }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .impossible }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .possible }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .possible }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .possible }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .impossible }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .possible }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .impossible }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .possible }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .impossible }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .possible }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .possible }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .possible }
  , { walsCode := "kko", language := "Koranko", iso := "knk", value := .impossible }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .impossible }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .impossible }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .impossible }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .impossible }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .possible }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .impossible }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .possible }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .impossible }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .possible }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .impossible }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .possible }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .impossible }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .impossible }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .possible }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .impossible }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .possible }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .impossible }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .impossible }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .impossible }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .impossible }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .impossible }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .possible }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .possible }
  , { walsCode := "lnw", language := "Lonwolwol", iso := "crc", value := .impossible }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .possible }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .possible }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .impossible }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .possible }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .impossible }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .possible }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .impossible }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .possible }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .impossible }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .possible }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .impossible }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .impossible }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .possible }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .possible }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .possible }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .impossible }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .impossible }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .possible }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .possible }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .impossible }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .possible }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .possible }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .possible }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .impossible }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .impossible }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .possible }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .impossible }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .impossible }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .possible }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .impossible }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .impossible }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .impossible }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .impossible }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .possible }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .impossible }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .impossible }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .possible }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .impossible }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .impossible }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .impossible }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .impossible }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .impossible }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .possible }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .impossible }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .impossible }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .possible }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .possible }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .possible }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .impossible }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .possible }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .impossible }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .impossible }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .possible }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .possible }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .possible }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .impossible }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .impossible }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .impossible }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .possible }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .possible }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .impossible }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .impossible }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .impossible }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .impossible }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .impossible }
  , { walsCode := "ojs", language := "Ojibwa (Severn)", iso := "ojs", value := .possible }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .impossible }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .possible }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .impossible }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .impossible }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .impossible }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .impossible }
  , { walsCode := "plr", language := "Palor", iso := "fap", value := .possible }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .impossible }
  , { walsCode := "pap", language := "Papiamentu", iso := "pap", value := .impossible }
  , { walsCode := "prd", language := "Parji (Dravidian)", iso := "pci", value := .impossible }
  , { walsCode := "ptp", language := "Patpatar", iso := "gfk", value := .possible }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .possible }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .possible }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .impossible }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .impossible }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .impossible }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .possible }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .possible }
  , { walsCode := "pop", language := "Popoloca (Metzontla)", iso := "pbe", value := .possible }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .possible }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .possible }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .possible }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .impossible }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .possible }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .possible }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .impossible }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .impossible }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .possible }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .possible }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .possible }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .impossible }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .possible }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .possible }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .possible }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .possible }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .impossible }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .possible }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .impossible }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .possible }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .impossible }
  , { walsCode := "sey", language := "Seychelles Creole", iso := "crs", value := .impossible }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .possible }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .possible }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .impossible }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .possible }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .possible }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .possible }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .impossible }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .impossible }
  , { walsCode := "som", language := "Somali", iso := "som", value := .possible }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .possible }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .impossible }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .impossible }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .impossible }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .possible }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .possible }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .impossible }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .impossible }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .impossible }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .impossible }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .possible }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .possible }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .possible }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .impossible }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .possible }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .possible }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .impossible }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .impossible }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .impossible }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .possible }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .possible }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .impossible }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .impossible }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .possible }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .impossible }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .impossible }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .possible }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .impossible }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .possible }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .possible }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .possible }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .possible }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .possible }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .possible }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .possible }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .impossible }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .impossible }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .impossible }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .impossible }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .possible }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .impossible }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .possible }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .possible }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .possible }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .possible }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .possible }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .impossible }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .possible }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .impossible }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .impossible }
  , { walsCode := "wrp", language := "Waropen", iso := "wrp", value := .possible }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .possible }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .impossible }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .impossible }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .impossible }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .impossible }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .possible }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .possible }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .impossible }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .possible }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .possible }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .impossible }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .possible }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .impossible }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .possible }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .impossible }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .impossible }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .impossible }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .possible }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .possible }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .impossible }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .impossible }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .impossible }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .impossible }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .impossible }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .impossible }
  ]

-- Count verification
theorem total_count : allData.length = 386 := by native_decide

theorem count_impossible :
    (allData.filter (·.value == .impossible)).length = 211 := by native_decide
theorem count_possible :
    (allData.filter (·.value == .possible)).length = 175 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F120A
