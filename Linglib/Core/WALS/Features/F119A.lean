import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 119A: Nominal and Locational Predication
@cite{stassen-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 119A`.

Chapter 119, 386 languages.
-/

namespace Core.WALS.F119A

/-- WALS 119A values. -/
inductive NominalLocationalPredication where
  | different  -- Different (269 languages)
  | identical  -- Identical (117 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 119A dataset (386 languages). -/
def allData : List (Datapoint NominalLocationalPredication) :=
  [ { walsCode := "abz", language := "Abaza", iso := "abq", value := .different }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .different }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .different }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .different }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .different }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .different }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .different }
  , { walsCode := "ahu", language := "Aghu", iso := "ahh", value := .identical }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .different }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .different }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .different }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .different }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .identical }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .different }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .identical }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .different }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .identical }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .identical }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .identical }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .different }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .identical }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .identical }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .different }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .identical }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .identical }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .identical }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .identical }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .different }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .identical }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .different }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .identical }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .different }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .different }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .identical }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .different }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .different }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .different }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .identical }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .identical }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .different }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .different }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .identical }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .different }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .different }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .different }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .different }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .different }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .identical }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .different }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .identical }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .different }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .identical }
  , { walsCode := "brj", language := "Burji", iso := "bji", value := .different }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .different }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .identical }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .different }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .different }
  , { walsCode := "car", language := "Carib", iso := "car", value := .identical }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .different }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .different }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .different }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .identical }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .different }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .different }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .different }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .different }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .different }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .different }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .different }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .identical }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .identical }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .identical }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .different }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .different }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .different }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .different }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .identical }
  , { walsCode := "dab", language := "Daba", iso := "dbq", value := .different }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .identical }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .different }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .different }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .identical }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .different }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .identical }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .different }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .identical }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .different }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .identical }
  , { walsCode := "eng", language := "English", iso := "eng", value := .identical }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .different }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .identical }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .identical }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .identical }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .different }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .different }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .identical }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .different }
  , { walsCode := "for", language := "Fore", iso := "for", value := .different }
  , { walsCode := "fre", language := "French", iso := "fra", value := .identical }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .different }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .different }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .different }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .different }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .different }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .identical }
  , { walsCode := "nbh", language := "Ghulfan", iso := "ghl", value := .different }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .different }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .different }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .identical }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .different }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .different }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .identical }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .different }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .different }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .different }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .different }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .different }
  , { walsCode := "grn", language := "Gurenne", iso := "gur", value := .different }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .different }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .different }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .different }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .different }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .identical }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .different }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .identical }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .identical }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .different }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .different }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .identical }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .identical }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .identical }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .different }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .identical }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .different }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .different }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .different }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .different }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .different }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .different }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .different }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .different }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .different }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .different }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .different }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .different }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .identical }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .different }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .different }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .different }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .different }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .different }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .identical }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .different }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .different }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .different }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .different }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .different }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .different }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .different }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .identical }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .identical }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .different }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .different }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .different }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .different }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .different }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .identical }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .different }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .identical }
  , { walsCode := "kko", language := "Koranko", iso := "knk", value := .different }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .different }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .identical }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .different }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .different }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .different }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .different }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .different }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .different }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .different }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .different }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .different }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .different }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .different }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .identical }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .identical }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .different }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .different }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .different }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .different }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .different }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .different }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .identical }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .different }
  , { walsCode := "lnw", language := "Lonwolwol", iso := "crc", value := .different }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .identical }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .different }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .different }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .identical }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .different }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .different }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .different }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .identical }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .different }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .different }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .different }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .different }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .identical }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .identical }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .different }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .different }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .different }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .identical }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .different }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .different }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .different }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .different }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .identical }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .identical }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .different }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .different }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .different }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .different }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .different }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .identical }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .different }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .different }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .identical }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .different }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .different }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .identical }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .different }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .different }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .different }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .different }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .different }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .identical }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .different }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .different }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .different }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .identical }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .different }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .different }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .different }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .identical }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .different }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .identical }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .identical }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .identical }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .different }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .identical }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .different }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .different }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .different }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .different }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .identical }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .different }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .different }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .different }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .different }
  , { walsCode := "ojs", language := "Ojibwa (Severn)", iso := "ojs", value := .different }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .different }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .identical }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .different }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .different }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .different }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .different }
  , { walsCode := "plr", language := "Palor", iso := "fap", value := .different }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .different }
  , { walsCode := "pap", language := "Papiamentu", iso := "pap", value := .different }
  , { walsCode := "prd", language := "Parji (Dravidian)", iso := "pci", value := .different }
  , { walsCode := "ptp", language := "Patpatar", iso := "gfk", value := .different }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .different }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .different }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .identical }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .identical }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .different }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .different }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .identical }
  , { walsCode := "pop", language := "Popoloca (Metzontla)", iso := "pbe", value := .different }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .identical }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .identical }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .identical }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .different }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .different }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .identical }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .identical }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .identical }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .different }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .different }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .identical }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .identical }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .different }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .different }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .identical }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .different }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .different }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .identical }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .different }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .different }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .identical }
  , { walsCode := "sey", language := "Seychelles Creole", iso := "crs", value := .different }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .different }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .identical }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .identical }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .different }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .different }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .identical }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .different }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .different }
  , { walsCode := "som", language := "Somali", iso := "som", value := .different }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .different }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .different }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .different }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .different }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .different }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .different }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .different }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .identical }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .identical }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .different }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .different }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .identical }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .different }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .identical }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .identical }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .different }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .different }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .different }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .different }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .different }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .different }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .identical }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .different }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .different }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .identical }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .different }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .different }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .different }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .different }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .different }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .different }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .different }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .different }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .different }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .different }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .identical }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .different }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .different }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .different }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .different }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .different }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .identical }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .different }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .different }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .identical }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .identical }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .different }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .different }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .identical }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .different }
  , { walsCode := "wrp", language := "Waropen", iso := "wrp", value := .different }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .different }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .identical }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .different }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .identical }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .different }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .different }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .different }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .different }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .identical }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .identical }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .identical }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .different }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .identical }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .identical }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .different }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .different }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .different }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .different }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .different }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .different }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .different }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .different }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .identical }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .different }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .identical }
  ]

-- Count verification
theorem total_count : allData.length = 386 := by native_decide

theorem count_different :
    (allData.filter (·.value == .different)).length = 269 := by native_decide
theorem count_identical :
    (allData.filter (·.value == .identical)).length = 117 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F119A
