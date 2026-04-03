import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 118A: Predicative Adjectives
@cite{stassen-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 118A`.

Chapter 118, 386 languages.
-/

namespace Core.WALS.F118A

/-- WALS 118A values. -/
inductive PredicativeAdjectiveType where
  | verbalEncoding  -- Verbal encoding (151 languages)
  | nonverbalEncoding  -- Nonverbal encoding (132 languages)
  | mixed  -- Mixed (103 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 118A dataset (386 languages). -/
def allData : List (Datapoint PredicativeAdjectiveType) :=
  [ { walsCode := "abz", language := "Abaza", iso := "abq", value := .verbalEncoding }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .verbalEncoding }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .verbalEncoding }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .mixed }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .mixed }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .verbalEncoding }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .verbalEncoding }
  , { walsCode := "ahu", language := "Aghu", iso := "ahh", value := .nonverbalEncoding }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .verbalEncoding }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .mixed }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .verbalEncoding }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .mixed }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .nonverbalEncoding }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nonverbalEncoding }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .nonverbalEncoding }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .verbalEncoding }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .nonverbalEncoding }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nonverbalEncoding }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .nonverbalEncoding }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .mixed }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .mixed }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .nonverbalEncoding }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .verbalEncoding }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nonverbalEncoding }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .nonverbalEncoding }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .nonverbalEncoding }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .nonverbalEncoding }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .nonverbalEncoding }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .mixed }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .verbalEncoding }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .nonverbalEncoding }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .mixed }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nonverbalEncoding }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .mixed }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .mixed }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .nonverbalEncoding }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .verbalEncoding }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .mixed }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .nonverbalEncoding }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .verbalEncoding }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .verbalEncoding }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .mixed }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .verbalEncoding }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .verbalEncoding }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .verbalEncoding }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .verbalEncoding }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .verbalEncoding }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .nonverbalEncoding }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .mixed }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .nonverbalEncoding }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .mixed }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .nonverbalEncoding }
  , { walsCode := "brj", language := "Burji", iso := "bji", value := .mixed }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .verbalEncoding }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .nonverbalEncoding }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .mixed }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .verbalEncoding }
  , { walsCode := "car", language := "Carib", iso := "car", value := .nonverbalEncoding }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .verbalEncoding }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .verbalEncoding }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .mixed }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .nonverbalEncoding }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .mixed }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .mixed }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .verbalEncoding }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .verbalEncoding }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .verbalEncoding }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .verbalEncoding }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .nonverbalEncoding }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .nonverbalEncoding }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .mixed }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .verbalEncoding }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .verbalEncoding }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .mixed }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .verbalEncoding }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .verbalEncoding }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .nonverbalEncoding }
  , { walsCode := "dab", language := "Daba", iso := "dbq", value := .mixed }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nonverbalEncoding }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .mixed }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .verbalEncoding }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .nonverbalEncoding }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .mixed }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .mixed }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .mixed }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .nonverbalEncoding }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nonverbalEncoding }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .nonverbalEncoding }
  , { walsCode := "eng", language := "English", iso := "eng", value := .nonverbalEncoding }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .verbalEncoding }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .nonverbalEncoding }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .nonverbalEncoding }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .nonverbalEncoding }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .mixed }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .verbalEncoding }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .nonverbalEncoding }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .mixed }
  , { walsCode := "for", language := "Fore", iso := "for", value := .nonverbalEncoding }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nonverbalEncoding }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .verbalEncoding }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .nonverbalEncoding }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .verbalEncoding }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .verbalEncoding }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .mixed }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .nonverbalEncoding }
  , { walsCode := "nbh", language := "Ghulfan", iso := "ghl", value := .mixed }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .verbalEncoding }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .verbalEncoding }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .nonverbalEncoding }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .mixed }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .verbalEncoding }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nonverbalEncoding }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .mixed }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .verbalEncoding }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .verbalEncoding }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .mixed }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .nonverbalEncoding }
  , { walsCode := "grn", language := "Gurenne", iso := "gur", value := .mixed }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .nonverbalEncoding }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .verbalEncoding }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .mixed }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .nonverbalEncoding }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nonverbalEncoding }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .verbalEncoding }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .nonverbalEncoding }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nonverbalEncoding }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .verbalEncoding }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .mixed }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .nonverbalEncoding }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .nonverbalEncoding }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .verbalEncoding }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .verbalEncoding }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .nonverbalEncoding }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .mixed }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .verbalEncoding }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .verbalEncoding }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .nonverbalEncoding }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .verbalEncoding }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .mixed }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .nonverbalEncoding }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .mixed }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nonverbalEncoding }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .verbalEncoding }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .mixed }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .verbalEncoding }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .verbalEncoding }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .verbalEncoding }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .mixed }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .verbalEncoding }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .nonverbalEncoding }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .nonverbalEncoding }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .nonverbalEncoding }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .mixed }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .verbalEncoding }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .verbalEncoding }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .mixed }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .verbalEncoding }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .nonverbalEncoding }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .nonverbalEncoding }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .nonverbalEncoding }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .nonverbalEncoding }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .mixed }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .verbalEncoding }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .verbalEncoding }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .verbalEncoding }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .verbalEncoding }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .nonverbalEncoding }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .nonverbalEncoding }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .nonverbalEncoding }
  , { walsCode := "kko", language := "Koranko", iso := "knk", value := .verbalEncoding }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .mixed }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .mixed }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .mixed }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .verbalEncoding }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .mixed }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .nonverbalEncoding }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .verbalEncoding }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .verbalEncoding }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .nonverbalEncoding }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .mixed }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .verbalEncoding }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .verbalEncoding }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .verbalEncoding }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .nonverbalEncoding }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .nonverbalEncoding }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .verbalEncoding }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .mixed }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .nonverbalEncoding }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .verbalEncoding }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .mixed }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .verbalEncoding }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .nonverbalEncoding }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nonverbalEncoding }
  , { walsCode := "lnw", language := "Lonwolwol", iso := "crc", value := .verbalEncoding }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .mixed }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .mixed }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .mixed }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .nonverbalEncoding }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .verbalEncoding }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .mixed }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .nonverbalEncoding }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .nonverbalEncoding }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .verbalEncoding }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .mixed }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .nonverbalEncoding }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .verbalEncoding }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .mixed }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .mixed }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .verbalEncoding }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .mixed }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .verbalEncoding }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .nonverbalEncoding }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .mixed }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .mixed }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .nonverbalEncoding }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .mixed }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .nonverbalEncoding }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .nonverbalEncoding }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .verbalEncoding }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .mixed }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .verbalEncoding }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .verbalEncoding }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .verbalEncoding }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .nonverbalEncoding }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .mixed }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .verbalEncoding }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .verbalEncoding }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .verbalEncoding }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .mixed }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .nonverbalEncoding }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .verbalEncoding }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .mixed }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .mixed }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .verbalEncoding }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .verbalEncoding }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .mixed }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .verbalEncoding }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .mixed }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .verbalEncoding }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .nonverbalEncoding }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .mixed }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .nonverbalEncoding }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .verbalEncoding }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .nonverbalEncoding }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .nonverbalEncoding }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .nonverbalEncoding }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .mixed }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .nonverbalEncoding }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .mixed }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .nonverbalEncoding }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nonverbalEncoding }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .verbalEncoding }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .verbalEncoding }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .verbalEncoding }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .mixed }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .mixed }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .mixed }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .verbalEncoding }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .verbalEncoding }
  , { walsCode := "ojs", language := "Ojibwa (Severn)", iso := "ojs", value := .verbalEncoding }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .verbalEncoding }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .mixed }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .mixed }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .verbalEncoding }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .mixed }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .verbalEncoding }
  , { walsCode := "plr", language := "Palor", iso := "fap", value := .verbalEncoding }
  , { walsCode := "pna", language := "Pamona", iso := "pmf", value := .verbalEncoding }
  , { walsCode := "pap", language := "Papiamentu", iso := "pap", value := .verbalEncoding }
  , { walsCode := "prd", language := "Parji (Dravidian)", iso := "pci", value := .nonverbalEncoding }
  , { walsCode := "ptp", language := "Patpatar", iso := "gfk", value := .verbalEncoding }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .verbalEncoding }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .verbalEncoding }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .mixed }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nonverbalEncoding }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .verbalEncoding }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .nonverbalEncoding }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .nonverbalEncoding }
  , { walsCode := "pop", language := "Popoloca (Metzontla)", iso := "pbe", value := .mixed }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .nonverbalEncoding }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .nonverbalEncoding }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nonverbalEncoding }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .nonverbalEncoding }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .nonverbalEncoding }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .nonverbalEncoding }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .nonverbalEncoding }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .nonverbalEncoding }
  , { walsCode := "rti", language := "Roti", iso := "twu", value := .mixed }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .verbalEncoding }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nonverbalEncoding }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .nonverbalEncoding }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .verbalEncoding }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .verbalEncoding }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .verbalEncoding }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .verbalEncoding }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .verbalEncoding }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .nonverbalEncoding }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .verbalEncoding }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .nonverbalEncoding }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .nonverbalEncoding }
  , { walsCode := "sey", language := "Seychelles Creole", iso := "crs", value := .verbalEncoding }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .mixed }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .nonverbalEncoding }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .mixed }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .nonverbalEncoding }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .nonverbalEncoding }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .nonverbalEncoding }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .verbalEncoding }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .verbalEncoding }
  , { walsCode := "som", language := "Somali", iso := "som", value := .mixed }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .mixed }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nonverbalEncoding }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .verbalEncoding }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .verbalEncoding }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .verbalEncoding }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .verbalEncoding }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mixed }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .mixed }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .nonverbalEncoding }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .verbalEncoding }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .mixed }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .nonverbalEncoding }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .verbalEncoding }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .nonverbalEncoding }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .nonverbalEncoding }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .verbalEncoding }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .mixed }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .mixed }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .verbalEncoding }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .verbalEncoding }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .verbalEncoding }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .nonverbalEncoding }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .verbalEncoding }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .nonverbalEncoding }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .verbalEncoding }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .verbalEncoding }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .verbalEncoding }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .verbalEncoding }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .verbalEncoding }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .nonverbalEncoding }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .verbalEncoding }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .mixed }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .verbalEncoding }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .mixed }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .verbalEncoding }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .nonverbalEncoding }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .verbalEncoding }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .verbalEncoding }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .verbalEncoding }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .mixed }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .verbalEncoding }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .mixed }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .nonverbalEncoding }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .verbalEncoding }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nonverbalEncoding }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .nonverbalEncoding }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .mixed }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .verbalEncoding }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .nonverbalEncoding }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .verbalEncoding }
  , { walsCode := "wrp", language := "Waropen", iso := "wrp", value := .mixed }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .nonverbalEncoding }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .nonverbalEncoding }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .nonverbalEncoding }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .mixed }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .mixed }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .verbalEncoding }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .verbalEncoding }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .verbalEncoding }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .nonverbalEncoding }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nonverbalEncoding }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .nonverbalEncoding }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .verbalEncoding }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .verbalEncoding }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nonverbalEncoding }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .mixed }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .verbalEncoding }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .verbalEncoding }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .verbalEncoding }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .nonverbalEncoding }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .mixed }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .mixed }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .mixed }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .nonverbalEncoding }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .verbalEncoding }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .mixed }
  ]

-- Count verification
theorem total_count : allData.length = 386 := by native_decide

theorem count_verbalEncoding :
    (allData.filter (·.value == .verbalEncoding)).length = 151 := by native_decide
theorem count_nonverbalEncoding :
    (allData.filter (·.value == .nonverbalEncoding)).length = 132 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 103 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F118A
