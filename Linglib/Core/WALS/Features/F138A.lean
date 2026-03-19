/-!
# WALS Feature 138A: Tea
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 138A`.

Chapter 138, 230 languages.
-/

namespace Core.WALS.F138A

/-- WALS 138A values. -/
inductive Tea where
  | wordsDerivedFromSiniticCha  -- Words derived from Sinitic cha (110 languages)
  | wordsDerivedFromMinNanChineseTe  -- Words derived from Min Nan Chinese te (84 languages)
  | others  -- Others (36 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 138A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : Tea
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 138A dataset (230 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "abz", language := "Abaza", iso := "abq", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .others }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "alt", language := "Alsatian", iso := "gsw", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ast", language := "Asturian", iso := "ast", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .others }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bdg", language := "Badaga", iso := "bfq", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .others }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .others }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "bru", language := "Bru (Eastern)", iso := "bru", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "brj", language := "Burji", iso := "bji", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .others }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .others }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .others }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "crh", language := "Chru", iso := "cje", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "com", language := "Comorian", iso := "swb", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .others }
  , { walsCode := "cua", language := "Cua", iso := "cua", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "eng", language := "English", iso := "eng", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "fre", language := "French", iso := "fra", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "fli", language := "Ful (Liptako)", iso := "fuh", value := .others }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "gml", language := "Gamilaraay", iso := "kld", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ger", language := "German", iso := "deu", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "grt", language := "Gorontalo", iso := "gor", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "gdl", language := "Guadeloupe Creole", iso := "gcf", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .others }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "hre", language := "Hre", iso := "hre", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "inu", language := "Iñupiaq", iso := "esi", value := .others }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .others }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "krm", language := "Karaim", iso := "kdr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .others }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .others }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "keu", language := "Kenyah (Uma' Lung)", iso := "keu", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .others }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .others }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kuq", language := "Kumyk", iso := "kum", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "kjn", language := "Kunjen", iso := "kjn", value := .others }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .others }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "lcr", language := "Lesser Antillean French Creole", iso := "", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .others }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .others }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .others }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "lux", language := "Luxemburgeois", iso := "ltz", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .others }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "mol", language := "Moldavian", iso := "ron", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "nyl", language := "Nyelâyu", iso := "yly", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "occ", language := "Occitan", iso := "oci", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ojm", language := "Ojibwe (Minnesota)", iso := "ciw", value := .others }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "owc", language := "Oromo (West-Central)", iso := "gaz", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "pak", language := "Pakanha", iso := "pkn", value := .others }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .others }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .others }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "pro", language := "Provençal", iso := "oci", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .others }
  , { walsCode := "rbg", language := "Romani (Burgenland)", iso := "rmo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .others }
  , { walsCode := "rlo", language := "Romani (Lovari)", iso := "rmy", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "rse", language := "Romani (Sepecides)", iso := "rmn", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "rmc", language := "Romansch", iso := "roh", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ssh", language := "Shinassha", iso := "bwo", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "som", language := "Somali", iso := "som", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .others }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .others }
  , { walsCode := "tsw", language := "Tswana", iso := "tsn", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .others }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .others }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .others }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "yms", language := "Yemsa", iso := "jnj", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .wordsDerivedFromMinNanChineseTe }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .wordsDerivedFromSiniticCha }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .others }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .others }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .others }
  ]

-- Count verification
theorem total_count : allData.length = 230 := by native_decide

theorem count_wordsDerivedFromSiniticCha :
    (allData.filter (·.value == .wordsDerivedFromSiniticCha)).length = 110 := by native_decide
theorem count_wordsDerivedFromMinNanChineseTe :
    (allData.filter (·.value == .wordsDerivedFromMinNanChineseTe)).length = 84 := by native_decide
theorem count_others :
    (allData.filter (·.value == .others)).length = 36 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F138A
