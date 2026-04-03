import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 34A: Occurrence of Nominal Plurality
@cite{haspelmath-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 34A`.

Chapter 34, 291 languages.
-/

namespace Core.WALS.F34A

/-- WALS 34A values. -/
inductive PluralityOccurrence where
  | noNominalPlural  -- No nominal plural (28 languages)
  | onlyHumanNounsOptional  -- Only human nouns, optional (20 languages)
  | onlyHumanNounsObligatory  -- Only human nouns, obligatory (40 languages)
  | allNounsAlwaysOptional  -- All nouns, always optional (55 languages)
  | allNounsOptionalInInanimates  -- All nouns, optional in inanimates (15 languages)
  | allNounsAlwaysObligatory  -- All nouns, always obligatory (133 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 34A dataset (291 languages). -/
def allData : List (Datapoint PluralityOccurrence) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .allNounsAlwaysObligatory }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noNominalPlural }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noNominalPlural }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .allNounsAlwaysOptional }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .allNounsAlwaysObligatory }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .allNounsAlwaysOptional }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .allNounsAlwaysObligatory }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .allNounsAlwaysOptional }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .onlyHumanNounsOptional }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .onlyHumanNounsObligatory }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .onlyHumanNounsOptional }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .allNounsAlwaysObligatory }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .allNounsAlwaysObligatory }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .allNounsAlwaysObligatory }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .allNounsAlwaysOptional }
  , { walsCode := "blj", language := "Baale", iso := "koe", value := .allNounsAlwaysObligatory }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .allNounsAlwaysObligatory }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .allNounsAlwaysObligatory }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .allNounsAlwaysOptional }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .allNounsAlwaysObligatory }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .allNounsAlwaysObligatory }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .allNounsAlwaysOptional }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .allNounsAlwaysObligatory }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .allNounsAlwaysOptional }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .allNounsOptionalInInanimates }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .onlyHumanNounsOptional }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .noNominalPlural }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .allNounsAlwaysObligatory }
  , { walsCode := "boz", language := "Bozo (Tigemaxo)", iso := "boz", value := .allNounsAlwaysOptional }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .allNounsAlwaysObligatory }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .allNounsAlwaysOptional }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .allNounsAlwaysObligatory }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .allNounsOptionalInInanimates }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .allNounsAlwaysObligatory }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .onlyHumanNounsOptional }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .allNounsAlwaysOptional }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .onlyHumanNounsObligatory }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .allNounsAlwaysObligatory }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noNominalPlural }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .onlyHumanNounsObligatory }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .allNounsAlwaysObligatory }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .allNounsOptionalInInanimates }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .onlyHumanNounsObligatory }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .onlyHumanNounsObligatory }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .onlyHumanNounsObligatory }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .allNounsAlwaysObligatory }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .allNounsAlwaysObligatory }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .allNounsAlwaysObligatory }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .onlyHumanNounsOptional }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .allNounsAlwaysObligatory }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .allNounsAlwaysObligatory }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .allNounsAlwaysObligatory }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .allNounsAlwaysObligatory }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .allNounsOptionalInInanimates }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .allNounsAlwaysObligatory }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .allNounsAlwaysOptional }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .allNounsAlwaysOptional }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .allNounsOptionalInInanimates }
  , { walsCode := "dug", language := "Dullay (Gollango)", iso := "gwd", value := .allNounsAlwaysObligatory }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .allNounsAlwaysObligatory }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .allNounsOptionalInInanimates }
  , { walsCode := "eng", language := "English", iso := "eng", value := .allNounsAlwaysObligatory }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .onlyHumanNounsObligatory }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .allNounsAlwaysObligatory }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .allNounsAlwaysObligatory }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .allNounsAlwaysObligatory }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .allNounsAlwaysObligatory }
  , { walsCode := "fre", language := "French", iso := "fra", value := .allNounsAlwaysObligatory }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .allNounsAlwaysObligatory }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .onlyHumanNounsObligatory }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .onlyHumanNounsObligatory }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .allNounsAlwaysOptional }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .allNounsAlwaysObligatory }
  , { walsCode := "ger", language := "German", iso := "deu", value := .allNounsAlwaysObligatory }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .allNounsAlwaysObligatory }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .allNounsAlwaysObligatory }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .allNounsAlwaysObligatory }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .allNounsAlwaysObligatory }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .onlyHumanNounsOptional }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .allNounsAlwaysObligatory }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .noNominalPlural }
  , { walsCode := "gus", language := "Gusii", iso := "guz", value := .allNounsAlwaysObligatory }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .onlyHumanNounsOptional }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .allNounsAlwaysObligatory }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .allNounsAlwaysOptional }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .allNounsAlwaysObligatory }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .allNounsAlwaysObligatory }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .onlyHumanNounsOptional }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .allNounsAlwaysOptional }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noNominalPlural }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .allNounsAlwaysObligatory }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .allNounsAlwaysObligatory }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .allNounsAlwaysObligatory }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .allNounsAlwaysObligatory }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .allNounsAlwaysObligatory }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noNominalPlural }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .allNounsAlwaysOptional }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .allNounsAlwaysObligatory }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .allNounsAlwaysObligatory }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .allNounsAlwaysObligatory }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .allNounsAlwaysObligatory }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .allNounsAlwaysOptional }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .onlyHumanNounsObligatory }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .onlyHumanNounsOptional }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .allNounsAlwaysObligatory }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .onlyHumanNounsObligatory }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .onlyHumanNounsObligatory }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noNominalPlural }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .allNounsOptionalInInanimates }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .allNounsAlwaysObligatory }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noNominalPlural }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .allNounsAlwaysObligatory }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .allNounsAlwaysObligatory }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .allNounsAlwaysOptional }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .allNounsAlwaysObligatory }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .allNounsAlwaysOptional }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .onlyHumanNounsOptional }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .onlyHumanNounsObligatory }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .onlyHumanNounsObligatory }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .allNounsAlwaysObligatory }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noNominalPlural }
  , { walsCode := "kda", language := "Konda", iso := "kfc", value := .allNounsAlwaysObligatory }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .allNounsAlwaysObligatory }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .onlyHumanNounsObligatory }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .allNounsAlwaysObligatory }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .onlyHumanNounsObligatory }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .allNounsAlwaysObligatory }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .allNounsAlwaysObligatory }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .allNounsAlwaysOptional }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .allNounsAlwaysObligatory }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .allNounsAlwaysObligatory }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .allNounsAlwaysObligatory }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .onlyHumanNounsObligatory }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .allNounsAlwaysOptional }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .onlyHumanNounsOptional }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .allNounsAlwaysObligatory }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .allNounsAlwaysOptional }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .onlyHumanNounsObligatory }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .allNounsAlwaysObligatory }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .allNounsAlwaysObligatory }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .allNounsOptionalInInanimates }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .onlyHumanNounsObligatory }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .allNounsAlwaysObligatory }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .allNounsAlwaysObligatory }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .allNounsAlwaysObligatory }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .noNominalPlural }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .allNounsAlwaysObligatory }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .allNounsOptionalInInanimates }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .allNounsOptionalInInanimates }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .allNounsAlwaysObligatory }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .onlyHumanNounsObligatory }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .allNounsOptionalInInanimates }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .noNominalPlural }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .allNounsAlwaysOptional }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .allNounsAlwaysOptional }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .allNounsAlwaysObligatory }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .allNounsAlwaysObligatory }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .allNounsAlwaysObligatory }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .onlyHumanNounsObligatory }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .allNounsAlwaysOptional }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noNominalPlural }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .onlyHumanNounsOptional }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .allNounsAlwaysOptional }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .allNounsAlwaysObligatory }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noNominalPlural }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noNominalPlural }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .onlyHumanNounsOptional }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .onlyHumanNounsObligatory }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .onlyHumanNounsOptional }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noNominalPlural }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .allNounsOptionalInInanimates }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .allNounsAlwaysOptional }
  , { walsCode := "mig", language := "Migama", iso := "mmy", value := .allNounsAlwaysObligatory }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .allNounsAlwaysOptional }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .allNounsAlwaysObligatory }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .allNounsAlwaysOptional }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .allNounsAlwaysObligatory }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .allNounsOptionalInInanimates }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .allNounsAlwaysObligatory }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .allNounsAlwaysOptional }
  , { walsCode := "nmi", language := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", value := .allNounsAlwaysObligatory }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .allNounsAlwaysOptional }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .allNounsAlwaysObligatory }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .allNounsAlwaysOptional }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .onlyHumanNounsObligatory }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .onlyHumanNounsOptional }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .onlyHumanNounsObligatory }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .allNounsAlwaysOptional }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .allNounsAlwaysOptional }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .noNominalPlural }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .allNounsAlwaysObligatory }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .allNounsAlwaysOptional }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .allNounsAlwaysObligatory }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .allNounsAlwaysObligatory }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .allNounsAlwaysObligatory }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .allNounsAlwaysObligatory }
  , { walsCode := "olu", language := "Olutec", iso := "plo", value := .allNounsAlwaysOptional }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .allNounsAlwaysOptional }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .onlyHumanNounsOptional }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .allNounsOptionalInInanimates }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .onlyHumanNounsObligatory }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .allNounsAlwaysObligatory }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .allNounsAlwaysObligatory }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .onlyHumanNounsObligatory }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .allNounsAlwaysObligatory }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noNominalPlural }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .onlyHumanNounsOptional }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .onlyHumanNounsObligatory }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .allNounsAlwaysObligatory }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .allNounsAlwaysObligatory }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .allNounsAlwaysOptional }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .allNounsAlwaysObligatory }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .onlyHumanNounsObligatory }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .allNounsAlwaysOptional }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .onlyHumanNounsObligatory }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .allNounsAlwaysObligatory }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .onlyHumanNounsObligatory }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .allNounsAlwaysObligatory }
  , { walsCode := "ski", language := "Saami (Kildin)", iso := "sjd", value := .allNounsAlwaysObligatory }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .allNounsAlwaysObligatory }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .onlyHumanNounsObligatory }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noNominalPlural }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .onlyHumanNounsObligatory }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .allNounsAlwaysObligatory }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .onlyHumanNounsObligatory }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .allNounsAlwaysObligatory }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .allNounsAlwaysObligatory }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .allNounsAlwaysOptional }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .allNounsAlwaysObligatory }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .allNounsAlwaysObligatory }
  , { walsCode := "som", language := "Somali", iso := "som", value := .allNounsAlwaysObligatory }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .noNominalPlural }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .allNounsAlwaysObligatory }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .allNounsAlwaysOptional }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .allNounsAlwaysObligatory }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .onlyHumanNounsObligatory }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .onlyHumanNounsOptional }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .allNounsAlwaysOptional }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .allNounsAlwaysObligatory }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .allNounsAlwaysObligatory }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .allNounsAlwaysObligatory }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .onlyHumanNounsObligatory }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .allNounsAlwaysOptional }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .allNounsAlwaysObligatory }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .allNounsAlwaysOptional }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .onlyHumanNounsObligatory }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .allNounsOptionalInInanimates }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .allNounsAlwaysOptional }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .allNounsAlwaysObligatory }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .allNounsAlwaysObligatory }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .allNounsAlwaysOptional }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .allNounsAlwaysOptional }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .noNominalPlural }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .allNounsAlwaysOptional }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noNominalPlural }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .allNounsAlwaysObligatory }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .onlyHumanNounsObligatory }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .allNounsAlwaysObligatory }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .onlyHumanNounsObligatory }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .onlyHumanNounsObligatory }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .noNominalPlural }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .allNounsAlwaysObligatory }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .onlyHumanNounsObligatory }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .allNounsAlwaysObligatory }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .allNounsAlwaysObligatory }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .allNounsAlwaysObligatory }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .allNounsAlwaysObligatory }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .onlyHumanNounsOptional }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .allNounsAlwaysObligatory }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .allNounsAlwaysOptional }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noNominalPlural }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .allNounsAlwaysOptional }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .allNounsAlwaysOptional }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .allNounsAlwaysOptional }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .noNominalPlural }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .onlyHumanNounsOptional }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .allNounsAlwaysObligatory }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .allNounsAlwaysOptional }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .allNounsAlwaysOptional }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .allNounsAlwaysObligatory }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noNominalPlural }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .allNounsAlwaysObligatory }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .noNominalPlural }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .allNounsAlwaysOptional }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .allNounsAlwaysObligatory }
  , { walsCode := "zaq", language := "Zapotec (Quiegolani)", iso := "zpi", value := .noNominalPlural }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .allNounsAlwaysObligatory }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .allNounsAlwaysObligatory }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .allNounsAlwaysObligatory }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .allNounsAlwaysObligatory }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .allNounsAlwaysObligatory }
  ]

-- Count verification
theorem total_count : allData.length = 291 := by native_decide

theorem count_noNominalPlural :
    (allData.filter (·.value == .noNominalPlural)).length = 28 := by native_decide
theorem count_onlyHumanNounsOptional :
    (allData.filter (·.value == .onlyHumanNounsOptional)).length = 20 := by native_decide
theorem count_onlyHumanNounsObligatory :
    (allData.filter (·.value == .onlyHumanNounsObligatory)).length = 40 := by native_decide
theorem count_allNounsAlwaysOptional :
    (allData.filter (·.value == .allNounsAlwaysOptional)).length = 55 := by native_decide
theorem count_allNounsOptionalInInanimates :
    (allData.filter (·.value == .allNounsOptionalInInanimates)).length = 15 := by native_decide
theorem count_allNounsAlwaysObligatory :
    (allData.filter (·.value == .allNounsAlwaysObligatory)).length = 133 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F34A
