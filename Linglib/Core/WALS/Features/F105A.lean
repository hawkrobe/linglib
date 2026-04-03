import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 105A: Ditransitive Constructions: The Verb 'Give'
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 105A`.

Chapter 105, 378 languages.
-/

namespace Core.WALS.F105A

/-- WALS 105A values. -/
inductive DitransitiveConstructionsTheVerbGive where
  | indirectObjectConstruction  -- Indirect-object construction (189 languages)
  | doubleObjectConstruction  -- Double-object construction (84 languages)
  | secondaryObjectConstruction  -- Secondary-object construction (65 languages)
  | mixed  -- Mixed (40 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 105A dataset (378 languages). -/
def allData : List (Datapoint DitransitiveConstructionsTheVerbGive) :=
  [ { walsCode := "xam", language := "/Xam", iso := "xam", value := .doubleObjectConstruction }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .indirectObjectConstruction }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .indirectObjectConstruction }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .mixed }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .secondaryObjectConstruction }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .doubleObjectConstruction }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .secondaryObjectConstruction }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .indirectObjectConstruction }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .secondaryObjectConstruction }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .secondaryObjectConstruction }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .indirectObjectConstruction }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .mixed }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .indirectObjectConstruction }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .indirectObjectConstruction }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .doubleObjectConstruction }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .indirectObjectConstruction }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .mixed }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .mixed }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .doubleObjectConstruction }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .indirectObjectConstruction }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .mixed }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .indirectObjectConstruction }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .mixed }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .indirectObjectConstruction }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .indirectObjectConstruction }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .indirectObjectConstruction }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .doubleObjectConstruction }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .indirectObjectConstruction }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .secondaryObjectConstruction }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .secondaryObjectConstruction }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .indirectObjectConstruction }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .indirectObjectConstruction }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .indirectObjectConstruction }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .mixed }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .secondaryObjectConstruction }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .secondaryObjectConstruction }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .indirectObjectConstruction }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .indirectObjectConstruction }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .indirectObjectConstruction }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .indirectObjectConstruction }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .secondaryObjectConstruction }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .indirectObjectConstruction }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .indirectObjectConstruction }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .secondaryObjectConstruction }
  , { walsCode := "boz", language := "Bozo (Tigemaxo)", iso := "boz", value := .indirectObjectConstruction }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .indirectObjectConstruction }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .indirectObjectConstruction }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .indirectObjectConstruction }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .doubleObjectConstruction }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .indirectObjectConstruction }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .indirectObjectConstruction }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .indirectObjectConstruction }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .mixed }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .secondaryObjectConstruction }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .indirectObjectConstruction }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .secondaryObjectConstruction }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .indirectObjectConstruction }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .indirectObjectConstruction }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .indirectObjectConstruction }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .doubleObjectConstruction }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .secondaryObjectConstruction }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .indirectObjectConstruction }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .secondaryObjectConstruction }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .doubleObjectConstruction }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .doubleObjectConstruction }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .doubleObjectConstruction }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .indirectObjectConstruction }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .doubleObjectConstruction }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .indirectObjectConstruction }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .indirectObjectConstruction }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .mixed }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .mixed }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .doubleObjectConstruction }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .mixed }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .doubleObjectConstruction }
  , { walsCode := "dug", language := "Dullay (Gollango)", iso := "gwd", value := .indirectObjectConstruction }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .mixed }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .doubleObjectConstruction }
  , { walsCode := "eng", language := "English", iso := "eng", value := .mixed }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .indirectObjectConstruction }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .secondaryObjectConstruction }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .indirectObjectConstruction }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .doubleObjectConstruction }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .indirectObjectConstruction }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .indirectObjectConstruction }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .doubleObjectConstruction }
  , { walsCode := "fre", language := "French", iso := "fra", value := .indirectObjectConstruction }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .doubleObjectConstruction }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .secondaryObjectConstruction }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .indirectObjectConstruction }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .secondaryObjectConstruction }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .indirectObjectConstruction }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .indirectObjectConstruction }
  , { walsCode := "ger", language := "German", iso := "deu", value := .indirectObjectConstruction }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .doubleObjectConstruction }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .secondaryObjectConstruction }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .doubleObjectConstruction }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .indirectObjectConstruction }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .secondaryObjectConstruction }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .indirectObjectConstruction }
  , { walsCode := "gdf", language := "Guduf", iso := "gdf", value := .indirectObjectConstruction }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .doubleObjectConstruction }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .secondaryObjectConstruction }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .indirectObjectConstruction }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .indirectObjectConstruction }
  , { walsCode := "hli", language := "Halkomelem (Island)", iso := "hur", value := .secondaryObjectConstruction }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .indirectObjectConstruction }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .secondaryObjectConstruction }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .secondaryObjectConstruction }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .doubleObjectConstruction }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .indirectObjectConstruction }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .indirectObjectConstruction }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .indirectObjectConstruction }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .mixed }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .indirectObjectConstruction }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .mixed }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .secondaryObjectConstruction }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .indirectObjectConstruction }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .indirectObjectConstruction }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .doubleObjectConstruction }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .indirectObjectConstruction }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .mixed }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .indirectObjectConstruction }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .mixed }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .indirectObjectConstruction }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .indirectObjectConstruction }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .indirectObjectConstruction }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .indirectObjectConstruction }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .indirectObjectConstruction }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .indirectObjectConstruction }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .secondaryObjectConstruction }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .indirectObjectConstruction }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .indirectObjectConstruction }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .indirectObjectConstruction }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .secondaryObjectConstruction }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .secondaryObjectConstruction }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .indirectObjectConstruction }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .mixed }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .indirectObjectConstruction }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .doubleObjectConstruction }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .indirectObjectConstruction }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .indirectObjectConstruction }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .indirectObjectConstruction }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .doubleObjectConstruction }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .indirectObjectConstruction }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .indirectObjectConstruction }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .doubleObjectConstruction }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .indirectObjectConstruction }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .secondaryObjectConstruction }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .mixed }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .indirectObjectConstruction }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .mixed }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .indirectObjectConstruction }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .doubleObjectConstruction }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .secondaryObjectConstruction }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .doubleObjectConstruction }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .doubleObjectConstruction }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .doubleObjectConstruction }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .indirectObjectConstruction }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .indirectObjectConstruction }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .doubleObjectConstruction }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .indirectObjectConstruction }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .mixed }
  , { walsCode := "kda", language := "Konda", iso := "kfc", value := .indirectObjectConstruction }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .mixed }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .indirectObjectConstruction }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .doubleObjectConstruction }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .secondaryObjectConstruction }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .mixed }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .indirectObjectConstruction }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .indirectObjectConstruction }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .indirectObjectConstruction }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .doubleObjectConstruction }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .indirectObjectConstruction }
  , { walsCode := "kug", language := "Kunming", iso := "cmn", value := .doubleObjectConstruction }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .secondaryObjectConstruction }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .indirectObjectConstruction }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .indirectObjectConstruction }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .secondaryObjectConstruction }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .indirectObjectConstruction }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .doubleObjectConstruction }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .mixed }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .indirectObjectConstruction }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .indirectObjectConstruction }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .secondaryObjectConstruction }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .doubleObjectConstruction }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .indirectObjectConstruction }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .indirectObjectConstruction }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .secondaryObjectConstruction }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .secondaryObjectConstruction }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .doubleObjectConstruction }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .indirectObjectConstruction }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .indirectObjectConstruction }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .indirectObjectConstruction }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .doubleObjectConstruction }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .indirectObjectConstruction }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .indirectObjectConstruction }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .indirectObjectConstruction }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .indirectObjectConstruction }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .indirectObjectConstruction }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .indirectObjectConstruction }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .doubleObjectConstruction }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .indirectObjectConstruction }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .indirectObjectConstruction }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .indirectObjectConstruction }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .mixed }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .doubleObjectConstruction }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .indirectObjectConstruction }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .indirectObjectConstruction }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .secondaryObjectConstruction }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .doubleObjectConstruction }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .indirectObjectConstruction }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .secondaryObjectConstruction }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .doubleObjectConstruction }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .secondaryObjectConstruction }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .doubleObjectConstruction }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .doubleObjectConstruction }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .mixed }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .indirectObjectConstruction }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .doubleObjectConstruction }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .indirectObjectConstruction }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .indirectObjectConstruction }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .mixed }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .indirectObjectConstruction }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .doubleObjectConstruction }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .doubleObjectConstruction }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .mixed }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .doubleObjectConstruction }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .indirectObjectConstruction }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .secondaryObjectConstruction }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .secondaryObjectConstruction }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .indirectObjectConstruction }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .indirectObjectConstruction }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .doubleObjectConstruction }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .indirectObjectConstruction }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .indirectObjectConstruction }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .secondaryObjectConstruction }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .indirectObjectConstruction }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .doubleObjectConstruction }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .doubleObjectConstruction }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .secondaryObjectConstruction }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .doubleObjectConstruction }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .secondaryObjectConstruction }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .indirectObjectConstruction }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .indirectObjectConstruction }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .secondaryObjectConstruction }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .secondaryObjectConstruction }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .doubleObjectConstruction }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .indirectObjectConstruction }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .indirectObjectConstruction }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .indirectObjectConstruction }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .secondaryObjectConstruction }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .secondaryObjectConstruction }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .doubleObjectConstruction }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .indirectObjectConstruction }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .indirectObjectConstruction }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .doubleObjectConstruction }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .doubleObjectConstruction }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .doubleObjectConstruction }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .doubleObjectConstruction }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .secondaryObjectConstruction }
  , { walsCode := "olu", language := "Olutec", iso := "plo", value := .mixed }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .indirectObjectConstruction }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .indirectObjectConstruction }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .indirectObjectConstruction }
  , { walsCode := "pta", language := "Paita", iso := "duf", value := .indirectObjectConstruction }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .mixed }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .secondaryObjectConstruction }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .doubleObjectConstruction }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .indirectObjectConstruction }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .indirectObjectConstruction }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .indirectObjectConstruction }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .doubleObjectConstruction }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .doubleObjectConstruction }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .doubleObjectConstruction }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .doubleObjectConstruction }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .indirectObjectConstruction }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .indirectObjectConstruction }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .indirectObjectConstruction }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .indirectObjectConstruction }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .secondaryObjectConstruction }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .indirectObjectConstruction }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .indirectObjectConstruction }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .indirectObjectConstruction }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .doubleObjectConstruction }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .indirectObjectConstruction }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .indirectObjectConstruction }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .indirectObjectConstruction }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .mixed }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .doubleObjectConstruction }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .indirectObjectConstruction }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .doubleObjectConstruction }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .indirectObjectConstruction }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .indirectObjectConstruction }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .mixed }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .indirectObjectConstruction }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .indirectObjectConstruction }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .doubleObjectConstruction }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .doubleObjectConstruction }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .secondaryObjectConstruction }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .indirectObjectConstruction }
  , { walsCode := "so", language := "So", iso := "teu", value := .indirectObjectConstruction }
  , { walsCode := "som", language := "Somali", iso := "som", value := .secondaryObjectConstruction }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .doubleObjectConstruction }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .indirectObjectConstruction }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .indirectObjectConstruction }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .indirectObjectConstruction }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .mixed }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .indirectObjectConstruction }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .doubleObjectConstruction }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .doubleObjectConstruction }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .mixed }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .indirectObjectConstruction }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .indirectObjectConstruction }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .doubleObjectConstruction }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .secondaryObjectConstruction }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .secondaryObjectConstruction }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .indirectObjectConstruction }
  , { walsCode := "trt", language := "Ternate", iso := "tft", value := .mixed }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .mixed }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .indirectObjectConstruction }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .indirectObjectConstruction }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .indirectObjectConstruction }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .mixed }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .indirectObjectConstruction }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .doubleObjectConstruction }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .doubleObjectConstruction }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .indirectObjectConstruction }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .secondaryObjectConstruction }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .secondaryObjectConstruction }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .indirectObjectConstruction }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .indirectObjectConstruction }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .indirectObjectConstruction }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .indirectObjectConstruction }
  , { walsCode := "tst", language := "Tsat", iso := "huq", value := .indirectObjectConstruction }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .indirectObjectConstruction }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .indirectObjectConstruction }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .indirectObjectConstruction }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .indirectObjectConstruction }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .doubleObjectConstruction }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .doubleObjectConstruction }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .doubleObjectConstruction }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .indirectObjectConstruction }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .indirectObjectConstruction }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .doubleObjectConstruction }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .indirectObjectConstruction }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .indirectObjectConstruction }
  , { walsCode := "uku", language := "Upper Kuskokwim", iso := "kuu", value := .indirectObjectConstruction }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .indirectObjectConstruction }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .secondaryObjectConstruction }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .doubleObjectConstruction }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .doubleObjectConstruction }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .doubleObjectConstruction }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .indirectObjectConstruction }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .doubleObjectConstruction }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .secondaryObjectConstruction }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .indirectObjectConstruction }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .secondaryObjectConstruction }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .mixed }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .mixed }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .secondaryObjectConstruction }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .indirectObjectConstruction }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .doubleObjectConstruction }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .secondaryObjectConstruction }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .mixed }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .secondaryObjectConstruction }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .indirectObjectConstruction }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .indirectObjectConstruction }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .secondaryObjectConstruction }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .doubleObjectConstruction }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .secondaryObjectConstruction }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .indirectObjectConstruction }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .indirectObjectConstruction }
  , { walsCode := "zaq", language := "Zapotec (Quiegolani)", iso := "zpi", value := .indirectObjectConstruction }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .indirectObjectConstruction }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .indirectObjectConstruction }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .secondaryObjectConstruction }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .doubleObjectConstruction }
  ]

-- Count verification
theorem total_count : allData.length = 378 := by native_decide

theorem count_indirectObjectConstruction :
    (allData.filter (·.value == .indirectObjectConstruction)).length = 189 := by native_decide
theorem count_doubleObjectConstruction :
    (allData.filter (·.value == .doubleObjectConstruction)).length = 84 := by native_decide
theorem count_secondaryObjectConstruction :
    (allData.filter (·.value == .secondaryObjectConstruction)).length = 65 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 40 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F105A
