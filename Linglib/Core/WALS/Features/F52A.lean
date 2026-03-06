/-!
# WALS Feature 52A: Comitatives and Instrumentals
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 52A`.

Chapter 52, 322 languages.
-/

namespace Core.WALS.F52A

/-- WALS 52A values. -/
inductive ComitativesAndInstrumentals where
  | identity  -- Identity (76 languages)
  | differentiation  -- Differentiation (213 languages)
  | mixed  -- Mixed (33 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 52A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ComitativesAndInstrumentals
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 52A dataset (322 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xam", language := "/Xam", iso := "xam", value := .identity }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .differentiation }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .differentiation }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .identity }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .differentiation }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .identity }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .differentiation }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .differentiation }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .identity }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .mixed }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .differentiation }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .differentiation }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .identity }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .differentiation }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .differentiation }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .differentiation }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .differentiation }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .differentiation }
  , { walsCode := "arr", language := "Arrernte", iso := "", value := .differentiation }
  , { walsCode := "auy", language := "Auyana", iso := "auy", value := .differentiation }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .differentiation }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .identity }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .identity }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .differentiation }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .identity }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .mixed }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .identity }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .identity }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .differentiation }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .differentiation }
  , { walsCode := "bou", language := "Berber (Wargla)", iso := "oua", value := .differentiation }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .identity }
  , { walsCode := "bnm", language := "Binumarien", iso := "bjr", value := .differentiation }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .differentiation }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .differentiation }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .differentiation }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .identity }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .differentiation }
  , { walsCode := "car", language := "Carib", iso := "car", value := .differentiation }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .identity }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .differentiation }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .identity }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .differentiation }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .identity }
  , { walsCode := "col", language := "Chol", iso := "ctu", value := .identity }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .differentiation }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .identity }
  , { walsCode := "cog", language := "Cogui", iso := "kog", value := .differentiation }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .differentiation }
  , { walsCode := "com", language := "Comorian", iso := "swb", value := .differentiation }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .identity }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .mixed }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .differentiation }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .differentiation }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .differentiation }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .differentiation }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .differentiation }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .differentiation }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .identity }
  , { walsCode := "des", language := "Desano", iso := "des", value := .differentiation }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .differentiation }
  , { walsCode := "dug", language := "Dullay (Gollango)", iso := "gwd", value := .differentiation }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .differentiation }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .differentiation }
  , { walsCode := "ena", language := "Enga", iso := "enq", value := .differentiation }
  , { walsCode := "eng", language := "English", iso := "eng", value := .identity }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .identity }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .differentiation }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .differentiation }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .identity }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .differentiation }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .differentiation }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .mixed }
  , { walsCode := "fre", language := "French", iso := "fra", value := .identity }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .differentiation }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .identity }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .identity }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .differentiation }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .mixed }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .identity }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .mixed }
  , { walsCode := "ger", language := "German", iso := "deu", value := .identity }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .differentiation }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .differentiation }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .differentiation }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .differentiation }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .identity }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .differentiation }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .differentiation }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .differentiation }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .differentiation }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .differentiation }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .differentiation }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .mixed }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .identity }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .mixed }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .identity }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .differentiation }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .differentiation }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .differentiation }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .differentiation }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .differentiation }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .differentiation }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .mixed }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .differentiation }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .differentiation }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .mixed }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .identity }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .differentiation }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .mixed }
  , { walsCode := "iga", language := "Inga", iso := "inb", value := .identity }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .mixed }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .identity }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .identity }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .differentiation }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .differentiation }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .differentiation }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .identity }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .differentiation }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .identity }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .differentiation }
  , { walsCode := "kwe", language := "Kanjobal (Western)", iso := "knj", value := .differentiation }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .differentiation }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .differentiation }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .differentiation }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .differentiation }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .identity }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .identity }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .identity }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .differentiation }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .identity }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .differentiation }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .differentiation }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .differentiation }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .differentiation }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .differentiation }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .identity }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .differentiation }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .differentiation }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .differentiation }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .mixed }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .differentiation }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .differentiation }
  , { walsCode := "ktt", language := "Kott", iso := "", value := .differentiation }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .mixed }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .mixed }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .differentiation }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .differentiation }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .differentiation }
  , { walsCode := "kwr", language := "Kwamera", iso := "tnk", value := .identity }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .differentiation }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .differentiation }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .differentiation }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .differentiation }
  , { walsCode := "ldn", language := "Ladin", iso := "lld", value := .identity }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .differentiation }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .differentiation }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .differentiation }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .mixed }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .identity }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .differentiation }
  , { walsCode := "les", language := "Lese", iso := "les", value := .differentiation }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .differentiation }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .differentiation }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .mixed }
  , { walsCode := "lga", language := "Luangiua", iso := "ojv", value := .identity }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .differentiation }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .differentiation }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .differentiation }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .differentiation }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .differentiation }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .differentiation }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .differentiation }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .differentiation }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .differentiation }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .differentiation }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .differentiation }
  , { walsCode := "mjk", language := "Manjaku", iso := "mfv", value := .differentiation }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .mixed }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .differentiation }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .differentiation }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .identity }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .differentiation }
  , { walsCode := "mah", language := "Mari (Hill)", iso := "mrj", value := .differentiation }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .differentiation }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .differentiation }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .differentiation }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .identity }
  , { walsCode := "myo", language := "Mayo", iso := "mfy", value := .differentiation }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .identity }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .identity }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .differentiation }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .identity }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .identity }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .identity }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .differentiation }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .differentiation }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .differentiation }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .differentiation }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .differentiation }
  , { walsCode := "nmi", language := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", value := .differentiation }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .identity }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .differentiation }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .differentiation }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .mixed }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .differentiation }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .mixed }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .differentiation }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .differentiation }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .differentiation }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .differentiation }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .identity }
  , { walsCode := "nkr", language := "Nukuoro", iso := "nkr", value := .differentiation }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .differentiation }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .mixed }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .differentiation }
  , { walsCode := "owc", language := "Oromo (West-Central)", iso := "gaz", value := .mixed }
  , { walsCode := "ots", language := "Otomí (Sierra)", iso := "otm", value := .differentiation }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .differentiation }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .differentiation }
  , { walsCode := "pen", language := "Pengo", iso := "peg", value := .mixed }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .differentiation }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .identity }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .differentiation }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .identity }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .differentiation }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .differentiation }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .differentiation }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .differentiation }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .identity }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .differentiation }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .differentiation }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .differentiation }
  , { walsCode := "qay", language := "Quechua (Ayacucho)", iso := "quy", value := .mixed }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .identity }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .differentiation }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .differentiation }
  , { walsCode := "rbu", language := "Romani (Bugurdzi)", iso := "rmn", value := .identity }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .identity }
  , { walsCode := "rmc", language := "Romansch", iso := "roh", value := .identity }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .mixed }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .identity }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .differentiation }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .differentiation }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .differentiation }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .identity }
  , { walsCode := "srm", language := "Saramaccan", iso := "srm", value := .mixed }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .differentiation }
  , { walsCode := "ssh", language := "Shinassha", iso := "bwo", value := .differentiation }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .differentiation }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .differentiation }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .differentiation }
  , { walsCode := "so", language := "So", iso := "teu", value := .differentiation }
  , { walsCode := "som", language := "Somali", iso := "som", value := .differentiation }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .identity }
  , { walsCode := "srl", language := "Sorbian (Lower)", iso := "dsb", value := .identity }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .mixed }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mixed }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .identity }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .differentiation }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .identity }
  , { walsCode := "tbs", language := "Tabassaran", iso := "tab", value := .differentiation }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .differentiation }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .differentiation }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .differentiation }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .mixed }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .differentiation }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .differentiation }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .differentiation }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .differentiation }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .identity }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .differentiation }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .identity }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .identity }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .differentiation }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .identity }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .differentiation }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .differentiation }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .differentiation }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .differentiation }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .differentiation }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .differentiation }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .differentiation }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .differentiation }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .differentiation }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .differentiation }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .identity }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .differentiation }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .differentiation }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .identity }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .differentiation }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .differentiation }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .identity }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .differentiation }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .differentiation }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .differentiation }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .mixed }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .differentiation }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .differentiation }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .mixed }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .differentiation }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .differentiation }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .differentiation }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .differentiation }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .differentiation }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .differentiation }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .mixed }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .differentiation }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .differentiation }
  , { walsCode := "bah", language := "Xiriana", iso := "xir", value := .differentiation }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .differentiation }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .differentiation }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .differentiation }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .differentiation }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .differentiation }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .identity }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .differentiation }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .differentiation }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .differentiation }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .mixed }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .identity }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .differentiation }
  ]

-- Count verification
theorem total_count : allData.length = 322 := by native_decide

theorem count_identity :
    (allData.filter (·.value == .identity)).length = 76 := by native_decide
theorem count_differentiation :
    (allData.filter (·.value == .differentiation)).length = 213 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 33 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F52A
