import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 9A: The Velar Nasal
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 9A`.

Chapter 9, 469 languages.
-/

namespace Core.WALS.F9A

/-- WALS 9A values. -/
inductive VelarNasal where
  | initialVelarNasal  -- Initial velar nasal (147 languages)
  | noInitialVelarNasal  -- No initial velar nasal (87 languages)
  | noVelarNasal  -- No velar nasal (235 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 9A dataset (469 languages). -/
def allData : List (Datapoint VelarNasal) :=
  [ { walsCode := "apk", language := "A-Pucikwar", iso := "apq", value := .initialVelarNasal }
  , { walsCode := "abz", language := "Abaza", iso := "abq", value := .noVelarNasal }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noVelarNasal }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noVelarNasal }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noVelarNasal }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .noVelarNasal }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .noVelarNasal }
  , { walsCode := "agr", language := "Aguaruna", iso := "agr", value := .noInitialVelarNasal }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .noVelarNasal }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noVelarNasal }
  , { walsCode := "akb", language := "Aka-Biada", iso := "abj", value := .initialVelarNasal }
  , { walsCode := "akc", language := "Aka-Cari", iso := "aci", value := .initialVelarNasal }
  , { walsCode := "akk", language := "Aka-Kede", iso := "akx", value := .initialVelarNasal }
  , { walsCode := "axv", language := "Akhvakh", iso := "akv", value := .noVelarNasal }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .noVelarNasal }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noVelarNasal }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noVelarNasal }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .initialVelarNasal }
  , { walsCode := "aso", language := "Altai (Southern)", iso := "alt", value := .noInitialVelarNasal }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noVelarNasal }
  , { walsCode := "alu", language := "Alutor", iso := "alr", value := .initialVelarNasal }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .noInitialVelarNasal }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noVelarNasal }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noVelarNasal }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .noVelarNasal }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .noVelarNasal }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .noVelarNasal }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noVelarNasal }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .noVelarNasal }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noVelarNasal }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .noVelarNasal }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noVelarNasal }
  , { walsCode := "aho", language := "Arapaho", iso := "arp", value := .noVelarNasal }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noVelarNasal }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noVelarNasal }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noVelarNasal }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noVelarNasal }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .noInitialVelarNasal }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noVelarNasal }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .noInitialVelarNasal }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noVelarNasal }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noVelarNasal }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .initialVelarNasal }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .noVelarNasal }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .noVelarNasal }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .initialVelarNasal }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .initialVelarNasal }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .initialVelarNasal }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noVelarNasal }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noInitialVelarNasal }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noVelarNasal }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .initialVelarNasal }
  , { walsCode := "bth", language := "Bathari", iso := "bhm", value := .noVelarNasal }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .initialVelarNasal }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noVelarNasal }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noVelarNasal }
  , { walsCode := "bez", language := "Bezhta", iso := "kap", value := .noVelarNasal }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noVelarNasal }
  , { walsCode := "bor", language := "Bora", iso := "boa", value := .noVelarNasal }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noVelarNasal }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noVelarNasal }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noVelarNasal }
  , { walsCode := "bdk", language := "Budukh", iso := "bdk", value := .noVelarNasal }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .initialVelarNasal }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .noInitialVelarNasal }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .initialVelarNasal }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noInitialVelarNasal }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noInitialVelarNasal }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .initialVelarNasal }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .initialVelarNasal }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noVelarNasal }
  , { walsCode := "crj", language := "Carijona", iso := "cbd", value := .noVelarNasal }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .noVelarNasal }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noVelarNasal }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noVelarNasal }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .noVelarNasal }
  , { walsCode := "chm", language := "Chamalal", iso := "cji", value := .noVelarNasal }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .initialVelarNasal }
  , { walsCode := "cht", language := "Chatino (Nopala)", iso := "cya", value := .noVelarNasal }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noVelarNasal }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .noVelarNasal }
  , { walsCode := "ckh", language := "Cheke Holo", iso := "mrn", value := .initialVelarNasal }
  , { walsCode := "cmk", language := "Chemakum", iso := "xch", value := .noVelarNasal }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noInitialVelarNasal }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noVelarNasal }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .initialVelarNasal }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .initialVelarNasal }
  , { walsCode := "csc", language := "Chinantec (Sochiapan)", iso := "cso", value := .initialVelarNasal }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .noVelarNasal }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noVelarNasal }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .initialVelarNasal }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .initialVelarNasal }
  , { walsCode := "cly", language := "Chulym", iso := "clw", value := .noInitialVelarNasal }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noVelarNasal }
  , { walsCode := "cla", language := "Clallam", iso := "clm", value := .initialVelarNasal }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noVelarNasal }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noVelarNasal }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noVelarNasal }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .noVelarNasal }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noVelarNasal }
  , { walsCode := "cri", language := "Crimean Tatar", iso := "crh", value := .noInitialVelarNasal }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .noVelarNasal }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noVelarNasal }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noInitialVelarNasal }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noInitialVelarNasal }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .initialVelarNasal }
  , { walsCode := "dol", language := "Dolgan", iso := "dlg", value := .initialVelarNasal }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .initialVelarNasal }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .initialVelarNasal }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .noVelarNasal }
  , { walsCode := "ene", language := "Enets", iso := "", value := .initialVelarNasal }
  , { walsCode := "ena", language := "Enga", iso := "enq", value := .initialVelarNasal }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noInitialVelarNasal }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noVelarNasal }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .initialVelarNasal }
  , { walsCode := "ess", language := "Esselen", iso := "esq", value := .noVelarNasal }
  , { walsCode := "ets", language := "Etsako", iso := "ets", value := .noVelarNasal }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .initialVelarNasal }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .initialVelarNasal }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .initialVelarNasal }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .initialVelarNasal }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noInitialVelarNasal }
  , { walsCode := "frd", language := "Fordata", iso := "frd", value := .initialVelarNasal }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noVelarNasal }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .initialVelarNasal }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .initialVelarNasal }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .noVelarNasal }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .initialVelarNasal }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .noVelarNasal }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noInitialVelarNasal }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .noVelarNasal }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .initialVelarNasal }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noVelarNasal }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noInitialVelarNasal }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noVelarNasal }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .initialVelarNasal }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .initialVelarNasal }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noVelarNasal }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noInitialVelarNasal }
  , { walsCode := "guq", language := "Guaque", iso := "cbd", value := .noVelarNasal }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noVelarNasal }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .noVelarNasal }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .noVelarNasal }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noVelarNasal }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .initialVelarNasal }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .initialVelarNasal }
  , { walsCode := "hrs", language := "Harsusi", iso := "hss", value := .noVelarNasal }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noVelarNasal }
  , { walsCode := "hav", language := "Havasupai", iso := "yuf", value := .noVelarNasal }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noVelarNasal }
  , { walsCode := "hia", language := "Hianacoto", iso := "cbd", value := .noVelarNasal }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .noVelarNasal }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noVelarNasal }
  , { walsCode := "hnk", language := "Hinuq", iso := "gin", value := .noVelarNasal }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noVelarNasal }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noInitialVelarNasal }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .noInitialVelarNasal }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noInitialVelarNasal }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noVelarNasal }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noVelarNasal }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noVelarNasal }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .initialVelarNasal }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noVelarNasal }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noVelarNasal }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .initialVelarNasal }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noVelarNasal }
  , { walsCode := "iql", language := "Inuktitut (Quebec-Labrador)", iso := "ike", value := .noInitialVelarNasal }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .initialVelarNasal }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noVelarNasal }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .initialVelarNasal }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .noVelarNasal }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .noVelarNasal }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .noVelarNasal }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noVelarNasal }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noVelarNasal }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noVelarNasal }
  , { walsCode := "jib", language := "Jibbali", iso := "shv", value := .noVelarNasal }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noInitialVelarNasal }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .initialVelarNasal }
  , { walsCode := "jur", language := "Jurchen", iso := "juc", value := .initialVelarNasal }
  , { walsCode := "jrn", language := "Juruna", iso := "jur", value := .noVelarNasal }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noInitialVelarNasal }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noVelarNasal }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .noInitialVelarNasal }
  , { walsCode := "kiq", language := "Kalmyk (Issyk-Kul)", iso := "xal", value := .noInitialVelarNasal }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noVelarNasal }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .initialVelarNasal }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .noInitialVelarNasal }
  , { walsCode := "krm", language := "Karaim", iso := "kdr", value := .noInitialVelarNasal }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .noVelarNasal }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .noInitialVelarNasal }
  , { walsCode := "krt", language := "Karata", iso := "kpt", value := .noVelarNasal }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noVelarNasal }
  , { walsCode := "ksh", language := "Kashaya", iso := "kju", value := .noVelarNasal }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noVelarNasal }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .initialVelarNasal }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .initialVelarNasal }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .noInitialVelarNasal }
  , { walsCode := "krq", language := "Kerek", iso := "krk", value := .initialVelarNasal }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noInitialVelarNasal }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noVelarNasal }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .noInitialVelarNasal }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .initialVelarNasal }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noInitialVelarNasal }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noInitialVelarNasal }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .initialVelarNasal }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .noVelarNasal }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noInitialVelarNasal }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .initialVelarNasal }
  , { walsCode := "khv", language := "Khwarshi", iso := "khv", value := .noVelarNasal }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noVelarNasal }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noVelarNasal }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noInitialVelarNasal }
  , { walsCode := "kfy", language := "Kirghiz (Fu-Yu)", iso := "kir", value := .noVelarNasal }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .initialVelarNasal }
  , { walsCode := "ksr", language := "Kisar", iso := "kje", value := .noVelarNasal }
  , { walsCode := "kit", language := "Kitsai", iso := "kii", value := .noVelarNasal }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noVelarNasal }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noInitialVelarNasal }
  , { walsCode := "koo", language := "Kola", iso := "kvv", value := .initialVelarNasal }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noInitialVelarNasal }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noInitialVelarNasal }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .initialVelarNasal }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .initialVelarNasal }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .initialVelarNasal }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .initialVelarNasal }
  , { walsCode := "kym", language := "Krymchak", iso := "jct", value := .noInitialVelarNasal }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .noVelarNasal }
  , { walsCode := "ksi", language := "Ksingmul", iso := "puo", value := .initialVelarNasal }
  , { walsCode := "kuq", language := "Kumyk", iso := "kum", value := .noInitialVelarNasal }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .initialVelarNasal }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .initialVelarNasal }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .noInitialVelarNasal }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noInitialVelarNasal }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noVelarNasal }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noVelarNasal }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .noVelarNasal }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .initialVelarNasal }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .initialVelarNasal }
  , { walsCode := "lha", language := "Laha", iso := "lha", value := .initialVelarNasal }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .initialVelarNasal }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noVelarNasal }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noVelarNasal }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .initialVelarNasal }
  , { walsCode := "lrk", language := "Larike", iso := "alo", value := .noInitialVelarNasal }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noVelarNasal }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .initialVelarNasal }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .initialVelarNasal }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noVelarNasal }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .noVelarNasal }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .initialVelarNasal }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noVelarNasal }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .initialVelarNasal }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .initialVelarNasal }
  , { walsCode := "lum", language := "Lummi", iso := "str", value := .initialVelarNasal }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .initialVelarNasal }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .initialVelarNasal }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noVelarNasal }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .initialVelarNasal }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .noVelarNasal }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noVelarNasal }
  , { walsCode := "mma", language := "Mandaic (Modern)", iso := "mid", value := .noVelarNasal }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noInitialVelarNasal }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .initialVelarNasal }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noInitialVelarNasal }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noInitialVelarNasal }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .initialVelarNasal }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .initialVelarNasal }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noVelarNasal }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .initialVelarNasal }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .initialVelarNasal }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .noVelarNasal }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noVelarNasal }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noVelarNasal }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .initialVelarNasal }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .noInitialVelarNasal }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .noInitialVelarNasal }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .noInitialVelarNasal }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noInitialVelarNasal }
  , { walsCode := "mxt", language := "Mixtec (Ayutla)", iso := "miy", value := .noVelarNasal }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noVelarNasal }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .noInitialVelarNasal }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .noVelarNasal }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noVelarNasal }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .noVelarNasal }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noInitialVelarNasal }
  , { walsCode := "muo", language := "Muong", iso := "mtq", value := .initialVelarNasal }
  , { walsCode := "mkw", language := "Máku", iso := "xak", value := .noVelarNasal }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .initialVelarNasal }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .noVelarNasal }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noVelarNasal }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .noVelarNasal }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .initialVelarNasal }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .initialVelarNasal }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noVelarNasal }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noVelarNasal }
  , { walsCode := "neg", language := "Negidal", iso := "neg", value := .initialVelarNasal }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .initialVelarNasal }
  , { walsCode := "naa", language := "Neo-Aramaic (Amadiya)", iso := "cld", value := .noVelarNasal }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .noVelarNasal }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noVelarNasal }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .initialVelarNasal }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noVelarNasal }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .initialVelarNasal }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noVelarNasal }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .initialVelarNasal }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noVelarNasal }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .noInitialVelarNasal }
  , { walsCode := "nok", language := "Noghay (Karagash)", iso := "nog", value := .noInitialVelarNasal }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .initialVelarNasal }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .initialVelarNasal }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .noVelarNasal }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .initialVelarNasal }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .noInitialVelarNasal }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noVelarNasal }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .initialVelarNasal }
  , { walsCode := "orc", language := "Oroch", iso := "oac", value := .initialVelarNasal }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .initialVelarNasal }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .initialVelarNasal }
  , { walsCode := "orl", language := "Orokolo", iso := "oro", value := .noVelarNasal }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noVelarNasal }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noVelarNasal }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noVelarNasal }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noVelarNasal }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .initialVelarNasal }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noInitialVelarNasal }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .noInitialVelarNasal }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .initialVelarNasal }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noInitialVelarNasal }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noVelarNasal }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .initialVelarNasal }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .initialVelarNasal }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noVelarNasal }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noVelarNasal }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noVelarNasal }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noVelarNasal }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .initialVelarNasal }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noVelarNasal }
  , { walsCode := "qec", language := "Quechua (Ecuadorean)", iso := "qug", value := .noVelarNasal }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noVelarNasal }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noVelarNasal }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .initialVelarNasal }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .initialVelarNasal }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .noInitialVelarNasal }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noVelarNasal }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .noVelarNasal }
  , { walsCode := "sch", language := "Saanich", iso := "str", value := .initialVelarNasal }
  , { walsCode := "sae", language := "Saek", iso := "skb", value := .initialVelarNasal }
  , { walsCode := "slr", language := "Salar", iso := "slr", value := .noInitialVelarNasal }
  , { walsCode := "sss", language := "Salish (Samish Straits)", iso := "str", value := .noInitialVelarNasal }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noVelarNasal }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .noInitialVelarNasal }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noVelarNasal }
  , { walsCode := "syg", language := "Saryg Yughur", iso := "ybe", value := .noInitialVelarNasal }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .initialVelarNasal }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noVelarNasal }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .noInitialVelarNasal }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .initialVelarNasal }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noVelarNasal }
  , { walsCode := "shw", language := "Shawnee", iso := "sjw", value := .noVelarNasal }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noVelarNasal }
  , { walsCode := "shr", language := "Shor", iso := "cjs", value := .noInitialVelarNasal }
  , { walsCode := "swr", language := "Shoshone (Wind River)", iso := "shh", value := .noVelarNasal }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noVelarNasal }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .noVelarNasal }
  , { walsCode := "sol", language := "Solon", iso := "evn", value := .noInitialVelarNasal }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noVelarNasal }
  , { walsCode := "sgs", language := "Songish", iso := "str", value := .initialVelarNasal }
  , { walsCode := "soo", language := "Sooke", iso := "str", value := .initialVelarNasal }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .noVelarNasal }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noVelarNasal }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .initialVelarNasal }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noVelarNasal }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .initialVelarNasal }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .initialVelarNasal }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noVelarNasal }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .initialVelarNasal }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .initialVelarNasal }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .initialVelarNasal }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .noVelarNasal }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .initialVelarNasal }
  , { walsCode := "tbr", language := "Tabaru", iso := "tby", value := .initialVelarNasal }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noVelarNasal }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .initialVelarNasal }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .noVelarNasal }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noVelarNasal }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .noInitialVelarNasal }
  , { walsCode := "ttb", language := "Tatar (Baraba)", iso := "tat", value := .noInitialVelarNasal }
  , { walsCode := "tlb", language := "Tatar-Noghay (Alabugat)", iso := "nog", value := .noInitialVelarNasal }
  , { walsCode := "tec", language := "Tectiteco", iso := "ttc", value := .noVelarNasal }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .noVelarNasal }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .initialVelarNasal }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .noVelarNasal }
  , { walsCode := "tew", language := "Tewa (Arizona)", iso := "tew", value := .noVelarNasal }
  , { walsCode := "thd", language := "Thadou", iso := "tcz", value := .initialVelarNasal }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .initialVelarNasal }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .initialVelarNasal }
  , { walsCode := "til", language := "Tillamook", iso := "til", value := .noVelarNasal }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .initialVelarNasal }
  , { walsCode := "tnd", language := "Tindi", iso := "tin", value := .noVelarNasal }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noVelarNasal }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noVelarNasal }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .initialVelarNasal }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noVelarNasal }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noVelarNasal }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .initialVelarNasal }
  , { walsCode := "tof", language := "Tofa", iso := "kim", value := .noInitialVelarNasal }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noVelarNasal }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noVelarNasal }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noVelarNasal }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noVelarNasal }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .initialVelarNasal }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noVelarNasal }
  , { walsCode := "tex", language := "Turkic (East-Central Xorasan)", iso := "kmz", value := .noInitialVelarNasal }
  , { walsCode := "twx", language := "Turkic (West Xorasan)", iso := "kmz", value := .noInitialVelarNasal }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noVelarNasal }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .noInitialVelarNasal }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noInitialVelarNasal }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .noInitialVelarNasal }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .noVelarNasal }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .noVelarNasal }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .initialVelarNasal }
  , { walsCode := "ulc", language := "Ulcha", iso := "ulc", value := .initialVelarNasal }
  , { walsCode := "umu", language := "Umaua", iso := "cbd", value := .noVelarNasal }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noInitialVelarNasal }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .initialVelarNasal }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noInitialVelarNasal }
  , { walsCode := "urm", language := "Urum", iso := "uum", value := .noInitialVelarNasal }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noVelarNasal }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .noInitialVelarNasal }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .noInitialVelarNasal }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noInitialVelarNasal }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .initialVelarNasal }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .initialVelarNasal }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .initialVelarNasal }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noVelarNasal }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noVelarNasal }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .initialVelarNasal }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .noVelarNasal }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noVelarNasal }
  , { walsCode := "was", language := "Washo", iso := "was", value := .initialVelarNasal }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noVelarNasal }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noVelarNasal }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .initialVelarNasal }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .noVelarNasal }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noVelarNasal }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .noVelarNasal }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noVelarNasal }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noInitialVelarNasal }
  , { walsCode := "ymd", language := "Yamdena", iso := "jmd", value := .initialVelarNasal }
  , { walsCode := "ynm", language := "Yanomámi", iso := "wca", value := .noVelarNasal }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noVelarNasal }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .initialVelarNasal }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .initialVelarNasal }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noVelarNasal }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noVelarNasal }
  , { walsCode := "yug", language := "Yugh", iso := "yug", value := .noInitialVelarNasal }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .initialVelarNasal }
  , { walsCode := "yki", language := "Yuki", iso := "yuk", value := .noVelarNasal }
  , { walsCode := "ykp", language := "Yukpa", iso := "yup", value := .noVelarNasal }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .initialVelarNasal }
  , { walsCode := "ysi", language := "Yupik (Sirenik)", iso := "ysr", value := .noInitialVelarNasal }
  , { walsCode := "yrc", language := "Yuracare", iso := "yuz", value := .noVelarNasal }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noVelarNasal }
  , { walsCode := "yta", language := "Yurt Tatar", iso := "nog", value := .noVelarNasal }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noInitialVelarNasal }
  , { walsCode := "zno", language := "Zulu (Northern)", iso := "zul", value := .initialVelarNasal }
  , { walsCode := "zso", language := "Zulu (Southern)", iso := "zul", value := .noVelarNasal }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noVelarNasal }
  ]

-- Count verification
theorem total_count : allData.length = 469 := by native_decide

theorem count_initialVelarNasal :
    (allData.filter (·.value == .initialVelarNasal)).length = 147 := by native_decide
theorem count_noInitialVelarNasal :
    (allData.filter (·.value == .noInitialVelarNasal)).length = 87 := by native_decide
theorem count_noVelarNasal :
    (allData.filter (·.value == .noVelarNasal)).length = 235 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F9A
