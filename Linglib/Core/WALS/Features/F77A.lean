import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 77A: Semantic Distinctions of Evidentiality
@cite{deandradedehaanValenzuela-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 77A`.

Chapter 77, 418 languages.
-/

namespace Core.WALS.F77A

/-- WALS 77A values. -/
inductive EvidentialityDistinctions where
  | noGrammaticalEvidentials  -- No grammatical evidentials (181 languages)
  | indirectOnly  -- Indirect only (166 languages)
  | directAndIndirect  -- Direct and indirect (71 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 77A dataset (418 languages). -/
def allData : List (Datapoint EvidentialityDistinctions) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noGrammaticalEvidentials }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .indirectOnly }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .indirectOnly }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .directAndIndirect }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .indirectOnly }
  , { walsCode := "agr", language := "Aguaruna", iso := "agr", value := .noGrammaticalEvidentials }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .directAndIndirect }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .directAndIndirect }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .indirectOnly }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noGrammaticalEvidentials }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noGrammaticalEvidentials }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .indirectOnly }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .indirectOnly }
  , { walsCode := "amd", language := "Amdo", iso := "adx", value := .directAndIndirect }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGrammaticalEvidentials }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .indirectOnly }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .directAndIndirect }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .noGrammaticalEvidentials }
  , { walsCode := "apc", language := "Apache (Chiricahua)", iso := "apm", value := .indirectOnly }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .directAndIndirect }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .indirectOnly }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noGrammaticalEvidentials }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .indirectOnly }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .indirectOnly }
  , { walsCode := "aho", language := "Arapaho", iso := "arp", value := .indirectOnly }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noGrammaticalEvidentials }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .indirectOnly }
  , { walsCode := "akr", language := "Arikara", iso := "ari", value := .indirectOnly }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .indirectOnly }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .indirectOnly }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noGrammaticalEvidentials }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .directAndIndirect }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noGrammaticalEvidentials }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .directAndIndirect }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .indirectOnly }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noGrammaticalEvidentials }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .indirectOnly }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noGrammaticalEvidentials }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .indirectOnly }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .indirectOnly }
  , { walsCode := "beb", language := "Benabena", iso := "bef", value := .noGrammaticalEvidentials }
  , { walsCode := "bse", language := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", value := .noGrammaticalEvidentials }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .indirectOnly }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noGrammaticalEvidentials }
  , { walsCode := "bor", language := "Bora", iso := "boa", value := .indirectOnly }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noGrammaticalEvidentials }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noGrammaticalEvidentials }
  , { walsCode := "bdk", language := "Budukh", iso := "bdk", value := .noGrammaticalEvidentials }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .directAndIndirect }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noGrammaticalEvidentials }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noGrammaticalEvidentials }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .indirectOnly }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noGrammaticalEvidentials }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGrammaticalEvidentials }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .indirectOnly }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .directAndIndirect }
  , { walsCode := "car", language := "Carib", iso := "car", value := .directAndIndirect }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noGrammaticalEvidentials }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .indirectOnly }
  , { walsCode := "cco", language := "Chasta Costa", iso := "tuu", value := .indirectOnly }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .noGrammaticalEvidentials }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .directAndIndirect }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .indirectOnly }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noGrammaticalEvidentials }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .indirectOnly }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .noGrammaticalEvidentials }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .indirectOnly }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noGrammaticalEvidentials }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .noGrammaticalEvidentials }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .indirectOnly }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .indirectOnly }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .indirectOnly }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .indirectOnly }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noGrammaticalEvidentials }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noGrammaticalEvidentials }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .indirectOnly }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .indirectOnly }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .indirectOnly }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .indirectOnly }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .indirectOnly }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .indirectOnly }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGrammaticalEvidentials }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .indirectOnly }
  , { walsCode := "den", language := "Dení", iso := "dny", value := .indirectOnly }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noGrammaticalEvidentials }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noGrammaticalEvidentials }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .directAndIndirect }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noGrammaticalEvidentials }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noGrammaticalEvidentials }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .indirectOnly }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .indirectOnly }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noGrammaticalEvidentials }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .indirectOnly }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noGrammaticalEvidentials }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .indirectOnly }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .indirectOnly }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .indirectOnly }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .directAndIndirect }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGrammaticalEvidentials }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .directAndIndirect }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGrammaticalEvidentials }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .indirectOnly }
  , { walsCode := "for", language := "Fore", iso := "for", value := .noGrammaticalEvidentials }
  , { walsCode := "fox", language := "Fox", iso := "sac", value := .indirectOnly }
  , { walsCode := "fre", language := "French", iso := "fra", value := .indirectOnly }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noGrammaticalEvidentials }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .directAndIndirect }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .indirectOnly }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .indirectOnly }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .directAndIndirect }
  , { walsCode := "ger", language := "German", iso := "deu", value := .indirectOnly }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .directAndIndirect }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .indirectOnly }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noGrammaticalEvidentials }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noGrammaticalEvidentials }
  , { walsCode := "gso", language := "Greenlandic (South)", iso := "kal", value := .indirectOnly }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .indirectOnly }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .indirectOnly }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .indirectOnly }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noGrammaticalEvidentials }
  , { walsCode := "gny", language := "Gunya", iso := "gyy", value := .indirectOnly }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noGrammaticalEvidentials }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .directAndIndirect }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .indirectOnly }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .indirectOnly }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noGrammaticalEvidentials }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noGrammaticalEvidentials }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .indirectOnly }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noGrammaticalEvidentials }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .directAndIndirect }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGrammaticalEvidentials }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .indirectOnly }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .directAndIndirect }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noGrammaticalEvidentials }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGrammaticalEvidentials }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .indirectOnly }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .directAndIndirect }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noGrammaticalEvidentials }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .noGrammaticalEvidentials }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .directAndIndirect }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noGrammaticalEvidentials }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGrammaticalEvidentials }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .directAndIndirect }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .indirectOnly }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noGrammaticalEvidentials }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noGrammaticalEvidentials }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noGrammaticalEvidentials }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .indirectOnly }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .indirectOnly }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .indirectOnly }
  , { walsCode := "jmm", language := "Jamamadi", iso := "jaa", value := .directAndIndirect }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .indirectOnly }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .directAndIndirect }
  , { walsCode := "jem", language := "Jemez", iso := "tow", value := .indirectOnly }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noGrammaticalEvidentials }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .indirectOnly }
  , { walsCode := "klh", language := "Kalasha", iso := "kls", value := .directAndIndirect }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .noGrammaticalEvidentials }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .indirectOnly }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .indirectOnly }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .indirectOnly }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noGrammaticalEvidentials }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .noGrammaticalEvidentials }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .indirectOnly }
  , { walsCode := "ksh", language := "Kashaya", iso := "kju", value := .directAndIndirect }
  , { walsCode := "kto", language := "Kato", iso := "ktw", value := .directAndIndirect }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .indirectOnly }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .directAndIndirect }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .directAndIndirect }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noGrammaticalEvidentials }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noGrammaticalEvidentials }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .directAndIndirect }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noGrammaticalEvidentials }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .directAndIndirect }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noGrammaticalEvidentials }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noGrammaticalEvidentials }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noGrammaticalEvidentials }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .directAndIndirect }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .indirectOnly }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noGrammaticalEvidentials }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .indirectOnly }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noGrammaticalEvidentials }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .directAndIndirect }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noGrammaticalEvidentials }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .directAndIndirect }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noGrammaticalEvidentials }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .directAndIndirect }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noGrammaticalEvidentials }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .indirectOnly }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .directAndIndirect }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noGrammaticalEvidentials }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noGrammaticalEvidentials }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noGrammaticalEvidentials }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noGrammaticalEvidentials }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .directAndIndirect }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noGrammaticalEvidentials }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .indirectOnly }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .directAndIndirect }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .indirectOnly }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noGrammaticalEvidentials }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .indirectOnly }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noGrammaticalEvidentials }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .indirectOnly }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noGrammaticalEvidentials }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .directAndIndirect }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .directAndIndirect }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noGrammaticalEvidentials }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .indirectOnly }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .indirectOnly }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .indirectOnly }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noGrammaticalEvidentials }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noGrammaticalEvidentials }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noGrammaticalEvidentials }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .noGrammaticalEvidentials }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noGrammaticalEvidentials }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .indirectOnly }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .directAndIndirect }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noGrammaticalEvidentials }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .indirectOnly }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .indirectOnly }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noGrammaticalEvidentials }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .indirectOnly }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGrammaticalEvidentials }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGrammaticalEvidentials }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noGrammaticalEvidentials }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noGrammaticalEvidentials }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .directAndIndirect }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .indirectOnly }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .indirectOnly }
  , { walsCode := "mtl", language := "Mattole", iso := "mvb", value := .indirectOnly }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noGrammaticalEvidentials }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noGrammaticalEvidentials }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .directAndIndirect }
  , { walsCode := "mgl", language := "Mingrelian", iso := "xmf", value := .directAndIndirect }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .indirectOnly }
  , { walsCode := "mth", language := "Mixe (Tlahuitoltepec)", iso := "mxp", value := .indirectOnly }
  , { walsCode := "mxt", language := "Mixtec (Ayutla)", iso := "miy", value := .noGrammaticalEvidentials }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noGrammaticalEvidentials }
  , { walsCode := "mxz", language := "Mixtec (Coatzospan)", iso := "miz", value := .noGrammaticalEvidentials }
  , { walsCode := "mja", language := "Mixtec (Jamiltepec)", iso := "mxt", value := .indirectOnly }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .indirectOnly }
  , { walsCode := "mxs", language := "Mixtec (Silacayoapan)", iso := "mks", value := .indirectOnly }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .indirectOnly }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .indirectOnly }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noGrammaticalEvidentials }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noGrammaticalEvidentials }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .noGrammaticalEvidentials }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noGrammaticalEvidentials }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "nmi", language := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", value := .indirectOnly }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .indirectOnly }
  , { walsCode := "nmp", language := "Nahuatl (Milpa Alta)", iso := "nhm", value := .noGrammaticalEvidentials }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .indirectOnly }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .indirectOnly }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noGrammaticalEvidentials }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .indirectOnly }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noGrammaticalEvidentials }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .directAndIndirect }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .indirectOnly }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .indirectOnly }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .indirectOnly }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noGrammaticalEvidentials }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noGrammaticalEvidentials }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .directAndIndirect }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .indirectOnly }
  , { walsCode := "nit", language := "Nitinaht", iso := "dtd", value := .indirectOnly }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .indirectOnly }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noGrammaticalEvidentials }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noGrammaticalEvidentials }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noGrammaticalEvidentials }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .indirectOnly }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .noGrammaticalEvidentials }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .indirectOnly }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .indirectOnly }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .indirectOnly }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noGrammaticalEvidentials }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .indirectOnly }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noGrammaticalEvidentials }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .indirectOnly }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .indirectOnly }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .indirectOnly }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noGrammaticalEvidentials }
  , { walsCode := "prc", language := "Paresi", iso := "pab", value := .indirectOnly }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .indirectOnly }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .indirectOnly }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .indirectOnly }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .indirectOnly }
  , { walsCode := "pem", language := "Pemon", iso := "aoc", value := .noGrammaticalEvidentials }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .directAndIndirect }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noGrammaticalEvidentials }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .directAndIndirect }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .indirectOnly }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .indirectOnly }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noGrammaticalEvidentials }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noGrammaticalEvidentials }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .directAndIndirect }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .directAndIndirect }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .directAndIndirect }
  , { walsCode := "pot", language := "Potawatomi", iso := "pot", value := .indirectOnly }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .directAndIndirect }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .indirectOnly }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .indirectOnly }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noGrammaticalEvidentials }
  , { walsCode := "que", language := "Quechan", iso := "yum", value := .directAndIndirect }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .directAndIndirect }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .directAndIndirect }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .indirectOnly }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGrammaticalEvidentials }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGrammaticalEvidentials }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .directAndIndirect }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noGrammaticalEvidentials }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noGrammaticalEvidentials }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .indirectOnly }
  , { walsCode := "slr", language := "Salar", iso := "slr", value := .directAndIndirect }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noGrammaticalEvidentials }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .directAndIndirect }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .indirectOnly }
  , { walsCode := "say", language := "Sayula Popoluca", iso := "pos", value := .noGrammaticalEvidentials }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noGrammaticalEvidentials }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noGrammaticalEvidentials }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noGrammaticalEvidentials }
  , { walsCode := "srr", language := "Serrano", iso := "ser", value := .indirectOnly }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .directAndIndirect }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .indirectOnly }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .indirectOnly }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .directAndIndirect }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .indirectOnly }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noGrammaticalEvidentials }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .indirectOnly }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noGrammaticalEvidentials }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .directAndIndirect }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .noGrammaticalEvidentials }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .indirectOnly }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noGrammaticalEvidentials }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noGrammaticalEvidentials }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .indirectOnly }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .noGrammaticalEvidentials }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noGrammaticalEvidentials }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .indirectOnly }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .indirectOnly }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .indirectOnly }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .indirectOnly }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .directAndIndirect }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .directAndIndirect }
  , { walsCode := "tsm", language := "Tasmanian", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noGrammaticalEvidentials }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .indirectOnly }
  , { walsCode := "trn", language := "Terêna", iso := "ter", value := .indirectOnly }
  , { walsCode := "tew", language := "Tewa (Arizona)", iso := "tew", value := .indirectOnly }
  , { walsCode := "trg", language := "Tewa (Rio Grande)", iso := "tew", value := .noGrammaticalEvidentials }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGrammaticalEvidentials }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .noGrammaticalEvidentials }
  , { walsCode := "til", language := "Tillamook", iso := "til", value := .noGrammaticalEvidentials }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noGrammaticalEvidentials }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .indirectOnly }
  , { walsCode := "tws", language := "Tiwa (Southern)", iso := "tix", value := .noGrammaticalEvidentials }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noGrammaticalEvidentials }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noGrammaticalEvidentials }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noGrammaticalEvidentials }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .indirectOnly }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .noGrammaticalEvidentials }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .noGrammaticalEvidentials }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .indirectOnly }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .indirectOnly }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .directAndIndirect }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .directAndIndirect }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .noGrammaticalEvidentials }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .indirectOnly }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .directAndIndirect }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .noGrammaticalEvidentials }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .directAndIndirect }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .indirectOnly }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .indirectOnly }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .indirectOnly }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noGrammaticalEvidentials }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noGrammaticalEvidentials }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noGrammaticalEvidentials }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .indirectOnly }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noGrammaticalEvidentials }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noGrammaticalEvidentials }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .indirectOnly }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noGrammaticalEvidentials }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .indirectOnly }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .indirectOnly }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noGrammaticalEvidentials }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .noGrammaticalEvidentials }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noGrammaticalEvidentials }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noGrammaticalEvidentials }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .noGrammaticalEvidentials }
  , { walsCode := "wur", language := "Waurá", iso := "wau", value := .indirectOnly }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .indirectOnly }
  , { walsCode := "wyn", language := "Wayana", iso := "way", value := .noGrammaticalEvidentials }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .indirectOnly }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noGrammaticalEvidentials }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .directAndIndirect }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noGrammaticalEvidentials }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noGrammaticalEvidentials }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noGrammaticalEvidentials }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .directAndIndirect }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .indirectOnly }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .indirectOnly }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noGrammaticalEvidentials }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .noGrammaticalEvidentials }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noGrammaticalEvidentials }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noGrammaticalEvidentials }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGrammaticalEvidentials }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noGrammaticalEvidentials }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .indirectOnly }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noGrammaticalEvidentials }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .indirectOnly }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noGrammaticalEvidentials }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .indirectOnly }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noGrammaticalEvidentials }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noGrammaticalEvidentials }
  ]

-- Count verification
theorem total_count : allData.length = 418 := by native_decide

theorem count_noGrammaticalEvidentials :
    (allData.filter (·.value == .noGrammaticalEvidentials)).length = 181 := by native_decide
theorem count_indirectOnly :
    (allData.filter (·.value == .indirectOnly)).length = 166 := by native_decide
theorem count_directAndIndirect :
    (allData.filter (·.value == .directAndIndirect)).length = 71 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F77A
