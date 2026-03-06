/-!
# WALS Feature 78A: Coding of Evidentiality
@cite{deandradedehaanValenzuela-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 78A`.

Chapter 78, 418 languages.
-/

namespace Core.WALS.F78A

/-- WALS 78A values. -/
inductive EvidentialityCoding where
  | noGrammaticalEvidentials  -- No grammatical evidentials (181 languages)
  | verbalAffixOrClitic  -- Verbal affix or clitic (131 languages)
  | partOfTheTenseSystem  -- Part of the tense system (24 languages)
  | separateParticle  -- Separate particle (65 languages)
  | modalMorpheme  -- Modal morpheme (7 languages)
  | mixed  -- Mixed (10 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 78A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : EvidentialityCoding
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 78A dataset (418 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noGrammaticalEvidentials }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .verbalAffixOrClitic }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .verbalAffixOrClitic }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .verbalAffixOrClitic }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .separateParticle }
  , { walsCode := "agr", language := "Aguaruna", iso := "agr", value := .noGrammaticalEvidentials }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .verbalAffixOrClitic }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .verbalAffixOrClitic }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .verbalAffixOrClitic }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noGrammaticalEvidentials }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noGrammaticalEvidentials }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .verbalAffixOrClitic }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .verbalAffixOrClitic }
  , { walsCode := "amd", language := "Amdo", iso := "adx", value := .verbalAffixOrClitic }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGrammaticalEvidentials }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .verbalAffixOrClitic }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .verbalAffixOrClitic }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .noGrammaticalEvidentials }
  , { walsCode := "apc", language := "Apache (Chiricahua)", iso := "apm", value := .verbalAffixOrClitic }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .separateParticle }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .verbalAffixOrClitic }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noGrammaticalEvidentials }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .verbalAffixOrClitic }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .separateParticle }
  , { walsCode := "aho", language := "Arapaho", iso := "arp", value := .verbalAffixOrClitic }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noGrammaticalEvidentials }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .verbalAffixOrClitic }
  , { walsCode := "akr", language := "Arikara", iso := "ari", value := .verbalAffixOrClitic }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .partOfTheTenseSystem }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .verbalAffixOrClitic }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noGrammaticalEvidentials }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .verbalAffixOrClitic }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noGrammaticalEvidentials }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .partOfTheTenseSystem }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .separateParticle }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noGrammaticalEvidentials }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .separateParticle }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noGrammaticalEvidentials }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .separateParticle }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .verbalAffixOrClitic }
  , { walsCode := "beb", language := "Benabena", iso := "bef", value := .noGrammaticalEvidentials }
  , { walsCode := "bse", language := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", value := .noGrammaticalEvidentials }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .separateParticle }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noGrammaticalEvidentials }
  , { walsCode := "bor", language := "Bora", iso := "boa", value := .verbalAffixOrClitic }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noGrammaticalEvidentials }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noGrammaticalEvidentials }
  , { walsCode := "bdk", language := "Budukh", iso := "bdk", value := .noGrammaticalEvidentials }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .partOfTheTenseSystem }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noGrammaticalEvidentials }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noGrammaticalEvidentials }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .verbalAffixOrClitic }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noGrammaticalEvidentials }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGrammaticalEvidentials }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .separateParticle }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .partOfTheTenseSystem }
  , { walsCode := "car", language := "Carib", iso := "car", value := .partOfTheTenseSystem }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noGrammaticalEvidentials }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .separateParticle }
  , { walsCode := "cco", language := "Chasta Costa", iso := "tuu", value := .verbalAffixOrClitic }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .noGrammaticalEvidentials }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .partOfTheTenseSystem }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .verbalAffixOrClitic }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noGrammaticalEvidentials }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .verbalAffixOrClitic }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .noGrammaticalEvidentials }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .verbalAffixOrClitic }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noGrammaticalEvidentials }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .noGrammaticalEvidentials }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .verbalAffixOrClitic }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .verbalAffixOrClitic }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .separateParticle }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .verbalAffixOrClitic }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noGrammaticalEvidentials }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noGrammaticalEvidentials }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .separateParticle }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .verbalAffixOrClitic }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .separateParticle }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .verbalAffixOrClitic }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .separateParticle }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .separateParticle }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGrammaticalEvidentials }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .separateParticle }
  , { walsCode := "den", language := "Dení", iso := "dny", value := .verbalAffixOrClitic }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noGrammaticalEvidentials }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noGrammaticalEvidentials }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .mixed }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noGrammaticalEvidentials }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noGrammaticalEvidentials }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .separateParticle }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .modalMorpheme }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noGrammaticalEvidentials }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .partOfTheTenseSystem }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noGrammaticalEvidentials }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .separateParticle }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .separateParticle }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .verbalAffixOrClitic }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .partOfTheTenseSystem }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGrammaticalEvidentials }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .verbalAffixOrClitic }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGrammaticalEvidentials }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .modalMorpheme }
  , { walsCode := "for", language := "Fore", iso := "for", value := .noGrammaticalEvidentials }
  , { walsCode := "fox", language := "Fox", iso := "sac", value := .verbalAffixOrClitic }
  , { walsCode := "fre", language := "French", iso := "fra", value := .modalMorpheme }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noGrammaticalEvidentials }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .partOfTheTenseSystem }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .verbalAffixOrClitic }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .verbalAffixOrClitic }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .mixed }
  , { walsCode := "ger", language := "German", iso := "deu", value := .modalMorpheme }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .partOfTheTenseSystem }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .modalMorpheme }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noGrammaticalEvidentials }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noGrammaticalEvidentials }
  , { walsCode := "gso", language := "Greenlandic (South)", iso := "kal", value := .verbalAffixOrClitic }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .verbalAffixOrClitic }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .separateParticle }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .separateParticle }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noGrammaticalEvidentials }
  , { walsCode := "gny", language := "Gunya", iso := "gyy", value := .verbalAffixOrClitic }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noGrammaticalEvidentials }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .partOfTheTenseSystem }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .separateParticle }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .separateParticle }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noGrammaticalEvidentials }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noGrammaticalEvidentials }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .verbalAffixOrClitic }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noGrammaticalEvidentials }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .verbalAffixOrClitic }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGrammaticalEvidentials }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .separateParticle }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .verbalAffixOrClitic }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noGrammaticalEvidentials }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGrammaticalEvidentials }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .partOfTheTenseSystem }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .verbalAffixOrClitic }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noGrammaticalEvidentials }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .noGrammaticalEvidentials }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .mixed }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noGrammaticalEvidentials }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGrammaticalEvidentials }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .partOfTheTenseSystem }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .separateParticle }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noGrammaticalEvidentials }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noGrammaticalEvidentials }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noGrammaticalEvidentials }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .separateParticle }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .separateParticle }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .separateParticle }
  , { walsCode := "jmm", language := "Jamamadi", iso := "jaa", value := .verbalAffixOrClitic }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .verbalAffixOrClitic }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .verbalAffixOrClitic }
  , { walsCode := "jem", language := "Jemez", iso := "tow", value := .separateParticle }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noGrammaticalEvidentials }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .verbalAffixOrClitic }
  , { walsCode := "klh", language := "Kalasha", iso := "kls", value := .verbalAffixOrClitic }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .noGrammaticalEvidentials }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .verbalAffixOrClitic }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .separateParticle }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .verbalAffixOrClitic }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noGrammaticalEvidentials }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .noGrammaticalEvidentials }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .separateParticle }
  , { walsCode := "ksh", language := "Kashaya", iso := "kju", value := .verbalAffixOrClitic }
  , { walsCode := "kto", language := "Kato", iso := "ktw", value := .verbalAffixOrClitic }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .separateParticle }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .verbalAffixOrClitic }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .verbalAffixOrClitic }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noGrammaticalEvidentials }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noGrammaticalEvidentials }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .verbalAffixOrClitic }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noGrammaticalEvidentials }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .mixed }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noGrammaticalEvidentials }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noGrammaticalEvidentials }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noGrammaticalEvidentials }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .partOfTheTenseSystem }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .separateParticle }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noGrammaticalEvidentials }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .verbalAffixOrClitic }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noGrammaticalEvidentials }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .verbalAffixOrClitic }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noGrammaticalEvidentials }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .verbalAffixOrClitic }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noGrammaticalEvidentials }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .mixed }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noGrammaticalEvidentials }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .verbalAffixOrClitic }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .verbalAffixOrClitic }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noGrammaticalEvidentials }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noGrammaticalEvidentials }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noGrammaticalEvidentials }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noGrammaticalEvidentials }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .partOfTheTenseSystem }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noGrammaticalEvidentials }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .verbalAffixOrClitic }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .partOfTheTenseSystem }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .separateParticle }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noGrammaticalEvidentials }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .separateParticle }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noGrammaticalEvidentials }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .verbalAffixOrClitic }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noGrammaticalEvidentials }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .partOfTheTenseSystem }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .separateParticle }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noGrammaticalEvidentials }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .verbalAffixOrClitic }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .separateParticle }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .verbalAffixOrClitic }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noGrammaticalEvidentials }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noGrammaticalEvidentials }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noGrammaticalEvidentials }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .noGrammaticalEvidentials }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noGrammaticalEvidentials }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .verbalAffixOrClitic }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .verbalAffixOrClitic }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noGrammaticalEvidentials }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .verbalAffixOrClitic }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .verbalAffixOrClitic }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noGrammaticalEvidentials }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .modalMorpheme }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGrammaticalEvidentials }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGrammaticalEvidentials }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noGrammaticalEvidentials }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noGrammaticalEvidentials }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .verbalAffixOrClitic }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .separateParticle }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .verbalAffixOrClitic }
  , { walsCode := "mtl", language := "Mattole", iso := "mvb", value := .verbalAffixOrClitic }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noGrammaticalEvidentials }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noGrammaticalEvidentials }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .verbalAffixOrClitic }
  , { walsCode := "mgl", language := "Mingrelian", iso := "xmf", value := .mixed }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .verbalAffixOrClitic }
  , { walsCode := "mth", language := "Mixe (Tlahuitoltepec)", iso := "mxp", value := .verbalAffixOrClitic }
  , { walsCode := "mxt", language := "Mixtec (Ayutla)", iso := "miy", value := .noGrammaticalEvidentials }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noGrammaticalEvidentials }
  , { walsCode := "mxz", language := "Mixtec (Coatzospan)", iso := "miz", value := .noGrammaticalEvidentials }
  , { walsCode := "mja", language := "Mixtec (Jamiltepec)", iso := "mxt", value := .separateParticle }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .separateParticle }
  , { walsCode := "mxs", language := "Mixtec (Silacayoapan)", iso := "mks", value := .separateParticle }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .separateParticle }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .verbalAffixOrClitic }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noGrammaticalEvidentials }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noGrammaticalEvidentials }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .noGrammaticalEvidentials }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noGrammaticalEvidentials }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "nmi", language := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", value := .verbalAffixOrClitic }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .separateParticle }
  , { walsCode := "nmp", language := "Nahuatl (Milpa Alta)", iso := "nhm", value := .noGrammaticalEvidentials }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .separateParticle }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .separateParticle }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noGrammaticalEvidentials }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .separateParticle }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noGrammaticalEvidentials }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .verbalAffixOrClitic }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .verbalAffixOrClitic }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .verbalAffixOrClitic }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .verbalAffixOrClitic }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noGrammaticalEvidentials }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noGrammaticalEvidentials }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .verbalAffixOrClitic }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .mixed }
  , { walsCode := "nit", language := "Nitinaht", iso := "dtd", value := .verbalAffixOrClitic }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .verbalAffixOrClitic }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noGrammaticalEvidentials }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noGrammaticalEvidentials }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noGrammaticalEvidentials }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .verbalAffixOrClitic }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .noGrammaticalEvidentials }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .verbalAffixOrClitic }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .verbalAffixOrClitic }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .separateParticle }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noGrammaticalEvidentials }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .separateParticle }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noGrammaticalEvidentials }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .verbalAffixOrClitic }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .verbalAffixOrClitic }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .verbalAffixOrClitic }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noGrammaticalEvidentials }
  , { walsCode := "prc", language := "Paresi", iso := "pab", value := .separateParticle }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .modalMorpheme }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .verbalAffixOrClitic }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .separateParticle }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .verbalAffixOrClitic }
  , { walsCode := "pem", language := "Pemon", iso := "aoc", value := .noGrammaticalEvidentials }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .partOfTheTenseSystem }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noGrammaticalEvidentials }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .verbalAffixOrClitic }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .separateParticle }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .separateParticle }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noGrammaticalEvidentials }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noGrammaticalEvidentials }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .verbalAffixOrClitic }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .verbalAffixOrClitic }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .verbalAffixOrClitic }
  , { walsCode := "pot", language := "Potawatomi", iso := "pot", value := .separateParticle }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .verbalAffixOrClitic }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .verbalAffixOrClitic }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .verbalAffixOrClitic }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noGrammaticalEvidentials }
  , { walsCode := "que", language := "Quechan", iso := "yum", value := .verbalAffixOrClitic }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .verbalAffixOrClitic }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .verbalAffixOrClitic }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .verbalAffixOrClitic }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGrammaticalEvidentials }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGrammaticalEvidentials }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .verbalAffixOrClitic }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noGrammaticalEvidentials }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noGrammaticalEvidentials }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .verbalAffixOrClitic }
  , { walsCode := "slr", language := "Salar", iso := "slr", value := .partOfTheTenseSystem }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noGrammaticalEvidentials }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .mixed }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .verbalAffixOrClitic }
  , { walsCode := "say", language := "Sayula Popoluca", iso := "pos", value := .noGrammaticalEvidentials }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noGrammaticalEvidentials }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noGrammaticalEvidentials }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noGrammaticalEvidentials }
  , { walsCode := "srr", language := "Serrano", iso := "ser", value := .verbalAffixOrClitic }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .verbalAffixOrClitic }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .verbalAffixOrClitic }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .verbalAffixOrClitic }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .verbalAffixOrClitic }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .verbalAffixOrClitic }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noGrammaticalEvidentials }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .separateParticle }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noGrammaticalEvidentials }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .separateParticle }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .noGrammaticalEvidentials }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .separateParticle }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noGrammaticalEvidentials }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noGrammaticalEvidentials }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .mixed }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .noGrammaticalEvidentials }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noGrammaticalEvidentials }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .separateParticle }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .separateParticle }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .verbalAffixOrClitic }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .verbalAffixOrClitic }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .verbalAffixOrClitic }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .partOfTheTenseSystem }
  , { walsCode := "tsm", language := "Tasmanian", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noGrammaticalEvidentials }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .verbalAffixOrClitic }
  , { walsCode := "trn", language := "Terêna", iso := "ter", value := .verbalAffixOrClitic }
  , { walsCode := "tew", language := "Tewa (Arizona)", iso := "tew", value := .separateParticle }
  , { walsCode := "trg", language := "Tewa (Rio Grande)", iso := "tew", value := .noGrammaticalEvidentials }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGrammaticalEvidentials }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .noGrammaticalEvidentials }
  , { walsCode := "til", language := "Tillamook", iso := "til", value := .noGrammaticalEvidentials }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noGrammaticalEvidentials }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .verbalAffixOrClitic }
  , { walsCode := "tws", language := "Tiwa (Southern)", iso := "tix", value := .noGrammaticalEvidentials }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noGrammaticalEvidentials }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noGrammaticalEvidentials }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noGrammaticalEvidentials }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .verbalAffixOrClitic }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .noGrammaticalEvidentials }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .noGrammaticalEvidentials }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .separateParticle }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .verbalAffixOrClitic }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .mixed }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .partOfTheTenseSystem }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noGrammaticalEvidentials }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .noGrammaticalEvidentials }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .verbalAffixOrClitic }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .partOfTheTenseSystem }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .noGrammaticalEvidentials }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .partOfTheTenseSystem }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .separateParticle }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .separateParticle }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .separateParticle }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noGrammaticalEvidentials }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noGrammaticalEvidentials }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noGrammaticalEvidentials }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .separateParticle }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noGrammaticalEvidentials }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noGrammaticalEvidentials }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .separateParticle }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noGrammaticalEvidentials }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .verbalAffixOrClitic }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .verbalAffixOrClitic }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noGrammaticalEvidentials }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .noGrammaticalEvidentials }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noGrammaticalEvidentials }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noGrammaticalEvidentials }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .noGrammaticalEvidentials }
  , { walsCode := "wur", language := "Waurá", iso := "wau", value := .verbalAffixOrClitic }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .separateParticle }
  , { walsCode := "wyn", language := "Wayana", iso := "way", value := .noGrammaticalEvidentials }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .verbalAffixOrClitic }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noGrammaticalEvidentials }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .verbalAffixOrClitic }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noGrammaticalEvidentials }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noGrammaticalEvidentials }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noGrammaticalEvidentials }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .partOfTheTenseSystem }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .verbalAffixOrClitic }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .verbalAffixOrClitic }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noGrammaticalEvidentials }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .noGrammaticalEvidentials }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noGrammaticalEvidentials }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noGrammaticalEvidentials }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGrammaticalEvidentials }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noGrammaticalEvidentials }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .verbalAffixOrClitic }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noGrammaticalEvidentials }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .verbalAffixOrClitic }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noGrammaticalEvidentials }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .verbalAffixOrClitic }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noGrammaticalEvidentials }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noGrammaticalEvidentials }
  ]

-- Count verification
theorem total_count : allData.length = 418 := by native_decide

theorem count_noGrammaticalEvidentials :
    (allData.filter (·.value == .noGrammaticalEvidentials)).length = 181 := by native_decide
theorem count_verbalAffixOrClitic :
    (allData.filter (·.value == .verbalAffixOrClitic)).length = 131 := by native_decide
theorem count_partOfTheTenseSystem :
    (allData.filter (·.value == .partOfTheTenseSystem)).length = 24 := by native_decide
theorem count_separateParticle :
    (allData.filter (·.value == .separateParticle)).length = 65 := by native_decide
theorem count_modalMorpheme :
    (allData.filter (·.value == .modalMorpheme)).length = 7 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 10 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F78A
