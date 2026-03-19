import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 124A: 'Want' Complement Subjects
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 124A`.

Chapter 124, 283 languages.
-/

namespace Core.WALS.F124A

/-- WALS 124A values. -/
inductive WantComplementSubject where
  | subjectIsLeftImplicit  -- Subject is left implicit (144 languages)
  | subjectIsExpressedOvertly  -- Subject is expressed overtly (72 languages)
  | bothConstructionTypesExist  -- Both construction types exist (14 languages)
  | desiderativeVerbalAffix  -- Desiderative verbal affix (45 languages)
  | desiderativeParticle  -- Desiderative particle (8 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 124A dataset (283 languages). -/
def allData : List (Datapoint WantComplementSubject) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .subjectIsExpressedOvertly }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .subjectIsExpressedOvertly }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .subjectIsLeftImplicit }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .desiderativeVerbalAffix }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .subjectIsLeftImplicit }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .subjectIsLeftImplicit }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .subjectIsExpressedOvertly }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .subjectIsExpressedOvertly }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .desiderativeVerbalAffix }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .subjectIsLeftImplicit }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .bothConstructionTypesExist }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .subjectIsExpressedOvertly }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .subjectIsLeftImplicit }
  , { walsCode := "apj", language := "Apache (Jicarilla)", iso := "apj", value := .subjectIsExpressedOvertly }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .desiderativeVerbalAffix }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .subjectIsExpressedOvertly }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .desiderativeVerbalAffix }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .subjectIsLeftImplicit }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .subjectIsLeftImplicit }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .desiderativeVerbalAffix }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .subjectIsLeftImplicit }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .subjectIsExpressedOvertly }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .subjectIsLeftImplicit }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .subjectIsLeftImplicit }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .subjectIsExpressedOvertly }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .subjectIsLeftImplicit }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .subjectIsLeftImplicit }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .subjectIsExpressedOvertly }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .subjectIsExpressedOvertly }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .subjectIsLeftImplicit }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .subjectIsExpressedOvertly }
  , { walsCode := "boz", language := "Bozo (Tigemaxo)", iso := "boz", value := .subjectIsLeftImplicit }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .subjectIsExpressedOvertly }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .subjectIsExpressedOvertly }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .subjectIsLeftImplicit }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .subjectIsLeftImplicit }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .subjectIsLeftImplicit }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .subjectIsLeftImplicit }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .subjectIsLeftImplicit }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .subjectIsLeftImplicit }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .subjectIsExpressedOvertly }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .desiderativeVerbalAffix }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .subjectIsLeftImplicit }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .subjectIsLeftImplicit }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .subjectIsExpressedOvertly }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .subjectIsLeftImplicit }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .subjectIsLeftImplicit }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .subjectIsLeftImplicit }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .subjectIsLeftImplicit }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .subjectIsLeftImplicit }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .subjectIsExpressedOvertly }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .subjectIsLeftImplicit }
  , { walsCode := "eng", language := "English", iso := "eng", value := .subjectIsLeftImplicit }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .subjectIsLeftImplicit }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .subjectIsLeftImplicit }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .desiderativeVerbalAffix }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .subjectIsExpressedOvertly }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .desiderativeParticle }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .subjectIsLeftImplicit }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .bothConstructionTypesExist }
  , { walsCode := "fre", language := "French", iso := "fra", value := .subjectIsLeftImplicit }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .subjectIsLeftImplicit }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .subjectIsLeftImplicit }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .bothConstructionTypesExist }
  , { walsCode := "ger", language := "German", iso := "deu", value := .subjectIsLeftImplicit }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .subjectIsExpressedOvertly }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .subjectIsExpressedOvertly }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .desiderativeVerbalAffix }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .subjectIsLeftImplicit }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .subjectIsExpressedOvertly }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .subjectIsExpressedOvertly }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .subjectIsLeftImplicit }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .subjectIsLeftImplicit }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .subjectIsLeftImplicit }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .subjectIsLeftImplicit }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .subjectIsLeftImplicit }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .subjectIsLeftImplicit }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .desiderativeVerbalAffix }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .subjectIsLeftImplicit }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .subjectIsLeftImplicit }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .subjectIsLeftImplicit }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .subjectIsLeftImplicit }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .subjectIsLeftImplicit }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .subjectIsLeftImplicit }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .subjectIsLeftImplicit }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .desiderativeParticle }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .subjectIsExpressedOvertly }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .subjectIsExpressedOvertly }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .desiderativeVerbalAffix }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .desiderativeVerbalAffix }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .subjectIsExpressedOvertly }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .bothConstructionTypesExist }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .subjectIsExpressedOvertly }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .subjectIsExpressedOvertly }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .desiderativeVerbalAffix }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .subjectIsLeftImplicit }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .subjectIsLeftImplicit }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .subjectIsLeftImplicit }
  , { walsCode := "kao", language := "Karao", iso := "kyj", value := .subjectIsLeftImplicit }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .subjectIsLeftImplicit }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .subjectIsLeftImplicit }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .desiderativeVerbalAffix }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .subjectIsLeftImplicit }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .subjectIsLeftImplicit }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .subjectIsLeftImplicit }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .subjectIsLeftImplicit }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .subjectIsLeftImplicit }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .subjectIsLeftImplicit }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .subjectIsExpressedOvertly }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .subjectIsLeftImplicit }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .desiderativeVerbalAffix }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .subjectIsLeftImplicit }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .subjectIsLeftImplicit }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .subjectIsLeftImplicit }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .bothConstructionTypesExist }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .desiderativeParticle }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .subjectIsExpressedOvertly }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .subjectIsLeftImplicit }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .subjectIsLeftImplicit }
  , { walsCode := "kuk", language := "Kukú", iso := "bfa", value := .subjectIsLeftImplicit }
  , { walsCode := "kug", language := "Kunming", iso := "cmn", value := .subjectIsLeftImplicit }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .subjectIsExpressedOvertly }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .subjectIsExpressedOvertly }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .desiderativeVerbalAffix }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .desiderativeVerbalAffix }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .desiderativeVerbalAffix }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .subjectIsLeftImplicit }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .subjectIsLeftImplicit }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .subjectIsLeftImplicit }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .subjectIsLeftImplicit }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .subjectIsLeftImplicit }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .subjectIsLeftImplicit }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .subjectIsLeftImplicit }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .subjectIsExpressedOvertly }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .bothConstructionTypesExist }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .desiderativeVerbalAffix }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .subjectIsLeftImplicit }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .subjectIsLeftImplicit }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .subjectIsLeftImplicit }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .subjectIsLeftImplicit }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .desiderativeVerbalAffix }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .subjectIsLeftImplicit }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .desiderativeVerbalAffix }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .subjectIsExpressedOvertly }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .subjectIsLeftImplicit }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .subjectIsLeftImplicit }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .desiderativeParticle }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .desiderativeVerbalAffix }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .subjectIsLeftImplicit }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .subjectIsExpressedOvertly }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .subjectIsLeftImplicit }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .desiderativeVerbalAffix }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .subjectIsExpressedOvertly }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .bothConstructionTypesExist }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .subjectIsLeftImplicit }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .subjectIsExpressedOvertly }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .subjectIsLeftImplicit }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .subjectIsExpressedOvertly }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .subjectIsLeftImplicit }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .subjectIsLeftImplicit }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .subjectIsExpressedOvertly }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .bothConstructionTypesExist }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .desiderativeVerbalAffix }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .subjectIsExpressedOvertly }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .subjectIsLeftImplicit }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .subjectIsLeftImplicit }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .subjectIsLeftImplicit }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .subjectIsExpressedOvertly }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .desiderativeVerbalAffix }
  , { walsCode := "nmi", language := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", value := .desiderativeVerbalAffix }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .subjectIsExpressedOvertly }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .subjectIsLeftImplicit }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .desiderativeVerbalAffix }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .subjectIsLeftImplicit }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .subjectIsExpressedOvertly }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .subjectIsLeftImplicit }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .desiderativeVerbalAffix }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .subjectIsExpressedOvertly }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .subjectIsLeftImplicit }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .desiderativeParticle }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .subjectIsLeftImplicit }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .subjectIsExpressedOvertly }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .subjectIsLeftImplicit }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .subjectIsLeftImplicit }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .subjectIsLeftImplicit }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .subjectIsExpressedOvertly }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .desiderativeVerbalAffix }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .bothConstructionTypesExist }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .desiderativeVerbalAffix }
  , { walsCode := "olu", language := "Olutec", iso := "plo", value := .desiderativeVerbalAffix }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .bothConstructionTypesExist }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .subjectIsExpressedOvertly }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .subjectIsExpressedOvertly }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .desiderativeVerbalAffix }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .subjectIsLeftImplicit }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .subjectIsLeftImplicit }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .subjectIsLeftImplicit }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .subjectIsLeftImplicit }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .bothConstructionTypesExist }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .subjectIsExpressedOvertly }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .subjectIsExpressedOvertly }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .desiderativeVerbalAffix }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .subjectIsLeftImplicit }
  , { walsCode := "pop", language := "Popoloca (Metzontla)", iso := "pbe", value := .subjectIsExpressedOvertly }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .subjectIsLeftImplicit }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .subjectIsLeftImplicit }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .subjectIsLeftImplicit }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .subjectIsExpressedOvertly }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .desiderativeVerbalAffix }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .subjectIsLeftImplicit }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .subjectIsLeftImplicit }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .subjectIsExpressedOvertly }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .subjectIsLeftImplicit }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .subjectIsLeftImplicit }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .subjectIsLeftImplicit }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .subjectIsLeftImplicit }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .subjectIsExpressedOvertly }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .subjectIsLeftImplicit }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .subjectIsLeftImplicit }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .subjectIsExpressedOvertly }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .subjectIsExpressedOvertly }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .desiderativeParticle }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .subjectIsLeftImplicit }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .subjectIsLeftImplicit }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .subjectIsLeftImplicit }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .desiderativeVerbalAffix }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .subjectIsLeftImplicit }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .desiderativeVerbalAffix }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .desiderativeVerbalAffix }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .subjectIsExpressedOvertly }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .subjectIsExpressedOvertly }
  , { walsCode := "som", language := "Somali", iso := "som", value := .subjectIsExpressedOvertly }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .subjectIsExpressedOvertly }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .subjectIsLeftImplicit }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .subjectIsExpressedOvertly }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .subjectIsLeftImplicit }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .subjectIsLeftImplicit }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .subjectIsLeftImplicit }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .subjectIsExpressedOvertly }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .subjectIsLeftImplicit }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .subjectIsExpressedOvertly }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .subjectIsLeftImplicit }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .subjectIsExpressedOvertly }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .desiderativeVerbalAffix }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .bothConstructionTypesExist }
  , { walsCode := "trt", language := "Ternate", iso := "tft", value := .bothConstructionTypesExist }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .subjectIsExpressedOvertly }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .subjectIsLeftImplicit }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .subjectIsLeftImplicit }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .subjectIsLeftImplicit }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .subjectIsExpressedOvertly }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .desiderativeVerbalAffix }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .subjectIsLeftImplicit }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .subjectIsExpressedOvertly }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .desiderativeVerbalAffix }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .bothConstructionTypesExist }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .subjectIsLeftImplicit }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .subjectIsExpressedOvertly }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .desiderativeVerbalAffix }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .subjectIsLeftImplicit }
  , { walsCode := "uku", language := "Upper Kuskokwim", iso := "kuu", value := .desiderativeParticle }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .desiderativeParticle }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .subjectIsLeftImplicit }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .subjectIsExpressedOvertly }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .subjectIsLeftImplicit }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .subjectIsLeftImplicit }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .subjectIsExpressedOvertly }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .subjectIsExpressedOvertly }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .subjectIsLeftImplicit }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .subjectIsLeftImplicit }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .subjectIsLeftImplicit }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .desiderativeVerbalAffix }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .subjectIsExpressedOvertly }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .subjectIsLeftImplicit }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .subjectIsLeftImplicit }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .desiderativeVerbalAffix }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .subjectIsLeftImplicit }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .subjectIsLeftImplicit }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .desiderativeVerbalAffix }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .desiderativeVerbalAffix }
  , { walsCode := "zaq", language := "Zapotec (Quiegolani)", iso := "zpi", value := .subjectIsExpressedOvertly }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .desiderativeVerbalAffix }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .subjectIsLeftImplicit }
  ]

-- Count verification
theorem total_count : allData.length = 283 := by native_decide

theorem count_subjectIsLeftImplicit :
    (allData.filter (·.value == .subjectIsLeftImplicit)).length = 144 := by native_decide
theorem count_subjectIsExpressedOvertly :
    (allData.filter (·.value == .subjectIsExpressedOvertly)).length = 72 := by native_decide
theorem count_bothConstructionTypesExist :
    (allData.filter (·.value == .bothConstructionTypesExist)).length = 14 := by native_decide
theorem count_desiderativeVerbalAffix :
    (allData.filter (·.value == .desiderativeVerbalAffix)).length = 45 := by native_decide
theorem count_desiderativeParticle :
    (allData.filter (·.value == .desiderativeParticle)).length = 8 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F124A
