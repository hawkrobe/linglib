import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 106A: Reciprocal Constructions
@cite{maslova-nedjalkov-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 106A`.

Chapter 106, 175 languages.
-/

namespace Core.WALS.F106A

/-- WALS 106A values. -/
inductive ReciprocalType where
  | noReciprocalConstruction  -- No reciprocal construction (16 languages)
  | distinctFromReflexive  -- Distinct from reflexive (99 languages)
  | mixed  -- Mixed (16 languages)
  | identicalToReflexive  -- Identical to reflexive (44 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 106A dataset (175 languages). -/
def allData : List (Datapoint ReciprocalType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .distinctFromReflexive }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .distinctFromReflexive }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .distinctFromReflexive }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noReciprocalConstruction }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .distinctFromReflexive }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .distinctFromReflexive }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .distinctFromReflexive }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .distinctFromReflexive }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noReciprocalConstruction }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .distinctFromReflexive }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .distinctFromReflexive }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .distinctFromReflexive }
  , { walsCode := "bnw", language := "Baniwa", iso := "bwi", value := .identicalToReflexive }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .identicalToReflexive }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .distinctFromReflexive }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .distinctFromReflexive }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .mixed }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .distinctFromReflexive }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noReciprocalConstruction }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .distinctFromReflexive }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .identicalToReflexive }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .distinctFromReflexive }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .distinctFromReflexive }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .distinctFromReflexive }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noReciprocalConstruction }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .distinctFromReflexive }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .identicalToReflexive }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .distinctFromReflexive }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .identicalToReflexive }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noReciprocalConstruction }
  , { walsCode := "ygd", language := "Dii", iso := "dur", value := .distinctFromReflexive }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .identicalToReflexive }
  , { walsCode := "eng", language := "English", iso := "eng", value := .distinctFromReflexive }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .distinctFromReflexive }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .distinctFromReflexive }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .distinctFromReflexive }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .distinctFromReflexive }
  , { walsCode := "fre", language := "French", iso := "fra", value := .mixed }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .distinctFromReflexive }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .distinctFromReflexive }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .distinctFromReflexive }
  , { walsCode := "ger", language := "German", iso := "deu", value := .mixed }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .identicalToReflexive }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .distinctFromReflexive }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .noReciprocalConstruction }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .identicalToReflexive }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .distinctFromReflexive }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .mixed }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .identicalToReflexive }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .distinctFromReflexive }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .distinctFromReflexive }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .mixed }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .distinctFromReflexive }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .mixed }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .distinctFromReflexive }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .mixed }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .identicalToReflexive }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .distinctFromReflexive }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .identicalToReflexive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .identicalToReflexive }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .distinctFromReflexive }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .distinctFromReflexive }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .identicalToReflexive }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .distinctFromReflexive }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .distinctFromReflexive }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .identicalToReflexive }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .distinctFromReflexive }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .distinctFromReflexive }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .distinctFromReflexive }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .distinctFromReflexive }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .identicalToReflexive }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .distinctFromReflexive }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .distinctFromReflexive }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noReciprocalConstruction }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .distinctFromReflexive }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .identicalToReflexive }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .distinctFromReflexive }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .distinctFromReflexive }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .distinctFromReflexive }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .distinctFromReflexive }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .identicalToReflexive }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .distinctFromReflexive }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .distinctFromReflexive }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .identicalToReflexive }
  , { walsCode := "lrd", language := "Lardil", iso := "lbz", value := .distinctFromReflexive }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .mixed }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .identicalToReflexive }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .identicalToReflexive }
  , { walsCode := "lye", language := "Lyele", iso := "lee", value := .distinctFromReflexive }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .distinctFromReflexive }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .distinctFromReflexive }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noReciprocalConstruction }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .distinctFromReflexive }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .identicalToReflexive }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .identicalToReflexive }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .distinctFromReflexive }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .identicalToReflexive }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .distinctFromReflexive }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .identicalToReflexive }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .identicalToReflexive }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noReciprocalConstruction }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .distinctFromReflexive }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .distinctFromReflexive }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .identicalToReflexive }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .distinctFromReflexive }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .distinctFromReflexive }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .distinctFromReflexive }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .distinctFromReflexive }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .distinctFromReflexive }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .distinctFromReflexive }
  , { walsCode := "nom", language := "Nomatsiguenga", iso := "not", value := .distinctFromReflexive }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .distinctFromReflexive }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .mixed }
  , { walsCode := "ojm", language := "Ojibwe (Minnesota)", iso := "ciw", value := .distinctFromReflexive }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .identicalToReflexive }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .distinctFromReflexive }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noReciprocalConstruction }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .mixed }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .identicalToReflexive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .distinctFromReflexive }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noReciprocalConstruction }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .distinctFromReflexive }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .mixed }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .distinctFromReflexive }
  , { walsCode := "qbo", language := "Quechua (Bolivian)", iso := "", value := .distinctFromReflexive }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .distinctFromReflexive }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .identicalToReflexive }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .mixed }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noReciprocalConstruction }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .identicalToReflexive }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .mixed }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noReciprocalConstruction }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .distinctFromReflexive }
  , { walsCode := "srr", language := "Serrano", iso := "ser", value := .identicalToReflexive }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .identicalToReflexive }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .distinctFromReflexive }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .mixed }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .identicalToReflexive }
  , { walsCode := "sur", language := "Sursurunga", iso := "sgz", value := .mixed }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .distinctFromReflexive }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .distinctFromReflexive }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .distinctFromReflexive }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .distinctFromReflexive }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .mixed }
  , { walsCode := "tpc", language := "Tepecano", iso := "tep", value := .noReciprocalConstruction }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .distinctFromReflexive }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .distinctFromReflexive }
  , { walsCode := "toq", language := "Toqabaqita", iso := "mlu", value := .identicalToReflexive }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .distinctFromReflexive }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .distinctFromReflexive }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .distinctFromReflexive }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .distinctFromReflexive }
  , { walsCode := "tbb", language := "Tübatulabal", iso := "tub", value := .distinctFromReflexive }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .distinctFromReflexive }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .identicalToReflexive }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .identicalToReflexive }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .identicalToReflexive }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .identicalToReflexive }
  , { walsCode := "wgu", language := "Warrongo", iso := "wrg", value := .distinctFromReflexive }
  , { walsCode := "wur", language := "Waurá", iso := "wau", value := .distinctFromReflexive }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noReciprocalConstruction }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .identicalToReflexive }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .distinctFromReflexive }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .identicalToReflexive }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .distinctFromReflexive }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .identicalToReflexive }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .distinctFromReflexive }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .identicalToReflexive }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .identicalToReflexive }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noReciprocalConstruction }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .identicalToReflexive }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .distinctFromReflexive }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .distinctFromReflexive }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .distinctFromReflexive }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .distinctFromReflexive }
  ]

-- Count verification
theorem total_count : allData.length = 175 := by native_decide

theorem count_noReciprocalConstruction :
    (allData.filter (·.value == .noReciprocalConstruction)).length = 16 := by native_decide
theorem count_distinctFromReflexive :
    (allData.filter (·.value == .distinctFromReflexive)).length = 99 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 16 := by native_decide
theorem count_identicalToReflexive :
    (allData.filter (·.value == .identicalToReflexive)).length = 44 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F106A
