import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 121A: Comparative Constructions
@cite{stassen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 121A`.

Chapter 121, 167 languages.
-/

namespace Core.WALS.F121A

/-- WALS 121A values. -/
inductive ComparativeType where
  | locational  -- Locational (78 languages)
  | exceed  -- Exceed (33 languages)
  | conjoined  -- Conjoined (34 languages)
  | particle  -- Particle (22 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 121A dataset (167 languages). -/
def allData : List (Datapoint ComparativeType) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .conjoined }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .particle }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .locational }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .exceed }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .locational }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .locational }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .conjoined }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .locational }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .locational }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .locational }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .conjoined }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .locational }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .locational }
  , { walsCode := "bgi", language := "Bagri", iso := "bgq", value := .locational }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .exceed }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .locational }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .particle }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .particle }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .locational }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .locational }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .conjoined }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .locational }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .locational }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .locational }
  , { walsCode := "car", language := "Carib", iso := "car", value := .locational }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .locational }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .exceed }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .locational }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .locational }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .particle }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .exceed }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .exceed }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .exceed }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .particle }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .conjoined }
  , { walsCode := "eng", language := "English", iso := "eng", value := .particle }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .locational }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .locational }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .particle }
  , { walsCode := "fre", language := "French", iso := "fra", value := .particle }
  , { walsCode := "fus", language := "Fula (Senegal)", iso := "fuc", value := .exceed }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .particle }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .exceed }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .locational }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .particle }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .particle }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .locational }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .locational }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .conjoined }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .exceed }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .locational }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .locational }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .conjoined }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .particle }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .locational }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .exceed }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .particle }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .particle }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .conjoined }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .locational }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .locational }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .particle }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .locational }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .locational }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .exceed }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .locational }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .locational }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .conjoined }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .locational }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .locational }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .locational }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .exceed }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .conjoined }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .conjoined }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .conjoined }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .locational }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .exceed }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .locational }
  , { walsCode := "kug", language := "Kunming", iso := "cmn", value := .exceed }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .conjoined }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .particle }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .locational }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .locational }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .locational }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .exceed }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .exceed }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .locational }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .particle }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .locational }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .locational }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .exceed }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .conjoined }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .locational }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .conjoined }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .locational }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .locational }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .exceed }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .exceed }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .conjoined }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .conjoined }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .locational }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .conjoined }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .conjoined }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .conjoined }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .conjoined }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .locational }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .locational }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .locational }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .exceed }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .locational }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .locational }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .exceed }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .locational }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .conjoined }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .particle }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .exceed }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .locational }
  , { walsCode := "ptp", language := "Patpatar", iso := "gfk", value := .conjoined }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .conjoined }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .conjoined }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .locational }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .locational }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .locational }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .locational }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .locational }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .locational }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .exceed }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .particle }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .locational }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .conjoined }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .locational }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .exceed }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .conjoined }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .exceed }
  , { walsCode := "sik", language := "Sika", iso := "ski", value := .conjoined }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .locational }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .exceed }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .particle }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .particle }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .exceed }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .locational }
  , { walsCode := "taz", language := "Talysh (Azerbaijan)", iso := "tly", value := .locational }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .locational }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .locational }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .exceed }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .locational }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .locational }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .locational }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .locational }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .locational }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .locational }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .particle }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .locational }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .locational }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .conjoined }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .locational }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .exceed }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .conjoined }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .conjoined }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .exceed }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .conjoined }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .exceed }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .locational }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .conjoined }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .conjoined }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .exceed }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .exceed }
  ]

-- Count verification
theorem total_count : allData.length = 167 := by native_decide

theorem count_locational :
    (allData.filter (·.value == .locational)).length = 78 := by native_decide
theorem count_exceed :
    (allData.filter (·.value == .exceed)).length = 33 := by native_decide
theorem count_conjoined :
    (allData.filter (·.value == .conjoined)).length = 34 := by native_decide
theorem count_particle :
    (allData.filter (·.value == .particle)).length = 22 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F121A
