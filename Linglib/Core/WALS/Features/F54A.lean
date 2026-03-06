/-!
# WALS Feature 54A: Distributive Numerals
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 54A`.

Chapter 54, 251 languages.
-/

namespace Core.WALS.F54A

/-- WALS 54A values. -/
inductive DistributiveNumerals where
  | noDistributiveNumerals  -- No distributive numerals (62 languages)
  | markedByReduplication  -- Marked by reduplication (85 languages)
  | markedByPrefix  -- Marked by prefix (23 languages)
  | markedBySuffix  -- Marked by suffix (32 languages)
  | markedByPrecedingWord  -- Marked by preceding word (21 languages)
  | markedByFollowingWord  -- Marked by following word (5 languages)
  | markedByMixedOrOtherStrategies  -- Marked by mixed or other strategies (23 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 54A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : DistributiveNumerals
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 54A dataset (251 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .noDistributiveNumerals }
  , { walsCode := "agl", language := "Aghul", iso := "agx", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .markedByFollowingWord }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .markedByReduplication }
  , { walsCode := "alx", language := "Alas", iso := "btz", value := .markedByReduplication }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .markedByPrecedingWord }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .markedBySuffix }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .markedByReduplication }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noDistributiveNumerals }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .markedByReduplication }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .noDistributiveNumerals }
  , { walsCode := "anx", language := "Andi", iso := "ani", value := .markedByReduplication }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .markedByReduplication }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noDistributiveNumerals }
  , { walsCode := "ako", language := "Arabic (Kormakiti)", iso := "acy", value := .noDistributiveNumerals }
  , { walsCode := "ars", language := "Arabic (San'ani)", iso := "ayn", value := .noDistributiveNumerals }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .markedByReduplication }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noDistributiveNumerals }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .markedByReduplication }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .markedByReduplication }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .markedBySuffix }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .markedBySuffix }
  , { walsCode := "bat", language := "Batak", iso := "bya", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noDistributiveNumerals }
  , { walsCode := "beg", language := "Begak-Ida'an", iso := "dbj", value := .noDistributiveNumerals }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .markedByReduplication }
  , { walsCode := "bez", language := "Bezhta", iso := "kap", value := .markedByReduplication }
  , { walsCode := "biq", language := "Bilaan (Koronadal)", iso := "bpr", value := .markedByPrefix }
  , { walsCode := "bkd", language := "Binukid", iso := "bkd", value := .markedByPrefix }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .markedByReduplication }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .markedByReduplication }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .markedByPrefix }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .markedByPrecedingWord }
  , { walsCode := "bpa", language := "Bura-Pabir", iso := "bwr", value := .markedByReduplication }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .markedBySuffix }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .markedBySuffix }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .markedByReduplication }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .markedByReduplication }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noDistributiveNumerals }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .markedBySuffix }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .noDistributiveNumerals }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .markedBySuffix }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .markedByReduplication }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .markedByPrecedingWord }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .markedByReduplication }
  , { walsCode := "dgi", language := "Dogri", iso := "dgo", value := .markedByReduplication }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noDistributiveNumerals }
  , { walsCode := "dbr", language := "Dutch (Brabantic)", iso := "nld", value := .noDistributiveNumerals }
  , { walsCode := "dli", language := "Dutch (Limburg)", iso := "nld", value := .noDistributiveNumerals }
  , { walsCode := "duz", language := "Dutch (Zeeuws)", iso := "zea", value := .noDistributiveNumerals }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noDistributiveNumerals }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .markedBySuffix }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .markedBySuffix }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .markedByPrefix }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noDistributiveNumerals }
  , { walsCode := "fox", language := "Fox", iso := "sac", value := .markedByReduplication }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noDistributiveNumerals }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .markedByPrefix }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .markedBySuffix }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .markedByReduplication }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .noDistributiveNumerals }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .markedByReduplication }
  , { walsCode := "ger", language := "German", iso := "deu", value := .markedByPrecedingWord }
  , { walsCode := "gpz", language := "German (Appenzell)", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "gba", language := "German (Bavarian)", iso := "bar", value := .noDistributiveNumerals }
  , { walsCode := "gbl", language := "German (Berlin)", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gbe", language := "German (Bern)", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "gha", language := "German (Hannover)", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gma", language := "German (Mansfeldisch)", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gos", language := "German (Ostschweiz)", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "grp", language := "German (Ripuarian)", iso := "ksh", value := .noDistributiveNumerals }
  , { walsCode := "gtg", language := "German (Thurgau)", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "gth", language := "German (Thuringian)", iso := "deu", value := .noDistributiveNumerals }
  , { walsCode := "gti", language := "German (Timisoara)", iso := "deu", value := .markedByPrecedingWord }
  , { walsCode := "gau", language := "German (Upper Austrian)", iso := "bar", value := .noDistributiveNumerals }
  , { walsCode := "gwe", language := "German (Westphalian)", iso := "wep", value := .noDistributiveNumerals }
  , { walsCode := "gzu", language := "German (Zurich)", iso := "gsw", value := .markedByPrecedingWord }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noDistributiveNumerals }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .markedByPrecedingWord }
  , { walsCode := "gdf", language := "Guduf", iso := "gdf", value := .markedByReduplication }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .markedByReduplication }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .markedBySuffix }
  , { walsCode := "hnn", language := "Hanunóo", iso := "hnn", value := .markedByPrefix }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .markedByReduplication }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .markedByPrefix }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noDistributiveNumerals }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .markedByPrefix }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .markedByReduplication }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noDistributiveNumerals }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .markedByReduplication }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .markedByReduplication }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noDistributiveNumerals }
  , { walsCode := "ibn", language := "Ibanag", iso := "ibg", value := .markedByPrefix }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noDistributiveNumerals }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noDistributiveNumerals }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .markedByReduplication }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .markedByReduplication }
  , { walsCode := "ish", language := "Ishkashimi", iso := "isk", value := .markedBySuffix }
  , { walsCode := "isn", language := "Isnag", iso := "isd", value := .markedByPrefix }
  , { walsCode := "itu", language := "Italian (Turinese)", iso := "pms", value := .noDistributiveNumerals }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .markedByPrefix }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .markedBySuffix }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kbi", language := "Kabui", iso := "nbu", value := .markedByReduplication }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .noDistributiveNumerals }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .markedByReduplication }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .markedByReduplication }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .markedByReduplication }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .markedByReduplication }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .markedBySuffix }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .markedBySuffix }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .markedBySuffix }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .markedBySuffix }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .markedByReduplication }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noDistributiveNumerals }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noDistributiveNumerals }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .markedBySuffix }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .markedByPrefix }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .markedByReduplication }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .markedByReduplication }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noDistributiveNumerals }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .markedByReduplication }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .markedBySuffix }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .markedByReduplication }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .markedByReduplication }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .markedByReduplication }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .markedByReduplication }
  , { walsCode := "kuy", language := "Kutai", iso := "vkt", value := .markedByReduplication }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noDistributiveNumerals }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .markedByReduplication }
  , { walsCode := "lch", language := "Lachi", iso := "lbt", value := .noDistributiveNumerals }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .markedByReduplication }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .markedByPrecedingWord }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .markedByReduplication }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .markedByPrecedingWord }
  , { walsCode := "lov", language := "Loven", iso := "lbo", value := .noDistributiveNumerals }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .markedByReduplication }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .markedByReduplication }
  , { walsCode := "mgn", language := "Magindanao", iso := "mdh", value := .markedBySuffix }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .markedByReduplication }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .markedByFollowingWord }
  , { walsCode := "mmu", language := "Malay (Ulu Muar)", iso := "zmi", value := .markedByReduplication }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .markedByReduplication }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .markedBySuffix }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noDistributiveNumerals }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .markedByPrefix }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .markedByReduplication }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .markedByReduplication }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .markedBySuffix }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noDistributiveNumerals }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noDistributiveNumerals }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .markedByReduplication }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .markedByReduplication }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .noDistributiveNumerals }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .markedByReduplication }
  , { walsCode := "mit", language := "Mituku", iso := "zmq", value := .markedByReduplication }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .noDistributiveNumerals }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "mmo", language := "Mordvin (Moksha)", iso := "mdf", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .markedByReduplication }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .markedByReduplication }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .markedByPrefix }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .noDistributiveNumerals }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .markedBySuffix }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .markedBySuffix }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .markedByReduplication }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .markedByPrefix }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .markedByPrefix }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "nvs", language := "Nivkh (South Sakhalin)", iso := "niv", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .markedByReduplication }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .markedByReduplication }
  , { walsCode := "nyl", language := "Nyelâyu", iso := "yly", value := .noDistributiveNumerals }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .markedBySuffix }
  , { walsCode := "pte", language := "Paite", iso := "pck", value := .markedByReduplication }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .markedByReduplication }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noDistributiveNumerals }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .markedByReduplication }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .markedByPrecedingWord }
  , { walsCode := "fma", language := "Pulaar", iso := "fuc", value := .noDistributiveNumerals }
  , { walsCode := "qcu", language := "Quechua (Cuzco)", iso := "quz", value := .markedBySuffix }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .markedByFollowingWord }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .markedByReduplication }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .markedByPrecedingWord }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .noDistributiveNumerals }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .markedByReduplication }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .markedByPrecedingWord }
  , { walsCode := "ski", language := "Saami (Kildin)", iso := "sjd", value := .markedByReduplication }
  , { walsCode := "slr", language := "Salar", iso := "slr", value := .noDistributiveNumerals }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .markedByPrefix }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .markedByFollowingWord }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noDistributiveNumerals }
  , { walsCode := "ssh", language := "Shinassha", iso := "bwo", value := .markedByReduplication }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noDistributiveNumerals }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .markedByReduplication }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noDistributiveNumerals }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .markedByReduplication }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .markedByReduplication }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "tgb", language := "Tagbanwa (Aborlan)", iso := "tbw", value := .markedByPrefix }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .markedByReduplication }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .markedBySuffix }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .markedByReduplication }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .markedByReduplication }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .markedByReduplication }
  , { walsCode := "thd", language := "Thadou", iso := "tcz", value := .markedByReduplication }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noDistributiveNumerals }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .markedByReduplication }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .markedBySuffix }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .markedByReduplication }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .markedByPrefix }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .markedByPrefix }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .markedByPrefix }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noDistributiveNumerals }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .markedBySuffix }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .markedByPrecedingWord }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .markedByReduplication }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .markedByPrecedingWord }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .markedBySuffix }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noDistributiveNumerals }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .markedByFollowingWord }
  , { walsCode := "wll", language := "Wallisian", iso := "wls", value := .markedByPrefix }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noDistributiveNumerals }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noDistributiveNumerals }
  , { walsCode := "was", language := "Washo", iso := "was", value := .markedByReduplication }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .markedByReduplication }
  , { walsCode := "ygn", language := "Yaghnobi", iso := "yai", value := .markedBySuffix }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .markedBySuffix }
  , { walsCode := "ymi", language := "Yami", iso := "tao", value := .markedByPrefix }
  , { walsCode := "yms", language := "Yemsa", iso := "jnj", value := .markedByReduplication }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "ydb", language := "Yiddish (Bessarabian)", iso := "ydd", value := .markedByPrecedingWord }
  , { walsCode := "ylt", language := "Yiddish (Lithuanian)", iso := "ydd", value := .markedByPrecedingWord }
  , { walsCode := "ydl", language := "Yiddish (Lodz)", iso := "ydd", value := .markedByPrecedingWord }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noDistributiveNumerals }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .markedByReduplication }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noDistributiveNumerals }
  ]

-- Count verification
theorem total_count : allData.length = 251 := by native_decide

theorem count_noDistributiveNumerals :
    (allData.filter (·.value == .noDistributiveNumerals)).length = 62 := by native_decide
theorem count_markedByReduplication :
    (allData.filter (·.value == .markedByReduplication)).length = 85 := by native_decide
theorem count_markedByPrefix :
    (allData.filter (·.value == .markedByPrefix)).length = 23 := by native_decide
theorem count_markedBySuffix :
    (allData.filter (·.value == .markedBySuffix)).length = 32 := by native_decide
theorem count_markedByPrecedingWord :
    (allData.filter (·.value == .markedByPrecedingWord)).length = 21 := by native_decide
theorem count_markedByFollowingWord :
    (allData.filter (·.value == .markedByFollowingWord)).length = 5 := by native_decide
theorem count_markedByMixedOrOtherStrategies :
    (allData.filter (·.value == .markedByMixedOrOtherStrategies)).length = 23 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F54A
