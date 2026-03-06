/-!
# WALS Language Metadata

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py`.

554 languages referenced across generated features.
-/

namespace Core.WALS

/-- WALS language metadata. -/
structure Language where
  walsCode : String
  name : String
  iso : String
  family : String
  genus : String
  deriving Repr, BEq, DecidableEq

/-- All languages referenced in generated WALS features (554). -/
def languages : List Language :=
  [ { walsCode := "ani", name := "//Ani", iso := "hnh", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "abz", name := "Abaza", iso := "abq", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "abi", name := "Abipón", iso := "axb", family := "Guaicuruan", genus := "Abipon" }
  , { walsCode := "abk", name := "Abkhaz", iso := "abk", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "abu", name := "Abun", iso := "kgr", family := "Abun", genus := "Abun" }
  , { walsCode := "ace", name := "Acehnese", iso := "ace", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "acg", name := "Achagua", iso := "aca", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "acm", name := "Achumawi", iso := "acv", family := "Hokan", genus := "Achumawi" }
  , { walsCode := "aco", name := "Acoma", iso := "kjq", family := "Keresan", genus := "Keresan" }
  , { walsCode := "adz", name := "Adzera", iso := "adz", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ain", name := "Ainu", iso := "ain", family := "Ainu", genus := "Ainu" }
  , { walsCode := "aji", name := "Ajië", iso := "aji", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ala", name := "Alamblak", iso := "amp", family := "Sepik", genus := "Sepik Hill" }
  , { walsCode := "alb", name := "Albanian", iso := "sqi", family := "Indo-European", genus := "Albanian" }
  , { walsCode := "aly", name := "Alyawarra", iso := "aly", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "ame", name := "Amele", iso := "aey", family := "Trans-New Guinea", genus := "Mabuso" }
  , { walsCode := "amh", name := "Amharic", iso := "amh", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "amu", name := "Amuesha", iso := "ame", family := "Arawakan", genus := "Yanesha'" }
  , { walsCode := "anj", name := "Anejom", iso := "aty", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "anc", name := "Angas", iso := "anc", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "ane", name := "Anêm", iso := "anz", family := "Anêm", genus := "Anêm" }
  , { walsCode := "apu", name := "Apurinã", iso := "apu", family := "Arawakan", genus := "Purus" }
  , { walsCode := "abn", name := "Arabana", iso := "ard", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "aeg", name := "Arabic (Egyptian)", iso := "arz", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "ana", name := "Araona", iso := "aro", family := "Pano-Tacanan", genus := "Tacanan" }
  , { walsCode := "arp", name := "Arapesh (Mountain)", iso := "ape", family := "Torricelli", genus := "Kombio-Arapesh" }
  , { walsCode := "arc", name := "Archi", iso := "aqc", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "arm", name := "Armenian (Eastern)", iso := "hye", family := "Indo-European", genus := "Armenian" }
  , { walsCode := "aro", name := "Arosi", iso := "aia", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "asm", name := "Asmat", iso := "cns", family := "Asmat-Kamrau Bay", genus := "Asmat-Kamrau Bay" }
  , { walsCode := "atk", name := "Atakapa", iso := "aqp", family := "Atakapa", genus := "Atakapa" }
  , { walsCode := "ata", name := "Atayal", iso := "tay", family := "Austronesian", genus := "Atayalic" }
  , { walsCode := "atc", name := "Atchin", iso := "upv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "au", name := "Au", iso := "avt", family := "Torricelli", genus := "Central Wapei" }
  , { walsCode := "awp", name := "Awa Pit", iso := "kwi", family := "Barbacoan", genus := "Barbacoan" }
  , { walsCode := "awn", name := "Awngi", iso := "awn", family := "Afro-Asiatic", genus := "Central Cushitic" }
  , { walsCode := "awt", name := "Awtuw", iso := "kmn", family := "Sepik", genus := "Ram" }
  , { walsCode := "aym", name := "Aymara (Central)", iso := "ayr", family := "Aymaran", genus := "Aymaran" }
  , { walsCode := "bab", name := "Babungo", iso := "bav", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "bag", name := "Bagirmi", iso := "bmi", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "baj", name := "Bajau (Sama)", iso := "bdl", family := "Austronesian", genus := "Sama-Bajaw" }
  , { walsCode := "bal", name := "Balinese", iso := "ban", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "bam", name := "Bambara", iso := "bam", family := "Mande", genus := "Western Mande" }
  , { walsCode := "bnj", name := "Bandjalang", iso := "bdy", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "bnw", name := "Baniwa", iso := "bwi", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "baa", name := "Barai", iso := "bbb", family := "Trans-New Guinea", genus := "Koiarian" }
  , { walsCode := "brs", name := "Barasano", iso := "bsn", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "bar", name := "Bari", iso := "bfa", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "bae", name := "Baré", iso := "bae", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "bsq", name := "Basque", iso := "eus", family := "Basque", genus := "Basque" }
  , { walsCode := "bkr", name := "Batak (Karo)", iso := "btx", family := "Austronesian", genus := "Northwest Sumatra-Barrier Islands" }
  , { walsCode := "baw", name := "Bawm", iso := "bgr", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "bej", name := "Beja", iso := "bej", family := "Afro-Asiatic", genus := "Beja" }
  , { walsCode := "bma", name := "Berber (Middle Atlas)", iso := "tzm", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "ber", name := "Berta", iso := "wti", family := "Berta", genus := "Berta" }
  , { walsCode := "bez", name := "Bezhta", iso := "kap", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "bln", name := "Bilin", iso := "byn", family := "Afro-Asiatic", genus := "Central Cushitic" }
  , { walsCode := "blx", name := "Biloxi", iso := "bll", family := "Siouan", genus := "Ohio Valley Siouan" }
  , { walsCode := "bla", name := "Blackfoot", iso := "bla", family := "Algic", genus := "Algonquian" }
  , { walsCode := "brr", name := "Bororo", iso := "bor", family := "Bororoan", genus := "Bororoan" }
  , { walsCode := "brh", name := "Brahui", iso := "brh", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "bri", name := "Bribri", iso := "bzd", family := "Chibchan", genus := "Western Isthmic Chibchan" }
  , { walsCode := "bro", name := "Broken", iso := "tcs", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "bul", name := "Bulgarian", iso := "bul", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "but", name := "Buriat", iso := "bxm", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "brm", name := "Burmese", iso := "mya", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "brn", name := "Burunge", iso := "bds", family := "Afro-Asiatic", genus := "Southern Cushitic" }
  , { walsCode := "bur", name := "Burushaski", iso := "bsk", family := "Burushaski", genus := "Burushaski" }
  , { walsCode := "bya", name := "Byansi", iso := "bee", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "cah", name := "Cahuilla", iso := "chl", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "cak", name := "Cakchiquel", iso := "cak", family := "Mayan", genus := "Mayan" }
  , { walsCode := "cax", name := "Campa (Axininca)", iso := "", family := "Arawakan", genus := "Pre-Andine Arawakan" }
  , { walsCode := "can", name := "Candoshi", iso := "cbu", family := "Candoshi", genus := "Candoshi" }
  , { walsCode := "cnl", name := "Canela", iso := "ram", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "cnt", name := "Cantonese", iso := "yue", family := "Sino-Tibetan", genus := "Chinese" }
  , { walsCode := "cap", name := "Capanahua", iso := "kaq", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "car", name := "Carib", iso := "car", family := "Cariban", genus := "Cariban" }
  , { walsCode := "crq", name := "Carrier", iso := "crx", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "csh", name := "Cashinahua", iso := "cbs", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "cav", name := "Cavineña", iso := "cav", family := "Pano-Tacanan", genus := "Tacanan" }
  , { walsCode := "cyv", name := "Cayuvava", iso := "cyb", family := "Cayuvava", genus := "Cayuvava" }
  , { walsCode := "ceb", name := "Cebuano", iso := "ceb", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "chh", name := "Chaha", iso := "sgw", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "cld", name := "Chaldean (Modern)", iso := "cld", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "cha", name := "Chamorro", iso := "cha", family := "Austronesian", genus := "Chamorro" }
  , { walsCode := "chc", name := "Chechen", iso := "che", family := "Nakh-Daghestanian", genus := "Nakh" }
  , { walsCode := "cpn", name := "Chepang", iso := "cdm", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "cic", name := "Chichewa", iso := "nya", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "cle", name := "Chinantec (Lealao)", iso := "cle", family := "Oto-Manguean", genus := "Chinantecan" }
  , { walsCode := "ckl", name := "Chinook (Lower)", iso := "chh", family := "Penutian", genus := "Chinookan" }
  , { walsCode := "cct", name := "Choctaw", iso := "cho", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "chr", name := "Chrau", iso := "crw", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "chk", name := "Chukchi", iso := "ckt", family := "Chukotko-Kamchatkan", genus := "Northern Chukotko-Kamchatkan" }
  , { walsCode := "cba", name := "Chumash (Barbareño)", iso := "boi", family := "Chumash", genus := "Chumash" }
  , { walsCode := "chv", name := "Chuvash", iso := "chv", family := "Altaic", genus := "Turkic" }
  , { walsCode := "cbo", name := "Chácobo", iso := "cao", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "coa", name := "Coahuilteco", iso := "xcw", family := "Coahuiltecan", genus := "Coahuiltecan" }
  , { walsCode := "cmn", name := "Comanche", iso := "com", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "cmx", name := "Comox", iso := "coo", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "coo", name := "Coos (Hanis)", iso := "csz", family := "Oregon Coast", genus := "Coosan" }
  , { walsCode := "cop", name := "Coptic", iso := "cop", family := "Afro-Asiatic", genus := "Egyptian-Coptic" }
  , { walsCode := "cor", name := "Cora", iso := "crn", family := "Uto-Aztecan", genus := "Corachol" }
  , { walsCode := "cre", name := "Cree (Plains)", iso := "crk", family := "Algic", genus := "Algonquian" }
  , { walsCode := "cea", name := "Cree (Swampy)", iso := "csw", family := "Algic", genus := "Algonquian" }
  , { walsCode := "cri", name := "Crimean Tatar", iso := "crh", family := "Altaic", genus := "Turkic" }
  , { walsCode := "cub", name := "Cubeo", iso := "cub", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "cui", name := "Cuiba", iso := "cui", family := "Guahiban", genus := "Guahiban" }
  , { walsCode := "cup", name := "Cupeño", iso := "cup", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "dag", name := "Daga", iso := "dgz", family := "Trans-New Guinea", genus := "Dagan" }
  , { walsCode := "dga", name := "Dagaare", iso := "dga", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "dgr", name := "Dagur", iso := "dta", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "dni", name := "Dani (Lower Grand Valley)", iso := "dni", family := "Trans-New Guinea", genus := "Dani" }
  , { walsCode := "die", name := "Diegueño (Mesa Grande)", iso := "dih", family := "Hokan", genus := "Yuman" }
  , { walsCode := "ygd", name := "Dii", iso := "dur", family := "Niger-Congo", genus := "Samba-Duru" }
  , { walsCode := "dio", name := "Diola-Fogny", iso := "dyo", family := "Niger-Congo", genus := "Jola" }
  , { walsCode := "diy", name := "Diyari", iso := "dif", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "diz", name := "Dizi", iso := "mdx", family := "Afro-Asiatic", genus := "Dizoid" }
  , { walsCode := "djr", name := "Djaru", iso := "ddj", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "dji", name := "Djingili", iso := "jig", family := "Mirndi", genus := "Djingili" }
  , { walsCode := "don", name := "Dong (Southern)", iso := "kmc", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "doy", name := "Doyayo", iso := "dow", family := "Niger-Congo", genus := "Samba-Duru" }
  , { walsCode := "dre", name := "Drehu", iso := "dhv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "dum", name := "Dumo", iso := "vam", family := "Skou", genus := "Western Skou" }
  , { walsCode := "dut", name := "Dutch", iso := "nld", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "dyi", name := "Dyirbal", iso := "dbl", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "eka", name := "Ekari", iso := "ekg", family := "Trans-New Guinea", genus := "Paniai Lakes" }
  , { walsCode := "eml", name := "Embaloh", iso := "emb", family := "Austronesian", genus := "South Sulawesi" }
  , { walsCode := "eng", name := "English", iso := "eng", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "epe", name := "Epena Pedee", iso := "sja", family := "Choco", genus := "Choco" }
  , { walsCode := "err", name := "Erromangan", iso := "erg", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "evn", name := "Even", iso := "eve", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "eve", name := "Evenki", iso := "evn", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "ewe", name := "Ewe", iso := "ewe", family := "Niger-Congo", genus := "Gbe" }
  , { walsCode := "fij", name := "Fijian", iso := "fij", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "fin", name := "Finnish", iso := "fin", family := "Uralic", genus := "Finnic" }
  , { walsCode := "fre", name := "French", iso := "fra", family := "Indo-European", genus := "Romance" }
  , { walsCode := "fua", name := "Fulfulde (Adamawa)", iso := "fub", family := "Niger-Congo", genus := "Peul-Serer" }
  , { walsCode := "fur", name := "Fur", iso := "fvr", family := "Fur", genus := "Fur" }
  , { walsCode := "fue", name := "Futuna (East)", iso := "fud", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "fut", name := "Futuna-Aniwa", iso := "fut", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "gae", name := "Gaelic (Scots)", iso := "gla", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "gar", name := "Garo", iso := "grt", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "gbb", name := "Gbeya Bossangoa", iso := "gbp", family := "Niger-Congo", genus := "Gbaya-Manza-Ngbaka" }
  , { walsCode := "geo", name := "Georgian", iso := "kat", family := "Kartvelian", genus := "Kartvelian" }
  , { walsCode := "ger", name := "German", iso := "deu", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "gim", name := "Gimira", iso := "bcq", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "goa", name := "Goajiro", iso := "guc", family := "Arawakan", genus := "Guajiro-Paraujano" }
  , { walsCode := "gdi", name := "Godié", iso := "god", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "god", name := "Godoberi", iso := "gdo", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "goo", name := "Gooniyandi", iso := "gni", family := "Bunuban", genus := "Bunuban" }
  , { walsCode := "grb", name := "Grebo", iso := "grj", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "grk", name := "Greek (Modern)", iso := "ell", family := "Indo-European", genus := "Greek" }
  , { walsCode := "grw", name := "Greenlandic (West)", iso := "kal", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "gua", name := "Guaraní", iso := "gug", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "gud", name := "Gude", iso := "gde", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "guj", name := "Gujarati", iso := "guj", family := "Indo-European", genus := "Indic" }
  , { walsCode := "gmw", name := "Gumawana", iso := "gvs", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "guu", name := "Guugu Yimidhirr", iso := "kky", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "hai", name := "Haida", iso := "hai", family := "Haida", genus := "Haida" }
  , { walsCode := "hli", name := "Halkomelem (Island)", iso := "hur", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "hlu", name := "Halkomelem (Upriver)", iso := "hur", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "hmr", name := "Hamer", iso := "amf", family := "Afro-Asiatic", genus := "South Omotic" }
  , { walsCode := "ham", name := "Hamtai", iso := "hmt", family := "Trans-New Guinea", genus := "Nuclear Angan" }
  , { walsCode := "hat", name := "Hatam", iso := "had", family := "Hatim-Mansim", genus := "Hatim-Mansim" }
  , { walsCode := "hau", name := "Hausa", iso := "hau", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "haw", name := "Hawaiian", iso := "haw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "heb", name := "Hebrew (Modern)", iso := "heb", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "hin", name := "Hindi", iso := "hin", family := "Indo-European", genus := "Indic" }
  , { walsCode := "hix", name := "Hixkaryana", iso := "hix", family := "Cariban", genus := "Cariban" }
  , { walsCode := "hmo", name := "Hmong Njua", iso := "hnj", family := "Hmong-Mien", genus := "Hmongic" }
  , { walsCode := "hop", name := "Hopi", iso := "hop", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "hua", name := "Hua", iso := "ygr", family := "Trans-New Guinea", genus := "Siane-Yagaria" }
  , { walsCode := "hui", name := "Huichol", iso := "hch", family := "Uto-Aztecan", genus := "Corachol" }
  , { walsCode := "hmi", name := "Huitoto (Minica)", iso := "hto", family := "Witotoan", genus := "Witoto" }
  , { walsCode := "hmu", name := "Huitoto (Muinane)", iso := "hux", family := "Witotoan", genus := "Witoto" }
  , { walsCode := "hun", name := "Hungarian", iso := "hun", family := "Uralic", genus := "Ugric" }
  , { walsCode := "hzb", name := "Hunzib", iso := "huz", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "iaa", name := "Iaai", iso := "iai", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ice", name := "Icelandic", iso := "isl", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "igb", name := "Igbo", iso := "ibo", family := "Niger-Congo", genus := "Igboid" }
  , { walsCode := "ign", name := "Ignaciano", iso := "ign", family := "Arawakan", genus := "Bolivia-Parana" }
  , { walsCode := "ijo", name := "Ijo (Kolokuma)", iso := "ijc", family := "Ijoid", genus := "Ijoid" }
  , { walsCode := "ika", name := "Ika", iso := "arh", family := "Chibchan", genus := "Arhuacic" }
  , { walsCode := "ila", name := "Ila", iso := "ilb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "imo", name := "Imonda", iso := "imn", family := "Border", genus := "Border" }
  , { walsCode := "ind", name := "Indonesian", iso := "ind", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "ing", name := "Ingush", iso := "inh", family := "Nakh-Daghestanian", genus := "Nakh" }
  , { walsCode := "iqu", name := "Iquito", iso := "iqu", family := "Zaparoan", genus := "Zaparoan" }
  , { walsCode := "irq", name := "Iraqw", iso := "irk", family := "Afro-Asiatic", genus := "Southern Cushitic" }
  , { walsCode := "iri", name := "Irish", iso := "gle", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "ita", name := "Italian", iso := "ita", family := "Indo-European", genus := "Romance" }
  , { walsCode := "ite", name := "Itelmen", iso := "itl", family := "Chukotko-Kamchatkan", genus := "Southern Chukotko-Kamchatkan" }
  , { walsCode := "jak", name := "Jakaltek", iso := "jac", family := "Mayan", genus := "Mayan" }
  , { walsCode := "jpn", name := "Japanese", iso := "jpn", family := "Japanese", genus := "Japanese" }
  , { walsCode := "jaq", name := "Jaqaru", iso := "jqr", family := "Aymaran", genus := "Aymaran" }
  , { walsCode := "juh", name := "Ju|'hoan", iso := "ktz", family := "Kxa", genus := "Ju-Kung" }
  , { walsCode := "kab", name := "Kabardian", iso := "kbd", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "kdz", name := "Kadazan", iso := "kzj", family := "Austronesian", genus := "North Borneo" }
  , { walsCode := "kng", name := "Kaingang", iso := "kgp", family := "Macro-Ge", genus := "Je Meridional" }
  , { walsCode := "kls", name := "Kalispel", iso := "fla", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "kgu", name := "Kalkatungu", iso := "ktg", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kmk", name := "Kalmyk", iso := "xal", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "kam", name := "Kambera", iso := "xbr", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "knd", name := "Kannada", iso := "kan", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "knr", name := "Kanuri", iso := "knc", family := "Saharan", genus := "Western Saharan" }
  , { walsCode := "kpm", name := "Kapampangan", iso := "pam", family := "Austronesian", genus := "Central Luzon" }
  , { walsCode := "krc", name := "Karachay-Balkar", iso := "krc", family := "Altaic", genus := "Turkic" }
  , { walsCode := "jva", name := "Karajá", iso := "kpj", family := "Macro-Ge", genus := "Karajá" }
  , { walsCode := "kna", name := "Karitiâna", iso := "ktn", family := "Tupian", genus := "Arikem" }
  , { walsCode := "krk", name := "Karok", iso := "kyh", family := "Hokan", genus := "Karok" }
  , { walsCode := "kas", name := "Kashmiri", iso := "kas", family := "Indo-European", genus := "Indic" }
  , { walsCode := "kws", name := "Kawaiisu", iso := "xaw", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "kyl", name := "Kayah Li (Eastern)", iso := "eky", family := "Sino-Tibetan", genus := "Karen" }
  , { walsCode := "kyp", name := "Kayapó", iso := "txu", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "kay", name := "Kayardild", iso := "gyd", family := "Tangkic", genus := "Tangkic" }
  , { walsCode := "kem", name := "Kemant", iso := "ahg", family := "Afro-Asiatic", genus := "Central Cushitic" }
  , { walsCode := "ker", name := "Kera", iso := "ker", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "ket", name := "Ket", iso := "ket", family := "Yeniseian", genus := "Yeniseian" }
  , { walsCode := "kew", name := "Kewa", iso := "kew", family := "Trans-New Guinea", genus := "Enga_Kewa-Huli" }
  , { walsCode := "khk", name := "Khakas", iso := "kjh", family := "Altaic", genus := "Turkic" }
  , { walsCode := "kha", name := "Khalkha", iso := "khk", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "khs", name := "Khasi", iso := "kha", family := "Austro-Asiatic", genus := "Khasian" }
  , { walsCode := "khm", name := "Khmer", iso := "khm", family := "Austro-Asiatic", genus := "Khmer" }
  , { walsCode := "kmu", name := "Khmu'", iso := "kjg", family := "Austro-Asiatic", genus := "Khmuic" }
  , { walsCode := "klv", name := "Kilivila", iso := "kij", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kin", name := "Kinyarwanda", iso := "kin", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kio", name := "Kiowa", iso := "kio", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "kgz", name := "Kirghiz", iso := "kir", family := "Altaic", genus := "Turkic" }
  , { walsCode := "krb", name := "Kiribati", iso := "gil", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kis", name := "Kisi", iso := "kss", family := "Niger-Congo", genus := "Southern Mel" }
  , { walsCode := "shp", name := "Klikitat", iso := "yak", family := "Penutian", genus := "Sahaptian" }
  , { walsCode := "koa", name := "Koasati", iso := "cku", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "kob", name := "Kobon", iso := "kpw", family := "Trans-New Guinea", genus := "Kalam-Kobon" }
  , { walsCode := "kol", name := "Kolami", iso := "kfb", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kom", name := "Komo", iso := "xom", family := "Koman", genus := "Koman" }
  , { walsCode := "kon", name := "Kongo", iso := "kng", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kjo", name := "Konjo", iso := "kjc", family := "Austronesian", genus := "South Sulawesi" }
  , { walsCode := "krn", name := "Korana", iso := "kqz", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "kor", name := "Korean", iso := "kor", family := "Korean", genus := "Korean" }
  , { walsCode := "kfe", name := "Koromfe", iso := "kfz", family := "Niger-Congo", genus := "Koromfe" }
  , { walsCode := "kos", name := "Kosraean", iso := "kos", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kch", name := "Koyra Chiini", iso := "khq", family := "Songhay", genus := "Songhay" }
  , { walsCode := "kse", name := "Koyraboro Senni", iso := "ses", family := "Songhay", genus := "Songhay" }
  , { walsCode := "kro", name := "Krongo", iso := "kgo", family := "Kadu", genus := "Kadugli" }
  , { walsCode := "kuk", name := "Kukú", iso := "bfa", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "knm", name := "Kunama", iso := "kun", family := "Kunama", genus := "Kunama" }
  , { walsCode := "krd", name := "Kurdish (Central)", iso := "ckb", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "kut", name := "Kutenai", iso := "kut", family := "Kutenai", genus := "Kutenai" }
  , { walsCode := "kwa", name := "Kwaio", iso := "kwd", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kwz", name := "Kwaza", iso := "xwa", family := "Kwaza", genus := "Kwaza" }
  , { walsCode := "lad", name := "Ladakhi", iso := "lbj", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "lah", name := "Lahu", iso := "lhu", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "lai", name := "Lai", iso := "cnh", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "lak", name := "Lak", iso := "lbe", family := "Nakh-Daghestanian", genus := "Lak" }
  , { walsCode := "lkt", name := "Lakhota", iso := "lkt", family := "Siouan", genus := "Mississippi Valley Siouan" }
  , { walsCode := "lal", name := "Lalo", iso := "ywt", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "lmp", name := "Lampung", iso := "ljp", family := "Austronesian", genus := "Lampungic" }
  , { walsCode := "lan", name := "Lango", iso := "laj", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "lrd", name := "Lardil", iso := "lbz", family := "Tangkic", genus := "Tangkic" }
  , { walsCode := "lat", name := "Latvian", iso := "lav", family := "Indo-European", genus := "Baltic" }
  , { walsCode := "lav", name := "Lavukaleve", iso := "lvk", family := "Solomons East Papuan", genus := "Lavukaleve" }
  , { walsCode := "lel", name := "Lele", iso := "lln", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "lep", name := "Lepcha", iso := "lep", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "let", name := "Leti", iso := "lti", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "lez", name := "Lezgian", iso := "lez", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "lim", name := "Limbu", iso := "lif", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "lin", name := "Lingala", iso := "lin", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lit", name := "Lithuanian", iso := "lit", family := "Indo-European", genus := "Baltic" }
  , { walsCode := "ara", name := "Lokono", iso := "arw", family := "Arawakan", genus := "Antillean Arawakan" }
  , { walsCode := "lui", name := "Luiseño", iso := "lui", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "kkv", name := "Lusi", iso := "khl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "luv", name := "Luvale", iso := "lue", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lye", name := "Lyele", iso := "lee", family := "Niger-Congo", genus := "Grusi" }
  , { walsCode := "mle", name := "Maale", iso := "mdy", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "maa", name := "Maasai", iso := "mas", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "mab", name := "Maba", iso := "mde", family := "Maban", genus := "Maban" }
  , { walsCode := "mac", name := "Macushi", iso := "mbc", family := "Cariban", genus := "Cariban" }
  , { walsCode := "mne", name := "Maidu (Northeast)", iso := "nmu", family := "Penutian", genus := "Maiduan" }
  , { walsCode := "msn", name := "Maisin", iso := "mbq", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mak", name := "Makah", iso := "myh", family := "Wakashan", genus := "Southern Wakashan" }
  , { walsCode := "mal", name := "Malagasy", iso := "plt", family := "Austronesian", genus := "Barito" }
  , { walsCode := "mlk", name := "Malakmalak", iso := "mpb", family := "Northern Daly", genus := "Northern Daly" }
  , { walsCode := "mym", name := "Malayalam", iso := "mal", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "mam", name := "Mam", iso := "mam", family := "Mayan", genus := "Mayan" }
  , { walsCode := "mnm", name := "Manam", iso := "mva", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mnd", name := "Mandarin", iso := "cmn", family := "Sino-Tibetan", genus := "Chinese" }
  , { walsCode := "myi", name := "Mangarrayi", iso := "mpc", family := "Mangarrayi-Maran", genus := "Mangarrayi" }
  , { walsCode := "mwb", name := "Manobo (Western Bukidnon)", iso := "mbb", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "mns", name := "Mansi", iso := "mns", family := "Uralic", genus := "Ugric" }
  , { walsCode := "mao", name := "Maori", iso := "mri", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "map", name := "Mapudungun", iso := "arn", family := "Araucanian", genus := "Araucanian" }
  , { walsCode := "mku", name := "Maranungku", iso := "zmr", family := "Western Daly", genus := "Wagaydy" }
  , { walsCode := "mhi", name := "Marathi", iso := "mar", family := "Indo-European", genus := "Indic" }
  , { walsCode := "mny", name := "Margany", iso := "zmc", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "mar", name := "Maricopa", iso := "mrc", family := "Hokan", genus := "Yuman" }
  , { walsCode := "mrd", name := "Marind", iso := "mrz", family := "Trans-New Guinea", genus := "Marind-Yaqay" }
  , { walsCode := "mrt", name := "Martuthunira", iso := "vma", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "msl", name := "Masalit", iso := "mls", family := "Maban", genus := "Maban" }
  , { walsCode := "mau", name := "Maung", iso := "mph", family := "Iwaidjan", genus := "Iwaidjan" }
  , { walsCode := "mcr", name := "Mauritian Creole", iso := "mfe", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "max", name := "Maxakalí", iso := "mbl", family := "Macro-Ge", genus := "Maxakalian" }
  , { walsCode := "may", name := "Maybrat", iso := "ayz", family := "Maybrat", genus := "Maybrat" }
  , { walsCode := "mby", name := "Mbay", iso := "myb", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "mei", name := "Meithei", iso := "mni", family := "Sino-Tibetan", genus := "Manipuri" }
  , { walsCode := "mde", name := "Mende", iso := "men", family := "Mande", genus := "Western Mande" }
  , { walsCode := "men", name := "Menomini", iso := "mez", family := "Algic", genus := "Algonquian" }
  , { walsCode := "mis", name := "Miskito", iso := "miq", family := "Misumalpan", genus := "Misumalpan" }
  , { walsCode := "mss", name := "Miwok (Southern Sierra)", iso := "skd", family := "Penutian", genus := "Miwok" }
  , { walsCode := "mxc", name := "Mixtec (Chalcatongo)", iso := "mig", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "miz", name := "Mizo", iso := "lus", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "mlm", name := "Mlabri (Minor)", iso := "mra", family := "Austro-Asiatic", genus := "Khmuic" }
  , { walsCode := "moh", name := "Mohawk", iso := "moh", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "mno", name := "Mono (in United States)", iso := "mnr", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "moa", name := "Mono-Alu", iso := "mte", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mul", name := "Mulao", iso := "mlm", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "mum", name := "Mumuye", iso := "mzm", family := "Niger-Congo", genus := "Mumuye-Yandang" }
  , { walsCode := "mna", name := "Muna", iso := "mnb", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "mud", name := "Mundani", iso := "mnf", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "mun", name := "Mundari", iso := "unr", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "mup", name := "Mupun", iso := "sur", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "mrl", name := "Murle", iso := "mur", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "nad", name := "Nadëb", iso := "mbj", family := "Nadahup", genus := "Nadahup" }
  , { walsCode := "nht", name := "Nahuatl (Tetelcingo)", iso := "nhg", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nak", name := "Nakanai", iso := "nak", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kho", name := "Nama", iso := "naq", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "nai", name := "Nanai", iso := "gld", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "nan", name := "Nandi", iso := "niq", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "nas", name := "Nasioi", iso := "nas", family := "South Bougainville", genus := "South Bougainville" }
  , { walsCode := "nav", name := "Navajo", iso := "nav", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "ndo", name := "Ndonga", iso := "ndo", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ndy", name := "Ndyuka", iso := "djk", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "neh", name := "Nehan", iso := "nsn", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nel", name := "Nelemwa", iso := "nee", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ntu", name := "Nenets", iso := "yrk", family := "Uralic", genus := "Samoyedic" }
  , { walsCode := "nez", name := "Nez Perce", iso := "nez", family := "Penutian", genus := "Sahaptian" }
  , { walsCode := "ngl", name := "Ngalakan", iso := "nig", family := "Gunwinyguan", genus := "Eastern Gunwinyguan" }
  , { walsCode := "ngn", name := "Ngandi", iso := "nid", family := "Gunwinyguan", genus := "Eastern Gunwinyguan" }
  , { walsCode := "ngk", name := "Ngankikurungkurr", iso := "nam", family := "Southern Daly", genus := "Ngankikurungkurr" }
  , { walsCode := "nti", name := "Ngiti", iso := "niy", family := "Central Sudanic", genus := "Lendu" }
  , { walsCode := "ngi", name := "Ngiyambaa", iso := "wyb", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "nbr", name := "Ngäbere", iso := "gym", family := "Chibchan", genus := "Guaymiic" }
  , { walsCode := "nca", name := "Nicobarese (Car)", iso := "caq", family := "Austro-Asiatic", genus := "Nicobarese" }
  , { walsCode := "niu", name := "Niuean", iso := "niu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "niv", name := "Nivkh", iso := "niv", family := "Nivkh", genus := "Nivkh" }
  , { walsCode := "nko", name := "Nkore-Kiga", iso := "cgg", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nom", name := "Nomatsiguenga", iso := "not", family := "Arawakan", genus := "Pre-Andine Arawakan" }
  , { walsCode := "noo", name := "Noon", iso := "snf", family := "Niger-Congo", genus := "Cangin" }
  , { walsCode := "nbd", name := "Nubian (Dongolese)", iso := "dgl", family := "Eastern Sudanic", genus := "Nubian" }
  , { walsCode := "nug", name := "Nunggubuyu", iso := "nuy", family := "Gunwinyguan", genus := "Nunggubuyu" }
  , { walsCode := "nup", name := "Nupe", iso := "nup", family := "Niger-Congo", genus := "Nupoid" }
  , { walsCode := "nuu", name := "Nuuchahnulth", iso := "nuk", family := "Wakashan", genus := "Southern Wakashan" }
  , { walsCode := "nym", name := "Nyamwezi", iso := "nym", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nyu", name := "Nyulnyul", iso := "nyv", family := "Nyulnyulan", genus := "Nyulnyulan" }
  , { walsCode := "ood", name := "O'odham", iso := "ood", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "oji", name := "Ojibwa (Eastern)", iso := "", family := "Algic", genus := "Algonquian" }
  , { walsCode := "ojm", name := "Ojibwe (Minnesota)", iso := "ciw", family := "Algic", genus := "Algonquian" }
  , { walsCode := "ond", name := "Oneida", iso := "one", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "orh", name := "Oromo (Harar)", iso := "hae", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "orw", name := "Oromo (Waata)", iso := "ssn", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "oss", name := "Ossetic", iso := "oss", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "otm", name := "Otomí (Mezquital)", iso := "ote", family := "Oto-Manguean", genus := "Otomian" }
  , { walsCode := "pkn", name := "Paakantyi", iso := "drl", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "pms", name := "Paamese", iso := "pma", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pno", name := "Paiute (Northern)", iso := "pao", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "put", name := "Paiute (Southern)", iso := "ute", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "pai", name := "Paiwan", iso := "pwn", family := "Austronesian", genus := "Paiwan" }
  , { walsCode := "pal", name := "Palauan", iso := "pau", family := "Austronesian", genus := "Palauan" }
  , { walsCode := "plk", name := "Palikur", iso := "plu", family := "Arawakan", genus := "Palikur" }
  , { walsCode := "pan", name := "Panjabi", iso := "pan", family := "Indo-European", genus := "Indic" }
  , { walsCode := "pny", name := "Panyjima", iso := "pnw", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "psh", name := "Pashto", iso := "pst", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "psm", name := "Passamaquoddy-Maliseet", iso := "pqm", family := "Algic", genus := "Algonquian" }
  , { walsCode := "pau", name := "Paumarí", iso := "pad", family := "Arauan", genus := "Arauan" }
  , { walsCode := "pwn", name := "Pawnee", iso := "paw", family := "Caddoan", genus := "Northern Caddoan" }
  , { walsCode := "pec", name := "Pech", iso := "pay", family := "Chibchan", genus := "Pech" }
  , { walsCode := "prs", name := "Persian", iso := "pes", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "pip", name := "Pipil", iso := "ppl", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "prh", name := "Pirahã", iso := "myp", family := "Mura", genus := "Mura" }
  , { walsCode := "pir", name := "Piro", iso := "pib", family := "Arawakan", genus := "Purus" }
  , { walsCode := "pit", name := "Pitjantjatjara", iso := "pjt", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "ppi", name := "Pitta Pitta", iso := "pit", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "pol", name := "Polish", iso := "pol", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "pmc", name := "Pomo (Central)", iso := "poo", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "pso", name := "Pomo (Southeastern)", iso := "pom", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "psj", name := "Popoloca (San Juan Atzingo)", iso := "poe", family := "Oto-Manguean", genus := "Popolocan" }
  , { walsCode := "pul", name := "Puluwat", iso := "puw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pur", name := "Purépecha", iso := "tsz", family := "Tarascan", genus := "Tarascan" }
  , { walsCode := "par", name := "Päri", iso := "lkr", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "qaf", name := "Qafar", iso := "aar", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "qaw", name := "Qawasqar", iso := "alc", family := "Alacalufan", genus := "Alacalufan" }
  , { walsCode := "qbo", name := "Quechua (Bolivian)", iso := "", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qcu", name := "Quechua (Cuzco)", iso := "quz", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qhu", name := "Quechua (Huallaga)", iso := "qub", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qim", name := "Quechua (Imbabura)", iso := "qvi", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qui", name := "Quileute", iso := "qui", family := "Chimakuan", genus := "Chimakuan" }
  , { walsCode := "ram", name := "Rama", iso := "rma", family := "Chibchan", genus := "Rama" }
  , { walsCode := "rap", name := "Rapanui", iso := "rap", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "rej", name := "Rejang", iso := "rej", family := "Austronesian", genus := "Rejang" }
  , { walsCode := "rem", name := "Remo", iso := "bfw", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "ret", name := "Retuarã", iso := "tnc", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "rot", name := "Rotuman", iso := "rtm", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ruk", name := "Rukai (Tanan)", iso := "dru", family := "Austronesian", genus := "Rukai" }
  , { walsCode := "rus", name := "Russian", iso := "rus", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "sah", name := "Sahu", iso := "saj", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "sal", name := "Salinan", iso := "sln", family := "Hokan", genus := "Salinan" }
  , { walsCode := "syu", name := "Salt-Yui", iso := "sll", family := "Trans-New Guinea", genus := "Chimbu-Wahgi" }
  , { walsCode := "sam", name := "Samoan", iso := "smo", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "san", name := "Sango", iso := "sag", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "snm", name := "Sanuma", iso := "xsu", family := "Yanomam", genus := "Yanomam" }
  , { walsCode := "srm", name := "Saramaccan", iso := "srm", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "src", name := "Sarcee", iso := "srs", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "saw", name := "Sawu", iso := "hvn", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "slp", name := "Selepet", iso := "spl", family := "Trans-New Guinea", genus := "Huon" }
  , { walsCode := "sel", name := "Selknam", iso := "ona", family := "Chonan", genus := "Chonan Proper" }
  , { walsCode := "sem", name := "Sema", iso := "nsm", family := "Sino-Tibetan", genus := "Angami-Pochuri" }
  , { walsCode := "sml", name := "Semelai", iso := "sza", family := "Austro-Asiatic", genus := "Aslian" }
  , { walsCode := "snc", name := "Seneca", iso := "see", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "snt", name := "Sentani", iso := "set", family := "Sentanic", genus := "Sentanic" }
  , { walsCode := "srr", name := "Serrano", iso := "ser", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "shk", name := "Shipibo-Konibo", iso := "shp", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "shn", name := "Shona", iso := "sna", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sho", name := "Shoshone", iso := "shh", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "shu", name := "Shuswap", iso := "shs", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "snh", name := "Sinhala", iso := "sin", family := "Indo-European", genus := "Indic" }
  , { walsCode := "srn", name := "Sirionó", iso := "srq", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "siu", name := "Siuslaw", iso := "sis", family := "Oregon Coast", genus := "Siuslawan" }
  , { walsCode := "sla", name := "Slave", iso := "den", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "so", name := "So", iso := "teu", family := "Eastern Sudanic", genus := "Kuliak" }
  , { walsCode := "son", name := "Sonsorol-Tobi", iso := "sov", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sor", name := "Sora", iso := "srb", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "spa", name := "Spanish", iso := "spa", family := "Indo-European", genus := "Romance" }
  , { walsCode := "squ", name := "Squamish", iso := "squ", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "sue", name := "Suena", iso := "sue", family := "Trans-New Guinea", genus := "Binanderean" }
  , { walsCode := "sun", name := "Sundanese", iso := "sun", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "sup", name := "Supyire", iso := "spp", family := "Niger-Congo", genus := "Senufo" }
  , { walsCode := "sur", name := "Sursurunga", iso := "sgz", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "swa", name := "Swahili", iso := "swh", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "swt", name := "Swati", iso := "ssw", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tab", name := "Taba", iso := "mky", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "tag", name := "Tagalog", iso := "tgl", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "tah", name := "Tahitian", iso := "tah", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tap", name := "Taiap", iso := "gpn", family := "Taiap", genus := "Taiap" }
  , { walsCode := "tkl", name := "Takelma", iso := "tkm", family := "Takelma", genus := "Takelma" }
  , { walsCode := "tml", name := "Tamil", iso := "tam", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "tce", name := "Tarahumara (Central)", iso := "tar", family := "Uto-Aztecan", genus := "Tarahumaran" }
  , { walsCode := "tar", name := "Tariana", iso := "tae", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "tas", name := "Tashlhiyt", iso := "shi", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "tau", name := "Tauya", iso := "tya", family := "Trans-New Guinea", genus := "Rai Coast" }
  , { walsCode := "taw", name := "Tawala", iso := "tbo", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tel", name := "Telugu", iso := "tel", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "tmr", name := "Temiar", iso := "tea", family := "Austro-Asiatic", genus := "Aslian" }
  , { walsCode := "tpc", name := "Tepecano", iso := "tep", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "tep", name := "Tepehua (Tlachichilco)", iso := "tpt", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "tpn", name := "Tepehuan (Northern)", iso := "ntp", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "trb", name := "Teribe", iso := "tfr", family := "Chibchan", genus := "Western Isthmic Chibchan" }
  , { walsCode := "tha", name := "Thai", iso := "tha", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "tho", name := "Thompson", iso := "thp", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "tib", name := "Tibetan (Standard Spoken)", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tid", name := "Tidore", iso := "tvo", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "tgk", name := "Tigak", iso := "tgc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tja", name := "Tiipay (Jamul)", iso := "dih", family := "Hokan", genus := "Yuman" }
  , { walsCode := "tim", name := "Timugon", iso := "tih", family := "Austronesian", genus := "North Borneo" }
  , { walsCode := "tin", name := "Tinrin", iso := "cir", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tir", name := "Tiriyo", iso := "tri", family := "Cariban", genus := "Cariban" }
  , { walsCode := "tiw", name := "Tiwi", iso := "tiw", family := "Tiwian", genus := "Tiwian" }
  , { walsCode := "tli", name := "Tlingit", iso := "tli", family := "Na-Dene", genus := "Tlingit" }
  , { walsCode := "tol", name := "Tol", iso := "jic", family := "Tol", genus := "Tol" }
  , { walsCode := "tla", name := "Tolai", iso := "ksd", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tms", name := "Tommo So", iso := "dto", family := "Dogon", genus := "Dogon" }
  , { walsCode := "tno", name := "Tondano", iso := "tdn", family := "Austronesian", genus := "Minahasan" }
  , { walsCode := "tng", name := "Tongan", iso := "ton", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ton", name := "Tonkawa", iso := "tqw", family := "Tonkawa", genus := "Tonkawa" }
  , { walsCode := "toq", name := "Toqabaqita", iso := "mlu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tot", name := "Totonac (Misantla)", iso := "tlc", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "tri", name := "Trique (Copala)", iso := "trc", family := "Oto-Manguean", genus := "Trique" }
  , { walsCode := "tru", name := "Trumai", iso := "tpy", family := "Trumai", genus := "Trumai" }
  , { walsCode := "tsz", name := "Tsez", iso := "ddo", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "tsi", name := "Tsimshian (Coast)", iso := "tsi", family := "Tsimshianic", genus := "Tsimshianic" }
  , { walsCode := "tso", name := "Tsou", iso := "tsu", family := "Austronesian", genus := "Tsou" }
  , { walsCode := "tsw", name := "Tswana", iso := "tsn", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tuc", name := "Tucano", iso := "tuo", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "tuk", name := "Tukang Besi", iso := "", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "tun", name := "Tunica", iso := "tun", family := "Tunica", genus := "Tunica" }
  , { walsCode := "tna", name := "Turkana", iso := "tuv", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "tur", name := "Turkish", iso := "tur", family := "Altaic", genus := "Turkic" }
  , { walsCode := "tus", name := "Tuscarora", iso := "tus", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "tvl", name := "Tuvaluan", iso := "tvl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tuv", name := "Tuvan", iso := "tyv", family := "Altaic", genus := "Turkic" }
  , { walsCode := "tzo", name := "Tzotzil", iso := "tzo", family := "Mayan", genus := "Mayan" }
  , { walsCode := "tzu", name := "Tzutujil", iso := "tzj", family := "Mayan", genus := "Mayan" }
  , { walsCode := "tbb", name := "Tübatulabal", iso := "tub", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "tsh", name := "Tümpisa Shoshone", iso := "par", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "udh", name := "Udihe", iso := "ude", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "ukr", name := "Ukrainian", iso := "ukr", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "uli", name := "Ulithian", iso := "uli", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "uma", name := "Uma", iso := "ppk", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "una", name := "Una", iso := "mtg", family := "Trans-New Guinea", genus := "Mek" }
  , { walsCode := "ung", name := "Ungarinjin", iso := "ung", family := "Worrorran", genus := "Worrorran" }
  , { walsCode := "ura", name := "Ura", iso := "uur", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "uhi", name := "Uradhi", iso := "urf", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "urk", name := "Urubú-Kaapor", iso := "urb", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "usa", name := "Usan", iso := "wnu", family := "Trans-New Guinea", genus := "North Adelbert" }
  , { walsCode := "ute", name := "Ute", iso := "ute", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "uzb", name := "Uzbek", iso := "", family := "Altaic", genus := "Turkic" }
  , { walsCode := "vai", name := "Vai", iso := "vai", family := "Mande", genus := "Western Mande" }
  , { walsCode := "vie", name := "Vietnamese", iso := "vie", family := "Austro-Asiatic", genus := "Vietic" }
  , { walsCode := "wam", name := "Wambaya", iso := "wmb", family := "Mirndi", genus := "Wambayan" }
  , { walsCode := "wbn", name := "Wambon", iso := "wms", family := "Trans-New Guinea", genus := "Dumut" }
  , { walsCode := "wao", name := "Waorani", iso := "auc", family := "Waorani", genus := "Waorani" }
  , { walsCode := "wap", name := "Wappo", iso := "wao", family := "Wappo-Yukian", genus := "Wappo" }
  , { walsCode := "wra", name := "Warao", iso := "wba", family := "Warao", genus := "Warao" }
  , { walsCode := "wrd", name := "Wardaman", iso := "wrr", family := "Yangmanic", genus := "Yangmanic" }
  , { walsCode := "wrk", name := "Warekena", iso := "gae", family := "Arawakan", genus := "Alto-Orinoco" }
  , { walsCode := "war", name := "Wari'", iso := "pav", family := "Chapacura-Wanham", genus := "Chapacura-Wanham" }
  , { walsCode := "wrl", name := "Warlpiri", iso := "wbp", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "wgu", name := "Warrongo", iso := "wrg", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "was", name := "Washo", iso := "was", family := "Washo", genus := "Washo" }
  , { walsCode := "wsk", name := "Waskia", iso := "wsk", family := "Trans-New Guinea", genus := "Kowan" }
  , { walsCode := "wat", name := "Watjarri", iso := "wbv", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "wur", name := "Waurá", iso := "wau", family := "Arawakan", genus := "Central Arawakan" }
  , { walsCode := "wel", name := "Welsh", iso := "cym", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "wma", name := "West Makian", iso := "mqs", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "wic", name := "Wichita", iso := "wic", family := "Caddoan", genus := "Northern Caddoan" }
  , { walsCode := "wch", name := "Wichí", iso := "mzh", family := "Matacoan", genus := "Matacoan" }
  , { walsCode := "wik", name := "Wikchamni", iso := "yok", family := "Penutian", genus := "Yokuts" }
  , { walsCode := "win", name := "Wintu", iso := "wnw", family := "Penutian", genus := "Wintuan" }
  , { walsCode := "wol", name := "Woleaian", iso := "woe", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "wlf", name := "Wolof", iso := "wol", family := "Niger-Congo", genus := "Wolof" }
  , { walsCode := "xer", name := "Xerénte", iso := "xer", family := "Macro-Ge", genus := "Je Central" }
  , { walsCode := "xok", name := "Xokleng", iso := "xok", family := "Macro-Ge", genus := "Je Meridional" }
  , { walsCode := "yag", name := "Yagua", iso := "yad", family := "Peba-Yaguan", genus := "Peba-Yaguan" }
  , { walsCode := "ykt", name := "Yakut", iso := "sah", family := "Altaic", genus := "Turkic" }
  , { walsCode := "ynk", name := "Yankuntjatjara", iso := "kdd", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "yap", name := "Yapese", iso := "yap", family := "Austronesian", genus := "Yapese" }
  , { walsCode := "yaq", name := "Yaqui", iso := "yaq", family := "Uto-Aztecan", genus := "Cahita" }
  , { walsCode := "yay", name := "Yay", iso := "pcc", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "yaz", name := "Yazgulyam", iso := "yah", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "yel", name := "Yelî Dnye", iso := "yle", family := "Yele", genus := "Yele" }
  , { walsCode := "yes", name := "Yessan-Mayo", iso := "yss", family := "Sepik", genus := "Tama Sepik" }
  , { walsCode := "yid", name := "Yidiny", iso := "yii", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "yim", name := "Yimas", iso := "yee", family := "Ramu-Lower Sepik", genus := "Lower Sepik" }
  , { walsCode := "yor", name := "Yoruba", iso := "yor", family := "Niger-Congo", genus := "Defoid" }
  , { walsCode := "yuc", name := "Yuchi", iso := "yuc", family := "Yuchi", genus := "Yuchi" }
  , { walsCode := "yko", name := "Yukaghir (Kolyma)", iso := "yux", family := "Yukaghir", genus := "Yukaghir" }
  , { walsCode := "ytu", name := "Yukaghir (Tundra)", iso := "ykg", family := "Yukaghir", genus := "Yukaghir" }
  , { walsCode := "yuk", name := "Yukulta", iso := "gcd", family := "Tangkic", genus := "Tangkic" }
  , { walsCode := "ypk", name := "Yup'ik (Central)", iso := "esu", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "yus", name := "Yupik (Siberian)", iso := "ess", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "yur", name := "Yurok", iso := "yur", family := "Algic", genus := "Yurok" }
  , { walsCode := "yuw", name := "Yuwaalaraay", iso := "kld", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "zan", name := "Zande", iso := "zne", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "zqc", name := "Zoque (Copainalá)", iso := "zoc", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "zul", name := "Zulu", iso := "zul", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "zun", name := "Zuni", iso := "zun", family := "Zuni", genus := "Zuni" }
  ]

/-- Look up a language by WALS code. -/
def findLanguage (code : String) : Option Language :=
  languages.find? (·.walsCode == code)

end Core.WALS
