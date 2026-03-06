/-!
# WALS Language Metadata

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py`.

1925 languages referenced across generated features.
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

private def languages_0 : List Language :=
  [ { walsCode := "xoo", name := "!Xóõ", iso := "nmn", family := "Tu", genus := "Tu" }
  , { walsCode := "ani", name := "//Ani", iso := "hnh", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "xam", name := "/Xam", iso := "xam", family := "Tu", genus := "Tu" }
  , { walsCode := "huc", name := "=|Hoan", iso := "huc", family := "Kxa", genus := "=|Hoan" }
  , { walsCode := "aar", name := "Aari", iso := "aiw", family := "Afro-Asiatic", genus := "South Omotic" }
  , { walsCode := "aba", name := "Abau", iso := "aau", family := "Sepik", genus := "Abau" }
  , { walsCode := "abz", name := "Abaza", iso := "abq", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "abi", name := "Abipón", iso := "axb", family := "Guaicuruan", genus := "Abipon" }
  , { walsCode := "abk", name := "Abkhaz", iso := "abk", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "abv", name := "Abui", iso := "abz", family := "Greater West Bomberai", genus := "Alor-Pantar" }
  , { walsCode := "abu", name := "Abun", iso := "kgr", family := "Abun", genus := "Abun" }
  , { walsCode := "ace", name := "Acehnese", iso := "ace", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "acg", name := "Achagua", iso := "aca", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "acn", name := "Achang", iso := "acn", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "acl", name := "Acholi", iso := "ach", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "acu", name := "Achuar", iso := "acu", family := "Jivaroan", genus := "Jivaroan" }
  , { walsCode := "acm", name := "Achumawi", iso := "acv", family := "Hokan", genus := "Achumawi" }
  , { walsCode := "aco", name := "Acoma", iso := "kjq", family := "Keresan", genus := "Keresan" }
  , { walsCode := "adg", name := "Adang", iso := "adn", family := "Greater West Bomberai", genus := "Alor-Pantar" }
  , { walsCode := "adi", name := "Adioukrou", iso := "adj", family := "Niger-Congo", genus := "Agneby" }
  , { walsCode := "ady", name := "Adyghe (Abzakh)", iso := "ady", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "ash", name := "Adyghe (Shapsugh)", iso := "ady", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "adn", name := "Adynyamathanha", iso := "adt", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "adz", name := "Adzera", iso := "adz", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "awi", name := "Aekyom", iso := "awi", family := "Kamula-Elevala", genus := "Elevala" }
  , { walsCode := "afr", name := "Afrikaans", iso := "afr", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "aga", name := "Agarabi", iso := "agd", family := "Trans-New Guinea", genus := "Gauwa" }
  , { walsCode := "agh", name := "Aghem", iso := "agq", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "ahu", name := "Aghu", iso := "ahh", family := "Trans-New Guinea", genus := "Awju" }
  , { walsCode := "agl", name := "Aghul", iso := "agx", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "agc", name := "Agta (Central)", iso := "agt", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "agd", name := "Agta (Dupaningan)", iso := "duo", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "agr", name := "Aguaruna", iso := "agr", family := "Jivaroan", genus := "Jivaroan" }
  , { walsCode := "ain", name := "Ainu", iso := "ain", family := "Ainu", genus := "Ainu" }
  , { walsCode := "aja", name := "Aja", iso := "aja", family := "Central Sudanic", genus := "Kresh" }
  , { walsCode := "ajg", name := "Ajagbe", iso := "ajg", family := "Niger-Congo", genus := "Gbe" }
  , { walsCode := "aji", name := "Ajië", iso := "aji", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "akn", name := "Akan", iso := "aka", family := "Niger-Congo", genus := "Tano" }
  , { walsCode := "akh", name := "Akha", iso := "ahk", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "all", name := "Ala'ala", iso := "nrz", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "abm", name := "Alabama", iso := "akz", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "agw", name := "Alagwa", iso := "wbj", family := "Afro-Asiatic", genus := "Southern Cushitic" }
  , { walsCode := "ala", name := "Alamblak", iso := "amp", family := "Sepik", genus := "Sepik Hill" }
  , { walsCode := "alw", name := "Alawa", iso := "alh", family := "Mangarrayi-Maran", genus := "Mara" }
  , { walsCode := "alb", name := "Albanian", iso := "sqi", family := "Indo-European", genus := "Albanian" }
  , { walsCode := "ale", name := "Aleut", iso := "ale", family := "Eskimo-Aleut", genus := "Aleut" }
  , { walsCode := "alc", name := "Allentiac", iso := "", family := "Huarpe", genus := "Huarpe" }
  , { walsCode := "als", name := "Alsea", iso := "aes", family := "Oregon Coast", genus := "Alsea" }
  , { walsCode := "aln", name := "Alune", iso := "alp", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "aly", name := "Alyawarra", iso := "aly", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "amm", name := "Ama", iso := "amm", family := "Left May", genus := "Left May" }
  , { walsCode := "amc", name := "Amahuaca", iso := "amc", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "amn", name := "Amanab", iso := "amn", family := "Border", genus := "Border" }
  , { walsCode := "ama", name := "Amara", iso := "aie", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "amk", name := "Amarakaeri", iso := "amr", family := "Harakmbet", genus := "Harakmbet" }
  , { walsCode := "aml", name := "Ambae (Lolovoli Northeast)", iso := "omb", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "amq", name := "Ambai", iso := "amk", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "amb", name := "Ambulas", iso := "abt", family := "Sepik", genus := "Ndu" }
  , { walsCode := "amd", name := "Amdo", iso := "adx", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "amt", name := "Amdo (Themchen)", iso := "adx", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "ame", name := "Amele", iso := "aey", family := "Trans-New Guinea", genus := "Mabuso" }
  , { walsCode := "amh", name := "Amharic", iso := "amh", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "ami", name := "Amis", iso := "ami", family := "Austronesian", genus := "East Formosan" }
  , { walsCode := "amo", name := "Amo", iso := "amo", family := "Niger-Congo", genus := "Central Kainji" }
  , { walsCode := "amu", name := "Amuesha", iso := "ame", family := "Arawakan", genus := "Yanesha'" }
  , { walsCode := "amx", name := "Anamuxra", iso := "imi", family := "Trans-New Guinea", genus := "Josephstaal" }
  , { walsCode := "adk", name := "Andoke", iso := "ano", family := "Andoke", genus := "Andoke" }
  , { walsCode := "anj", name := "Anejom", iso := "aty", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "agm", name := "Angami", iso := "njm", family := "Sino-Tibetan", genus := "Angami-Pochuri" }
  , { walsCode := "anc", name := "Angas", iso := "anc", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "ang", name := "Anggor", iso := "agg", family := "Senagi", genus := "Senagi" }
  , { walsCode := "agt", name := "Anguthimri", iso := "awg", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "ann", name := "Anindilyakwa", iso := "aoi", family := "Gunwinyguan", genus := "Anindilyakwa" }
  , { walsCode := "ano", name := "Anong", iso := "nun", family := "Sino-Tibetan", genus := "Nungish" }
  , { walsCode := "anu", name := "Anufo", iso := "cko", family := "Niger-Congo", genus := "Tano" }
  , { walsCode := "ayi", name := "Anyi", iso := "any", family := "Niger-Congo", genus := "Tano" }
  , { walsCode := "any", name := "Anywa", iso := "anu", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "ane", name := "Anêm", iso := "anz", family := "Anêm", genus := "Anêm" }
  , { walsCode := "ao", name := "Ao", iso := "njo", family := "Sino-Tibetan", genus := "Central Naga" }
  , { walsCode := "apc", name := "Apache (Chiricahua)", iso := "apm", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "apj", name := "Apache (Jicarilla)", iso := "apj", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "apw", name := "Apache (Western)", iso := "apw", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "apl", name := "Apalaí", iso := "apy", family := "Cariban", genus := "Cariban" }
  , { walsCode := "apt", name := "Apatani", iso := "apt", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "api", name := "Apinayé", iso := "apn", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "apu", name := "Apurinã", iso := "apu", family := "Arawakan", genus := "Purus" }
  , { walsCode := "abn", name := "Arabana", iso := "ard", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "arb", name := "Arabela", iso := "arl", family := "Zaparoan", genus := "Zaparoan" }
  , { walsCode := "aeg", name := "Arabic (Egyptian)", iso := "arz", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "arg", name := "Arabic (Gulf)", iso := "afb", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "arq", name := "Arabic (Iraqi)", iso := "acm", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "arj", name := "Arabic (Kuwaiti)", iso := "afb", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "ams", name := "Arabic (Modern Standard)", iso := "arb", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "amr", name := "Arabic (Moroccan)", iso := "ary", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "asy", name := "Arabic (Syrian)", iso := "apc", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "atu", name := "Arabic (Tunisian)", iso := "aeb", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "ana", name := "Araona", iso := "aro", family := "Pano-Tacanan", genus := "Tacanan" }
  , { walsCode := "aho", name := "Arapaho", iso := "arp", family := "Algic", genus := "Algonquian" }
  , { walsCode := "aab", name := "Arapesh (Abu)", iso := "aah", family := "Torricelli", genus := "Kombio-Arapesh" }
  , { walsCode := "arp", name := "Arapesh (Mountain)", iso := "ape", family := "Torricelli", genus := "Kombio-Arapesh" }
  , { walsCode := "abo", name := "Arbore", iso := "arv", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "arc", name := "Archi", iso := "aqc", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "ari", name := "Aribwatsa", iso := "laz", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "akr", name := "Arikara", iso := "ari", family := "Caddoan", genus := "Northern Caddoan" }
  , { walsCode := "arm", name := "Armenian (Eastern)", iso := "hye", family := "Indo-European", genus := "Armenian" }
  , { walsCode := "arw", name := "Armenian (Western)", iso := "hyw", family := "Indo-European", genus := "Armenian" }
  , { walsCode := "alk", name := "Arop-Lokep", iso := "apr", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "aro", name := "Arosi", iso := "aia", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "amp", name := "Arrernte (Mparntwe)", iso := "aer", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "awe", name := "Arrernte (Western)", iso := "are", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "asm", name := "Asmat", iso := "cns", family := "Asmat-Kamrau Bay", genus := "Asmat-Kamrau Bay" }
  , { walsCode := "ass", name := "Assamese", iso := "asm", family := "Indo-European", genus := "Indic" }
  , { walsCode := "asu", name := "Asuriní", iso := "asu", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "atm", name := "Atacameño", iso := "kuz", family := "Kunza", genus := "Kunza" }
  , { walsCode := "atk", name := "Atakapa", iso := "aqp", family := "Atakapa", genus := "Atakapa" }
  , { walsCode := "ata", name := "Atayal", iso := "tay", family := "Austronesian", genus := "Atayalic" }
  , { walsCode := "atc", name := "Atchin", iso := "upv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ath", name := "Athpare", iso := "aph", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "ats", name := "Atsugewi", iso := "atw", family := "Hokan", genus := "Atsugewi" }
  , { walsCode := "au", name := "Au", iso := "avt", family := "Torricelli", genus := "Central Wapei" }
  , { walsCode := "ava", name := "Avar", iso := "ava", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "avk", name := "Avikam", iso := "avi", family := "Niger-Congo", genus := "Avikam-Alladian" }
  , { walsCode := "avo", name := "Avokaya", iso := "avu", family := "Central Sudanic", genus := "Moru-Ma'di" }
  , { walsCode := "awa", name := "Awa", iso := "awb", family := "Trans-New Guinea", genus := "Gauwa" }
  , { walsCode := "awp", name := "Awa Pit", iso := "kwi", family := "Barbacoan", genus := "Barbacoan" }
  , { walsCode := "awn", name := "Awngi", iso := "awn", family := "Afro-Asiatic", genus := "Central Cushitic" }
  , { walsCode := "awt", name := "Awtuw", iso := "kmn", family := "Sepik", genus := "Ram" }
  , { walsCode := "awy", name := "Awyi", iso := "auw", family := "Border", genus := "Border" }
  , { walsCode := "ayw", name := "Ayiwo", iso := "nfl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "aym", name := "Aymara (Central)", iso := "ayr", family := "Aymaran", genus := "Aymaran" }
  , { walsCode := "ayo", name := "Ayomán", iso := "", family := "Jirajaran", genus := "Jirajaran" }
  , { walsCode := "ayr", name := "Ayoreo", iso := "ayo", family := "Zamucoan", genus := "Zamucoan" }
  , { walsCode := "azi", name := "Azari (Iranian)", iso := "azb", family := "Altaic", genus := "Turkic" }
  , { walsCode := "aze", name := "Azerbaijani", iso := "", family := "Altaic", genus := "Turkic" }
  , { walsCode := "blj", name := "Baale", iso := "koe", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "bbl", name := "Babole", iso := "bvx", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bab", name := "Babungo", iso := "bav", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "bac", name := "Bachamal", iso := "wdj", family := "Wandjiginy", genus := "Wandjiginy" }
  , { walsCode := "bdm", name := "Badimaya", iso := "bia", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "bfi", name := "Bafia", iso := "ksf", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "baf", name := "Bafut", iso := "bfd", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "bgs", name := "Baga Sitemu", iso := "bsp", family := "Niger-Congo", genus := "Northern Mel" }
  , { walsCode := "bag", name := "Bagirmi", iso := "bmi", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "bgr", name := "Bagiro", iso := "fuu", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "bgi", name := "Bagri", iso := "bgq", family := "Indo-European", genus := "Indic" }
  , { walsCode := "bgv", name := "Bagvalal", iso := "kva", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "bdw", name := "Baham", iso := "bdw", family := "Greater West Bomberai", genus := "West Bomberai" }
  , { walsCode := "bai", name := "Bai", iso := "bca", family := "Sino-Tibetan", genus := "Macro-Bai" }
  , { walsCode := "baj", name := "Bajau (Sama)", iso := "bdl", family := "Austronesian", genus := "Sama-Bajaw" }
  , { walsCode := "bwc", name := "Bajau (West Coast)", iso := "bdr", family := "Austronesian", genus := "Sama-Bajaw" }
  , { walsCode := "bak", name := "Baka (in Cameroon)", iso := "bkc", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "bka", name := "Baka (in South Sudan)", iso := "bdh", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "bku", name := "Bakueri", iso := "bri", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bkn", name := "Bakundu", iso := "bdu", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "blg", name := "Balangao", iso := "blw", family := "Austronesian", genus := "Northern Luzon" }
  , { walsCode := "blz", name := "Balanta", iso := "", family := "Niger-Congo", genus := "Balanta" }
  , { walsCode := "bvi", name := "Bali-Vitu", iso := "", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "bal", name := "Balinese", iso := "ban", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "blt", name := "Balti", iso := "bft", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "blc", name := "Baluchi", iso := "bgn", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "bam", name := "Bambara", iso := "bam", family := "Mande", genus := "Western Mande" }
  , { walsCode := "bnj", name := "Bandjalang", iso := "bdy", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "bgg", name := "Banggai", iso := "bgz", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "bgz", name := "Banggi", iso := "bdg", family := "Austronesian", genus := "North Borneo" }
  , { walsCode := "bgm", name := "Bangime", iso := "dba", family := "Bangime", genus := "Bangime" }
  , { walsCode := "bnw", name := "Baniwa", iso := "bwi", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "bnk", name := "Bankon", iso := "abb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bnn", name := "Banoni", iso := "bcm", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "bao", name := "Bao'an", iso := "peh", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "ble", name := "Baoulé", iso := "bci", family := "Niger-Congo", genus := "Tano" }
  , { walsCode := "brl", name := "Baragaunle", iso := "loy", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "baa", name := "Barai", iso := "bbb", family := "Trans-New Guinea", genus := "Koiarian" }
  , { walsCode := "bbu", name := "Barambu", iso := "brm", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "brs", name := "Barasano", iso := "bsn", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "mug", name := "Bargam", iso := "mlp", family := "Trans-New Guinea", genus := "Bargam" }
  , { walsCode := "bar", name := "Bari", iso := "bfa", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "brp", name := "Barupu", iso := "bpe", family := "Skou", genus := "Warapu" }
  , { walsCode := "bry", name := "Baruya", iso := "byr", family := "Trans-New Guinea", genus := "Nuclear Angan" }
  , { walsCode := "bae", name := "Baré", iso := "bae", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "bsr", name := "Basari", iso := "bsc", family := "Niger-Congo", genus := "Tenda" }
  , { walsCode := "bas", name := "Basaá", iso := "bas", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bsk", name := "Bashkir", iso := "bak", family := "Altaic", genus := "Turkic" }
  , { walsCode := "bsq", name := "Basque", iso := "eus", family := "Basque", genus := "Basque" }
  , { walsCode := "bkr", name := "Batak (Karo)", iso := "btx", family := "Austronesian", genus := "Northwest Sumatra-Barrier Islands" }
  , { walsCode := "bto", name := "Batak (Toba)", iso := "bbc", family := "Austronesian", genus := "Northwest Sumatra-Barrier Islands" }
  , { walsCode := "bau", name := "Bau", iso := "bbd", family := "Trans-New Guinea", genus := "Mabuso" }
  , { walsCode := "baq", name := "Baure", iso := "brg", family := "Arawakan", genus := "Bolivia-Parana" }
  , { walsCode := "bzi", name := "Bauzi", iso := "bvz", family := "Geelvink Bay", genus := "Geelvink Bay" }
  , { walsCode := "baw", name := "Bawm", iso := "bgr", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "bys", name := "Bayso", iso := "bsw", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "bej", name := "Beja", iso := "bej", family := "Afro-Asiatic", genus := "Beja" }
  , { walsCode := "bel", name := "Belhare", iso := "byw", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "bco", name := "Bella Coola", iso := "blc", family := "Salishan", genus := "Bella Coola" }
  , { walsCode := "blr", name := "Belorussian", iso := "bel", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "bem", name := "Bemba", iso := "bem", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "blu", name := "Bena-Lulua", iso := "lua", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "beb", name := "Benabena", iso := "bef", family := "Trans-New Guinea", genus := "Siane-Yagaria" }
  , { walsCode := "bga", name := "Benga", iso := "bng", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ben", name := "Bengali", iso := "ben", family := "Indo-European", genus := "Indic" }
  , { walsCode := "bec", name := "Bengali (Chittagong)", iso := "ctg", family := "Indo-European", genus := "Indic" }
  , { walsCode := "brq", name := "Bera", iso := "brf", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bse", name := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "bch", name := "Berber (Chaouia)", iso := "shy", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "bfg", name := "Berber (Figuig)", iso := "grr", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "bma", name := "Berber (Middle Atlas)", iso := "tzm", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "bmz", name := "Berber (Mzab)", iso := "mzb", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "brf", name := "Berber (Rif)", iso := "rif", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "bsi", name := "Berber (Siwa)", iso := "siz", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "bdc", name := "Berbice Dutch Creole", iso := "brc", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "zag", name := "Beria", iso := "zag", family := "Saharan", genus := "Eastern Saharan" }
  , { walsCode := "ber", name := "Berta", iso := "wti", family := "Berta", genus := "Berta" }
  , { walsCode := "bti", name := "Betoi", iso := "", family := "Betoi", genus := "Betoi" }
  , { walsCode := "bkb", name := "Betta Kurumba", iso := "xub", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "bez", name := "Bezhta", iso := "kap", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "bho", name := "Bhojpuri", iso := "bho", family := "Indo-European", genus := "Indic" }
  , { walsCode := "bhu", name := "Bhumij", iso := "unr", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "bik", name := "Biak", iso := "bhw", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "bid", name := "Bidiya", iso := "bid", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "bkl", name := "Bikol", iso := "bcl", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "bia", name := "Bila", iso := "bip", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bln", name := "Bilin", iso := "byn", family := "Afro-Asiatic", genus := "Central Cushitic" }
  , { walsCode := "bnr", name := "Bilinarra", iso := "nbj", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "blx", name := "Biloxi", iso := "bll", family := "Siouan", genus := "Ohio Valley Siouan" }
  , { walsCode := "bil", name := "Bilua", iso := "blb", family := "Solomons East Papuan", genus := "Bilua" }
  , { walsCode := "bmb", name := "Bimoba", iso := "bim", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "bin", name := "Binandere", iso := "bhg", family := "Trans-New Guinea", genus := "Binanderean" }
  , { walsCode := "big", name := "Binga", iso := "yul", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "bni", name := "Bini", iso := "bin", family := "Niger-Congo", genus := "Edoid" }
  , { walsCode := "bbw", name := "Bininj Gun-Wok", iso := "gup", family := "Gunwinyguan", genus := "Marne" }
  , { walsCode := "bii", name := "Biri", iso := "bzr", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "bir", name := "Birom", iso := "bom", family := "Niger-Congo", genus := "Benue-Congo Plateau" }
  , { walsCode := "bis", name := "Bisa", iso := "bib", family := "Mande", genus := "Eastern Mande" }
  , { walsCode := "bsm", name := "Bislama", iso := "bis", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "biu", name := "Bisu", iso := "", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "bla", name := "Blackfoot", iso := "bla", family := "Algic", genus := "Algonquian" }
  , { walsCode := "boa", name := "Boazi (Kuni)", iso := "kvg", family := "Trans-New Guinea", genus := "Boazi" }
  , { walsCode := "bob", name := "Bobangi", iso := "bni", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bbf", name := "Bobo Madaré (Northern)", iso := "bbo", family := "Mande", genus := "Western Mande" }
  , { walsCode := "bod", name := "Bodo", iso := "brx", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "boi", name := "Boiken", iso := "bzf", family := "Sepik", genus := "Ndu" }
  , { walsCode := "boq", name := "Bokar", iso := "", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "bok", name := "Boko", iso := "bqc", family := "Mande", genus := "Eastern Mande" }
  , { walsCode := "blq", name := "Bole", iso := "bol", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "bol", name := "Bolia", iso := "bli", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bgo", name := "Bongo", iso := "bot", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "bon", name := "Bongu", iso := "bpu", family := "Trans-New Guinea", genus := "Rai Coast" }
  , { walsCode := "btk", name := "Bontok", iso := "lbk", family := "Austronesian", genus := "Northern Luzon" }
  , { walsCode := "bor", name := "Bora", iso := "boa", family := "Boran", genus := "Boran" }
  , { walsCode := "boj", name := "Bori", iso := "adi", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "brr", name := "Bororo", iso := "bor", family := "Bororoan", genus := "Bororoan" }
  , { walsCode := "boz", name := "Bozo (Tigemaxo)", iso := "boz", family := "Mande", genus := "Western Mande" }
  , { walsCode := "brh", name := "Brahui", iso := "brh", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "bra", name := "Brao", iso := "brb", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "bre", name := "Breton", iso := "bre", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "bri", name := "Bribri", iso := "bzd", family := "Chibchan", genus := "Western Isthmic Chibchan" }
  , { walsCode := "bro", name := "Broken", iso := "tcs", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "bkt", name := "Brokskat", iso := "bkk", family := "Indo-European", genus := "Indic" }
  , { walsCode := "bub", name := "Bubi", iso := "bvb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bdu", name := "Budu", iso := "buu", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bdk", name := "Budukh", iso := "bdk", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "bud", name := "Buduma", iso := "bdm", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "bug", name := "Bugis", iso := "bug", family := "Austronesian", genus := "South Sulawesi" }
  , { walsCode := "bgn", name := "Bugun", iso := "bgg", family := "Sino-Tibetan", genus := "Kho-Bwa" }
  , { walsCode := "bun", name := "Buin", iso := "buo", family := "South Bougainville", genus := "South Bougainville" }
  , { walsCode := "buj", name := "Bujeba", iso := "nmg", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bnu", name := "Bularnu", iso := "", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "bul", name := "Bulgarian", iso := "bul", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "buy", name := "Buli (in Ghana)", iso := "bwu", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "bui", name := "Buli (in Indonesia)", iso := "bzq", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "buw", name := "Bulu", iso := "bum", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bum", name := "Buma", iso := "tkw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ghr", name := "Bunan", iso := "bfu", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "pnu", name := "Bunu (Younuo)", iso := "buh", family := "Hmong-Mien", genus := "Hmongic" }
  , { walsCode := "bnb", name := "Bunuba", iso := "bck", family := "Bunuban", genus := "Bunuban" }
  , { walsCode := "bua", name := "Burarra", iso := "bvr", family := "Mangrida", genus := "Burarran" }
  , { walsCode := "but", name := "Buriat", iso := "bxm", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "brj", name := "Burji", iso := "bji", family := "Afro-Asiatic", genus := "Highland East Cushitic" }
  , { walsCode := "brm", name := "Burmese", iso := "mya", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "buu", name := "Buru", iso := "mhs", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "bmr", name := "Burum", iso := "bmu", family := "Trans-New Guinea", genus := "Huon" }
  , { walsCode := "brn", name := "Burunge", iso := "bds", family := "Afro-Asiatic", genus := "Southern Cushitic" }
  , { walsCode := "bur", name := "Burushaski", iso := "bsk", family := "Burushaski", genus := "Burushaski" }
  , { walsCode := "bus", name := "Busa", iso := "bqp", family := "Mande", genus := "Eastern Mande" }
  , { walsCode := "bsh", name := "Bushoong", iso := "buf", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "dok", name := "Bwele", iso := "ngc", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "bya", name := "Byansi", iso := "bee", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "bet", name := "Bété", iso := "bev", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "cah", name := "Cahuilla", iso := "chl", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "cak", name := "Cakchiquel", iso := "cak", family := "Mayan", genus := "Mayan" }
  , { walsCode := "cml", name := "Camling", iso := "rab", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "cax", name := "Campa (Axininca)", iso := "", family := "Arawakan", genus := "Pre-Andine Arawakan" }
  , { walsCode := "cam", name := "Camsá", iso := "kbh", family := "Camsá", genus := "Camsá" }
  , { walsCode := "cnm", name := "Canamarí", iso := "knm", family := "Katukinan", genus := "Katukinan" }
  , { walsCode := "can", name := "Candoshi", iso := "cbu", family := "Candoshi", genus := "Candoshi" }
  , { walsCode := "cnl", name := "Canela", iso := "ram", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "cnt", name := "Cantonese", iso := "yue", family := "Sino-Tibetan", genus := "Chinese" }
  , { walsCode := "cap", name := "Capanahua", iso := "kaq", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "crp", name := "Carapana", iso := "cbc", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "car", name := "Carib", iso := "car", family := "Cariban", genus := "Cariban" }
  , { walsCode := "cde", name := "Carib (De'kwana)", iso := "mch", family := "Cariban", genus := "Cariban" }
  , { walsCode := "crq", name := "Carrier", iso := "crx", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "cas", name := "Cashibo", iso := "cbr", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "csh", name := "Cashinahua", iso := "cbs", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "ctl", name := "Catalan", iso := "cat", family := "Indo-European", genus := "Romance" }
  , { walsCode := "ctw", name := "Catawba", iso := "chc", family := "Siouan", genus := "Catawban" }
  , { walsCode := "cav", name := "Cavineña", iso := "cav", family := "Pano-Tacanan", genus := "Tacanan" }
  , { walsCode := "cay", name := "Cayapa", iso := "cbi", family := "Barbacoan", genus := "Barbacoan" }
  , { walsCode := "cyv", name := "Cayuvava", iso := "cyb", family := "Cayuvava", genus := "Cayuvava" }
  , { walsCode := "ceb", name := "Cebuano", iso := "ceb", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "cga", name := "Chaga", iso := "old", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "chh", name := "Chaha", iso := "sgw", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "cai", name := "Chai", iso := "suq", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "cld", name := "Chaldean (Modern)", iso := "cld", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "cme", name := "Cham (Eastern)", iso := "cjm", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "chw", name := "Cham (Western)", iso := "cja", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "chb", name := "Chambri", iso := "can", family := "Ramu-Lower Sepik", genus := "Lower Sepik" }
  , { walsCode := "cha", name := "Chamorro", iso := "cha", family := "Austronesian", genus := "Chamorro" }
  , { walsCode := "chg", name := "Chang", iso := "nbc", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "chn", name := "Chantyal", iso := "chx", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "cco", name := "Chasta Costa", iso := "tuu", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "cso", name := "Chatino (Sierra Occidental)", iso := "ctp", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "cya", name := "Chatino (Yaitepec)", iso := "ctp", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "chd", name := "Chaudangsi", iso := "cdn", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "cvc", name := "Chavacano", iso := "cbk", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "chc", name := "Chechen", iso := "che", family := "Nakh-Daghestanian", genus := "Nakh" }
  , { walsCode := "chl", name := "Chehalis (Upper)", iso := "cjh", family := "Salishan", genus := "Tsamosan" }
  , { walsCode := "cmk", name := "Chemakum", iso := "xch", family := "Chimakuan", genus := "Chimakuan" }
  , { walsCode := "cmh", name := "Chemehuevi", iso := "ute", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "cpn", name := "Chepang", iso := "cdm", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "che", name := "Cherokee", iso := "chr", family := "Iroquoian", genus := "Southern Iroquoian" }
  , { walsCode := "cyn", name := "Cheyenne", iso := "chy", family := "Algic", genus := "Algonquian" }
  , { walsCode := "cic", name := "Chichewa", iso := "nya", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "cjo", name := "Chichimeca-Jonaz", iso := "pei", family := "Oto-Manguean", genus := "Chichimec" }
  , { walsCode := "cck", name := "Chickasaw", iso := "cic", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "chi", name := "Chimariko", iso := "cid", family := "Hokan", genus := "Chimariko" }
  , { walsCode := "cmr", name := "Chin (Mara)", iso := "mrh", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "chs", name := "Chin (Siyin)", iso := "csy", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "cti", name := "Chin (Tiddim)", iso := "ctd", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "ccm", name := "Chinantec (Comaltepec)", iso := "cco", family := "Oto-Manguean", genus := "Chinantecan" }
  , { walsCode := "cle", name := "Chinantec (Lealao)", iso := "cle", family := "Oto-Manguean", genus := "Chinantecan" }
  , { walsCode := "cpl", name := "Chinantec (Palantla)", iso := "cpa", family := "Oto-Manguean", genus := "Chinantecan" }
  , { walsCode := "chq", name := "Chinantec (Quiotepec)", iso := "chq", family := "Oto-Manguean", genus := "Chinantecan" }
  , { walsCode := "ckl", name := "Chinook (Lower)", iso := "chh", family := "Penutian", genus := "Chinookan" }
  , { walsCode := "cku", name := "Chinook (Upper)", iso := "wac", family := "Penutian", genus := "Chinookan" }
  , { walsCode := "cpy", name := "Chipaya", iso := "cap", family := "Uru-Chipaya", genus := "Uru-Chipaya" }
  , { walsCode := "chp", name := "Chipewyan", iso := "chp", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "cqt", name := "Chiquitano", iso := "cax", family := "Chiquitano", genus := "Chiquitano" }
  , { walsCode := "ctm", name := "Chitimacha", iso := "ctm", family := "Chitimacha", genus := "Chitimacha" }
  , { walsCode := "cch", name := "Chocho", iso := "coz", family := "Oto-Manguean", genus := "Popolocan" }
  , { walsCode := "cct", name := "Choctaw", iso := "cho", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "col", name := "Chol", iso := "ctu", family := "Mayan", genus := "Mayan" }
  , { walsCode := "cln", name := "Cholón", iso := "cht", family := "Hobitu-Cholon", genus := "Hobitu-Cholon" }
  , { walsCode := "cho", name := "Chontal (Highland)", iso := "chd", family := "Hokan", genus := "Tequistlatecan" }
  , { walsCode := "chx", name := "Chontal (Huamelultec Oaxaca)", iso := "clo", family := "Hokan", genus := "Tequistlatecan" }
  , { walsCode := "cmy", name := "Chontal Maya", iso := "chf", family := "Mayan", genus := "Mayan" }
  , { walsCode := "crt", name := "Chorote", iso := "", family := "Matacoan", genus := "Matacoan" }
  , { walsCode := "chr", name := "Chrau", iso := "crw", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "chj", name := "Chuj", iso := "cac", family := "Mayan", genus := "Mayan" }
  , { walsCode := "chk", name := "Chukchi", iso := "ckt", family := "Chukotko-Kamchatkan", genus := "Northern Chukotko-Kamchatkan" }
  , { walsCode := "cba", name := "Chumash (Barbareño)", iso := "boi", family := "Chumash", genus := "Chumash" }
  , { walsCode := "cin", name := "Chumash (Ineseño)", iso := "inz", family := "Chumash", genus := "Chumash" }
  , { walsCode := "cuu", name := "Chuukese", iso := "chk", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "chv", name := "Chuvash", iso := "chv", family := "Altaic", genus := "Turkic" }
  , { walsCode := "cbo", name := "Chácobo", iso := "cao", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "cil", name := "CiLuba", iso := "lua", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "cla", name := "Clallam", iso := "clm", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "coa", name := "Coahuilteco", iso := "xcw", family := "Coahuiltecan", genus := "Coahuiltecan" }
  , { walsCode := "coc", name := "Cocama", iso := "cod", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "ccp", name := "Cocopa", iso := "coc", family := "Hokan", genus := "Yuman" }
  , { walsCode := "coe", name := "Coeur d'Alene", iso := "crd", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "cwe", name := "Columbia-Wenatchi", iso := "col", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "cmn", name := "Comanche", iso := "com", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "cmx", name := "Comox", iso := "coo", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "coo", name := "Coos (Hanis)", iso := "csz", family := "Oregon Coast", genus := "Coosan" }
  , { walsCode := "cop", name := "Coptic", iso := "cop", family := "Afro-Asiatic", genus := "Egyptian-Coptic" }
  , { walsCode := "cor", name := "Cora", iso := "crn", family := "Uto-Aztecan", genus := "Corachol" }
  , { walsCode := "crn", name := "Cornish", iso := "cor", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "cre", name := "Cree (Plains)", iso := "crk", family := "Algic", genus := "Algonquian" }
  , { walsCode := "cea", name := "Cree (Swampy)", iso := "csw", family := "Algic", genus := "Algonquian" }
  , { walsCode := "cri", name := "Crimean Tatar", iso := "crh", family := "Altaic", genus := "Turkic" }
  , { walsCode := "cro", name := "Crow", iso := "cro", family := "Siouan", genus := "Missouri River Siouan" }
  , { walsCode := "cua", name := "Cua", iso := "cua", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "cub", name := "Cubeo", iso := "cub", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "cui", name := "Cuiba", iso := "cui", family := "Guahiban", genus := "Guahiban" }
  , { walsCode := "cuc", name := "Cuica", iso := "", family := "Timote-Cuica", genus := "Timote-Cuica" }
  , { walsCode := "cup", name := "Cupeño", iso := "cup", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "cze", name := "Czech", iso := "ces", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "cem", name := "Cèmuhî", iso := "cam", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "dab", name := "Daba", iso := "dbq", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "ddj", name := "Dadjriwalé", iso := "god", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "dag", name := "Daga", iso := "dgz", family := "Trans-New Guinea", genus := "Dagan" }
  , { walsCode := "dga", name := "Dagaare", iso := "dga", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "dgb", name := "Dagbani", iso := "dag", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "dgr", name := "Dagur", iso := "dta", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "dah", name := "Dahalo", iso := "dal", family := "Afro-Asiatic", genus := "Dahalo" }
  , { walsCode := "dam", name := "Damana", iso := "mbp", family := "Chibchan", genus := "Arhuacic" }
  , { walsCode := "dan", name := "Dan", iso := "dnj", family := "Mande", genus := "Eastern Mande" }
  , { walsCode := "dni", name := "Dani (Lower Grand Valley)", iso := "dni", family := "Trans-New Guinea", genus := "Dani" }
  , { walsCode := "dsh", name := "Danish", iso := "dan", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "drg", name := "Dargwa", iso := "dar", family := "Nakh-Daghestanian", genus := "Dargwic" }
  , { walsCode := "dri", name := "Dari", iso := "prs", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "drm", name := "Darma", iso := "drd", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "day", name := "Day", iso := "dai", family := "Niger-Congo", genus := "Day" }
  , { walsCode := "def", name := "Defaka", iso := "afn", family := "Ijoid", genus := "Ijoid" }
  , { walsCode := "deg", name := "Degema", iso := "deg", family := "Niger-Congo", genus := "Edoid" }
  , { walsCode := "den", name := "Dení", iso := "dny", family := "Arauan", genus := "Arauan" }
  , { walsCode := "des", name := "Desano", iso := "des", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "deu", name := "Deuri", iso := "der", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "dha", name := "Dhaasanac", iso := "dsh", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "dhw", name := "Dharawal", iso := "tbh", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "dhr", name := "Dhargari", iso := "dhr", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "dhb", name := "Dharumbal", iso := "xgm", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "dhm", name := "Dhimal", iso := "dhi", family := "Sino-Tibetan", genus := "Dhimalic" }
  , { walsCode := "dhi", name := "Dhivehi", iso := "div", family := "Indo-European", genus := "Indic" }
  , { walsCode := "did", name := "Didinga", iso := "did", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "die", name := "Diegueño (Mesa Grande)", iso := "dih", family := "Hokan", genus := "Yuman" }
  , { walsCode := "dig", name := "Digaro", iso := "mhu", family := "Sino-Tibetan", genus := "Digaroan" }
  , { walsCode := "ygd", name := "Dii", iso := "dur", family := "Niger-Congo", genus := "Samba-Duru" }
  , { walsCode := "dms", name := "Dimasa", iso := "dis", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "dim", name := "Dime", iso := "dim", family := "Afro-Asiatic", genus := "South Omotic" }
  , { walsCode := "dng", name := "Ding", iso := "diz", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "din", name := "Dinka", iso := "din", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "dio", name := "Diola-Fogny", iso := "dyo", family := "Niger-Congo", genus := "Jola" }
  , { walsCode := "diy", name := "Diyari", iso := "dif", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "diz", name := "Dizi", iso := "mdx", family := "Afro-Asiatic", genus := "Dizoid" }
  , { walsCode := "dja", name := "Djabugay", iso := "dyy", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "djm", name := "Djambarrpuyngu", iso := "djr", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "djp", name := "Djapu", iso := "dwu", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "djr", name := "Djaru", iso := "ddj", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "djn", name := "Djinang", iso := "dji", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "dji", name := "Djingili", iso := "jig", family := "Mirndi", genus := "Djingili" }
  , { walsCode := "dlm", name := "Dla (Menggwa)", iso := "kbv", family := "Senagi", genus := "Senagi" }
  , { walsCode := "der", name := "Dla (Proper)", iso := "kbv", family := "Senagi", genus := "Senagi" }
  , { walsCode := "dmk", name := "Domaaki", iso := "dmk", family := "Indo-European", genus := "Indic" }
  , { walsCode := "dom", name := "Domari", iso := "rmt", family := "Indo-European", genus := "Indic" }
  , { walsCode := "don", name := "Dong (Southern)", iso := "kmc", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "dgo", name := "Dongo", iso := "doo", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "dds", name := "Donno So", iso := "dds", family := "Dogon", genus := "Dogon" }
  , { walsCode := "doy", name := "Doyayo", iso := "dow", family := "Niger-Congo", genus := "Samba-Duru" }
  , { walsCode := "dre", name := "Drehu", iso := "dhv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "dua", name := "Duala", iso := "dua", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "duk", name := "Duka", iso := "dud", family := "Niger-Congo", genus := "Central Kainji" }
  , { walsCode := "dug", name := "Dullay (Gollango)", iso := "gwd", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "dul", name := "Dulong", iso := "duu", family := "Sino-Tibetan", genus := "Nungish" }
  , { walsCode := "dma", name := "Duma", iso := "dma", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "dmi", name := "Dumi", iso := "dus", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "dum", name := "Dumo", iso := "vam", family := "Skou", genus := "Western Skou" }
  , { walsCode := "dun", name := "Duna", iso := "duc", family := "Duna-Bogaya", genus := "Duna" }
  , { walsCode := "dut", name := "Dutch", iso := "nld", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "dyi", name := "Dyirbal", iso := "dbl", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "daw", name := "Dâw", iso := "kwa", family := "Nadahup", genus := "Nadahup" }
  , { walsCode := "ebi", name := "Ebira", iso := "igb", family := "Niger-Congo", genus := "Nupoid" }
  , { walsCode := "edo", name := "Edolo", iso := "etr", family := "Trans-New Guinea", genus := "Bosavi" }
  , { walsCode := "erk", name := "Efate (South)", iso := "erk", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "efi", name := "Efik", iso := "efi", family := "Niger-Congo", genus := "Lower Cross" }
  , { walsCode := "ega", name := "Ega", iso := "ega", family := "Niger-Congo", genus := "Ega" }
  , { walsCode := "eip", name := "Eipo", iso := "eip", family := "Trans-New Guinea", genus := "Mek" }
  , { walsCode := "eka", name := "Ekari", iso := "ekg", family := "Trans-New Guinea", genus := "Paniai Lakes" }
  , { walsCode := "eko", name := "Ekoti", iso := "eko", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "els", name := "Elseng", iso := "mrf", family := "Morwap", genus := "Morwap" }
  , { walsCode := "ora", name := "Emai", iso := "ema", family := "Niger-Congo", genus := "Edoid" }
  , { walsCode := "eml", name := "Embaloh", iso := "emb", family := "Austronesian", genus := "South Sulawesi" }
  , { walsCode := "emb", name := "Emberá (Northern)", iso := "emp", family := "Choco", genus := "Choco" }
  , { walsCode := "emm", name := "Emmi", iso := "amy", family := "Western Daly", genus := "Wagaydy" }
  , { walsCode := "ene", name := "Enets", iso := "", family := "Uralic", genus := "Samoyedic" }
  , { walsCode := "egn", name := "Engenni", iso := "enn", family := "Niger-Congo", genus := "Edoid" }
  , { walsCode := "eno", name := "Enggano", iso := "eno", family := "Austronesian", genus := "Enggano" }
  , { walsCode := "eng", name := "English", iso := "eng", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "eny", name := "Enya", iso := "gey", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "epe", name := "Epena Pedee", iso := "sja", family := "Choco", genus := "Choco" }
  , { walsCode := "err", name := "Erromangan", iso := "erg", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ese", name := "Ese Ejja", iso := "ese", family := "Pano-Tacanan", genus := "Tacanan" }
  , { walsCode := "esm", name := "Esmeraldeño", iso := "", family := "Tacame", genus := "Tacame" }
  , { walsCode := "ess", name := "Esselen", iso := "esq", family := "Esselen", genus := "Esselen" }
  , { walsCode := "est", name := "Estonian", iso := "ekk", family := "Uralic", genus := "Finnic" }
  , { walsCode := "eud", name := "Eudeve", iso := "", family := "Uto-Aztecan", genus := "Opata-Eudeve" }
  , { walsCode := "evn", name := "Even", iso := "eve", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "eve", name := "Evenki", iso := "evn", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "ewe", name := "Ewe", iso := "ewe", family := "Niger-Congo", genus := "Gbe" }
  , { walsCode := "ewa", name := "Ewe (Anlo)", iso := "ewe", family := "Niger-Congo", genus := "Gbe" }
  , { walsCode := "ewo", name := "Ewondo", iso := "ewo", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "far", name := "Faroese", iso := "fao", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "fas", name := "Fasu", iso := "faa", family := "Trans-New Guinea", genus := "Fasu" }
  , { walsCode := "fij", name := "Fijian", iso := "fij", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "fin", name := "Finnish", iso := "fin", family := "Uralic", genus := "Finnic" }
  , { walsCode := "foe", name := "Foe", iso := "foi", family := "Trans-New Guinea", genus := "Foe" }
  , { walsCode := "pdp", name := "Folopa", iso := "ppo", family := "Teberan-Pawaian", genus := "Teberan" }
  , { walsCode := "fon", name := "Fongbe", iso := "fon", family := "Niger-Congo", genus := "Gbe" }
  , { walsCode := "frd", name := "Fordata", iso := "frd", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "for", name := "Fore", iso := "for", family := "Trans-New Guinea", genus := "Fore-Gimi" }
  , { walsCode := "fox", name := "Fox", iso := "sac", family := "Algic", genus := "Algonquian" }
  , { walsCode := "fre", name := "French", iso := "fra", family := "Indo-European", genus := "Romance" }
  , { walsCode := "fri", name := "Frisian", iso := "fry", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "frw", name := "Frisian (Western)", iso := "fry", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "fgu", name := "Fula (Guinean)", iso := "fuf", family := "Niger-Congo", genus := "Peul-Serer" }
  , { walsCode := "fus", name := "Fula (Senegal)", iso := "fuc", family := "Niger-Congo", genus := "Peul-Serer" }
  , { walsCode := "fua", name := "Fulfulde (Adamawa)", iso := "fub", family := "Niger-Congo", genus := "Peul-Serer" }
  , { walsCode := "fni", name := "Fulfulde (Nigerian)", iso := "fuv", family := "Niger-Congo", genus := "Peul-Serer" }
  , { walsCode := "ful", name := "Fulniô", iso := "fun", family := "Fulniô", genus := "Fulniô" }
  , { walsCode := "fur", name := "Fur", iso := "fvr", family := "Fur", genus := "Fur" }
  ]

private def languages_1 : List Language :=
  [ { walsCode := "fue", name := "Futuna (East)", iso := "fud", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "fut", name := "Futuna-Aniwa", iso := "fut", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "fye", name := "Fyem", iso := "pym", family := "Niger-Congo", genus := "Benue-Congo Plateau" }
  , { walsCode := "gnd", name := "Ga'anda", iso := "gqa", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "gaa", name := "Gaagudju", iso := "gbu", family := "Gaagudju", genus := "Gaagudju" }
  , { walsCode := "gdk", name := "Gadaba (Kondekor)", iso := "gdb", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "gds", name := "Gadsup", iso := "gaj", family := "Trans-New Guinea", genus := "Gauwa" }
  , { walsCode := "gae", name := "Gaelic (Scots)", iso := "gla", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "gag", name := "Gagauz", iso := "gag", family := "Altaic", genus := "Turkic" }
  , { walsCode := "gah", name := "Gahuku", iso := "gah", family := "Trans-New Guinea", genus := "Gahuku" }
  , { walsCode := "gll", name := "Galela", iso := "gbi", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "gal", name := "Galo", iso := "adl", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "gam", name := "Gamo", iso := "gmv", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "gap", name := "Gapapaiwa", iso := "pwg", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "gar", name := "Garo", iso := "grt", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "grr", name := "Garrwa", iso := "wrk", family := "Garrwan", genus := "Garrwan" }
  , { walsCode := "grs", name := "Garus", iso := "gyb", family := "Trans-New Guinea", genus := "Mabuso" }
  , { walsCode := "grf", name := "Garífuna", iso := "cab", family := "Arawakan", genus := "Antillean Arawakan" }
  , { walsCode := "gav", name := "Gavião", iso := "gvo", family := "Tupian", genus := "Monde" }
  , { walsCode := "gbs", name := "Gbaya (Southwest)", iso := "gso", family := "Niger-Congo", genus := "Gbaya-Manza-Ngbaka" }
  , { walsCode := "gbb", name := "Gbeya Bossangoa", iso := "gbp", family := "Niger-Congo", genus := "Gbaya-Manza-Ngbaka" }
  , { walsCode := "gel", name := "Gela", iso := "nlg", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "gla", name := "Gelao", iso := "gqu", family := "Tai-Kadai", genus := "Kadai" }
  , { walsCode := "geo", name := "Georgian", iso := "kat", family := "Kartvelian", genus := "Kartvelian" }
  , { walsCode := "ger", name := "German", iso := "deu", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "nbh", name := "Ghulfan", iso := "ghl", family := "Eastern Sudanic", genus := "Nubian" }
  , { walsCode := "gid", name := "Gidabal", iso := "gih", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "gdr", name := "Gidar", iso := "gid", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "gil", name := "Gilaki", iso := "glk", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "gim", name := "Gimira", iso := "bcq", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "git", name := "Gitksan", iso := "git", family := "Tsimshianic", genus := "Tsimshianic" }
  , { walsCode := "giz", name := "Giziga", iso := "gis", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "goa", name := "Goajiro", iso := "guc", family := "Arawakan", genus := "Guajiro-Paraujano" }
  , { walsCode := "gdi", name := "Godié", iso := "god", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "god", name := "Godoberi", iso := "gdo", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "goe", name := "Goemai", iso := "ank", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "gog", name := "Gogodala", iso := "ggw", family := "Trans-New Guinea", genus := "Gogodala" }
  , { walsCode := "goj", name := "Gojri", iso := "gju", family := "Indo-European", genus := "Indic" }
  , { walsCode := "gok", name := "Gokana", iso := "gkn", family := "Niger-Congo", genus := "Ogonoid" }
  , { walsCode := "gol", name := "Gola", iso := "gol", family := "Niger-Congo", genus := "Gola" }
  , { walsCode := "gln", name := "Golin", iso := "gvf", family := "Trans-New Guinea", genus := "Chimbu-Wahgi" }
  , { walsCode := "gon", name := "Gondi", iso := "gno", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "goo", name := "Gooniyandi", iso := "gni", family := "Bunuban", genus := "Bunuban" }
  , { walsCode := "gan", name := "Great Andamanese", iso := "apq", family := "Great Andamanese", genus := "Great Andamanese" }
  , { walsCode := "grb", name := "Grebo", iso := "grj", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "grk", name := "Greek (Modern)", iso := "ell", family := "Indo-European", genus := "Greek" }
  , { walsCode := "gso", name := "Greenlandic (South)", iso := "kal", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "grw", name := "Greenlandic (West)", iso := "kal", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "ghb", name := "Guahibo", iso := "guh", family := "Guahiban", genus := "Guahiban" }
  , { walsCode := "gjj", name := "Guajajara", iso := "gub", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "gno", name := "Guanano", iso := "gvc", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "gua", name := "Guaraní", iso := "gug", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "grj", name := "Guarijío", iso := "var", family := "Uto-Aztecan", genus := "Tarahumaran" }
  , { walsCode := "gto", name := "Guató", iso := "gta", family := "Guató", genus := "Guató" }
  , { walsCode := "gud", name := "Gude", iso := "gde", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "gug", name := "Gugada", iso := "ktd", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "guh", name := "Guhu-Samane", iso := "ghs", family := "Trans-New Guinea", genus := "Guhu-Samane" }
  , { walsCode := "guj", name := "Gujarati", iso := "guj", family := "Indo-European", genus := "Indic" }
  , { walsCode := "gul", name := "Gula (in Central African Republic)", iso := "kcm", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "gir", name := "Gula Iro", iso := "glj", family := "Niger-Congo", genus := "Bua" }
  , { walsCode := "gmt", name := "Gumatj", iso := "gnn", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "gmw", name := "Gumawana", iso := "gvs", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "gum", name := "Gumbaynggir", iso := "kgs", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "gmz", name := "Gumuz", iso := "guk", family := "Gumuz", genus := "Gumuz" }
  , { walsCode := "gnb", name := "Gunbalang", iso := "wlg", family := "Gunwinyguan", genus := "Marne" }
  , { walsCode := "guw", name := "Gungbe", iso := "guw", family := "Niger-Congo", genus := "Gbe" }
  , { walsCode := "gnn", name := "Gunin", iso := "gww", family := "Worrorran", genus := "Worrorran" }
  , { walsCode := "gny", name := "Gunya", iso := "gyy", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "ggu", name := "Gureng Gureng", iso := "gnr", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "grn", name := "Gurenne", iso := "gur", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "grg", name := "Gurr-goni", iso := "gge", family := "Mangrida", genus := "Burarran" }
  , { walsCode := "gur", name := "Gurung", iso := "", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "gus", name := "Gusii", iso := "guz", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "gdb", name := "Gutob", iso := "gbj", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "guu", name := "Guugu Yimidhirr", iso := "kky", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "gwa", name := "Gwari", iso := "gbr", family := "Niger-Congo", genus := "Nupoid" }
  , { walsCode := "gwo", name := "Gworok", iso := "kcg", family := "Niger-Congo", genus := "Benue-Congo Plateau" }
  , { walsCode := "gyc", name := "Gyarong (Cogtse)", iso := "jya", family := "Sino-Tibetan", genus := "Na-Qiangic" }
  , { walsCode := "ga", name := "Gã", iso := "gaa", family := "Niger-Congo", genus := "Ga-Dangme" }
  , { walsCode := "gku", name := "Gününa Küne", iso := "pue", family := "Chonan", genus := "Puelche" }
  , { walsCode := "hai", name := "Haida", iso := "hai", family := "Haida", genus := "Haida" }
  , { walsCode := "hcr", name := "Haitian Creole", iso := "hat", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "hak", name := "Hakka", iso := "hak", family := "Sino-Tibetan", genus := "Chinese" }
  , { walsCode := "hal", name := "Halia", iso := "hla", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "hli", name := "Halkomelem (Island)", iso := "hur", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "hlu", name := "Halkomelem (Upriver)", iso := "hur", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "hmr", name := "Hamer", iso := "amf", family := "Afro-Asiatic", genus := "South Omotic" }
  , { walsCode := "ham", name := "Hamtai", iso := "hmt", family := "Trans-New Guinea", genus := "Nuclear Angan" }
  , { walsCode := "hhu", name := "Hanga Hundi", iso := "wos", family := "Sepik", genus := "Ndu" }
  , { walsCode := "han", name := "Hani", iso := "hni", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "hrr", name := "Harari", iso := "har", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "har", name := "Haruai", iso := "tmd", family := "Piawi", genus := "Piawi" }
  , { walsCode := "hat", name := "Hatam", iso := "had", family := "Hatim-Mansim", genus := "Hatim-Mansim" }
  , { walsCode := "hau", name := "Hausa", iso := "hau", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "haw", name := "Hawaiian", iso := "haw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "hwc", name := "Hawaiian Creole", iso := "hwc", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "hwr", name := "Hawrami", iso := "hac", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "hya", name := "Haya", iso := "hay", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "hay", name := "Hayu", iso := "vay", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "hdi", name := "Hdi", iso := "xed", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "heb", name := "Hebrew (Modern)", iso := "heb", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "heh", name := "Hehe", iso := "heh", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "hei", name := "Heiltsuk", iso := "hei", family := "Wakashan", genus := "Northern Wakashan" }
  , { walsCode := "hem", name := "Hemba", iso := "hem", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "hid", name := "Hidatsa", iso := "hid", family := "Siouan", genus := "Missouri River Siouan" }
  , { walsCode := "hil", name := "Hiligaynon", iso := "hil", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "hin", name := "Hindi", iso := "hin", family := "Indo-European", genus := "Indic" }
  , { walsCode := "hix", name := "Hixkaryana", iso := "hix", family := "Cariban", genus := "Cariban" }
  , { walsCode := "lic", name := "Hlai (Baoding)", iso := "lic", family := "Tai-Kadai", genus := "Hlai" }
  , { walsCode := "hma", name := "Hmar", iso := "hmr", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "hmo", name := "Hmong Njua", iso := "hnj", family := "Hmong-Mien", genus := "Hmongic" }
  , { walsCode := "ho", name := "Ho", iso := "hoc", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "hoa", name := "Hoava", iso := "hoa", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "hol", name := "Holoholo", iso := "hoo", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "hop", name := "Hopi", iso := "hop", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "hua", name := "Hua", iso := "ygr", family := "Trans-New Guinea", genus := "Siane-Yagaria" }
  , { walsCode := "hlp", name := "Hualapai", iso := "yuf", family := "Hokan", genus := "Yuman" }
  , { walsCode := "htc", name := "Huastec", iso := "hus", family := "Mayan", genus := "Mayan" }
  , { walsCode := "hve", name := "Huave (San Mateo del Mar)", iso := "huv", family := "Huavean", genus := "Huavean" }
  , { walsCode := "hui", name := "Huichol", iso := "hch", family := "Uto-Aztecan", genus := "Corachol" }
  , { walsCode := "hmi", name := "Huitoto (Minica)", iso := "hto", family := "Witotoan", genus := "Witoto" }
  , { walsCode := "hmu", name := "Huitoto (Muinane)", iso := "hux", family := "Witotoan", genus := "Witoto" }
  , { walsCode := "hum", name := "Huitoto (Murui)", iso := "huu", family := "Witotoan", genus := "Witoto" }
  , { walsCode := "hnd", name := "Hunde", iso := "hke", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "hun", name := "Hungarian", iso := "hun", family := "Uralic", genus := "Ugric" }
  , { walsCode := "hzb", name := "Hunzib", iso := "huz", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "hpd", name := "Hup", iso := "jup", family := "Nadahup", genus := "Nadahup" }
  , { walsCode := "hup", name := "Hupa", iso := "hup", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "isa", name := "I'saka", iso := "ksi", family := "Skou", genus := "Krisa" }
  , { walsCode := "iaa", name := "Iaai", iso := "iai", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "iat", name := "Iatmul", iso := "ian", family := "Sepik", genus := "Ndu" }
  , { walsCode := "iau", name := "Iau", iso := "tmu", family := "Lakes Plain", genus := "Central Tariku" }
  , { walsCode := "iba", name := "Iban", iso := "iba", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "ice", name := "Icelandic", iso := "isl", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "ido", name := "Idoma", iso := "idu", family := "Niger-Congo", genus := "Idomoid" }
  , { walsCode := "idu", name := "Idu", iso := "clk", family := "Sino-Tibetan", genus := "Digaroan" }
  , { walsCode := "idn", name := "Iduna", iso := "viv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mxe", name := "Ifira-Mele", iso := "mxe", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ifu", name := "Ifugao (Batad)", iso := "ifb", family := "Austronesian", genus := "Northern Luzon" }
  , { walsCode := "ifm", name := "Ifumu", iso := "ifm", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "igb", name := "Igbo", iso := "ibo", family := "Niger-Congo", genus := "Igboid" }
  , { walsCode := "ige", name := "Igede", iso := "ige", family := "Niger-Congo", genus := "Idomoid" }
  , { walsCode := "ign", name := "Ignaciano", iso := "ign", family := "Arawakan", genus := "Bolivia-Parana" }
  , { walsCode := "iha", name := "Iha", iso := "ihp", family := "Greater West Bomberai", genus := "West Bomberai" }
  , { walsCode := "ijo", name := "Ijo (Kolokuma)", iso := "ijc", family := "Ijoid", genus := "Ijoid" }
  , { walsCode := "ik", name := "Ik", iso := "ikx", family := "Eastern Sudanic", genus := "Kuliak" }
  , { walsCode := "ika", name := "Ika", iso := "arh", family := "Chibchan", genus := "Arhuacic" }
  , { walsCode := "ila", name := "Ila", iso := "ilb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ilo", name := "Ilocano", iso := "ilo", family := "Austronesian", genus := "Northern Luzon" }
  , { walsCode := "imo", name := "Imonda", iso := "imn", family := "Border", genus := "Border" }
  , { walsCode := "ina", name := "Inanwatan", iso := "szp", family := "South Bird's Head", genus := "Inanwatan" }
  , { walsCode := "ind", name := "Indonesian", iso := "ind", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "igs", name := "Ingessana", iso := "tbi", family := "Eastern Sudanic", genus := "Eastern Jebel" }
  , { walsCode := "ing", name := "Ingush", iso := "inh", family := "Nakh-Daghestanian", genus := "Nakh" }
  , { walsCode := "inn", name := "Innamincka", iso := "ynd", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "ins", name := "Inuktitut (Salluit)", iso := "ike", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "iqu", name := "Iquito", iso := "iqu", family := "Zaparoan", genus := "Zaparoan" }
  , { walsCode := "irx", name := "Iranxe", iso := "irn", family := "Iranxe", genus := "Iranxe" }
  , { walsCode := "irq", name := "Iraqw", iso := "irk", family := "Afro-Asiatic", genus := "Southern Cushitic" }
  , { walsCode := "irr", name := "Irarutu", iso := "irh", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "iri", name := "Irish", iso := "gle", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "ise", name := "Isekiri", iso := "its", family := "Niger-Congo", genus := "Defoid" }
  , { walsCode := "isi", name := "Isirawa", iso := "srl", family := "Tor-Kwerba", genus := "Isirawa" }
  , { walsCode := "ita", name := "Italian", iso := "ita", family := "Indo-European", genus := "Romance" }
  , { walsCode := "ite", name := "Itelmen", iso := "itl", family := "Chukotko-Kamchatkan", genus := "Southern Chukotko-Kamchatkan" }
  , { walsCode := "ito", name := "Itonama", iso := "ito", family := "Itonama", genus := "Itonama" }
  , { walsCode := "itz", name := "Itzaj", iso := "itz", family := "Mayan", genus := "Mayan" }
  , { walsCode := "iwa", name := "Iwaidja", iso := "ibd", family := "Iwaidjan", genus := "Iwaidjan" }
  , { walsCode := "iwm", name := "Iwam", iso := "iwm", family := "Sepik", genus := "Iwamic" }
  , { walsCode := "kwy", name := "Iwoyo", iso := "yom", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ixi", name := "Ixil", iso := "ixl", family := "Mayan", genus := "Mayan" }
  , { walsCode := "jar", name := "Izere", iso := "izr", family := "Niger-Congo", genus := "Benue-Congo Plateau" }
  , { walsCode := "izi", name := "Izi", iso := "izz", family := "Niger-Congo", genus := "Igboid" }
  , { walsCode := "jbt", name := "Jabutí", iso := "jbt", family := "Macro-Ge", genus := "Jabutí" }
  , { walsCode := "jab", name := "Jabêm", iso := "jae", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "jad", name := "Jad", iso := "jda", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "jak", name := "Jakaltek", iso := "jac", family := "Mayan", genus := "Mayan" }
  , { walsCode := "jmm", name := "Jamamadi", iso := "jaa", family := "Arauan", genus := "Arauan" }
  , { walsCode := "jam", name := "Jaminjung", iso := "djd", family := "Mirndi", genus := "Jaminjungan" }
  , { walsCode := "jms", name := "Jamsay", iso := "djm", family := "Dogon", genus := "Dogon" }
  , { walsCode := "jpn", name := "Japanese", iso := "jpn", family := "Japanese", genus := "Japanese" }
  , { walsCode := "jaq", name := "Jaqaru", iso := "jqr", family := "Aymaran", genus := "Aymaran" }
  , { walsCode := "jrw", name := "Jarawa (in Andamans)", iso := "anq", family := "South Andamanese", genus := "South Andamanese" }
  , { walsCode := "jwr", name := "Jarawara", iso := "jaa", family := "Arauan", genus := "Arauan" }
  , { walsCode := "jav", name := "Javanese", iso := "jav", family := "Austronesian", genus := "Javanese" }
  , { walsCode := "jeb", name := "Jebero", iso := "jeb", family := "Cahuapanan", genus := "Cahuapanan" }
  , { walsCode := "jel", name := "Jeli", iso := "jek", family := "Mande", genus := "Western Mande" }
  , { walsCode := "jem", name := "Jemez", iso := "tow", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "jng", name := "Jingpho", iso := "kac", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "jin", name := "Jino", iso := "jiu", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "jiv", name := "Jivaro", iso := "jiv", family := "Jivaroan", genus := "Jivaroan" }
  , { walsCode := "joh", name := "Johari", iso := "rgk", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "jun", name := "Juang", iso := "jun", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "jug", name := "Jugli", iso := "nst", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "juk", name := "Jukun", iso := "jbu", family := "Niger-Congo", genus := "Jukunoid" }
  , { walsCode := "jmo", name := "Jur Mödö", iso := "bex", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "juh", name := "Ju|'hoan", iso := "ktz", family := "Kxa", genus := "Ju-Kung" }
  , { walsCode := "kab", name := "Kabardian", iso := "kbd", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "kbt", name := "Kabatei", iso := "xkp", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "kby", name := "Kabiyé", iso := "kbp", family := "Niger-Congo", genus := "Grusi" }
  , { walsCode := "kbl", name := "Kabyle", iso := "kab", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "kac", name := "Kachari", iso := "xac", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "kdz", name := "Kadazan", iso := "kzj", family := "Austronesian", genus := "North Borneo" }
  , { walsCode := "kdw", name := "Kadiwéu", iso := "kbc", family := "Guaicuruan", genus := "Kadiwéu" }
  , { walsCode := "kad", name := "Kadugli", iso := "xtc", family := "Kadu", genus := "Kadugli" }
  , { walsCode := "kgr", name := "Kagulu", iso := "kki", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kai", name := "Kaian", iso := "kct", family := "Ramu-Lower Sepik", genus := "Lower Ramu" }
  , { walsCode := "kng", name := "Kaingang", iso := "kgp", family := "Macro-Ge", genus := "Je Meridional" }
  , { walsCode := "krr", name := "Kairiru", iso := "kxa", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kae", name := "Kaki Ae", iso := "tbd", family := "Tate", genus := "Tate" }
  , { walsCode := "kly", name := "Kala Lagaw Ya", iso := "mwp", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "klq", name := "Kalam", iso := "kmh", family := "Trans-New Guinea", genus := "Kalam-Kobon" }
  , { walsCode := "klh", name := "Kalasha", iso := "kls", family := "Indo-European", genus := "Indic" }
  , { walsCode := "kls", name := "Kalispel", iso := "fla", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "kgu", name := "Kalkatungu", iso := "ktg", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kmk", name := "Kalmyk", iso := "xal", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "kll", name := "Kaluli", iso := "bco", family := "Trans-New Guinea", genus := "Bosavi" }
  , { walsCode := "kma", name := "Kamaiurá", iso := "kay", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "kmz", name := "Kamasau", iso := "kms", family := "Torricelli", genus := "Marienberg" }
  , { walsCode := "kms", name := "Kamass", iso := "xas", family := "Uralic", genus := "Samoyedic" }
  , { walsCode := "kba", name := "Kamba", iso := "kam", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kam", name := "Kambera", iso := "xbr", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "kbo", name := "Kambot", iso := "kbx", family := "Keram", genus := "Ap Ma" }
  , { walsCode := "kmi", name := "Kami", iso := "kcu", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kmr", name := "Kamoro", iso := "kgq", family := "Asmat-Kamrau Bay", genus := "Asmat-Kamrau Bay" }
  , { walsCode := "kmw", name := "Kamu", iso := "xmu", family := "Eastern Daly", genus := "Eastern Daly" }
  , { walsCode := "kan", name := "Kana", iso := "ogo", family := "Niger-Congo", genus := "Ogonoid" }
  , { walsCode := "knk", name := "Kanakuru", iso := "kna", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "xns", name := "Kanashi", iso := "xns", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "kbu", name := "Kanembu", iso := "kbl", family := "Saharan", genus := "Western Saharan" }
  , { walsCode := "knd", name := "Kannada", iso := "kan", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kno", name := "Kanoê", iso := "kxo", family := "Kapixana", genus := "Kapixana" }
  , { walsCode := "knb", name := "Kanum (Bädi)", iso := "khd", family := "Yam", genus := "Kanum" }
  , { walsCode := "knr", name := "Kanuri", iso := "knc", family := "Saharan", genus := "Western Saharan" }
  , { walsCode := "kyo", name := "Kanyok", iso := "kny", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kpm", name := "Kapampangan", iso := "pam", family := "Austronesian", genus := "Central Luzon" }
  , { walsCode := "kar", name := "Kara (in Central African Republic)", iso := "kah", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "krc", name := "Karachay-Balkar", iso := "krc", family := "Altaic", genus := "Turkic" }
  , { walsCode := "krj", name := "Karadjeri", iso := "gbd", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "jva", name := "Karajá", iso := "kpj", family := "Macro-Ge", genus := "Karajá" }
  , { walsCode := "kkp", name := "Karakalpak", iso := "kaa", family := "Altaic", genus := "Turkic" }
  , { walsCode := "kkw", name := "Karankawa", iso := "zkk", family := "Karankawa", genus := "Karankawa" }
  , { walsCode := "kao", name := "Karao", iso := "kyj", family := "Austronesian", genus := "Northern Luzon" }
  , { walsCode := "kbw", name := "Karen (Bwe)", iso := "bwe", family := "Sino-Tibetan", genus := "Karen" }
  , { walsCode := "kpw", name := "Karen (Pwo)", iso := "kjp", family := "Sino-Tibetan", genus := "Karen" }
  , { walsCode := "ksg", name := "Karen (Sgaw)", iso := "ksw", family := "Sino-Tibetan", genus := "Karen" }
  , { walsCode := "kmj", name := "Karimojong", iso := "kdj", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "kna", name := "Karitiâna", iso := "ktn", family := "Tupian", genus := "Arikem" }
  , { walsCode := "kyr", name := "Karkar-Yuri", iso := "yuj", family := "Pauwasi", genus := "Eastern Pauwasi" }
  , { walsCode := "krk", name := "Karok", iso := "kyh", family := "Hokan", genus := "Karok" }
  , { walsCode := "kaa", name := "Karó (Arára)", iso := "arr", family := "Tupian", genus := "Ramarama" }
  , { walsCode := "ksm", name := "Kasem", iso := "xsm", family := "Niger-Congo", genus := "Grusi" }
  , { walsCode := "ksh", name := "Kashaya", iso := "kju", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "kas", name := "Kashmiri", iso := "kas", family := "Indo-European", genus := "Indic" }
  , { walsCode := "ksn", name := "Kasong", iso := "cog", family := "Austro-Asiatic", genus := "Pearic" }
  , { walsCode := "ktc", name := "Katcha", iso := "xtc", family := "Kadu", genus := "Kadugli" }
  , { walsCode := "ktm", name := "Kathlamet", iso := "", family := "Penutian", genus := "Chinookan" }
  , { walsCode := "kti", name := "Kati (in West Papua, Indonesia)", iso := "kts", family := "Trans-New Guinea", genus := "Ok" }
  , { walsCode := "ktl", name := "Katla", iso := "kcr", family := "Kordofanian", genus := "Katla-Tima" }
  , { walsCode := "kto", name := "Kato", iso := "ktw", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "ktu", name := "Katu", iso := "", family := "Austro-Asiatic", genus := "Katuic" }
  , { walsCode := "kau", name := "Kaulong", iso := "pss", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kws", name := "Kawaiisu", iso := "xaw", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "kyz", name := "Kayabí", iso := "kyz", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "kyl", name := "Kayah Li (Eastern)", iso := "eky", family := "Sino-Tibetan", genus := "Karen" }
  , { walsCode := "kyp", name := "Kayapó", iso := "txu", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "kay", name := "Kayardild", iso := "gyd", family := "Tangkic", genus := "Tangkic" }
  , { walsCode := "kaz", name := "Kazakh", iso := "kaz", family := "Altaic", genus := "Turkic" }
  , { walsCode := "kel", name := "Kele", iso := "sbc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kem", name := "Kemant", iso := "ahg", family := "Afro-Asiatic", genus := "Central Cushitic" }
  , { walsCode := "ken", name := "Kenga", iso := "kyq", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "ker", name := "Kera", iso := "ker", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "ksa", name := "Keresan (Santa Ana)", iso := "kee", family := "Keresan", genus := "Keresan" }
  , { walsCode := "ket", name := "Ket", iso := "ket", family := "Yeniseian", genus := "Yeniseian" }
  , { walsCode := "kte", name := "Kete", iso := "kcv", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kew", name := "Kewa", iso := "kew", family := "Trans-New Guinea", genus := "Enga_Kewa-Huli" }
  , { walsCode := "khk", name := "Khakas", iso := "kjh", family := "Altaic", genus := "Turkic" }
  , { walsCode := "khl", name := "Khalaj", iso := "klj", family := "Altaic", genus := "Turkic" }
  , { walsCode := "khg", name := "Khaling", iso := "klr", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "kha", name := "Khalkha", iso := "khk", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "kmh", name := "Kham", iso := "kjl", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "khd", name := "Kham (Dege)", iso := "khg", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "knz", name := "Kham (Tibetan) (Nangchen)", iso := "khg", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "kty", name := "Khanty", iso := "kca", family := "Uralic", genus := "Ugric" }
  , { walsCode := "khr", name := "Kharia", iso := "khr", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "khs", name := "Khasi", iso := "kha", family := "Austro-Asiatic", genus := "Khasian" }
  , { walsCode := "khi", name := "Khinalug", iso := "kjj", family := "Nakh-Daghestanian", genus := "Khinalug" }
  , { walsCode := "khm", name := "Khmer", iso := "khm", family := "Austro-Asiatic", genus := "Khmer" }
  , { walsCode := "kmu", name := "Khmu'", iso := "kjg", family := "Austro-Asiatic", genus := "Khmuic" }
  , { walsCode := "khw", name := "Khowar", iso := "khw", family := "Indo-European", genus := "Indic" }
  , { walsCode := "khn", name := "Khün", iso := "kkh", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "kic", name := "Kickapoo", iso := "kic", family := "Algic", genus := "Algonquian" }
  , { walsCode := "kik", name := "Kikuyu", iso := "kik", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "klv", name := "Kilivila", iso := "kij", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "klw", name := "Kiliwa", iso := "klb", family := "Hokan", genus := "Yuman" }
  , { walsCode := "kil", name := "Kiluba", iso := "lub", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kim", name := "Kimaghama", iso := "kig", family := "Kolopom", genus := "Kolopom" }
  , { walsCode := "kga", name := "Kinga", iso := "zga", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "knn", name := "Kinnauri", iso := "kfk", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "kin", name := "Kinyarwanda", iso := "kin", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kio", name := "Kiowa", iso := "kio", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "kri", name := "Kipea", iso := "kzw", family := "Kariri", genus := "Kariri" }
  , { walsCode := "kie", name := "Kire", iso := "geb", family := "Ramu-Lower Sepik", genus := "Ruboni" }
  , { walsCode := "kgz", name := "Kirghiz", iso := "kir", family := "Altaic", genus := "Turkic" }
  , { walsCode := "krb", name := "Kiribati", iso := "gil", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kir", name := "Kirma", iso := "cme", family := "Niger-Congo", genus := "Kirma-Tyurama" }
  , { walsCode := "kis", name := "Kisi", iso := "kss", family := "Niger-Congo", genus := "Southern Mel" }
  , { walsCode := "kiw", name := "Kiwai (Southern)", iso := "kjd", family := "Trans-New Guinea", genus := "Kiwaian" }
  , { walsCode := "klm", name := "Klamath", iso := "kla", family := "Penutian", genus := "Klamath-Modoc" }
  , { walsCode := "kla", name := "Klao", iso := "klu", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "shp", name := "Klikitat", iso := "yak", family := "Penutian", genus := "Sahaptian" }
  , { walsCode := "koa", name := "Koasati", iso := "cku", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "kob", name := "Kobon", iso := "kpw", family := "Trans-New Guinea", genus := "Kalam-Kobon" }
  , { walsCode := "kod", name := "Kodava", iso := "kfa", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "koe", name := "Koegu", iso := "xwg", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "klk", name := "Koh", iso := "xuo", family := "Niger-Congo", genus := "Mbumic" }
  , { walsCode := "kmo", name := "Koiali (Mountain)", iso := "kpx", family := "Trans-New Guinea", genus := "Koiarian" }
  , { walsCode := "koi", name := "Koiari", iso := "kbk", family := "Trans-New Guinea", genus := "Koiarian" }
  , { walsCode := "kta", name := "Koita", iso := "kqi", family := "Trans-New Guinea", genus := "Koiarian" }
  , { walsCode := "kok", name := "Kokborok", iso := "trp", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "kkt", name := "Kokota", iso := "kkk", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "koo", name := "Kola", iso := "kvv", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "kol", name := "Kolami", iso := "kfb", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "klr", name := "Koluri", iso := "shm", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "kmb", name := "Kombai", iso := "", family := "Trans-New Guinea", genus := "Ndeiram" }
  , { walsCode := "xbi", name := "Kombio", iso := "xbi", family := "Torricelli", genus := "Kombio-Arapesh" }
  , { walsCode := "kop", name := "Komi-Permyak", iso := "koi", family := "Uralic", genus := "Permic" }
  , { walsCode := "kzy", name := "Komi-Zyrian", iso := "kpv", family := "Uralic", genus := "Permic" }
  , { walsCode := "kom", name := "Komo", iso := "xom", family := "Koman", genus := "Koman" }
  , { walsCode := "kda", name := "Konda", iso := "kfc", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kon", name := "Kongo", iso := "kng", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kjo", name := "Konjo", iso := "kjc", family := "Austronesian", genus := "South Sulawesi" }
  , { walsCode := "kkn", name := "Konkani", iso := "knn", family := "Indo-European", genus := "Indic" }
  , { walsCode := "knw", name := "Konkow", iso := "mjd", family := "Penutian", genus := "Maiduan" }
  , { walsCode := "kni", name := "Konni", iso := "kma", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "kjr", name := "Koorete", iso := "kqy", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "krn", name := "Korana", iso := "kqz", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "kko", name := "Koranko", iso := "knk", family := "Mande", genus := "Western Mande" }
  , { walsCode := "kor", name := "Korean", iso := "kor", family := "Korean", genus := "Korean" }
  , { walsCode := "kje", name := "Koreguaje", iso := "coe", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "kku", name := "Korku", iso := "kfq", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "kfe", name := "Koromfe", iso := "kfz", family := "Niger-Congo", genus := "Koromfe" }
  , { walsCode := "krw", name := "Korowai", iso := "khe", family := "Trans-New Guinea", genus := "Becking-Dawi" }
  , { walsCode := "kry", name := "Koryak", iso := "kpy", family := "Chukotko-Kamchatkan", genus := "Northern Chukotko-Kamchatkan" }
  , { walsCode := "kos", name := "Kosraean", iso := "kos", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ktt", name := "Kott", iso := "", family := "Yeniseian", genus := "Yeniseian" }
  , { walsCode := "koy", name := "Koya", iso := "kff", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kch", name := "Koyra Chiini", iso := "khq", family := "Songhay", genus := "Songhay" }
  , { walsCode := "kse", name := "Koyraboro Senni", iso := "ses", family := "Songhay", genus := "Songhay" }
  , { walsCode := "kyn", name := "Koyukon", iso := "koy", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "kpe", name := "Kpelle", iso := "xpe", family := "Mande", genus := "Western Mande" }
  , { walsCode := "kpo", name := "Kposo", iso := "kpo", family := "Niger-Congo", genus := "Ka-Togo" }
  , { walsCode := "krh", name := "Krahô", iso := "xra", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "kqq", name := "Krenak", iso := "kqq", family := "Macro-Ge", genus := "Aimore" }
  , { walsCode := "kre", name := "Kresh", iso := "krs", family := "Central Sudanic", genus := "Kresh" }
  , { walsCode := "kfc", name := "Kriol (Fitzroy Crossing)", iso := "rop", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "kro", name := "Krongo", iso := "kgo", family := "Kadu", genus := "Kadugli" }
  , { walsCode := "krz", name := "Kryz", iso := "kry", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "knc", name := "Kugu Nganhcara", iso := "uwa", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kui", name := "Kui (in India)", iso := "kxu", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kkq", name := "Kuikúro", iso := "kui", family := "Cariban", genus := "Cariban" }
  , { walsCode := "kya", name := "Kuku-Yalanji", iso := "gvn", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kuk", name := "Kukú", iso := "bfa", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "kul", name := "Kullo", iso := "dwr", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "klg", name := "Kulung", iso := "kle", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "kmn", name := "Kuman", iso := "kue", family := "Trans-New Guinea", genus := "Chimbu-Wahgi" }
  , { walsCode := "kum", name := "Kumauni", iso := "kfy", family := "Indo-European", genus := "Indic" }
  , { walsCode := "kun", name := "Kuna", iso := "kvn", family := "Chibchan", genus := "Kuna" }
  , { walsCode := "knm", name := "Kunama", iso := "kun", family := "Kunama", genus := "Kunama" }
  , { walsCode := "kmp", name := "Kunimaipa", iso := "kup", family := "Trans-New Guinea", genus := "Core Goilalan" }
  , { walsCode := "kjn", name := "Kunjen", iso := "kjn", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kug", name := "Kunming", iso := "cmn", family := "Sino-Tibetan", genus := "Chinese" }
  , { walsCode := "kuo", name := "Kuot", iso := "kto", family := "Kuot", genus := "Kuot" }
  , { walsCode := "krd", name := "Kurdish (Central)", iso := "ckb", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "kji", name := "Kurmanji", iso := "kmr", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "kur", name := "Kurukh", iso := "kru", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kus", name := "Kusunda", iso := "kgg", family := "Kusunda", genus := "Kusunda" }
  , { walsCode := "kut", name := "Kutenai", iso := "kut", family := "Kutenai", genus := "Kutenai" }
  , { walsCode := "thy", name := "Kuuk Thaayorre", iso := "thd", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kuu", name := "Kuuku Ya'u", iso := "kuy", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "kuv", name := "Kuvi", iso := "kxv", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "kwa", name := "Kwaio", iso := "kwd", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kwk", name := "Kwakw'ala", iso := "kwk", family := "Wakashan", genus := "Northern Wakashan" }
  , { walsCode := "kwm", name := "Kwami", iso := "ksq", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "kwn", name := "Kwangali", iso := "kwn", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "kwz", name := "Kwaza", iso := "xwa", family := "Kwaza", genus := "Kwaza" }
  , { walsCode := "kwb", name := "Kwerba", iso := "kwe", family := "Tor-Kwerba", genus := "Kwerba" }
  , { walsCode := "kwo", name := "Kwoma", iso := "kmo", family := "Sepik", genus := "Nukuma" }
  , { walsCode := "kwt", name := "Kwomtari", iso := "kwo", family := "Kwomtari", genus := "Kwomtari" }
  , { walsCode := "kxo", name := "Kxoe", iso := "xuu", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "kyk", name := "Kyaka", iso := "kyc", family := "Trans-New Guinea", genus := "Enga_Kewa-Huli" }
  , { walsCode := "kgy", name := "Kyirong", iso := "kgy", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "kyq", name := "Kyuquot", iso := "nuk", family := "Wakashan", genus := "Southern Wakashan" }
  , { walsCode := "kat", name := "Kâte", iso := "kmg", family := "Trans-New Guinea", genus := "Huon" }
  , { walsCode := "laa", name := "Laal", iso := "gdm", family := "Laal", genus := "Laal" }
  , { walsCode := "lab", name := "Labu", iso := "lbu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "lac", name := "Lacandón", iso := "lac", family := "Mayan", genus := "Mayan" }
  , { walsCode := "lad", name := "Ladakhi", iso := "lbj", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "laf", name := "Lafofa", iso := "laf", family := "Kordofanian", genus := "Lafofa" }
  , { walsCode := "lag", name := "Lagwan", iso := "kot", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "lah", name := "Lahu", iso := "lhu", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "lai", name := "Lai", iso := "cnh", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "lak", name := "Lak", iso := "lbe", family := "Nakh-Daghestanian", genus := "Lak" }
  , { walsCode := "lkt", name := "Lakhota", iso := "lkt", family := "Siouan", genus := "Mississippi Valley Siouan" }
  , { walsCode := "lal", name := "Lalo", iso := "ywt", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "lmh", name := "Lamaholot", iso := "slp", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "lmg", name := "Lamang", iso := "hia", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "lmn", name := "Lamani", iso := "lmn", family := "Indo-European", genus := "Indic" }
  , { walsCode := "lmb", name := "Lamba", iso := "lam", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lmu", name := "Lamen", iso := "lmu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "lmp", name := "Lampung", iso := "ljp", family := "Austronesian", genus := "Lampungic" }
  , { walsCode := "lgi", name := "Langi", iso := "lag", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lan", name := "Lango", iso := "laj", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "lao", name := "Lao", iso := "lao", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "lar", name := "Laragia", iso := "lrg", family := "Darwin Region", genus := "Laragiya" }
  , { walsCode := "lrd", name := "Lardil", iso := "lbz", family := "Tangkic", genus := "Tangkic" }
  , { walsCode := "lrk", name := "Larike", iso := "alo", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "lat", name := "Latvian", iso := "lav", family := "Indo-European", genus := "Baltic" }
  , { walsCode := "lav", name := "Lavukaleve", iso := "lvk", family := "Solomons East Papuan", genus := "Lavukaleve" }
  , { walsCode := "laz", name := "Laz", iso := "lzz", family := "Kartvelian", genus := "Kartvelian" }
  , { walsCode := "leb", name := "Lebeo", iso := "agh", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "leg", name := "Lega", iso := "lea", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "agb", name := "Leggbó", iso := "agb", family := "Niger-Congo", genus := "Upper Cross" }
  , { walsCode := "lec", name := "Leko", iso := "lec", family := "Leko", genus := "Leko" }
  , { walsCode := "lel", name := "Lele", iso := "lln", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "llm", name := "Lelemi", iso := "lef", family := "Niger-Congo", genus := "Na-Togo" }
  , { walsCode := "len", name := "Lenakel", iso := "tnl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ldu", name := "Lendu", iso := "led", family := "Central Sudanic", genus := "Lendu" }
  , { walsCode := "lng", name := "Lengua", iso := "enx", family := "Mascoian", genus := "Mascoian" }
  , { walsCode := "lep", name := "Lepcha", iso := "lep", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "les", name := "Lese", iso := "les", family := "Central Sudanic", genus := "Mangbutu-Efe" }
  , { walsCode := "let", name := "Leti", iso := "lti", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "lew", name := "Lewo", iso := "lww", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "lez", name := "Lezgian", iso := "lez", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "lho", name := "Lhomi", iso := "lhm", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "lil", name := "Lillooet", iso := "lil", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "lim", name := "Limbu", iso := "lif", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "lml", name := "Limilngan", iso := "lmc", family := "Darwin Region", genus := "Limilngan" }
  , { walsCode := "lnd", name := "Linda", iso := "liy", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "lin", name := "Lingala", iso := "lin", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lis", name := "Lisu", iso := "lis", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "lit", name := "Lithuanian", iso := "lit", family := "Indo-European", genus := "Baltic" }
  , { walsCode := "lgt", name := "Logoti", iso := "log", family := "Central Sudanic", genus := "Moru-Ma'di" }
  , { walsCode := "ara", name := "Lokono", iso := "arw", family := "Arawakan", genus := "Antillean Arawakan" }
  , { walsCode := "ldo", name := "Londo", iso := "bdu", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lgu", name := "Longgu", iso := "lgu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "lon", name := "Loniu", iso := "los", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "lnw", name := "Lonwolwol", iso := "crc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "lot", name := "Lotha", iso := "njh", family := "Sino-Tibetan", genus := "Central Naga" }
  , { walsCode := "lou", name := "Lou", iso := "loj", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "loz", name := "Lozi", iso := "loz", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "luc", name := "Lucazi", iso := "lch", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lda", name := "Luganda", iso := "lug", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lug", name := "Lugbara", iso := "lgg", family := "Central Sudanic", genus := "Moru-Ma'di" }
  , { walsCode := "lui", name := "Luiseño", iso := "lui", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "lul", name := "Lule", iso := "ule", family := "Lule", genus := "Lule" }
  , { walsCode := "lbu", name := "Lunda", iso := "lun", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lun", name := "Lungchang", iso := "nst", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "luo", name := "Luo", iso := "luo", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "lus", name := "Lushootseed", iso := "lut", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "kkv", name := "Lusi", iso := "khl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "luv", name := "Luvale", iso := "lue", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "jlu", name := "Luwo", iso := "lwo", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "luy", name := "Luyia", iso := "luy", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "lye", name := "Lyele", iso := "lee", family := "Niger-Congo", genus := "Grusi" }
  , { walsCode := "ma", name := "Ma", iso := "msj", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "myn", name := "Ma'anyan", iso := "mhy", family := "Austronesian", genus := "Barito" }
  , { walsCode := "mad", name := "Ma'di", iso := "mhi", family := "Central Sudanic", genus := "Moru-Ma'di" }
  , { walsCode := "mle", name := "Maale", iso := "mdy", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "maa", name := "Maasai", iso := "mas", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "mab", name := "Maba", iso := "mde", family := "Maban", genus := "Maban" }
  , { walsCode := "mcd", name := "Macedonian", iso := "mkd", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "mch", name := "Machiguenga", iso := "mcb", family := "Arawakan", genus := "Pre-Andine Arawakan" }
  , { walsCode := "mac", name := "Macushi", iso := "mbc", family := "Cariban", genus := "Cariban" }
  , { walsCode := "mda", name := "Mada (in Cameroon)", iso := "mxu", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "mdm", name := "Madimadi", iso := "dmd", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "mdr", name := "Madurese", iso := "mad", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "mae", name := "Mae", iso := "mmw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mgh", name := "Magahi", iso := "mag", family := "Indo-European", genus := "Indic" }
  , { walsCode := "mag", name := "Magar", iso := "mgp", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "mgi", name := "Magi", iso := "mgu", family := "Trans-New Guinea", genus := "Mailuan" }
  , { walsCode := "mne", name := "Maidu (Northeast)", iso := "nmu", family := "Penutian", genus := "Maiduan" }
  , { walsCode := "mpr", name := "Maipure", iso := "", family := "Arawakan", genus := "Alto-Orinoco" }
  , { walsCode := "mrs", name := "Mairasi", iso := "zrs", family := "Mairasic", genus := "Mairasic" }
  , { walsCode := "msn", name := "Maisin", iso := "mbq", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mai", name := "Maithili", iso := "mai", family := "Indo-European", genus := "Indic" }
  , { walsCode := "maj", name := "Majang", iso := "mpe", family := "Eastern Sudanic", genus := "Majang" }
  , { walsCode := "mkz", name := "Makaa", iso := "mcp", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mak", name := "Makah", iso := "myh", family := "Wakashan", genus := "Southern Wakashan" }
  , { walsCode := "mkj", name := "Makasae", iso := "mkz", family := "Greater West Bomberai", genus := "East Timor" }
  , { walsCode := "mks", name := "Makassar", iso := "mak", family := "Austronesian", genus := "South Sulawesi" }
  , { walsCode := "mkl", name := "Maklew", iso := "mgf", family := "Bulaka River", genus := "Bulaka River" }
  , { walsCode := "mkd", name := "Makonde", iso := "kde", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mua", name := "Makua", iso := "mgh", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mal", name := "Malagasy", iso := "plt", family := "Austronesian", genus := "Barito" }
  , { walsCode := "mlk", name := "Malakmalak", iso := "mpb", family := "Northern Daly", genus := "Northern Daly" }
  , { walsCode := "mym", name := "Malayalam", iso := "mal", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "mlu", name := "Maleu", iso := "mgl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mlg", name := "Malgwa", iso := "", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "mlt", name := "Maltese", iso := "mlt", family := "Afro-Asiatic", genus := "Semitic" }
  ]

private def languages_2 : List Language :=
  [ { walsCode := "mto", name := "Malto", iso := "kmj", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "mam", name := "Mam", iso := "mam", family := "Mayan", genus := "Mayan" }
  , { walsCode := "mmn", name := "Mamanwa", iso := "mmn", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "mmi", name := "Mambai", iso := "mcs", family := "Niger-Congo", genus := "Mbumic" }
  , { walsCode := "mla", name := "Mambila", iso := "", family := "Niger-Congo", genus := "Mambiloid" }
  , { walsCode := "mmw", name := "Mambwe", iso := "mgr", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mmv", name := "Mamvu", iso := "mdi", family := "Central Sudanic", genus := "Mangbutu-Efe" }
  , { walsCode := "mds", name := "Manadonese", iso := "xmm", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "mnm", name := "Manam", iso := "mva", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nmm", name := "Manange", iso := "nmm", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "mnc", name := "Manchu", iso := "mnc", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "mdn", name := "Mandan", iso := "mhq", family := "Siouan", genus := "Mandan" }
  , { walsCode := "mnd", name := "Mandarin", iso := "cmn", family := "Sino-Tibetan", genus := "Chinese" }
  , { walsCode := "mkg", name := "Mandinka (Gambian)", iso := "mnk", family := "Mande", genus := "Western Mande" }
  , { walsCode := "mem", name := "Manem", iso := "jet", family := "Border", genus := "Border" }
  , { walsCode := "mmb", name := "Mangap-Mbula", iso := "mna", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "myi", name := "Mangarrayi", iso := "mpc", family := "Mangarrayi-Maran", genus := "Mangarrayi" }
  , { walsCode := "mbt", name := "Mangbetu", iso := "mdj", family := "Central Sudanic", genus := "Mangbetu" }
  , { walsCode := "mng", name := "Manggarai", iso := "mqy", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "mgg", name := "Mangghuer", iso := "mjg", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "mgq", name := "Mango", iso := "mge", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "maw", name := "Maninka (Western)", iso := "mlq", family := "Mande", genus := "Western Mande" }
  , { walsCode := "mkq", name := "Mankon", iso := "nge", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "man", name := "Mano", iso := "mev", family := "Mande", genus := "Eastern Mande" }
  , { walsCode := "mwb", name := "Manobo (Western Bukidnon)", iso := "mbb", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "mns", name := "Mansi", iso := "mns", family := "Uralic", genus := "Ugric" }
  , { walsCode := "mao", name := "Maori", iso := "mri", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "map", name := "Mapudungun", iso := "arn", family := "Araucanian", genus := "Araucanian" }
  , { walsCode := "mra", name := "Mara", iso := "mec", family := "Mangarrayi-Maran", genus := "Mara" }
  , { walsCode := "mku", name := "Maranungku", iso := "zmr", family := "Western Daly", genus := "Wagaydy" }
  , { walsCode := "mhi", name := "Marathi", iso := "mar", family := "Indo-European", genus := "Indic" }
  , { walsCode := "mrc", name := "Marchha", iso := "rnp", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "mny", name := "Margany", iso := "zmc", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "mrg", name := "Margi", iso := "mrt", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "mme", name := "Mari (Meadow)", iso := "mhr", family := "Uralic", genus := "Mari" }
  , { walsCode := "mar", name := "Maricopa", iso := "mrc", family := "Hokan", genus := "Yuman" }
  , { walsCode := "mrd", name := "Marind", iso := "mrz", family := "Trans-New Guinea", genus := "Marind-Yaqay" }
  , { walsCode := "mrr", name := "Maringarr", iso := "zmt", family := "Western Daly", genus := "Bringen" }
  , { walsCode := "mrq", name := "Marquesan", iso := "", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mrh", name := "Marrithiyel", iso := "mfr", family := "Western Daly", genus := "Bringen" }
  , { walsCode := "msh", name := "Marshallese", iso := "mah", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mrt", name := "Martuthunira", iso := "vma", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "mru", name := "Maru", iso := "mhx", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "mas", name := "Masa", iso := "mcn", family := "Afro-Asiatic", genus := "Masa" }
  , { walsCode := "msk", name := "Masakin", iso := "jle", family := "Kordofanian", genus := "Talodi" }
  , { walsCode := "msl", name := "Masalit", iso := "mls", family := "Maban", genus := "Maban" }
  , { walsCode := "mtt", name := "Massachusett", iso := "wam", family := "Algic", genus := "Algonquian" }
  , { walsCode := "mts", name := "Matis", iso := "mpq", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "mdl", name := "Matngele", iso := "zml", family := "Eastern Daly", genus := "Eastern Daly" }
  , { walsCode := "myr", name := "Matsés", iso := "mcf", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "mtl", name := "Mattole", iso := "mvb", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "mtk", name := "Matukar", iso := "mjk", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mtb", name := "Matuumbi", iso := "mgw", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mka", name := "Mauka", iso := "mxx", family := "Mande", genus := "Western Mande" }
  , { walsCode := "mau", name := "Maung", iso := "mph", family := "Iwaidjan", genus := "Iwaidjan" }
  , { walsCode := "mcr", name := "Mauritian Creole", iso := "mfe", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "max", name := "Maxakalí", iso := "mbl", family := "Macro-Ge", genus := "Maxakalian" }
  , { walsCode := "may", name := "Maybrat", iso := "ayz", family := "Maybrat", genus := "Maybrat" }
  , { walsCode := "myg", name := "Mayogo", iso := "mdm", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "mzn", name := "Mazanderani", iso := "mzn", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "mzc", name := "Mazatec (Chiquihuitlán)", iso := "maq", family := "Oto-Manguean", genus := "Popolocan" }
  , { walsCode := "mzh", name := "Mazatec (Huautla)", iso := "mau", family := "Oto-Manguean", genus := "Popolocan" }
  , { walsCode := "mba", name := "Mba", iso := "mfc", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "mhu", name := "Mbalanhu", iso := "lnb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mbr", name := "Mbara", iso := "mpk", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "mby", name := "Mbay", iso := "myb", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "mbe", name := "Mbere", iso := "mdt", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mbi", name := "Mbili", iso := "baw", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "mdo", name := "Mbodomo", iso := "gmm", family := "Niger-Congo", genus := "Gbaya-Manza-Ngbaka" }
  , { walsCode := "mbl", name := "Mbole", iso := "mdq", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mdw", name := "Mbosi", iso := "mdw", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mbm", name := "Mbum", iso := "mdd", family := "Niger-Congo", genus := "Mbumic" }
  , { walsCode := "mee", name := "Me'en", iso := "mym", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "mhk", name := "Mehek", iso := "nux", family := "Sepik", genus := "Tama Sepik" }
  , { walsCode := "meh", name := "Mehri", iso := "gdq", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "mei", name := "Meithei", iso := "mni", family := "Sino-Tibetan", genus := "Manipuri" }
  , { walsCode := "mek", name := "Mekens", iso := "skf", family := "Tupian", genus := "Tupari" }
  , { walsCode := "mke", name := "Mekeo", iso := "mek", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mde", name := "Mende", iso := "men", family := "Mande", genus := "Western Mande" }
  , { walsCode := "men", name := "Menomini", iso := "mez", family := "Algic", genus := "Algonquian" }
  , { walsCode := "mnt", name := "Mentawai", iso := "mwv", family := "Austronesian", genus := "Northwest Sumatra-Barrier Islands" }
  , { walsCode := "mey", name := "Menya", iso := "mcr", family := "Trans-New Guinea", genus := "Nuclear Angan" }
  , { walsCode := "mer", name := "Meryam Mir", iso := "ulk", family := "Eastern Trans-Fly", genus := "Eastern Trans-Fly" }
  , { walsCode := "mea", name := "Meyah", iso := "mej", family := "East Bird's Head", genus := "East Bird's Head" }
  , { walsCode := "mpt", name := "Mian", iso := "mpt", family := "Trans-New Guinea", genus := "Ok" }
  , { walsCode := "mid", name := "Midob", iso := "mei", family := "Eastern Sudanic", genus := "Nubian" }
  , { walsCode := "mie", name := "Mien", iso := "ium", family := "Hmong-Mien", genus := "Mienic" }
  , { walsCode := "mig", name := "Migama", iso := "mmy", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "mii", name := "Miisiirii", iso := "", family := "Eastern Sudanic", genus := "Taman" }
  , { walsCode := "mij", name := "Miju", iso := "mxj", family := "Sino-Tibetan", genus := "Kman-Meyor" }
  , { walsCode := "mkr", name := "Mikarew", iso := "msy", family := "Ramu-Lower Sepik", genus := "Ruboni" }
  , { walsCode := "mki", name := "Mikasuki", iso := "mik", family := "Muskogean", genus := "Muskogean" }
  , { walsCode := "mik", name := "Mikir", iso := "mjw", family := "Sino-Tibetan", genus := "Karbic" }
  , { walsCode := "mil", name := "Milang", iso := "", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "hna", name := "Mina", iso := "hna", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "min", name := "Minangkabau", iso := "min", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "mnv", name := "Minaveha", iso := "mvn", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mgl", name := "Mingrelian", iso := "xmf", family := "Kartvelian", genus := "Kartvelian" }
  , { walsCode := "mhl", name := "Miri (Hill):", iso := "mrg", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "mir", name := "Miriwung", iso := "mep", family := "Jarrakan", genus := "Jarrakan" }
  , { walsCode := "msg", name := "Mising", iso := "mrg", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "mis", name := "Miskito", iso := "miq", family := "Misumalpan", genus := "Misumalpan" }
  , { walsCode := "mcs", name := "Miwok (Central Sierra)", iso := "csm", family := "Penutian", genus := "Miwok" }
  , { walsCode := "mss", name := "Miwok (Southern Sierra)", iso := "skd", family := "Penutian", genus := "Miwok" }
  , { walsCode := "mxx", name := "Mixe (Ayutla)", iso := "mxp", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "mco", name := "Mixe (Coatlán)", iso := "mco", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "mth", name := "Mixe (Tlahuitoltepec)", iso := "mxp", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "mxl", name := "Mixtec (Alacatlatzala)", iso := "mim", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxa", name := "Mixtec (Atatlahuca)", iso := "mib", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxt", name := "Mixtec (Ayutla)", iso := "miy", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxc", name := "Mixtec (Chalcatongo)", iso := "mig", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxz", name := "Mixtec (Coatzospan)", iso := "miz", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mja", name := "Mixtec (Jamiltepec)", iso := "mxt", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxj", name := "Mixtec (Jicaltepec)", iso := "mio", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxo", name := "Mixtec (Ocotepec)", iso := "mie", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxp", name := "Mixtec (Peñoles)", iso := "mil", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxs", name := "Mixtec (Silacayoapan)", iso := "mks", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "mxy", name := "Mixtec (Yosondúa)", iso := "mpm", family := "Oto-Manguean", genus := "Mixtec" }
  , { walsCode := "miy", name := "Miya", iso := "mkf", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "miz", name := "Mizo", iso := "lus", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "mlm", name := "Mlabri (Minor)", iso := "mra", family := "Austro-Asiatic", genus := "Khmuic" }
  , { walsCode := "mcc", name := "Mochica", iso := "omc", family := "Mochica", genus := "Mochica" }
  , { walsCode := "mcv", name := "Mocoví", iso := "moc", family := "Guaicuruan", genus := "Qom" }
  , { walsCode := "mof", name := "Mofu-Gudur", iso := "mif", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "mog", name := "Moghol", iso := "mhj", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "moh", name := "Mohawk", iso := "moh", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "moj", name := "Mojave", iso := "mov", family := "Hokan", genus := "Yuman" }
  , { walsCode := "mok", name := "Mokilese", iso := "mkj", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mko", name := "Mokilko", iso := "moz", family := "Afro-Asiatic", genus := "East Chadic" }
  , { walsCode := "mom", name := "Mombum", iso := "mso", family := "Mombum", genus := "Mombum" }
  , { walsCode := "fqs", name := "Momu", iso := "fqs", family := "Baibai-Fas", genus := "Baibai-Fas" }
  , { walsCode := "mqf", name := "Momuna", iso := "mqf", family := "Trans-New Guinea", genus := "Somahai" }
  , { walsCode := "mon", name := "Mon", iso := "mnw", family := "Austro-Asiatic", genus := "Monic" }
  , { walsCode := "mga", name := "Mondunga", iso := "ndt", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "mgo", name := "Mongo", iso := "lol", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mkh", name := "Mongol (Khamnigan)", iso := "", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "mni", name := "Moni", iso := "mnz", family := "Trans-New Guinea", genus := "Paniai Lakes" }
  , { walsCode := "mno", name := "Mono (in United States)", iso := "mnr", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "moa", name := "Mono-Alu", iso := "mte", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mtg", name := "Montagnais", iso := "moe", family := "Algic", genus := "Algonquian" }
  , { walsCode := "mbo", name := "Monumbo", iso := "mxk", family := "Bogia", genus := "Bogia" }
  , { walsCode := "moo", name := "Mooré", iso := "mos", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "mor", name := "Mor", iso := "mhz", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "mri", name := "Moraori", iso := "mok", family := "Moraori", genus := "Moraori" }
  , { walsCode := "moe", name := "Mordvin (Erzya)", iso := "myv", family := "Uralic", genus := "Mordvin" }
  , { walsCode := "mro", name := "Moro", iso := "mor", family := "Kordofanian", genus := "Heiban" }
  , { walsCode := "mou", name := "Moru", iso := "mgd", family := "Central Sudanic", genus := "Moru-Ma'di" }
  , { walsCode := "mos", name := "Mosetén", iso := "cas", family := "Mosetenan", genus := "Mosetenan" }
  , { walsCode := "mtu", name := "Motu", iso := "meu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mot", name := "Motuna", iso := "siw", family := "South Bougainville", genus := "South Bougainville" }
  , { walsCode := "mov", name := "Movima", iso := "mzp", family := "Movima", genus := "Movima" }
  , { walsCode := "mpo", name := "Mpongwe", iso := "mye", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mpu", name := "Mpur", iso := "akc", family := "Mpur", genus := "Mpur" }
  , { walsCode := "aoj", name := "Mufian", iso := "aoj", family := "Torricelli", genus := "Kombio-Arapesh" }
  , { walsCode := "muh", name := "Muher", iso := "sgw", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "mui", name := "Muinane", iso := "bmr", family := "Boran", genus := "Boran" }
  , { walsCode := "msc", name := "Muisca", iso := "chb", family := "Chibchan", genus := "Chibcha-Duit" }
  , { walsCode := "mul", name := "Mulao", iso := "mlm", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "mum", name := "Mumuye", iso := "mzm", family := "Niger-Congo", genus := "Mumuye-Yandang" }
  , { walsCode := "mna", name := "Muna", iso := "mnb", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "mdg", name := "Mundang", iso := "mua", family := "Niger-Congo", genus := "Mbumic" }
  , { walsCode := "mud", name := "Mundani", iso := "mnf", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "mun", name := "Mundari", iso := "unr", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "muu", name := "Mundurukú", iso := "myu", family := "Tupian", genus := "Munduruku" }
  , { walsCode := "mgk", name := "Mungaka", iso := "mhk", family := "Niger-Congo", genus := "Wide Grassfields" }
  , { walsCode := "mse", name := "Munsee", iso := "umu", family := "Algic", genus := "Algonquian" }
  , { walsCode := "mnz", name := "Munzombo", iso := "moj", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "mup", name := "Mupun", iso := "sur", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "mrl", name := "Murle", iso := "mur", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "mpa", name := "Murrinh-Patha", iso := "mwf", family := "Southern Daly", genus := "Murrinh-Patha" }
  , { walsCode := "mur", name := "Mursi", iso := "muz", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "mrw", name := "Muruwari", iso := "zmu", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "mgu", name := "Musgu", iso := "mug", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "msm", name := "Musom", iso := "msu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "msq", name := "Musqueam", iso := "hur", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "mus", name := "Mussau", iso := "emi", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "mut", name := "Mutsun", iso := "css", family := "Penutian", genus := "Costanoan" }
  , { walsCode := "mwe", name := "Mwera", iso := "mwe", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "mwo", name := "Mwotlap", iso := "mlv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nab", name := "Nabak", iso := "naf", family := "Trans-New Guinea", genus := "Huon" }
  , { walsCode := "ndr", name := "Nadroga", iso := "wyy", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nad", name := "Nadëb", iso := "mbj", family := "Nadahup", genus := "Nadahup" }
  , { walsCode := "nma", name := "Naga (Mao)", iso := "nbi", family := "Sino-Tibetan", genus := "Angami-Pochuri" }
  , { walsCode := "ngt", name := "Naga (Tangkhul)", iso := "nmf", family := "Sino-Tibetan", genus := "Tangkhul-Maring" }
  , { walsCode := "nze", name := "Naga (Zeme)", iso := "nzm", family := "Sino-Tibetan", genus := "Zemeic" }
  , { walsCode := "nag", name := "Nagatman", iso := "nce", family := "Yale", genus := "Yale" }
  , { walsCode := "nah", name := "Nahali", iso := "nll", family := "Nahali", genus := "Nahali" }
  , { walsCode := "nhc", name := "Nahuatl (Central)", iso := "nhn", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nhh", name := "Nahuatl (Huasteca)", iso := "", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nmi", name := "Nahuatl (Mecayapan Isthmus)", iso := "nhx", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nhm", name := "Nahuatl (Michoacán)", iso := "ncl", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nmp", name := "Nahuatl (Milpa Alta)", iso := "nhm", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nhn", name := "Nahuatl (North Puebla)", iso := "ncj", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nhp", name := "Nahuatl (Pochutla)", iso := "xpo", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "nht", name := "Nahuatl (Tetelcingo)", iso := "nhg", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "bio", name := "Nai", iso := "bio", family := "Kwomtari", genus := "Kwomtari" }
  , { walsCode := "nak", name := "Nakanai", iso := "nak", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nkk", name := "Nakkara", iso := "nck", family := "Mangrida", genus := "Nakkara" }
  , { walsCode := "nal", name := "Nalik", iso := "nal", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "kho", name := "Nama", iso := "naq", family := "Khoe-Kwadi", genus := "Khoe-Kwadi" }
  , { walsCode := "nbb", name := "Nambas (Big)", iso := "nmb", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nmb", name := "Nambikuára (Southern)", iso := "nab", family := "Nambikuaran", genus := "Nambikuaran" }
  , { walsCode := "nam", name := "Namia", iso := "nnm", family := "Sepik", genus := "Yellow River" }
  , { walsCode := "nai", name := "Nanai", iso := "gld", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "nnc", name := "Nancowry", iso := "ncb", family := "Austro-Asiatic", genus := "Nicobarese" }
  , { walsCode := "nde", name := "Nande", iso := "nnb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nan", name := "Nandi", iso := "niq", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "nrg", name := "Nanerge", iso := "sen", family := "Niger-Congo", genus := "Senufo" }
  , { walsCode := "nnk", name := "Nankina", iso := "nnk", family := "Trans-New Guinea", genus := "Finisterre" }
  , { walsCode := "nph", name := "Nar-Phu", iso := "npa", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "nar", name := "Nara (in Ethiopia)", iso := "nrb", family := "Eastern Sudanic", genus := "Nara" }
  , { walsCode := "nas", name := "Nasioi", iso := "nas", family := "South Bougainville", genus := "South Bougainville" }
  , { walsCode := "nat", name := "Natchez", iso := "ncz", family := "Natchez", genus := "Natchez" }
  , { walsCode := "nau", name := "Nauruan", iso := "nau", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nav", name := "Navajo", iso := "nav", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "nax", name := "Naxi", iso := "nxq", family := "Sino-Tibetan", genus := "Na-Qiangic" }
  , { walsCode := "ncm", name := "Ncàm", iso := "bud", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "ndb", name := "Ndebele", iso := "nde", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ndj", name := "Ndjébbana", iso := "djj", family := "Mangrida", genus := "Ndjébbana" }
  , { walsCode := "ndo", name := "Ndonga", iso := "ndo", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ndu", name := "Ndumu", iso := "nmd", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ndt", name := "Ndut", iso := "ndv", family := "Niger-Congo", genus := "Cangin" }
  , { walsCode := "ndy", name := "Ndyuka", iso := "djk", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "neh", name := "Nehan", iso := "nsn", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nel", name := "Nelemwa", iso := "nee", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nnd", name := "Nend", iso := "anh", family := "Trans-New Guinea", genus := "Sogeram" }
  , { walsCode := "ntu", name := "Nenets", iso := "yrk", family := "Uralic", genus := "Samoyedic" }
  , { walsCode := "nne", name := "Nengone", iso := "nen", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "naj", name := "Neo-Aramaic (Arbel Jewish)", iso := "aij", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "nep", name := "Nepali", iso := "npi", family := "Indo-European", genus := "Indic" }
  , { walsCode := "nev", name := "Nevome", iso := "pia", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "nwd", name := "Newar (Dolakha)", iso := "new", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "new", name := "Newari (Kathmandu)", iso := "new", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "ney", name := "Neyo", iso := "ney", family := "Niger-Congo", genus := "Kru" }
  , { walsCode := "nez", name := "Nez Perce", iso := "nez", family := "Penutian", genus := "Sahaptian" }
  , { walsCode := "ntj", name := "Ngaanyatjarra", iso := "ntj", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "ngd", name := "Ngad'a", iso := "nxg", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "ngj", name := "Ngadjumaja", iso := "nju", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "ngl", name := "Ngalakan", iso := "nig", family := "Gunwinyguan", genus := "Eastern Gunwinyguan" }
  , { walsCode := "nkb", name := "Ngalkbun", iso := "ngk", family := "Gunwinyguan", genus := "Marne" }
  , { walsCode := "ngm", name := "Ngambay", iso := "sba", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "ngg", name := "Ngan'gityemerri", iso := "nam", family := "Southern Daly", genus := "Ngankikurungkurr" }
  , { walsCode := "nga", name := "Nganasan", iso := "nio", family := "Uralic", genus := "Samoyedic" }
  , { walsCode := "ngn", name := "Ngandi", iso := "nid", family := "Gunwinyguan", genus := "Eastern Gunwinyguan" }
  , { walsCode := "ngk", name := "Ngankikurungkurr", iso := "nam", family := "Southern Daly", genus := "Ngankikurungkurr" }
  , { walsCode := "ngr", name := "Ngarinyeri", iso := "nay", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "ngw", name := "Ngawun", iso := "nxn", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "nbm", name := "Ngbaka (Ma'bo)", iso := "nbm", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "ngb", name := "Ngbaka (Minagende)", iso := "nga", family := "Niger-Congo", genus := "Gbaya-Manza-Ngbaka" }
  , { walsCode := "ndi", name := "Ngbandi", iso := "ngb", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "nge", name := "Ngemba", iso := "nge", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nti", name := "Ngiti", iso := "niy", family := "Central Sudanic", genus := "Lendu" }
  , { walsCode := "ngi", name := "Ngiyambaa", iso := "wyb", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "ngz", name := "Ngizim", iso := "ngi", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "nbe", name := "Ngombe", iso := "ngc", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ngo", name := "Ngoni", iso := "ngo", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ngu", name := "Nguna", iso := "llp", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nbr", name := "Ngäbere", iso := "gym", family := "Chibchan", genus := "Guaymiic" }
  , { walsCode := "nha", name := "Nhanda", iso := "nha", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "nia", name := "Nias", iso := "nia", family := "Austronesian", genus := "Northwest Sumatra-Barrier Islands" }
  , { walsCode := "nic", name := "Nicobarese", iso := "ncb", family := "Austro-Asiatic", genus := "Nicobarese" }
  , { walsCode := "nca", name := "Nicobarese (Car)", iso := "caq", family := "Austro-Asiatic", genus := "Nicobarese" }
  , { walsCode := "npi", name := "Nigerian Pidgin", iso := "pcm", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "nim", name := "Nimboran", iso := "nir", family := "Nimboran", genus := "Nimboran" }
  , { walsCode := "nsn", name := "Nisenan", iso := "nsz", family := "Penutian", genus := "Maiduan" }
  , { walsCode := "nsg", name := "Nisgha", iso := "ncg", family := "Tsimshianic", genus := "Tsimshianic" }
  , { walsCode := "nit", name := "Nitinaht", iso := "dtd", family := "Wakashan", genus := "Southern Wakashan" }
  , { walsCode := "nif", name := "Niuafo'ou", iso := "num", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "niu", name := "Niuean", iso := "niu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "niv", name := "Nivkh", iso := "niv", family := "Nivkh", genus := "Nivkh" }
  , { walsCode := "nke", name := "Nkem", iso := "isi", family := "Niger-Congo", genus := "Ekoid-Mbe" }
  , { walsCode := "nkn", name := "Nkonya", iso := "nko", family := "Niger-Congo", genus := "Tano" }
  , { walsCode := "nko", name := "Nkore-Kiga", iso := "cgg", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "noc", name := "Nocte", iso := "njb", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "nog", name := "Noghay", iso := "nog", family := "Altaic", genus := "Turkic" }
  , { walsCode := "nom", name := "Nomatsiguenga", iso := "not", family := "Arawakan", genus := "Pre-Andine Arawakan" }
  , { walsCode := "non", name := "Noni", iso := "nhu", family := "Niger-Congo", genus := "Beboid" }
  , { walsCode := "noo", name := "Noon", iso := "snf", family := "Niger-Congo", genus := "Cangin" }
  , { walsCode := "nor", name := "Norwegian", iso := "nor", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "nse", name := "Nsenga", iso := "nse", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nto", name := "Ntomba", iso := "nto", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nua", name := "Nuaulu", iso := "nxl", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "nbd", name := "Nubian (Dongolese)", iso := "dgl", family := "Eastern Sudanic", genus := "Nubian" }
  , { walsCode := "nku", name := "Nubian (Kunuz)", iso := "xnz", family := "Eastern Sudanic", genus := "Nubian" }
  , { walsCode := "nue", name := "Nuer", iso := "nus", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "nkr", name := "Nukuoro", iso := "nkr", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "nun", name := "Nung (in Vietnam)", iso := "nut", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "nug", name := "Nunggubuyu", iso := "nuy", family := "Gunwinyguan", genus := "Nunggubuyu" }
  , { walsCode := "yi", name := "Nuosu", iso := "iii", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "nup", name := "Nupe", iso := "nup", family := "Niger-Congo", genus := "Nupoid" }
  , { walsCode := "nus", name := "Nusu", iso := "nuf", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "nuu", name := "Nuuchahnulth", iso := "nuk", family := "Wakashan", genus := "Southern Wakashan" }
  , { walsCode := "nyk", name := "Nyamkad", iso := "tpq", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "nym", name := "Nyamwezi", iso := "nym", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nng", name := "Nyanga", iso := "nyj", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nyr", name := "Nyangumarda", iso := "nna", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "nya", name := "Nyawaygi", iso := "nyt", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "nyn", name := "Nyigina", iso := "nyh", family := "Nyulnyulan", genus := "Nyulnyulan" }
  , { walsCode := "nyh", name := "Nyiha", iso := "nih", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "nyi", name := "Nyimang", iso := "nyi", family := "Eastern Sudanic", genus := "Nyimang" }
  , { walsCode := "nis", name := "Nyishi", iso := "njz", family := "Sino-Tibetan", genus := "Tani" }
  , { walsCode := "nyu", name := "Nyulnyul", iso := "nyv", family := "Nyulnyulan", genus := "Nyulnyulan" }
  , { walsCode := "nza", name := "Nzakara", iso := "nzk", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "ood", name := "O'odham", iso := "ood", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "obo", name := "Obolo", iso := "ann", family := "Niger-Congo", genus := "Lower Cross" }
  , { walsCode := "ocu", name := "Ocuilteco", iso := "ocu", family := "Oto-Manguean", genus := "Matlatzincan" }
  , { walsCode := "obg", name := "Ogbronuagum", iso := "ogu", family := "Niger-Congo", genus := "Central Delta" }
  , { walsCode := "oir", name := "Oirat", iso := "xal", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "oji", name := "Ojibwa (Eastern)", iso := "", family := "Algic", genus := "Algonquian" }
  , { walsCode := "ojs", name := "Ojibwa (Severn)", iso := "ojs", family := "Algic", genus := "Algonquian" }
  , { walsCode := "ojm", name := "Ojibwe (Minnesota)", iso := "ciw", family := "Algic", genus := "Algonquian" }
  , { walsCode := "oka", name := "Okanagan", iso := "oka", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "oks", name := "Oksapmin", iso := "opm", family := "Trans-New Guinea", genus := "Oksapmin" }
  , { walsCode := "olo", name := "Olo", iso := "ong", family := "Torricelli", genus := "Central Wapei" }
  , { walsCode := "olu", name := "Olutec", iso := "plo", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "omh", name := "Omaha", iso := "oma", family := "Siouan", genus := "Mississippi Valley Siouan" }
  , { walsCode := "one", name := "One", iso := "aun", family := "Torricelli", genus := "West Wapei" }
  , { walsCode := "ond", name := "Oneida", iso := "one", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "ong", name := "Onge", iso := "oon", family := "South Andamanese", genus := "South Andamanese" }
  , { walsCode := "ono", name := "Ono", iso := "ons", family := "Trans-New Guinea", genus := "Huon" }
  , { walsCode := "ord", name := "Ordos", iso := "mvf", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "ori", name := "Orig", iso := "tag", family := "Kordofanian", genus := "Rashad" }
  , { walsCode := "oya", name := "Oriya", iso := "ory", family := "Indo-European", genus := "Indic" }
  , { walsCode := "orm", name := "Ormuri", iso := "oru", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "ork", name := "Orok", iso := "oaa", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "oro", name := "Orokaiva", iso := "okv", family := "Trans-New Guinea", genus := "Binanderean" }
  , { walsCode := "orb", name := "Oromo (Boraana)", iso := "gax", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "orh", name := "Oromo (Harar)", iso := "hae", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "orw", name := "Oromo (Waata)", iso := "ssn", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "ory", name := "Orya", iso := "ury", family := "Tor-Kwerba", genus := "Tor-Orya" }
  , { walsCode := "osa", name := "Osage", iso := "osa", family := "Siouan", genus := "Mississippi Valley Siouan" }
  , { walsCode := "oss", name := "Ossetic", iso := "oss", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "otm", name := "Otomí (Mezquital)", iso := "ote", family := "Oto-Manguean", genus := "Otomian" }
  , { walsCode := "ots", name := "Otomí (Sierra)", iso := "otm", family := "Oto-Manguean", genus := "Otomian" }
  , { walsCode := "otr", name := "Otoro", iso := "otr", family := "Kordofanian", genus := "Heiban" }
  , { walsCode := "owi", name := "Owininga", iso := "owi", family := "Left May", genus := "Left May" }
  , { walsCode := "paa", name := "Pa'a", iso := "pqa", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "pkn", name := "Paakantyi", iso := "drl", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "pms", name := "Paamese", iso := "pma", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pac", name := "Pacoh", iso := "pac", family := "Austro-Asiatic", genus := "Katuic" }
  , { walsCode := "pno", name := "Paiute (Northern)", iso := "pao", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "put", name := "Paiute (Southern)", iso := "ute", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "pai", name := "Paiwan", iso := "pwn", family := "Austronesian", genus := "Paiwan" }
  , { walsCode := "pal", name := "Palauan", iso := "pau", family := "Austronesian", genus := "Palauan" }
  , { walsCode := "plg", name := "Palaung", iso := "pll", family := "Austro-Asiatic", genus := "Palaungic" }
  , { walsCode := "plk", name := "Palikur", iso := "plu", family := "Arawakan", genus := "Palikur" }
  , { walsCode := "plr", name := "Palor", iso := "fap", family := "Niger-Congo", genus := "Cangin" }
  , { walsCode := "pam", name := "Pame", iso := "pmz", family := "Oto-Manguean", genus := "Pamean" }
  , { walsCode := "pna", name := "Pamona", iso := "pmf", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "pnx", name := "Panará", iso := "kre", family := "Macro-Ge", genus := "Je Setentrional" }
  , { walsCode := "pnn", name := "Pangasinan", iso := "pag", family := "Austronesian", genus := "Northern Luzon" }
  , { walsCode := "png", name := "Pangwa", iso := "pbr", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "pan", name := "Panjabi", iso := "pan", family := "Indo-European", genus := "Indic" }
  , { walsCode := "pny", name := "Panyjima", iso := "pnw", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "pap", name := "Papiamentu", iso := "pap", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "pre", name := "Pare", iso := "asa", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "prc", name := "Paresi", iso := "pab", family := "Arawakan", genus := "Central Arawakan" }
  , { walsCode := "prd", name := "Parji (Dravidian)", iso := "pci", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "psh", name := "Pashto", iso := "pst", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "psm", name := "Passamaquoddy-Maliseet", iso := "pqm", family := "Algic", genus := "Algonquian" }
  , { walsCode := "pat", name := "Patep", iso := "ptp", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ptp", name := "Patpatar", iso := "gfk", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ptt", name := "Pattani", iso := "lae", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "ptw", name := "Patwin", iso := "pwi", family := "Penutian", genus := "Wintuan" }
  , { walsCode := "plh", name := "Paulohi", iso := "plh", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "pau", name := "Paumarí", iso := "pad", family := "Arauan", genus := "Arauan" }
  , { walsCode := "paw", name := "Pawaian", iso := "pwa", family := "Teberan-Pawaian", genus := "Pawaian" }
  , { walsCode := "pwn", name := "Pawnee", iso := "paw", family := "Caddoan", genus := "Northern Caddoan" }
  , { walsCode := "pec", name := "Pech", iso := "pay", family := "Chibchan", genus := "Pech" }
  , { walsCode := "pem", name := "Pemon", iso := "aoc", family := "Cariban", genus := "Cariban" }
  , { walsCode := "per", name := "Pero", iso := "pip", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "prs", name := "Persian", iso := "pes", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "ppc", name := "Piapoco", iso := "pio", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "pia", name := "Piaroa", iso := "pid", family := "Sáliban", genus := "Maco-Piaroa" }
  , { walsCode := "pga", name := "Pilagá", iso := "plg", family := "Guaicuruan", genus := "Qom" }
  , { walsCode := "pil", name := "Pileni", iso := "piv", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pba", name := "Pima Bajo", iso := "pia", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "pgl", name := "Pingilapese", iso := "pif", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pip", name := "Pipil", iso := "ppl", family := "Uto-Aztecan", genus := "Aztecan" }
  , { walsCode := "prh", name := "Pirahã", iso := "myp", family := "Mura", genus := "Mura" }
  , { walsCode := "pir", name := "Piro", iso := "pib", family := "Arawakan", genus := "Purus" }
  , { walsCode := "pis", name := "Pisa", iso := "psa", family := "Trans-New Guinea", genus := "Awju" }
  , { walsCode := "pit", name := "Pitjantjatjara", iso := "pjt", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "ppi", name := "Pitta Pitta", iso := "pit", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "pod", name := "Podoko", iso := "pbi", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "pog", name := "Pogoro", iso := "poy", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "poh", name := "Pohnpeian", iso := "pon", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pok", name := "Poko-Rawo", iso := "rwa", family := "Skou", genus := "Serra Hills" }
  , { walsCode := "pkt", name := "Pokot", iso := "pko", family := "Eastern Sudanic", genus := "Southern Nilotic" }
  , { walsCode := "pol", name := "Polish", iso := "pol", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "pmc", name := "Pomo (Central)", iso := "poo", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "pme", name := "Pomo (Eastern)", iso := "peb", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "pmn", name := "Pomo (Northern)", iso := "pej", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "pso", name := "Pomo (Southeastern)", iso := "pom", family := "Hokan", genus := "Pomoan" }
  , { walsCode := "pop", name := "Popoloca (Metzontla)", iso := "pbe", family := "Oto-Manguean", genus := "Popolocan" }
  , { walsCode := "psj", name := "Popoloca (San Juan Atzingo)", iso := "poe", family := "Oto-Manguean", genus := "Popolocan" }
  , { walsCode := "zqs", name := "Popoluca (Sierra)", iso := "poi", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "psw", name := "Port Sandwich", iso := "psw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "por", name := "Portuguese", iso := "por", family := "Indo-European", genus := "Romance" }
  , { walsCode := "pot", name := "Potawatomi", iso := "pot", family := "Algic", genus := "Algonquian" }
  , { walsCode := "pra", name := "Prasuni", iso := "prn", family := "Indo-European", genus := "Nuristani" }
  , { walsCode := "pul", name := "Puluwat", iso := "puw", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "pum", name := "Pumi", iso := "pmi", family := "Sino-Tibetan", genus := "Na-Qiangic" }
  , { walsCode := "pun", name := "Pungupungu", iso := "wdj", family := "Wandjiginy", genus := "Wandjiginy" }
  , { walsCode := "puq", name := "Puquina", iso := "puq", family := "Puquina", genus := "Puquina" }
  , { walsCode := "prk", name := "Purki", iso := "prx", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "pur", name := "Purépecha", iso := "tsz", family := "Tarascan", genus := "Tarascan" }
  , { walsCode := "pae", name := "Páez", iso := "pbb", family := "Páezan", genus := "Páezan" }
  , { walsCode := "par", name := "Päri", iso := "lkr", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "qaf", name := "Qafar", iso := "aar", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "bng", name := "Qaqet", iso := "byx", family := "Baining", genus := "Baining" }
  , { walsCode := "qaw", name := "Qawasqar", iso := "alc", family := "Alacalufan", genus := "Alacalufan" }
  , { walsCode := "qia", name := "Qiang", iso := "", family := "Sino-Tibetan", genus := "Na-Qiangic" }
  , { walsCode := "que", name := "Quechan", iso := "yum", family := "Hokan", genus := "Yuman" }
  , { walsCode := "qay", name := "Quechua (Ayacucho)", iso := "quy", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qbo", name := "Quechua (Bolivian)", iso := "", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qco", name := "Quechua (Cochabamba)", iso := "quh", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qcu", name := "Quechua (Cuzco)", iso := "quz", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qhu", name := "Quechua (Huallaga)", iso := "qub", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qim", name := "Quechua (Imbabura)", iso := "qvi", family := "Quechuan", genus := "Quechuan" }
  , { walsCode := "qui", name := "Quileute", iso := "qui", family := "Chimakuan", genus := "Chimakuan" }
  , { walsCode := "rag", name := "Raga", iso := "lml", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "rji", name := "Raji", iso := "rji", family := "Sino-Tibetan", genus := "Raji-Raute" }
  , { walsCode := "ral", name := "Ralte", iso := "ral", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "ram", name := "Rama", iso := "rma", family := "Chibchan", genus := "Rama" }
  , { walsCode := "rpa", name := "Rang Pas", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "rao", name := "Rao", iso := "rao", family := "Ramu-Lower Sepik", genus := "Rao" }
  , { walsCode := "rap", name := "Rapanui", iso := "rap", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ras", name := "Rashad", iso := "ras", family := "Kordofanian", genus := "Rashad" }
  , { walsCode := "rwa", name := "Rawa", iso := "rwo", family := "Trans-New Guinea", genus := "Finisterre" }
  , { walsCode := "raw", name := "Rawang", iso := "raw", family := "Sino-Tibetan", genus := "Nungish" }
  , { walsCode := "rej", name := "Rejang", iso := "rej", family := "Austronesian", genus := "Rejang" }
  , { walsCode := "rmb", name := "Rembarnga", iso := "rmb", family := "Gunwinyguan", genus := "Eastern Gunwinyguan" }
  , { walsCode := "rem", name := "Remo", iso := "bfw", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "ren", name := "Rendille", iso := "rel", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "res", name := "Resígaro", iso := "rgr", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "ret", name := "Retuarã", iso := "tnc", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "ria", name := "Riantana", iso := "ran", family := "Kolopom", genus := "Kolopom" }
  , { walsCode := "rik", name := "Rikbaktsa", iso := "rkb", family := "Macro-Ge", genus := "Rikbaktsa" }
  , { walsCode := "rim", name := "Rimi", iso := "rim", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "rit", name := "Ritharngu", iso := "rit", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "rka", name := "Romani (Kalderash)", iso := "rmy", family := "Indo-European", genus := "Indic" }
  , { walsCode := "rwe", name := "Romani (Welsh)", iso := "rmw", family := "Indo-European", genus := "Indic" }
  , { walsCode := "rom", name := "Romanian", iso := "ron", family := "Indo-European", genus := "Romance" }
  , { walsCode := "rsu", name := "Romansch (Sursilvan)", iso := "roh", family := "Indo-European", genus := "Romance" }
  , { walsCode := "ron", name := "Ron", iso := "cla", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "rga", name := "Ronga", iso := "rng", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "rti", name := "Roti", iso := "twu", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "rot", name := "Rotuman", iso := "rtm", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "rov", name := "Roviana", iso := "rug", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ruk", name := "Rukai (Tanan)", iso := "dru", family := "Austronesian", genus := "Rukai" }
  , { walsCode := "cos", name := "Rumsien", iso := "", family := "Penutian", genus := "Costanoan" }
  , { walsCode := "rum", name := "Rumu", iso := "klq", family := "Trans-New Guinea", genus := "Turama-Kikorian" }
  , { walsCode := "rnd", name := "Rundi", iso := "run", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "run", name := "Runga", iso := "rou", family := "Maban", genus := "Maban" }
  , { walsCode := "rny", name := "Runyankore", iso := "nyn", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "rru", name := "Runyoro-Rutooro", iso := "nyo", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "rus", name := "Russian", iso := "rus", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "rut", name := "Rutul", iso := "rut", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "saa", name := "Sa'a", iso := "apb", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ski", name := "Saami (Kildin)", iso := "sjd", family := "Uralic", genus := "Saami" }
  , { walsCode := "sno", name := "Saami (Northern)", iso := "sme", family := "Uralic", genus := "Saami" }
  , { walsCode := "smt", name := "Sahaptin (Umatilla)", iso := "uma", family := "Penutian", genus := "Sahaptian" }
  , { walsCode := "sah", name := "Sahu", iso := "saj", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "sak", name := "Sakao", iso := "sku", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "slr", name := "Salar", iso := "slr", family := "Altaic", genus := "Turkic" }
  , { walsCode := "slb", name := "Saliba (in Papua New Guinea)", iso := "sbe", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sal", name := "Salinan", iso := "sln", family := "Hokan", genus := "Salinan" }
  , { walsCode := "sst", name := "Salish (Straits)", iso := "str", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "syu", name := "Salt-Yui", iso := "sll", family := "Trans-New Guinea", genus := "Chimbu-Wahgi" }
  , { walsCode := "sle", name := "Samba Leko", iso := "ndi", family := "Niger-Congo", genus := "Samba-Duru" }
  , { walsCode := "nmd", name := "Samo", iso := "smq", family := "Trans-New Guinea", genus := "East Strickland" }
  , { walsCode := "sam", name := "Samoan", iso := "smo", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sdw", name := "Sandawe", iso := "sad", family := "Sandawe", genus := "Sandawe" }
  , { walsCode := "san", name := "Sango", iso := "sag", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "sgu", name := "Sangu", iso := "snq", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sta", name := "Santa", iso := "sce", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "stl", name := "Santali", iso := "sat", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "snm", name := "Sanuma", iso := "xsu", family := "Yanomam", genus := "Yanomam" }
  , { walsCode := "sap", name := "Sapuan", iso := "spu", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "srm", name := "Saramaccan", iso := "srm", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "src", name := "Sarcee", iso := "srs", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "srd", name := "Sardinian", iso := "sro", family := "Indo-European", genus := "Romance" }
  , { walsCode := "sar", name := "Sare", iso := "dju", family := "Sepik", genus := "Sepik Hill" }
  , { walsCode := "sav", name := "Savi", iso := "sdg", family := "Indo-European", genus := "Indic" }
  , { walsCode := "svs", name := "Savosavo", iso := "svs", family := "Solomons East Papuan", genus := "Savosavo" }
  , { walsCode := "swi", name := "Sawai", iso := "szw", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "saw", name := "Sawu", iso := "hvn", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "say", name := "Sayula Popoluca", iso := "pos", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "seb", name := "Sebei", iso := "kpz", family := "Eastern Sudanic", genus := "Southern Nilotic" }
  , { walsCode := "sec", name := "Secoya", iso := "sey", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "sed", name := "Sedang", iso := "sed", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "see", name := "Seediq", iso := "trv", family := "Austronesian", genus := "Atayalic" }
  , { walsCode := "slp", name := "Selepet", iso := "spl", family := "Trans-New Guinea", genus := "Huon" }
  , { walsCode := "sel", name := "Selknam", iso := "ona", family := "Chonan", genus := "Chonan Proper" }
  , { walsCode := "skp", name := "Selkup", iso := "sel", family := "Uralic", genus := "Samoyedic" }
  , { walsCode := "sem", name := "Sema", iso := "nsm", family := "Sino-Tibetan", genus := "Angami-Pochuri" }
  , { walsCode := "sme", name := "Seme", iso := "sif", family := "Siamou", genus := "Siamou" }
  , { walsCode := "sml", name := "Semelai", iso := "sza", family := "Austro-Asiatic", genus := "Aslian" }
  , { walsCode := "smn", name := "Seminole", iso := "mus", family := "Muskogean", genus := "Muskogean" }
  ]

private def languages_3 : List Language :=
  [ { walsCode := "sen", name := "Sena", iso := "seh", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "snc", name := "Seneca", iso := "see", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "sgl", name := "Sengele", iso := "szg", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "snt", name := "Sentani", iso := "set", family := "Sentanic", genus := "Sentanic" }
  , { walsCode := "scr", name := "Serbian-Croatian", iso := "hbs", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "ser", name := "Seri", iso := "sei", family := "Hokan", genus := "Seri" }
  , { walsCode := "srr", name := "Serrano", iso := "ser", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "ses", name := "Sesotho", iso := "sot", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sey", name := "Seychelles Creole", iso := "crs", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "shb", name := "Shabo", iso := "sbf", family := "Shabo", genus := "Shabo" }
  , { walsCode := "shm", name := "Shambala", iso := "ksb", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sha", name := "Shan", iso := "shn", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "shh", name := "Sharanahua", iso := "mcd", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "shs", name := "Shasta", iso := "sht", family := "Hokan", genus := "Shasta" }
  , { walsCode := "sht", name := "Shatt", iso := "shj", family := "Eastern Sudanic", genus := "Daju" }
  , { walsCode := "skw", name := "Shekhawati", iso := "swv", family := "Indo-European", genus := "Indic" }
  , { walsCode := "shd", name := "Sherdukpen", iso := "sdp", family := "Sino-Tibetan", genus := "Kho-Bwa" }
  , { walsCode := "she", name := "Sherpa", iso := "xsr", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "shl", name := "Shilluk", iso := "shk", family := "Eastern Sudanic", genus := "Western Nilotic" }
  , { walsCode := "sna", name := "Shina", iso := "scl", family := "Indo-European", genus := "Indic" }
  , { walsCode := "shk", name := "Shipibo-Konibo", iso := "shp", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "shy", name := "Shira Yughur", iso := "yuy", family := "Altaic", genus := "Mongolic" }
  , { walsCode := "shi", name := "Shiriana", iso := "shb", family := "Yanomam", genus := "Yanomam" }
  , { walsCode := "smp", name := "Shompen", iso := "sii", family := "Shompen", genus := "Shompen" }
  , { walsCode := "shn", name := "Shona", iso := "sna", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sho", name := "Shoshone", iso := "shh", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "ryu", name := "Shuri", iso := "ryu", family := "Japanese", genus := "Japanese" }
  , { walsCode := "shu", name := "Shuswap", iso := "shs", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "sia", name := "Siane", iso := "snp", family := "Trans-New Guinea", genus := "Siane-Yagaria" }
  , { walsCode := "sir", name := "Siar", iso := "sjr", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sid", name := "Sidaama", iso := "sid", family := "Afro-Asiatic", genus := "Highland East Cushitic" }
  , { walsCode := "sik", name := "Sika", iso := "ski", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "skr", name := "Sikaritai", iso := "tty", family := "Lakes Plain", genus := "East Tariku" }
  , { walsCode := "skk", name := "Sikkimese", iso := "sip", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "sil", name := "Sila", iso := "dau", family := "Eastern Sudanic", genus := "Daju" }
  , { walsCode := "sim", name := "Simeulue", iso := "smr", family := "Austronesian", genus := "Northwest Sumatra-Barrier Islands" }
  , { walsCode := "sng", name := "Sinaugoro", iso := "snc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "snh", name := "Sinhala", iso := "sin", family := "Indo-European", genus := "Indic" }
  , { walsCode := "sio", name := "Sio", iso := "xsi", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sin", name := "Siona", iso := "snn", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "qum", name := "Sipakapense", iso := "qum", family := "Mayan", genus := "Mayan" }
  , { walsCode := "sry", name := "Siraya", iso := "fos", family := "Austronesian", genus := "East Formosan" }
  , { walsCode := "srn", name := "Sirionó", iso := "srq", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "sro", name := "Siroi", iso := "ssd", family := "Trans-New Guinea", genus := "Rai Coast" }
  , { walsCode := "ssa", name := "Sisaala", iso := "sil", family := "Niger-Congo", genus := "Grusi" }
  , { walsCode := "sis", name := "Sisiqa", iso := "baa", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "siu", name := "Siuslaw", iso := "sis", family := "Oregon Coast", genus := "Siuslawan" }
  , { walsCode := "sko", name := "Skou", iso := "skv", family := "Skou", genus := "Western Skou" }
  , { walsCode := "sla", name := "Slave", iso := "den", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "svk", name := "Slovak", iso := "slk", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "slo", name := "Slovene", iso := "slv", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "so", name := "So", iso := "teu", family := "Eastern Sudanic", genus := "Kuliak" }
  , { walsCode := "sob", name := "Sobei", iso := "sob", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sod", name := "Soddo", iso := "gru", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "som", name := "Somali", iso := "som", family := "Afro-Asiatic", genus := "Lowland East Cushitic" }
  , { walsCode := "sge", name := "Songe", iso := "sop", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "snn", name := "Soninke", iso := "snk", family := "Mande", genus := "Western Mande" }
  , { walsCode := "son", name := "Sonsorol-Tobi", iso := "sov", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "soq", name := "Soqotri", iso := "sqt", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "sor", name := "Sora", iso := "srb", family := "Austro-Asiatic", genus := "Munda" }
  , { walsCode := "srb", name := "Sorbian", iso := "", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "stn", name := "Sotho (Northern)", iso := "nso", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sgb", name := "Sougb", iso := "mnx", family := "East Bird's Head", genus := "East Bird's Head" }
  , { walsCode := "sea", name := "Southeast Ambrym", iso := "tvk", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tou", name := "Southern Toussian", iso := "wib", family := "Niger-Congo", genus := "Tusia" }
  , { walsCode := "spa", name := "Spanish", iso := "spa", family := "Indo-European", genus := "Romance" }
  , { walsCode := "spi", name := "Spitian", iso := "spt", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "spo", name := "Spokane", iso := "spo", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "squ", name := "Squamish", iso := "squ", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "sra", name := "Sranan", iso := "srn", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "sre", name := "Sre", iso := "kpm", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "sti", name := "Stieng", iso := "", family := "Austro-Asiatic", genus := "Bahnaric" }
  , { walsCode := "sub", name := "Subiya", iso := "sbs", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sud", name := "Sudest", iso := "tgo", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sue", name := "Suena", iso := "sue", family := "Trans-New Guinea", genus := "Binanderean" }
  , { walsCode := "suk", name := "Suki", iso := "sui", family := "Trans-New Guinea", genus := "Suki" }
  , { walsCode := "sku", name := "Suku", iso := "sub", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "skm", name := "Sukuma", iso := "suk", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "sul", name := "Sulka", iso := "sua", family := "Sulka", genus := "Sulka" }
  , { walsCode := "slg", name := "Sulung", iso := "suv", family := "Sino-Tibetan", genus := "Kho-Bwa" }
  , { walsCode := "sun", name := "Sundanese", iso := "sun", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "sug", name := "Sungor", iso := "sjg", family := "Eastern Sudanic", genus := "Taman" }
  , { walsCode := "sup", name := "Supyire", iso := "spp", family := "Niger-Congo", genus := "Senufo" }
  , { walsCode := "sur", name := "Sursurunga", iso := "sgz", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "sus", name := "Susu", iso := "sus", family := "Mande", genus := "Western Mande" }
  , { walsCode := "swa", name := "Swahili", iso := "swh", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "swt", name := "Swati", iso := "ssw", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "swe", name := "Swedish", iso := "swe", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "sba", name := "Sáliba (in Colombia)", iso := "slc", family := "Sáliban", genus := "Sáliba" }
  , { walsCode := "tab", name := "Taba", iso := "mky", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "tba", name := "Tabare", iso := "sst", family := "Trans-New Guinea", genus := "Chimbu-Wahgi" }
  , { walsCode := "tbl", name := "Tabla", iso := "tnm", family := "Sentanic", genus := "Sentanic" }
  , { walsCode := "tbw", name := "Tabwa", iso := "tap", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tac", name := "Tacana", iso := "tna", family := "Pano-Tacanan", genus := "Tacanan" }
  , { walsCode := "tag", name := "Tagalog", iso := "tgl", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "tah", name := "Tahitian", iso := "tah", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tap", name := "Taiap", iso := "gpn", family := "Taiap", genus := "Taiap" }
  , { walsCode := "taf", name := "Taiof", iso := "sps", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "trr", name := "Tairora", iso := "tbg", family := "Trans-New Guinea", genus := "Tairora" }
  , { walsCode := "taj", name := "Tajik", iso := "tgk", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "tkl", name := "Takelma", iso := "tkm", family := "Takelma", genus := "Takelma" }
  , { walsCode := "tak", name := "Takia", iso := "tbc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tal", name := "Talinga", iso := "tlj", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "taz", name := "Talysh (Azerbaijan)", iso := "tly", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "tls", name := "Talysh (Southern)", iso := "shm", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "tma", name := "Tama", iso := "tma", family := "Eastern Sudanic", genus := "Taman" }
  , { walsCode := "tmm", name := "Tamabo", iso := "mla", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tmg", name := "Tamagario", iso := "tcg", family := "Kayagar", genus := "Kayagar" }
  , { walsCode := "tam", name := "Tamang (Eastern)", iso := "taj", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tsk", name := "Tamashek", iso := "taq", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "tml", name := "Tamil", iso := "tam", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "tnc", name := "Tanacross", iso := "tcb", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "tan", name := "Tangale", iso := "tan", family := "Afro-Asiatic", genus := "West Chadic" }
  , { walsCode := "tbx", name := "Tangbe", iso := "skj", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tga", name := "Tangga", iso := "hrc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tpt", name := "Tapieté", iso := "tpj", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "tce", name := "Tarahumara (Central)", iso := "tar", family := "Uto-Aztecan", genus := "Tarahumaran" }
  , { walsCode := "twe", name := "Tarahumara (Western)", iso := "tac", family := "Uto-Aztecan", genus := "Tarahumaran" }
  , { walsCode := "tao", name := "Tarao", iso := "tro", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "tar", name := "Tariana", iso := "tae", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "tas", name := "Tashlhiyt", iso := "shi", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "tsm", name := "Tasmanian", iso := "", family := "Tasmanian", genus := "Tasmanian" }
  , { walsCode := "tat", name := "Tatana'", iso := "txx", family := "Austronesian", genus := "North Borneo" }
  , { walsCode := "tvo", name := "Tatar", iso := "tat", family := "Altaic", genus := "Turkic" }
  , { walsCode := "tts", name := "Tati (Southern)", iso := "tks", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "tsr", name := "Taushiro", iso := "trr", family := "Taushiro", genus := "Taushiro" }
  , { walsCode := "tsg", name := "Tausug", iso := "tsg", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "tau", name := "Tauya", iso := "tya", family := "Trans-New Guinea", genus := "Rai Coast" }
  , { walsCode := "taw", name := "Tawala", iso := "tbo", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tbo", name := "Tboli", iso := "tbl", family := "Austronesian", genus := "Bilic" }
  , { walsCode := "tlf", name := "Telefol", iso := "tlf", family := "Trans-New Guinea", genus := "Ok" }
  , { walsCode := "tel", name := "Telugu", iso := "tel", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "tem", name := "Tem", iso := "kdh", family := "Niger-Congo", genus := "Grusi" }
  , { walsCode := "tmn", name := "Temein", iso := "teq", family := "Eastern Sudanic", genus := "Temein" }
  , { walsCode := "tmr", name := "Temiar", iso := "tea", family := "Austro-Asiatic", genus := "Aslian" }
  , { walsCode := "tne", name := "Temne", iso := "tem", family := "Niger-Congo", genus := "Northern Mel" }
  , { walsCode := "ten", name := "Tennet", iso := "tex", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "tny", name := "Tenyer", iso := "kza", family := "Niger-Congo", genus := "Senufo" }
  , { walsCode := "teo", name := "Teop", iso := "tio", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tpc", name := "Tepecano", iso := "tep", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "tee", name := "Tepehua (Huehuetla)", iso := "tee", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "tep", name := "Tepehua (Tlachichilco)", iso := "tpt", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "tpn", name := "Tepehuan (Northern)", iso := "ntp", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "tps", name := "Tepehuan (Southeastern)", iso := "stp", family := "Uto-Aztecan", genus := "Tepiman" }
  , { walsCode := "ter", name := "Tera", iso := "ttr", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "trb", name := "Teribe", iso := "tfr", family := "Chibchan", genus := "Western Isthmic Chibchan" }
  , { walsCode := "trt", name := "Ternate", iso := "tft", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "trn", name := "Terêna", iso := "ter", family := "Arawakan", genus := "Bolivia-Parana" }
  , { walsCode := "tes", name := "Teso", iso := "teo", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "tet", name := "Tetela", iso := "tll", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "ttn", name := "Tetun", iso := "tet", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "ttd", name := "Tetun Dili", iso := "tet", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "tew", name := "Tewa (Arizona)", iso := "tew", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "trg", name := "Tewa (Rio Grande)", iso := "tew", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "thd", name := "Thadou", iso := "tcz", family := "Sino-Tibetan", genus := "Kuki-Chin" }
  , { walsCode := "tha", name := "Thai", iso := "tha", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "thk", name := "Thakali", iso := "ths", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "thn", name := "Thangmi", iso := "thf", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "thw", name := "Thao", iso := "ssf", family := "Austronesian", genus := "Western Plains Austronesian" }
  , { walsCode := "tho", name := "Thompson", iso := "thp", family := "Salishan", genus := "Interior Salish" }
  , { walsCode := "thu", name := "Thulung", iso := "tdh", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "tdi", name := "Tibetan (Dingri)", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tdr", name := "Tibetan (Drokpa)", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tmo", name := "Tibetan (Modern Literary)", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tis", name := "Tibetan (Shigatse)", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tib", name := "Tibetan (Standard Spoken)", iso := "bod", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tic", name := "Ticuna", iso := "tca", family := "Ticuna", genus := "Ticuna" }
  , { walsCode := "tid", name := "Tidore", iso := "tvo", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "tgk", name := "Tigak", iso := "tgc", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tig", name := "Tigrinya", iso := "tir", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "tgr", name := "Tigré", iso := "tig", family := "Afro-Asiatic", genus := "Semitic" }
  , { walsCode := "tja", name := "Tiipay (Jamul)", iso := "dih", family := "Hokan", genus := "Yuman" }
  , { walsCode := "tik", name := "Tikar", iso := "tik", family := "Niger-Congo", genus := "Tikar" }
  , { walsCode := "til", name := "Tillamook", iso := "til", family := "Salishan", genus := "Tillamook" }
  , { walsCode := "tia", name := "Tima", iso := "tms", family := "Kordofanian", genus := "Katla-Tima" }
  , { walsCode := "tmc", name := "Timucua", iso := "tjm", family := "Timucua", genus := "Timucua" }
  , { walsCode := "tim", name := "Timugon", iso := "tih", family := "Austronesian", genus := "North Borneo" }
  , { walsCode := "tni", name := "Tinani", iso := "lbf", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tin", name := "Tinrin", iso := "cir", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tir", name := "Tiriyo", iso := "tri", family := "Cariban", genus := "Cariban" }
  , { walsCode := "trm", name := "Tirmaga", iso := "suq", family := "Eastern Sudanic", genus := "South Surmic" }
  , { walsCode := "tiv", name := "Tiv", iso := "tiv", family := "Niger-Congo", genus := "Tivoid" }
  , { walsCode := "twn", name := "Tiwa (Northern)", iso := "twf", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "tws", name := "Tiwa (Southern)", iso := "tix", family := "Kiowa-Tanoan", genus := "Kiowa-Tanoan" }
  , { walsCode := "tiw", name := "Tiwi", iso := "tiw", family := "Tiwian", genus := "Tiwian" }
  , { walsCode := "tlp", name := "Tlapanec", iso := "tcf", family := "Oto-Manguean", genus := "Subtiaba-Tlapanec" }
  , { walsCode := "tli", name := "Tlingit", iso := "tli", family := "Na-Dene", genus := "Tlingit" }
  , { walsCode := "tob", name := "Toba", iso := "tob", family := "Guaicuruan", genus := "Qom" }
  , { walsCode := "tbt", name := "Tobati", iso := "tti", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tlo", name := "Tobelo", iso := "tlb", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "tod", name := "Tod", iso := "sbu", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tda", name := "Toda", iso := "tcx", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "toj", name := "Tojolabal", iso := "toj", family := "Mayan", genus := "Mayan" }
  , { walsCode := "tpi", name := "Tok Pisin", iso := "tpi", family := "other", genus := "Creoles and Pidgins" }
  , { walsCode := "tke", name := "Tokelauan", iso := "tkl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tol", name := "Tol", iso := "jic", family := "Tol", genus := "Tol" }
  , { walsCode := "tla", name := "Tolai", iso := "ksd", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tms", name := "Tommo So", iso := "dto", family := "Dogon", genus := "Dogon" }
  , { walsCode := "tno", name := "Tondano", iso := "tdn", family := "Austronesian", genus := "Minahasan" }
  , { walsCode := "toz", name := "Tonga (in Zambia)", iso := "toi", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tng", name := "Tongan", iso := "ton", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ton", name := "Tonkawa", iso := "tqw", family := "Tonkawa", genus := "Tonkawa" }
  , { walsCode := "toq", name := "Toqabaqita", iso := "mlu", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tor", name := "Toratán", iso := "rth", family := "Austronesian", genus := "Sangiric" }
  , { walsCode := "trw", name := "Torwali", iso := "trw", family := "Indo-European", genus := "Indic" }
  , { walsCode := "tot", name := "Totonac (Misantla)", iso := "tlc", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "tpa", name := "Totonac (Papantla)", iso := "top", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "txj", name := "Totonac (Xicotepec de Juárez)", iso := "too", family := "Totonacan", genus := "Totonacan" }
  , { walsCode := "tri", name := "Trique (Copala)", iso := "trc", family := "Oto-Manguean", genus := "Trique" }
  , { walsCode := "tru", name := "Trumai", iso := "tpy", family := "Trumai", genus := "Trumai" }
  , { walsCode := "tsf", name := "Tsafiki", iso := "cof", family := "Barbacoan", genus := "Barbacoan" }
  , { walsCode := "tsa", name := "Tsakhur", iso := "tkr", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "tsz", name := "Tsez", iso := "ddo", family := "Nakh-Daghestanian", genus := "Avar-Andic-Tsezic" }
  , { walsCode := "tgl", name := "Tshangla", iso := "tsj", family := "Sino-Tibetan", genus := "Bodic" }
  , { walsCode := "tsi", name := "Tsimshian (Coast)", iso := "tsi", family := "Tsimshianic", genus := "Tsimshianic" }
  , { walsCode := "tgo", name := "Tsogo", iso := "tsv", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tsn", name := "Tsonga", iso := "tso", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tso", name := "Tsou", iso := "tsu", family := "Austronesian", genus := "Tsou" }
  , { walsCode := "ttu", name := "Tsova-Tush", iso := "bbl", family := "Nakh-Daghestanian", genus := "Nakh" }
  , { walsCode := "tsw", name := "Tswana", iso := "tsn", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tug", name := "Tuareg (Ahaggar)", iso := "thv", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "tai", name := "Tuareg (Air)", iso := "thz", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "tgh", name := "Tuareg (Ghat)", iso := "thv", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "tbu", name := "Tubu", iso := "", family := "Saharan", genus := "Western Saharan" }
  , { walsCode := "tuc", name := "Tucano", iso := "tuo", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "tgn", name := "Tugun", iso := "tzn", family := "Austronesian", genus := "Central Malayo-Polynesian" }
  , { walsCode := "tuk", name := "Tukang Besi", iso := "", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "tki", name := "Tuki", iso := "bag", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tul", name := "Tulu", iso := "tcy", family := "Dravidian", genus := "Dravidian" }
  , { walsCode := "tum", name := "Tumleo", iso := "tmq", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tnb", name := "Tunebo", iso := "tuf", family := "Chibchan", genus := "Tunebo" }
  , { walsCode := "tnn", name := "Tunen", iso := "tvu", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "tnk", name := "Tungak", iso := "lcm", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tun", name := "Tunica", iso := "tun", family := "Tunica", genus := "Tunica" }
  , { walsCode := "tup", name := "Tupi", iso := "tpn", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "tpr", name := "Tupuri", iso := "tui", family := "Niger-Congo", genus := "Mbumic" }
  , { walsCode := "tna", name := "Turkana", iso := "tuv", family := "Eastern Sudanic", genus := "Eastern Nilotic" }
  , { walsCode := "tur", name := "Turkish", iso := "tur", family := "Altaic", genus := "Turkic" }
  , { walsCode := "tkm", name := "Turkmen", iso := "tuk", family := "Altaic", genus := "Turkic" }
  , { walsCode := "tus", name := "Tuscarora", iso := "tus", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "tte", name := "Tutelo", iso := "tta", family := "Siouan", genus := "Ohio Valley Siouan" }
  , { walsCode := "tvt", name := "Tutsa", iso := "tvt", family := "Sino-Tibetan", genus := "Brahmaputran" }
  , { walsCode := "tvl", name := "Tuvaluan", iso := "tvl", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "tuv", name := "Tuvan", iso := "tyv", family := "Altaic", genus := "Turkic" }
  , { walsCode := "tuy", name := "Tuyuca", iso := "tue", family := "Tucanoan", genus := "Tucanoan" }
  , { walsCode := "twa", name := "Twana", iso := "twa", family := "Salishan", genus := "Central Salish" }
  , { walsCode := "tye", name := "Tyeraity", iso := "woa", family := "Northern Daly", genus := "Northern Daly" }
  , { walsCode := "tze", name := "Tzeltal", iso := "tzh", family := "Mayan", genus := "Mayan" }
  , { walsCode := "tzo", name := "Tzotzil", iso := "tzo", family := "Mayan", genus := "Mayan" }
  , { walsCode := "tzu", name := "Tzutujil", iso := "tzj", family := "Mayan", genus := "Mayan" }
  , { walsCode := "tbb", name := "Tübatulabal", iso := "tub", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "tsh", name := "Tümpisa Shoshone", iso := "par", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "uby", name := "Ubykh", iso := "uby", family := "Northwest Caucasian", genus := "Northwest Caucasian" }
  , { walsCode := "udi", name := "Udi", iso := "udi", family := "Nakh-Daghestanian", genus := "Lezgic" }
  , { walsCode := "udh", name := "Udihe", iso := "ude", family := "Altaic", genus := "Tungusic" }
  , { walsCode := "udm", name := "Udmurt", iso := "udm", family := "Uralic", genus := "Permic" }
  , { walsCode := "ukr", name := "Ukrainian", iso := "ukr", family := "Indo-European", genus := "Slavic" }
  , { walsCode := "uld", name := "Uldeme", iso := "udl", family := "Afro-Asiatic", genus := "Biu-Mandara" }
  , { walsCode := "uli", name := "Ulithian", iso := "uli", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "uma", name := "Uma", iso := "ppk", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "una", name := "Una", iso := "mtg", family := "Trans-New Guinea", genus := "Mek" }
  , { walsCode := "ung", name := "Ungarinjin", iso := "ung", family := "Worrorran", genus := "Worrorran" }
  , { walsCode := "uku", name := "Upper Kuskokwim", iso := "kuu", family := "Na-Dene", genus := "Athapaskan" }
  , { walsCode := "ura", name := "Ura", iso := "uur", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "uhi", name := "Uradhi", iso := "urf", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "url", name := "Urak Lawoi'", iso := "urk", family := "Austronesian", genus := "Malayo-Sumbawan" }
  , { walsCode := "urn", name := "Urarina", iso := "ura", family := "Urarina", genus := "Urarina" }
  , { walsCode := "urt", name := "Urat", iso := "urt", family := "Torricelli", genus := "Urat" }
  , { walsCode := "urd", name := "Urdu", iso := "urd", family := "Indo-European", genus := "Indic" }
  , { walsCode := "urh", name := "Urhobo", iso := "urh", family := "Niger-Congo", genus := "Edoid" }
  , { walsCode := "uru", name := "Uru", iso := "ure", family := "Uru-Chipaya", genus := "Uru-Chipaya" }
  , { walsCode := "urk", name := "Urubú-Kaapor", iso := "urb", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "usa", name := "Usan", iso := "wnu", family := "Trans-New Guinea", genus := "North Adelbert" }
  , { walsCode := "usr", name := "Usarufa", iso := "usa", family := "Trans-New Guinea", genus := "Gauwa" }
  , { walsCode := "ute", name := "Ute", iso := "ute", family := "Uto-Aztecan", genus := "Northern Uto-Aztecan" }
  , { walsCode := "uyg", name := "Uyghur", iso := "uig", family := "Altaic", genus := "Turkic" }
  , { walsCode := "uzb", name := "Uzbek", iso := "", family := "Altaic", genus := "Turkic" }
  , { walsCode := "vaf", name := "Vafsi", iso := "vaf", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "vai", name := "Vai", iso := "vai", family := "Mande", genus := "Western Mande" }
  , { walsCode := "ven", name := "Venda", iso := "ven", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "vie", name := "Vietnamese", iso := "vie", family := "Austro-Asiatic", genus := "Vietic" }
  , { walsCode := "vif", name := "Vili", iso := "vif", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "vnm", name := "Vinmavis", iso := "vnm", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "vot", name := "Votic", iso := "vot", family := "Uralic", genus := "Finnic" }
  , { walsCode := "wwa", name := "Waama", iso := "wwa", family := "Niger-Congo", genus := "Oti-Volta" }
  , { walsCode := "wag", name := "Wagiman", iso := "waq", family := "Wagiman", genus := "Wagiman" }
  , { walsCode := "wah", name := "Wahgi", iso := "", family := "Trans-New Guinea", genus := "Chimbu-Wahgi" }
  , { walsCode := "wai", name := "Wai Wai", iso := "waw", family := "Cariban", genus := "Cariban" }
  , { walsCode := "wak", name := "Wakhi", iso := "wbl", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "wal", name := "Walman", iso := "van", family := "Torricelli", genus := "West Palei" }
  , { walsCode := "wlm", name := "Walmatjari", iso := "wmt", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "wam", name := "Wambaya", iso := "wmb", family := "Mirndi", genus := "Wambayan" }
  , { walsCode := "wbn", name := "Wambon", iso := "wms", family := "Trans-New Guinea", genus := "Dumut" }
  , { walsCode := "wme", name := "Wambule", iso := "wme", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "wna", name := "Wan", iso := "wan", family := "Mande", genus := "Eastern Mande" }
  , { walsCode := "wan", name := "Wangkumara", iso := "xwk", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "wao", name := "Waorani", iso := "auc", family := "Waorani", genus := "Waorani" }
  , { walsCode := "wap", name := "Wappo", iso := "wao", family := "Wappo-Yukian", genus := "Wappo" }
  , { walsCode := "wra", name := "Warao", iso := "wba", family := "Warao", genus := "Warao" }
  , { walsCode := "wry", name := "Waray (in Australia)", iso := "wrz", family := "Gunwinyguan", genus := "Western Gunwinyguan" }
  , { walsCode := "wwy", name := "Waray-Waray", iso := "war", family := "Austronesian", genus := "Greater Central Philippine" }
  , { walsCode := "wrd", name := "Wardaman", iso := "wrr", family := "Yangmanic", genus := "Yangmanic" }
  , { walsCode := "wrk", name := "Warekena", iso := "gae", family := "Arawakan", genus := "Alto-Orinoco" }
  , { walsCode := "wrm", name := "Warembori", iso := "wsa", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "war", name := "Wari'", iso := "pav", family := "Chapacura-Wanham", genus := "Chapacura-Wanham" }
  , { walsCode := "wrl", name := "Warlpiri", iso := "wbp", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "wlw", name := "Warluwara", iso := "wrb", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "wrn", name := "Warndarang", iso := "wnd", family := "Mangarrayi-Maran", genus := "Mara" }
  , { walsCode := "wrp", name := "Waropen", iso := "wrp", family := "Austronesian", genus := "South Halmahera - West New Guinea" }
  , { walsCode := "wrg", name := "Warrgamay", iso := "wgy", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "wrb", name := "Warrnambool", iso := "gjm", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "wgu", name := "Warrongo", iso := "wrg", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "wrw", name := "Warrwa", iso := "wwr", family := "Nyulnyulan", genus := "Nyulnyulan" }
  , { walsCode := "was", name := "Washo", iso := "was", family := "Washo", genus := "Washo" }
  , { walsCode := "wsk", name := "Waskia", iso := "wsk", family := "Trans-New Guinea", genus := "Kowan" }
  , { walsCode := "wtm", name := "Watam", iso := "wax", family := "Ramu-Lower Sepik", genus := "Lower Ramu" }
  , { walsCode := "wth", name := "Wathawurrung", iso := "wth", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "wat", name := "Watjarri", iso := "wbv", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "wau", name := "Waunana", iso := "noa", family := "Choco", genus := "Choco" }
  , { walsCode := "wur", name := "Waurá", iso := "wau", family := "Arawakan", genus := "Central Arawakan" }
  , { walsCode := "way", name := "Wayampi", iso := "oym", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "wyn", name := "Wayana", iso := "way", family := "Cariban", genus := "Cariban" }
  , { walsCode := "wed", name := "Wedau", iso := "wed", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "wel", name := "Welsh", iso := "cym", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "wec", name := "Welsh (Colloquial)", iso := "cym", family := "Indo-European", genus := "Celtic" }
  , { walsCode := "wem", name := "Wembawemba", iso := "xww", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "wma", name := "West Makian", iso := "mqs", family := "North Halmaheran", genus := "North Halmaheran" }
  , { walsCode := "wic", name := "Wichita", iso := "wic", family := "Caddoan", genus := "Northern Caddoan" }
  , { walsCode := "wch", name := "Wichí", iso := "mzh", family := "Matacoan", genus := "Matacoan" }
  , { walsCode := "wmu", name := "Wik Munkan", iso := "wim", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "wn", name := "Wik Ngathana", iso := "wig", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "wik", name := "Wikchamni", iso := "yok", family := "Penutian", genus := "Yokuts" }
  , { walsCode := "win", name := "Wintu", iso := "wnw", family := "Penutian", genus := "Wintuan" }
  , { walsCode := "wir", name := "Wirangu", iso := "wgu", family := "Pama-Nyungan", genus := "Central Pama-Nyungan" }
  , { walsCode := "wiy", name := "Wiyot", iso := "wiy", family := "Algic", genus := "Wiyot" }
  , { walsCode := "wog", name := "Wogamusin", iso := "wog", family := "Sepik", genus := "Wogamusin-Chenapian" }
  , { walsCode := "woi", name := "Woisika", iso := "woi", family := "Greater West Bomberai", genus := "Alor-Pantar" }
  , { walsCode := "wly", name := "Wolaytta", iso := "wal", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "wol", name := "Woleaian", iso := "woe", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "wlo", name := "Wolio", iso := "wlo", family := "Austronesian", genus := "Celebic" }
  , { walsCode := "wlf", name := "Wolof", iso := "wol", family := "Niger-Congo", genus := "Wolof" }
  , { walsCode := "wom", name := "Womo", iso := "wmx", family := "Skou", genus := "Serra Hills" }
  , { walsCode := "wor", name := "Worora", iso := "wro", family := "Worrorran", genus := "Worrorran" }
  , { walsCode := "wya", name := "Wyandot", iso := "wya", family := "Iroquoian", genus := "Northern Iroquoian" }
  , { walsCode := "xas", name := "Xasonga", iso := "kao", family := "Mande", genus := "Western Mande" }
  , { walsCode := "xav", name := "Xavánte", iso := "xav", family := "Macro-Ge", genus := "Je Central" }
  , { walsCode := "xer", name := "Xerénte", iso := "xer", family := "Macro-Ge", genus := "Je Central" }
  , { walsCode := "xho", name := "Xhosa", iso := "xho", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "xok", name := "Xokleng", iso := "xok", family := "Macro-Ge", genus := "Je Meridional" }
  , { walsCode := "xar", name := "Xârâcùù", iso := "ane", family := "Austronesian", genus := "Oceanic" }
  , { walsCode := "ygr", name := "Yagaria", iso := "ygr", family := "Trans-New Guinea", genus := "Siane-Yagaria" }
  , { walsCode := "yag", name := "Yagua", iso := "yad", family := "Peba-Yaguan", genus := "Peba-Yaguan" }
  , { walsCode := "yah", name := "Yahgan", iso := "yag", family := "Yámana", genus := "Yámana" }
  , { walsCode := "ykt", name := "Yakut", iso := "sah", family := "Altaic", genus := "Turkic" }
  , { walsCode := "yal", name := "Yale (Kosarek)", iso := "kkl", family := "Trans-New Guinea", genus := "Mek" }
  , { walsCode := "yam", name := "Yaminahua", iso := "yaa", family := "Pano-Tacanan", genus := "Panoan" }
  , { walsCode := "ybi", name := "Yamphu", iso := "ybi", family := "Sino-Tibetan", genus := "Himalayish" }
  , { walsCode := "yan", name := "Yana", iso := "ynn", family := "Hokan", genus := "Yana" }
  , { walsCode := "ynk", name := "Yankuntjatjara", iso := "kdd", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "yns", name := "Yansi", iso := "yns", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "yny", name := "Yanyuwa", iso := "jao", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "yao", name := "Yao (in Malawi)", iso := "yao", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "yap", name := "Yapese", iso := "yap", family := "Austronesian", genus := "Yapese" }
  , { walsCode := "yqy", name := "Yaqay", iso := "jaq", family := "Trans-New Guinea", genus := "Marind-Yaqay" }
  , { walsCode := "yaq", name := "Yaqui", iso := "yaq", family := "Uto-Aztecan", genus := "Cahita" }
  , { walsCode := "yar", name := "Yareba", iso := "yrb", family := "Trans-New Guinea", genus := "Yareban" }
  , { walsCode := "yrr", name := "Yaruro", iso := "yae", family := "Yaruro", genus := "Yaruro" }
  , { walsCode := "yav", name := "Yavapai", iso := "yuf", family := "Hokan", genus := "Yuman" }
  , { walsCode := "yaw", name := "Yawa", iso := "yva", family := "Yawa", genus := "Yawa" }
  , { walsCode := "ywl", name := "Yawelmani", iso := "yok", family := "Penutian", genus := "Yokuts" }
  , { walsCode := "ywr", name := "Yawuru", iso := "ywr", family := "Nyulnyulan", genus := "Nyulnyulan" }
  , { walsCode := "yay", name := "Yay", iso := "pcc", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "yyg", name := "Yaygir", iso := "xya", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "yaz", name := "Yazgulyam", iso := "yah", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "yei", name := "Yei", iso := "jei", family := "Yam", genus := "Yei" }
  , { walsCode := "ylm", name := "Yelmek", iso := "jel", family := "Bulaka River", genus := "Bulaka River" }
  , { walsCode := "yel", name := "Yelî Dnye", iso := "yle", family := "Yele", genus := "Yele" }
  , { walsCode := "yes", name := "Yessan-Mayo", iso := "yss", family := "Sepik", genus := "Tama Sepik" }
  , { walsCode := "yey", name := "Yeyi", iso := "yey", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "yiw", name := "Yi (Wuding-Luquan)", iso := "ywq", family := "Sino-Tibetan", genus := "Burmese-Lolo" }
  , { walsCode := "ydd", name := "Yiddish", iso := "ydd", family := "Indo-European", genus := "Germanic" }
  , { walsCode := "yid", name := "Yidiny", iso := "yii", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "yim", name := "Yimas", iso := "yee", family := "Ramu-Lower Sepik", genus := "Lower Sepik" }
  , { walsCode := "yin", name := "Yindjibarndi", iso := "yij", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "yng", name := "Yingkarta", iso := "yia", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "yir", name := "Yir Yoront", iso := "yyr", family := "Pama-Nyungan", genus := "Northern Pama-Nyungan" }
  , { walsCode := "yok", name := "Yokuts (Yaudanchi)", iso := "yok", family := "Penutian", genus := "Yokuts" }
  , { walsCode := "yor", name := "Yoruba", iso := "yor", family := "Niger-Congo", genus := "Defoid" }
  , { walsCode := "yct", name := "Yucatec", iso := "yua", family := "Mayan", genus := "Mayan" }
  , { walsCode := "yuc", name := "Yuchi", iso := "yuc", family := "Yuchi", genus := "Yuchi" }
  , { walsCode := "ycn", name := "Yucuna", iso := "ycn", family := "Arawakan", genus := "Japura-Colombia" }
  , { walsCode := "yko", name := "Yukaghir (Kolyma)", iso := "yux", family := "Yukaghir", genus := "Yukaghir" }
  , { walsCode := "ytu", name := "Yukaghir (Tundra)", iso := "ykg", family := "Yukaghir", genus := "Yukaghir" }
  , { walsCode := "yuk", name := "Yukulta", iso := "gcd", family := "Tangkic", genus := "Tangkic" }
  , { walsCode := "ylb", name := "Yulparija", iso := "mpj", family := "Pama-Nyungan", genus := "Western Pama-Nyungan" }
  , { walsCode := "yul", name := "Yulu", iso := "yul", family := "Central Sudanic", genus := "Bongo-Bagirmi" }
  , { walsCode := "ypk", name := "Yup'ik (Central)", iso := "esu", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "yna", name := "Yupik (Naukan)", iso := "ynk", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "yus", name := "Yupik (Siberian)", iso := "ess", family := "Eskimo-Aleut", genus := "Eskimo" }
  , { walsCode := "yrm", name := "Yurimangí", iso := "", family := "Yurimangí", genus := "Yurimangí" }
  , { walsCode := "yur", name := "Yurok", iso := "yur", family := "Algic", genus := "Yurok" }
  , { walsCode := "yuw", name := "Yuwaalaraay", iso := "kld", family := "Pama-Nyungan", genus := "Southeastern Pama-Nyungan" }
  , { walsCode := "zan", name := "Zande", iso := "zne", family := "Niger-Congo", genus := "Ubangi" }
  , { walsCode := "zpr", name := "Zaparo", iso := "zro", family := "Zaparoan", genus := "Zaparoan" }
  , { walsCode := "zai", name := "Zapotec (Isthmus)", iso := "zai", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zpi", name := "Zapotec (Ixtlan)", iso := "zpd", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zap", name := "Zapotec (Mitla)", iso := "zaw", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zaq", name := "Zapotec (Quiegolani)", iso := "zpi", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zsq", name := "Zapotec (San Lucas Quiaviní)", iso := "zab", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zya", name := "Zapotec (Yatzachi)", iso := "zav", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zzo", name := "Zapotec (Zoogocho)", iso := "zpq", family := "Oto-Manguean", genus := "Zapotecan" }
  , { walsCode := "zar", name := "Zarma", iso := "dje", family := "Songhay", genus := "Songhay" }
  , { walsCode := "zay", name := "Zayse", iso := "zay", family := "Afro-Asiatic", genus := "Ta-Ne-Omotic" }
  , { walsCode := "zaz", name := "Zazaki", iso := "diq", family := "Indo-European", genus := "Iranian" }
  , { walsCode := "zen", name := "Zenaga", iso := "zen", family := "Afro-Asiatic", genus := "Berber" }
  , { walsCode := "zhn", name := "Zhuang (Northern)", iso := "zgb", family := "Tai-Kadai", genus := "Kam-Tai" }
  , { walsCode := "zim", name := "Zimakani", iso := "zik", family := "Trans-New Guinea", genus := "Boazi" }
  , { walsCode := "zch", name := "Zoque (Chimalapa)", iso := "zoh", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "zqc", name := "Zoque (Copainalá)", iso := "zoc", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "zqo", name := "Zoque (Ostuacan)", iso := "zoc", family := "Mixe-Zoque", genus := "Mixe-Zoque" }
  , { walsCode := "zul", name := "Zulu", iso := "zul", family := "Niger-Congo", genus := "Bantu" }
  , { walsCode := "zun", name := "Zuni", iso := "zun", family := "Zuni", genus := "Zuni" }
  , { walsCode := "rgc", name := "rGyalrong (Caodeng)", iso := "jya", family := "Sino-Tibetan", genus := "Na-Qiangic" }
  , { walsCode := "eme", name := "Émérillon", iso := "eme", family := "Tupian", genus := "Maweti-Guarani" }
  , { walsCode := "omi", name := "Ömie", iso := "aom", family := "Trans-New Guinea", genus := "Koiarian" }
  ]

/-- All languages referenced in generated WALS features (1925). -/
def languages : List Language := languages_0 ++ languages_1 ++ languages_2 ++ languages_3

/-- Look up a language by WALS code. -/
def findLanguage (code : String) : Option Language :=
  languages.find? (·.walsCode == code)

end Core.WALS
