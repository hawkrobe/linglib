import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 13A: Tone
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 13A`.

Chapter 13, 527 languages.
-/

namespace Core.WALS.F13A

/-- WALS 13A values. -/
inductive Tone where
  | noTones  -- No tones (307 languages)
  | simpleToneSystem  -- Simple tone system (132 languages)
  | complexToneSystem  -- Complex tone system (88 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint Tone) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .complexToneSystem }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .simpleToneSystem }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noTones }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .simpleToneSystem }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .complexToneSystem }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .simpleToneSystem }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .noTones }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .simpleToneSystem }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .simpleToneSystem }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .simpleToneSystem }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .noTones }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noTones }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noTones }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noTones }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .noTones }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .simpleToneSystem }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noTones }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noTones }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .simpleToneSystem }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .noTones }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .complexToneSystem }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .simpleToneSystem }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .simpleToneSystem }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .complexToneSystem }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .complexToneSystem }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .noTones }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noTones }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .noTones }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noTones }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noTones }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noTones }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noTones }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noTones }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noTones }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noTones }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noTones }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .noTones }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noTones }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .simpleToneSystem }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noTones }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noTones }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .complexToneSystem }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .complexToneSystem }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .noTones }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .noTones }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .simpleToneSystem }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .noTones }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .noTones }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .complexToneSystem }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noTones }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noTones }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noTones }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noTones }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .simpleToneSystem }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .simpleToneSystem }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .simpleToneSystem }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .noTones }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noTones }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noTones }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .simpleToneSystem }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .complexToneSystem }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .noTones }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .complexToneSystem }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .simpleToneSystem }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noTones }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noTones }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noTones }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .noTones }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noTones }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noTones }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .complexToneSystem }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noTones }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .complexToneSystem }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .simpleToneSystem }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .simpleToneSystem }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noTones }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noTones }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noTones }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noTones }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .complexToneSystem }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noTones }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noTones }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noTones }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .simpleToneSystem }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noTones }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .complexToneSystem }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .noTones }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .simpleToneSystem }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .noTones }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .complexToneSystem }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .complexToneSystem }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .complexToneSystem }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .simpleToneSystem }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noTones }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noTones }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .simpleToneSystem }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noTones }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noTones }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noTones }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noTones }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .simpleToneSystem }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .simpleToneSystem }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .simpleToneSystem }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noTones }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .simpleToneSystem }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .noTones }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .complexToneSystem }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .simpleToneSystem }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noTones }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .noTones }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .simpleToneSystem }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noTones }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .complexToneSystem }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noTones }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noTones }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .complexToneSystem }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noTones }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .noTones }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .complexToneSystem }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .complexToneSystem }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noTones }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .complexToneSystem }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noTones }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .simpleToneSystem }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .complexToneSystem }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .simpleToneSystem }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noTones }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noTones }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .noTones }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noTones }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .simpleToneSystem }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .complexToneSystem }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .noTones }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .simpleToneSystem }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .complexToneSystem }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noTones }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noTones }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noTones }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .simpleToneSystem }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .simpleToneSystem }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .complexToneSystem }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .simpleToneSystem }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .complexToneSystem }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noTones }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noTones }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .simpleToneSystem }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .complexToneSystem }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noTones }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noTones }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noTones }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .noTones }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .complexToneSystem }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noTones }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noTones }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noTones }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .complexToneSystem }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .complexToneSystem }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .simpleToneSystem }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noTones }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .complexToneSystem }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .simpleToneSystem }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .simpleToneSystem }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .simpleToneSystem }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noTones }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .noTones }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noTones }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noTones }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .complexToneSystem }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .simpleToneSystem }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noTones }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .simpleToneSystem }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noTones }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noTones }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noTones }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noTones }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noTones }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noTones }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .simpleToneSystem }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .simpleToneSystem }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .simpleToneSystem }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noTones }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noTones }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noTones }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .simpleToneSystem }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noTones }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noTones }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .simpleToneSystem }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noTones }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .noTones }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .simpleToneSystem }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .noTones }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noTones }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .simpleToneSystem }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .noTones }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noTones }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noTones }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noTones }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .noTones }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .complexToneSystem }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .simpleToneSystem }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .complexToneSystem }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noTones }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .complexToneSystem }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noTones }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .noTones }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .simpleToneSystem }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noTones }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .simpleToneSystem }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noTones }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .simpleToneSystem }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .complexToneSystem }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .simpleToneSystem }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noTones }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noTones }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .complexToneSystem }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noTones }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .noTones }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .simpleToneSystem }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .complexToneSystem }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noTones }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .simpleToneSystem }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noTones }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noTones }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .noTones }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noTones }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noTones }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .simpleToneSystem }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noTones }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .simpleToneSystem }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noTones }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noTones }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .simpleToneSystem }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .simpleToneSystem }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noTones }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .complexToneSystem }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .complexToneSystem }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noTones }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .complexToneSystem }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .simpleToneSystem }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noTones }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .complexToneSystem }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .noTones }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .simpleToneSystem }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noTones }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noTones }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .noTones }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noTones }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .simpleToneSystem }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .noTones }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noTones }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .complexToneSystem }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .complexToneSystem }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .simpleToneSystem }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noTones }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .simpleToneSystem }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noTones }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .simpleToneSystem }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .noTones }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noTones }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noTones }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noTones }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .noTones }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noTones }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .complexToneSystem }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noTones }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noTones }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .complexToneSystem }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .complexToneSystem }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .simpleToneSystem }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .simpleToneSystem }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noTones }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .simpleToneSystem }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noTones }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noTones }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .complexToneSystem }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .complexToneSystem }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noTones }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .simpleToneSystem }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .noTones }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noTones }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .simpleToneSystem }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .complexToneSystem }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .complexToneSystem }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .simpleToneSystem }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .simpleToneSystem }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noTones }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noTones }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noTones }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noTones }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .complexToneSystem }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .complexToneSystem }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noTones }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noTones }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noTones }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noTones }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .noTones }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noTones }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .simpleToneSystem }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noTones }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noTones }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noTones }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noTones }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .noTones }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noTones }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .simpleToneSystem }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .complexToneSystem }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .complexToneSystem }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .noTones }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .simpleToneSystem }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .simpleToneSystem }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .complexToneSystem }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .complexToneSystem }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noTones }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .noTones }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .complexToneSystem }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .complexToneSystem }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .noTones }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .simpleToneSystem }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .simpleToneSystem }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noTones }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .simpleToneSystem }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .complexToneSystem }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noTones }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .simpleToneSystem }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noTones }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .noTones }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noTones }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .complexToneSystem }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .complexToneSystem }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noTones }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .noTones }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .simpleToneSystem }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .simpleToneSystem }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .simpleToneSystem }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .complexToneSystem }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .complexToneSystem }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .simpleToneSystem }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noTones }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .noTones }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noTones }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .noTones }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noTones }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noTones }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .complexToneSystem }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noTones }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .simpleToneSystem }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .noTones }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .simpleToneSystem }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .simpleToneSystem }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .simpleToneSystem }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .complexToneSystem }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .simpleToneSystem }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .complexToneSystem }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noTones }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noTones }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .simpleToneSystem }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .simpleToneSystem }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .complexToneSystem }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .simpleToneSystem }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noTones }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .simpleToneSystem }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .simpleToneSystem }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noTones }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .simpleToneSystem }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .noTones }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .complexToneSystem }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .simpleToneSystem }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noTones }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .noTones }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noTones }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .noTones }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .noTones }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noTones }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .simpleToneSystem }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noTones }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .simpleToneSystem }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .simpleToneSystem }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noTones }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .complexToneSystem }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .simpleToneSystem }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noTones }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .complexToneSystem }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noTones }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noTones }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noTones }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noTones }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .noTones }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noTones }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .noTones }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .simpleToneSystem }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noTones }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noTones }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .simpleToneSystem }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noTones }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .noTones }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .noTones }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .noTones }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noTones }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noTones }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .simpleToneSystem }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .noTones }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .simpleToneSystem }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .simpleToneSystem }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noTones }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .noTones }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noTones }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noTones }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noTones }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .complexToneSystem }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noTones }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .complexToneSystem }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .simpleToneSystem }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noTones }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noTones }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noTones }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .noTones }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .noTones }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noTones }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .simpleToneSystem }
  , { walsCode := "som", language := "Somali", iso := "som", value := .simpleToneSystem }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .noTones }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .noTones }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noTones }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noTones }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .simpleToneSystem }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .simpleToneSystem }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .complexToneSystem }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .complexToneSystem }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noTones }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .noTones }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noTones }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noTones }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noTones }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .complexToneSystem }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .simpleToneSystem }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .simpleToneSystem }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .complexToneSystem }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noTones }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .noTones }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .noTones }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .simpleToneSystem }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noTones }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .simpleToneSystem }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .simpleToneSystem }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .complexToneSystem }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noTones }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .complexToneSystem }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .simpleToneSystem }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .complexToneSystem }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noTones }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noTones }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .noTones }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .simpleToneSystem }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noTones }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .complexToneSystem }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .simpleToneSystem }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .noTones }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noTones }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noTones }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .simpleToneSystem }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .noTones }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noTones }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noTones }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .noTones }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noTones }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .noTones }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noTones }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noTones }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noTones }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noTones }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .noTones }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .simpleToneSystem }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .simpleToneSystem }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noTones }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noTones }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noTones }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .noTones }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .complexToneSystem }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .simpleToneSystem }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .simpleToneSystem }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noTones }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .noTones }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noTones }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .noTones }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noTones }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noTones }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noTones }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noTones }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noTones }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noTones }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .noTones }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noTones }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noTones }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .noTones }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noTones }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noTones }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .noTones }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noTones }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .complexToneSystem }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .simpleToneSystem }
  ]

private def allData_1 : List (Datapoint Tone) :=
  [ { walsCode := "yag", language := "Yagua", iso := "yad", value := .simpleToneSystem }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noTones }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .noTones }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .noTones }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noTones }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .simpleToneSystem }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noTones }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .noTones }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .complexToneSystem }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noTones }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noTones }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .simpleToneSystem }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noTones }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noTones }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .complexToneSystem }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .simpleToneSystem }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noTones }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .noTones }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noTones }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .noTones }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .complexToneSystem }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .noTones }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noTones }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .simpleToneSystem }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noTones }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .simpleToneSystem }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noTones }
  ]

/-- Complete WALS 13A dataset (527 languages). -/
def allData : List (Datapoint Tone) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 527 := by native_decide

theorem count_noTones :
    (allData.filter (·.value == .noTones)).length = 307 := by native_decide
theorem count_simpleToneSystem :
    (allData.filter (·.value == .simpleToneSystem)).length = 132 := by native_decide
theorem count_complexToneSystem :
    (allData.filter (·.value == .complexToneSystem)).length = 88 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F13A
