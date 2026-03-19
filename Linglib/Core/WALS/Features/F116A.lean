import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 116A: Polar Questions
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 116A`.

Chapter 116, 955 languages.
-/

namespace Core.WALS.F116A

/-- WALS 116A values. -/
inductive PolarQuestionType where
  | questionParticle  -- Question particle (585 languages)
  | interrogativeVerbMorphology  -- Interrogative verb morphology (164 languages)
  | mixtureOfPreviousTwoTypes  -- Mixture of previous two types (15 languages)
  | interrogativeWordOrder  -- Interrogative word order (13 languages)
  | absenceOfDeclarativeMorphemes  -- Absence of declarative morphemes (4 languages)
  | interrogativeIntonationOnly  -- Interrogative intonation only (173 languages)
  | noInterrogativeDeclarativeDistinction  -- No interrogative-declarative distinction (1 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PolarQuestionType) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .questionParticle }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .questionParticle }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .questionParticle }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .interrogativeVerbMorphology }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .interrogativeVerbMorphology }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .questionParticle }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .questionParticle }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .questionParticle }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .interrogativeVerbMorphology }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .questionParticle }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .interrogativeIntonationOnly }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .interrogativeVerbMorphology }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .questionParticle }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .questionParticle }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .questionParticle }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .questionParticle }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .questionParticle }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .questionParticle }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .questionParticle }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .interrogativeIntonationOnly }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .questionParticle }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .questionParticle }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .questionParticle }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .questionParticle }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .interrogativeIntonationOnly }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .questionParticle }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .questionParticle }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .questionParticle }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .questionParticle }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .questionParticle }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .questionParticle }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .questionParticle }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .questionParticle }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .interrogativeVerbMorphology }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .questionParticle }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .interrogativeIntonationOnly }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .questionParticle }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .questionParticle }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .interrogativeVerbMorphology }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .interrogativeIntonationOnly }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .questionParticle }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .questionParticle }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .interrogativeIntonationOnly }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .questionParticle }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .interrogativeIntonationOnly }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .questionParticle }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .questionParticle }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .questionParticle }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .interrogativeVerbMorphology }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .questionParticle }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .questionParticle }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .interrogativeVerbMorphology }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .interrogativeIntonationOnly }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .interrogativeIntonationOnly }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .interrogativeIntonationOnly }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .questionParticle }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .questionParticle }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .questionParticle }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .interrogativeVerbMorphology }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .questionParticle }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .interrogativeVerbMorphology }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .questionParticle }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .questionParticle }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .questionParticle }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .questionParticle }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .questionParticle }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .interrogativeIntonationOnly }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .questionParticle }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .questionParticle }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .interrogativeIntonationOnly }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .interrogativeIntonationOnly }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .questionParticle }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .questionParticle }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .questionParticle }
  , { walsCode := "bkn", language := "Bakundu", iso := "bdu", value := .questionParticle }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .interrogativeVerbMorphology }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .questionParticle }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .questionParticle }
  , { walsCode := "bgz", language := "Banggi", iso := "bdg", value := .interrogativeIntonationOnly }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .interrogativeVerbMorphology }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .interrogativeIntonationOnly }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .questionParticle }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .interrogativeVerbMorphology }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .questionParticle }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .questionParticle }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .interrogativeIntonationOnly }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .questionParticle }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .questionParticle }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .questionParticle }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .questionParticle }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .interrogativeVerbMorphology }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .questionParticle }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .interrogativeVerbMorphology }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .questionParticle }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .questionParticle }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .questionParticle }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .questionParticle }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .questionParticle }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .interrogativeVerbMorphology }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .questionParticle }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .interrogativeVerbMorphology }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .questionParticle }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .interrogativeIntonationOnly }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .interrogativeVerbMorphology }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .questionParticle }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .interrogativeIntonationOnly }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .interrogativeVerbMorphology }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .questionParticle }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .interrogativeIntonationOnly }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .questionParticle }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .interrogativeVerbMorphology }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .interrogativeVerbMorphology }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .questionParticle }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .interrogativeVerbMorphology }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .questionParticle }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .questionParticle }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .questionParticle }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .questionParticle }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .questionParticle }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .questionParticle }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .questionParticle }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .questionParticle }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .questionParticle }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .questionParticle }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .interrogativeIntonationOnly }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .questionParticle }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .interrogativeVerbMorphology }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .interrogativeVerbMorphology }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .interrogativeVerbMorphology }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .questionParticle }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .interrogativeIntonationOnly }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .questionParticle }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .interrogativeIntonationOnly }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .interrogativeIntonationOnly }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .questionParticle }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .questionParticle }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .interrogativeVerbMorphology }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .questionParticle }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .questionParticle }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .interrogativeVerbMorphology }
  , { walsCode := "car", language := "Carib", iso := "car", value := .interrogativeVerbMorphology }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .interrogativeIntonationOnly }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .questionParticle }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .questionParticle }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .interrogativeIntonationOnly }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .questionParticle }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .questionParticle }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .questionParticle }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .interrogativeVerbMorphology }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .questionParticle }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .questionParticle }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .questionParticle }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .interrogativeVerbMorphology }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .questionParticle }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .questionParticle }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .questionParticle }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .questionParticle }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .questionParticle }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .interrogativeIntonationOnly }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .questionParticle }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .interrogativeVerbMorphology }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .questionParticle }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .questionParticle }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .questionParticle }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .questionParticle }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .interrogativeIntonationOnly }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .questionParticle }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .interrogativeIntonationOnly }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .interrogativeVerbMorphology }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .interrogativeVerbMorphology }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .questionParticle }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .interrogativeVerbMorphology }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .questionParticle }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .questionParticle }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .questionParticle }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .questionParticle }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .questionParticle }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .questionParticle }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .questionParticle }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .interrogativeVerbMorphology }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .interrogativeIntonationOnly }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .interrogativeWordOrder }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .questionParticle }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .questionParticle }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .questionParticle }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .interrogativeVerbMorphology }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .interrogativeWordOrder }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .questionParticle }
  , { walsCode := "des", language := "Desano", iso := "des", value := .interrogativeVerbMorphology }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .interrogativeVerbMorphology }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .interrogativeIntonationOnly }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .questionParticle }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .interrogativeVerbMorphology }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .interrogativeVerbMorphology }
  , { walsCode := "dng", language := "Ding", iso := "diz", value := .questionParticle }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .absenceOfDeclarativeMorphemes }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .interrogativeIntonationOnly }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .interrogativeIntonationOnly }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .interrogativeIntonationOnly }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .questionParticle }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .interrogativeIntonationOnly }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .questionParticle }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .questionParticle }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .questionParticle }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .questionParticle }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .questionParticle }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .questionParticle }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .questionParticle }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .questionParticle }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .questionParticle }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .interrogativeWordOrder }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .questionParticle }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .questionParticle }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .interrogativeIntonationOnly }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .questionParticle }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .questionParticle }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .interrogativeVerbMorphology }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .interrogativeIntonationOnly }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .interrogativeVerbMorphology }
  , { walsCode := "ene", language := "Enets", iso := "", value := .interrogativeVerbMorphology }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .questionParticle }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .interrogativeIntonationOnly }
  , { walsCode := "eng", language := "English", iso := "eng", value := .interrogativeWordOrder }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .interrogativeVerbMorphology }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .questionParticle }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .questionParticle }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .questionParticle }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .questionParticle }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .questionParticle }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .questionParticle }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .questionParticle }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .questionParticle }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .interrogativeVerbMorphology }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .interrogativeIntonationOnly }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .questionParticle }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .interrogativeVerbMorphology }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .interrogativeVerbMorphology }
  , { walsCode := "fre", language := "French", iso := "fra", value := .questionParticle }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .interrogativeWordOrder }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .questionParticle }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .interrogativeVerbMorphology }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .questionParticle }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .questionParticle }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .interrogativeVerbMorphology }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .interrogativeVerbMorphology }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .interrogativeVerbMorphology }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .interrogativeVerbMorphology }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .questionParticle }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .interrogativeVerbMorphology }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .questionParticle }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .questionParticle }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .questionParticle }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .questionParticle }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .interrogativeIntonationOnly }
  , { walsCode := "ger", language := "German", iso := "deu", value := .interrogativeWordOrder }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .interrogativeVerbMorphology }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .questionParticle }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .questionParticle }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .questionParticle }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .questionParticle }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .interrogativeVerbMorphology }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .questionParticle }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .questionParticle }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .questionParticle }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .interrogativeVerbMorphology }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .interrogativeIntonationOnly }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .questionParticle }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .interrogativeIntonationOnly }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .questionParticle }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .questionParticle }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .questionParticle }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .interrogativeIntonationOnly }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .questionParticle }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .interrogativeIntonationOnly }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .interrogativeIntonationOnly }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .interrogativeVerbMorphology }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .interrogativeIntonationOnly }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .questionParticle }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .questionParticle }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .questionParticle }
  , { walsCode := "gdb", language := "Gutob", iso := "gbj", value := .interrogativeVerbMorphology }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .questionParticle }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .interrogativeVerbMorphology }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .questionParticle }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .questionParticle }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .questionParticle }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .questionParticle }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .interrogativeIntonationOnly }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .interrogativeIntonationOnly }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .questionParticle }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .questionParticle }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .questionParticle }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .questionParticle }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .interrogativeIntonationOnly }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .questionParticle }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .questionParticle }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .questionParticle }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .interrogativeIntonationOnly }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .questionParticle }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .interrogativeVerbMorphology }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .interrogativeIntonationOnly }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .questionParticle }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .interrogativeIntonationOnly }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .questionParticle }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .questionParticle }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .interrogativeVerbMorphology }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .interrogativeWordOrder }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .questionParticle }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .questionParticle }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .interrogativeVerbMorphology }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .questionParticle }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .questionParticle }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .interrogativeIntonationOnly }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .questionParticle }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .interrogativeVerbMorphology }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .questionParticle }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .questionParticle }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .questionParticle }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .questionParticle }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .interrogativeVerbMorphology }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .interrogativeVerbMorphology }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .interrogativeIntonationOnly }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .questionParticle }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .interrogativeIntonationOnly }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .questionParticle }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .interrogativeVerbMorphology }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .questionParticle }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .questionParticle }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .questionParticle }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .questionParticle }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .questionParticle }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .interrogativeIntonationOnly }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .questionParticle }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .questionParticle }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .questionParticle }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .questionParticle }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .interrogativeVerbMorphology }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .questionParticle }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .interrogativeIntonationOnly }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .questionParticle }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .absenceOfDeclarativeMorphemes }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .questionParticle }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .interrogativeIntonationOnly }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .questionParticle }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .interrogativeVerbMorphology }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .interrogativeVerbMorphology }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .interrogativeIntonationOnly }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .interrogativeIntonationOnly }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .interrogativeIntonationOnly }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .interrogativeVerbMorphology }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .interrogativeVerbMorphology }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .questionParticle }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .questionParticle }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .questionParticle }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .interrogativeVerbMorphology }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .questionParticle }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .interrogativeVerbMorphology }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .questionParticle }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .interrogativeVerbMorphology }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .questionParticle }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .questionParticle }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .questionParticle }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .questionParticle }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .questionParticle }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .questionParticle }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .questionParticle }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .questionParticle }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .interrogativeIntonationOnly }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .questionParticle }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .questionParticle }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .questionParticle }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .interrogativeIntonationOnly }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .questionParticle }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .interrogativeVerbMorphology }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .questionParticle }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .questionParticle }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .questionParticle }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .questionParticle }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .questionParticle }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .questionParticle }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .questionParticle }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .interrogativeVerbMorphology }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .questionParticle }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .questionParticle }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .interrogativeVerbMorphology }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .questionParticle }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .questionParticle }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .questionParticle }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .interrogativeIntonationOnly }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .interrogativeIntonationOnly }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .interrogativeVerbMorphology }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .questionParticle }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .questionParticle }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .interrogativeVerbMorphology }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .questionParticle }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .questionParticle }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .interrogativeIntonationOnly }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .questionParticle }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .questionParticle }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .questionParticle }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .interrogativeVerbMorphology }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .questionParticle }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .questionParticle }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .interrogativeVerbMorphology }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .interrogativeVerbMorphology }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .questionParticle }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .interrogativeIntonationOnly }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .interrogativeVerbMorphology }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .interrogativeIntonationOnly }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .questionParticle }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .interrogativeVerbMorphology }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .interrogativeVerbMorphology }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .questionParticle }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .questionParticle }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .questionParticle }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .interrogativeIntonationOnly }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .questionParticle }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .interrogativeIntonationOnly }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .questionParticle }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .interrogativeVerbMorphology }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .interrogativeIntonationOnly }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .questionParticle }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .interrogativeVerbMorphology }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .questionParticle }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .interrogativeIntonationOnly }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .interrogativeVerbMorphology }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .interrogativeIntonationOnly }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .questionParticle }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .interrogativeIntonationOnly }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .interrogativeIntonationOnly }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .questionParticle }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .questionParticle }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .interrogativeVerbMorphology }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .questionParticle }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .questionParticle }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .interrogativeVerbMorphology }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .questionParticle }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .interrogativeIntonationOnly }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .questionParticle }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .interrogativeVerbMorphology }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .questionParticle }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .questionParticle }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .questionParticle }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .questionParticle }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .questionParticle }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .interrogativeIntonationOnly }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .questionParticle }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .questionParticle }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .questionParticle }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .questionParticle }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .interrogativeIntonationOnly }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .questionParticle }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .questionParticle }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .questionParticle }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .questionParticle }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .questionParticle }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .questionParticle }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .questionParticle }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .questionParticle }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .interrogativeVerbMorphology }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .interrogativeVerbMorphology }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .questionParticle }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .interrogativeIntonationOnly }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .interrogativeVerbMorphology }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .questionParticle }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .questionParticle }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .interrogativeIntonationOnly }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .questionParticle }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .interrogativeIntonationOnly }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .interrogativeVerbMorphology }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .questionParticle }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .questionParticle }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .questionParticle }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .interrogativeIntonationOnly }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .questionParticle }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .interrogativeIntonationOnly }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .questionParticle }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .questionParticle }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .questionParticle }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .interrogativeVerbMorphology }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .questionParticle }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .interrogativeIntonationOnly }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .questionParticle }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .interrogativeVerbMorphology }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .questionParticle }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .questionParticle }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .questionParticle }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .questionParticle }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .questionParticle }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .questionParticle }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .questionParticle }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .interrogativeIntonationOnly }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .questionParticle }
  ]

private def allData_1 : List (Datapoint PolarQuestionType) :=
  [ { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .questionParticle }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .questionParticle }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .questionParticle }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .questionParticle }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .interrogativeIntonationOnly }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .interrogativeVerbMorphology }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .interrogativeVerbMorphology }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .questionParticle }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .questionParticle }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .questionParticle }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .interrogativeWordOrder }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .interrogativeVerbMorphology }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .questionParticle }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .interrogativeIntonationOnly }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .questionParticle }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .interrogativeIntonationOnly }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .questionParticle }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .interrogativeIntonationOnly }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .interrogativeIntonationOnly }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .questionParticle }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .questionParticle }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .questionParticle }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .interrogativeVerbMorphology }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .questionParticle }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .interrogativeIntonationOnly }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .questionParticle }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .questionParticle }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .interrogativeVerbMorphology }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .interrogativeVerbMorphology }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .interrogativeVerbMorphology }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .questionParticle }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .questionParticle }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .questionParticle }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .questionParticle }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .questionParticle }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .questionParticle }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .questionParticle }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .questionParticle }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .questionParticle }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .questionParticle }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .questionParticle }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .interrogativeIntonationOnly }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .questionParticle }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .questionParticle }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .questionParticle }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .interrogativeIntonationOnly }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .interrogativeVerbMorphology }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .questionParticle }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .interrogativeIntonationOnly }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .questionParticle }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .questionParticle }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .questionParticle }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .interrogativeVerbMorphology }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .questionParticle }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .questionParticle }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .interrogativeVerbMorphology }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .questionParticle }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .questionParticle }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noInterrogativeDeclarativeDistinction }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .questionParticle }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .questionParticle }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .questionParticle }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .questionParticle }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .questionParticle }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .questionParticle }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .questionParticle }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .questionParticle }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .questionParticle }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .questionParticle }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .interrogativeVerbMorphology }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .questionParticle }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .questionParticle }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .questionParticle }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .questionParticle }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .questionParticle }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .questionParticle }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .questionParticle }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .interrogativeIntonationOnly }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .questionParticle }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .questionParticle }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .interrogativeVerbMorphology }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .questionParticle }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .interrogativeIntonationOnly }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .questionParticle }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .questionParticle }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .questionParticle }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .interrogativeIntonationOnly }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .questionParticle }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .questionParticle }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .questionParticle }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .questionParticle }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .questionParticle }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .interrogativeIntonationOnly }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .interrogativeIntonationOnly }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .interrogativeIntonationOnly }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .interrogativeIntonationOnly }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .questionParticle }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .interrogativeVerbMorphology }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .questionParticle }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .questionParticle }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .interrogativeIntonationOnly }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .questionParticle }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .interrogativeVerbMorphology }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .questionParticle }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .questionParticle }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .questionParticle }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .interrogativeIntonationOnly }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .interrogativeVerbMorphology }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .questionParticle }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .questionParticle }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .questionParticle }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .questionParticle }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .questionParticle }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .questionParticle }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .interrogativeIntonationOnly }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .interrogativeIntonationOnly }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .interrogativeVerbMorphology }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .interrogativeIntonationOnly }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .questionParticle }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .questionParticle }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .questionParticle }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .questionParticle }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .questionParticle }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .questionParticle }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .interrogativeIntonationOnly }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .questionParticle }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .questionParticle }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .interrogativeVerbMorphology }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .questionParticle }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .interrogativeIntonationOnly }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .questionParticle }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .questionParticle }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .interrogativeIntonationOnly }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .questionParticle }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .questionParticle }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .interrogativeIntonationOnly }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .interrogativeIntonationOnly }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .interrogativeIntonationOnly }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .questionParticle }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .questionParticle }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .questionParticle }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .interrogativeIntonationOnly }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .questionParticle }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .questionParticle }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .questionParticle }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .questionParticle }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .questionParticle }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .interrogativeVerbMorphology }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .questionParticle }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .questionParticle }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .interrogativeWordOrder }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .interrogativeIntonationOnly }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .interrogativeVerbMorphology }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .questionParticle }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .questionParticle }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .questionParticle }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .interrogativeVerbMorphology }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .questionParticle }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .questionParticle }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .questionParticle }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .questionParticle }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .questionParticle }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .questionParticle }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .questionParticle }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .questionParticle }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .questionParticle }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .questionParticle }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .questionParticle }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .interrogativeIntonationOnly }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .interrogativeIntonationOnly }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .questionParticle }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .interrogativeIntonationOnly }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .interrogativeIntonationOnly }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .questionParticle }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .interrogativeIntonationOnly }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .interrogativeWordOrder }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .questionParticle }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .questionParticle }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .questionParticle }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .interrogativeIntonationOnly }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .interrogativeVerbMorphology }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .interrogativeVerbMorphology }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .interrogativeVerbMorphology }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .questionParticle }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .questionParticle }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .questionParticle }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .interrogativeIntonationOnly }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .questionParticle }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .questionParticle }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .interrogativeIntonationOnly }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .questionParticle }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .interrogativeIntonationOnly }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .questionParticle }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .questionParticle }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .interrogativeVerbMorphology }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .interrogativeVerbMorphology }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .interrogativeIntonationOnly }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .questionParticle }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .questionParticle }
  , { walsCode := "puq", language := "Puquina", iso := "puq", value := .absenceOfDeclarativeMorphemes }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .interrogativeVerbMorphology }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .interrogativeVerbMorphology }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .interrogativeIntonationOnly }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .interrogativeVerbMorphology }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .interrogativeVerbMorphology }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .interrogativeVerbMorphology }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .questionParticle }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .interrogativeVerbMorphology }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .questionParticle }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .questionParticle }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .interrogativeVerbMorphology }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .questionParticle }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .questionParticle }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .questionParticle }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .questionParticle }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .interrogativeIntonationOnly }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .questionParticle }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .questionParticle }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .interrogativeIntonationOnly }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .interrogativeIntonationOnly }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .questionParticle }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .interrogativeVerbMorphology }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .interrogativeIntonationOnly }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .questionParticle }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .questionParticle }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .interrogativeIntonationOnly }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .questionParticle }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .interrogativeVerbMorphology }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .interrogativeVerbMorphology }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .questionParticle }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .questionParticle }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .questionParticle }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .interrogativeVerbMorphology }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .interrogativeVerbMorphology }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .interrogativeIntonationOnly }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .questionParticle }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .interrogativeVerbMorphology }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .questionParticle }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .interrogativeIntonationOnly }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .interrogativeIntonationOnly }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .questionParticle }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .questionParticle }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .interrogativeIntonationOnly }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .interrogativeVerbMorphology }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .questionParticle }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .questionParticle }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .interrogativeIntonationOnly }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .questionParticle }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .interrogativeIntonationOnly }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .questionParticle }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .interrogativeIntonationOnly }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .interrogativeVerbMorphology }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .questionParticle }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .questionParticle }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .interrogativeVerbMorphology }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .questionParticle }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .interrogativeVerbMorphology }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .interrogativeIntonationOnly }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .questionParticle }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .questionParticle }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .questionParticle }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .questionParticle }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .questionParticle }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .questionParticle }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .questionParticle }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .questionParticle }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .questionParticle }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .questionParticle }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .questionParticle }
  , { walsCode := "so", language := "So", iso := "teu", value := .questionParticle }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .questionParticle }
  , { walsCode := "som", language := "Somali", iso := "som", value := .questionParticle }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .questionParticle }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .questionParticle }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .questionParticle }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .interrogativeIntonationOnly }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .interrogativeWordOrder }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .questionParticle }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .questionParticle }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .questionParticle }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .interrogativeIntonationOnly }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .interrogativeVerbMorphology }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .interrogativeIntonationOnly }
  , { walsCode := "slg", language := "Sulung", iso := "suv", value := .questionParticle }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .questionParticle }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .questionParticle }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .questionParticle }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .questionParticle }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .interrogativeWordOrder }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .interrogativeIntonationOnly }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .interrogativeIntonationOnly }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .questionParticle }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .questionParticle }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .questionParticle }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .interrogativeIntonationOnly }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .questionParticle }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .questionParticle }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .questionParticle }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .questionParticle }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .questionParticle }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .interrogativeVerbMorphology }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .interrogativeVerbMorphology }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .questionParticle }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .questionParticle }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .interrogativeIntonationOnly }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .mixtureOfPreviousTwoTypes }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .questionParticle }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .questionParticle }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .questionParticle }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .questionParticle }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .interrogativeVerbMorphology }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .questionParticle }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .interrogativeIntonationOnly }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .questionParticle }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .interrogativeIntonationOnly }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .questionParticle }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .questionParticle }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .interrogativeIntonationOnly }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .questionParticle }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .questionParticle }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .questionParticle }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .questionParticle }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .questionParticle }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .questionParticle }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .interrogativeVerbMorphology }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .questionParticle }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .interrogativeIntonationOnly }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .questionParticle }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .questionParticle }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .questionParticle }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .interrogativeVerbMorphology }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .questionParticle }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .interrogativeIntonationOnly }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .questionParticle }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .questionParticle }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .interrogativeIntonationOnly }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .interrogativeIntonationOnly }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .interrogativeIntonationOnly }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .questionParticle }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .questionParticle }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .interrogativeVerbMorphology }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .questionParticle }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .questionParticle }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .interrogativeVerbMorphology }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .interrogativeVerbMorphology }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .questionParticle }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .interrogativeIntonationOnly }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .questionParticle }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .questionParticle }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .interrogativeIntonationOnly }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .questionParticle }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .questionParticle }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .interrogativeVerbMorphology }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .questionParticle }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .questionParticle }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .interrogativeVerbMorphology }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .questionParticle }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .questionParticle }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .questionParticle }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .interrogativeVerbMorphology }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .questionParticle }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .interrogativeIntonationOnly }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .questionParticle }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .interrogativeVerbMorphology }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .questionParticle }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .questionParticle }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .questionParticle }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .interrogativeVerbMorphology }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .interrogativeIntonationOnly }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .questionParticle }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .questionParticle }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .interrogativeIntonationOnly }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .interrogativeVerbMorphology }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .questionParticle }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .questionParticle }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .questionParticle }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .questionParticle }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .interrogativeIntonationOnly }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .interrogativeVerbMorphology }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .questionParticle }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .interrogativeVerbMorphology }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .questionParticle }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .interrogativeIntonationOnly }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .questionParticle }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .questionParticle }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .interrogativeVerbMorphology }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .questionParticle }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .questionParticle }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .interrogativeVerbMorphology }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .interrogativeVerbMorphology }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .interrogativeVerbMorphology }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .interrogativeWordOrder }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .interrogativeIntonationOnly }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .questionParticle }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .interrogativeIntonationOnly }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .interrogativeIntonationOnly }
  , { walsCode := "was", language := "Washo", iso := "was", value := .questionParticle }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .questionParticle }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .interrogativeVerbMorphology }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .questionParticle }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .questionParticle }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .questionParticle }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .interrogativeIntonationOnly }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .interrogativeIntonationOnly }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .questionParticle }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .questionParticle }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .questionParticle }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .questionParticle }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .questionParticle }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .interrogativeVerbMorphology }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .interrogativeIntonationOnly }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .questionParticle }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .questionParticle }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .questionParticle }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .questionParticle }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .questionParticle }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .questionParticle }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .interrogativeVerbMorphology }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .interrogativeIntonationOnly }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .questionParticle }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .questionParticle }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .questionParticle }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .questionParticle }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .questionParticle }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .interrogativeIntonationOnly }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .questionParticle }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .interrogativeIntonationOnly }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .questionParticle }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .interrogativeIntonationOnly }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .questionParticle }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .interrogativeIntonationOnly }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .questionParticle }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .questionParticle }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .questionParticle }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .questionParticle }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .questionParticle }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .questionParticle }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .questionParticle }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .questionParticle }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .interrogativeIntonationOnly }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .absenceOfDeclarativeMorphemes }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .interrogativeIntonationOnly }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .questionParticle }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .interrogativeIntonationOnly }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .interrogativeVerbMorphology }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .questionParticle }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .questionParticle }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .questionParticle }
  ]

/-- Complete WALS 116A dataset (955 languages). -/
def allData : List (Datapoint PolarQuestionType) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 955 := by native_decide

theorem count_questionParticle :
    (allData.filter (·.value == .questionParticle)).length = 585 := by native_decide
theorem count_interrogativeVerbMorphology :
    (allData.filter (·.value == .interrogativeVerbMorphology)).length = 164 := by native_decide
theorem count_mixtureOfPreviousTwoTypes :
    (allData.filter (·.value == .mixtureOfPreviousTwoTypes)).length = 15 := by native_decide
theorem count_interrogativeWordOrder :
    (allData.filter (·.value == .interrogativeWordOrder)).length = 13 := by native_decide
theorem count_absenceOfDeclarativeMorphemes :
    (allData.filter (·.value == .absenceOfDeclarativeMorphemes)).length = 4 := by native_decide
theorem count_interrogativeIntonationOnly :
    (allData.filter (·.value == .interrogativeIntonationOnly)).length = 173 := by native_decide
theorem count_noInterrogativeDeclarativeDistinction :
    (allData.filter (·.value == .noInterrogativeDeclarativeDistinction)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F116A
