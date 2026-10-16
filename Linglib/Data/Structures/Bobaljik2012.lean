module

public import Linglib.Data.Structures.Schema

/-!
# `Bobaljik2012`: language sample

Auto-generated from `Linglib/Data/Structures/Bobaljik2012.json` by `scripts/gen_structures.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in
`namespace Bobaljik2012.Structures`.
-/

@[expose] public section

namespace Bobaljik2012.Structures

open Data.Structures

/-- region: The broad geographic region under which the table groups the language (p. 229). -/
inductive Region where
  /-- `Africa`: Africa -/
  | africa
  /-- `Eurasia`: Eurasia -/
  | eurasia
  /-- `E Asia`: East Asia -/
  | eAsia
  /-- `Pacific`: the Pacific -/
  | pacific
  /-- `Americas`: the Americas -/
  | americas
  deriving DecidableEq, Repr

/-- CMPR TYP: The type of comparative construction the descriptions consulted indicate (pp. 229-230). -/
inductive CmprTyp where
  /-- `EX`: an 'exceed' comparative, with a verb meaning 'exceed' or 'surpass' -/
  | exceed
  /-- `CN`: a conjoined comparative, two conjoined clauses -/
  | conjoined
  /-- `ST`: a standard comparative, monoclausal with a marked standard of comparison -/
  | standard
  /-- `OTH`: none of the three main types -/
  | other
  deriving DecidableEq, Repr

/-- CMPR: The morphological expression of comparison on the adjective (pp. 230-231); a code in parentheses is described as optional. -/
inductive Cmpr where
  /-- `M`: a synthetic comparative, an affix or process on the adjective, for at least some adjectives -/
  | morphological
  /-- `PER`: no regular synthetic comparative; an adverb or other free element marks comparison -/
  | periphrastic
  /-- `ZERO`: no marking of comparison on the adjective -/
  | zero
  deriving DecidableEq, Repr

/-- SPRL: The morphosyntactic expression of the relative superlative (pp. 232-233). -/
inductive Sprl where
  /-- `M`: a synthetic superlative -/
  | morphological
  /-- `PER`: a periphrastic superlative -/
  | periphrastic
  /-- `ABS`: the source indicates only absolute superlatives -/
  | absolute
  /-- `ALL`: the comparative construction with a universal quantifier as the standard -/
  | universal
  /-- `CPR`: no clear morphosyntactic distinction between comparative and superlative -/
  | comparative
  /-- `DEF`: the comparative (or positive) with a marker of definiteness -/
  | definite
  /-- `VERY`: the comparative with an intensifier -/
  | intensified
  /-- `POS`: the positive, the superlative sense from context -/
  | positive
  /-- `NONE`: no fixed superlative construction -/
  | none
  /-- `n/i`: no information available -/
  | noInformation
  /-- `OTH`: see the note at the entry -/
  | other
  deriving DecidableEq, Repr

/-- SUPPL: Whether there is evidence of suppletion in comparative or superlative formation (p. 233). -/
inductive Suppl where
  /-- `Y`: there is suppletion (YES in the legend) -/
  | yes
  /-- `NO`: there is no suppletion -/
  | no
  /-- `MORE`: suppletion only in 'many/much - more' -/
  | more
  /-- `V`: suppletive verbs may replace an 'exceed' comparative -/
  | verb
  /-- `n/i`: no suppletion is indicated in the available description -/
  | notIndicated
  /-- `?`: printed '?', a mark the legend does not define -/
  | unclear
  deriving DecidableEq, Repr

/-- A row of the sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for region. -/
  region : List (Coded Region)
  /-- The codes for CMPR TYP. -/
  cmprTyp : List (Coded CmprTyp)
  /-- The codes for CMPR. -/
  cmpr : List (Coded Cmpr)
  /-- The codes for SPRL. -/
  sprl : List (Coded Sprl)
  /-- The codes for SUPPL. -/
  suppl : List (Coded Suppl)
  deriving DecidableEq, Repr

def tamashek : Language :=
  { id := "tamashek", name := "Tamashek", glottocode := some "tama1365" }

def hausa : Language :=
  { id := "hausa", name := "Hausa", glottocode := some "haus1257" }

def lele : Language :=
  { id := "lele", name := "Lele", glottocode := some "lele1276" }

def mina : Language :=
  { id := "mina", name := "Mina", glottocode := some "mina1276" }

def qimant : Language :=
  { id := "qimant", name := "Qimant", glottocode := some "qima1242" }

def somali : Language :=
  { id := "somali", name := "Somali", glottocode := some "soma1255" }

def arabic_std : Language :=
  { id := "arabic_std", name := "Arabic (Std.)", glottocode := some "stan1318" }

def neo_aramaic : Language :=
  { id := "neo_aramaic", name := "Neo-Aramaic", glottocode := none }

def hebrew : Language :=
  { id := "hebrew", name := "Hebrew", glottocode := some "hebr1245" }

def khoekhoe_nama : Language :=
  { id := "khoekhoe_nama", name := "Khoekhoe (Nama)", glottocode := some "nama1264" }

def khwe : Language :=
  { id := "khwe", name := "Khwe", glottocode := some "kxoe1243" }

def koromfe : Language :=
  { id := "koromfe", name := "Koromfe", glottocode := some "koro1298" }

def ijo : Language :=
  { id := "ijo", name := "Ịjọ", glottocode := none }

def kana : Language :=
  { id := "kana", name := "Kana", glottocode := some "khan1278" }

def ogbronuagum : Language :=
  { id := "ogbronuagum", name := "Ogbronuagum", glottocode := some "ogbr1243" }

def banda : Language :=
  { id := "banda", name := "Banda", glottocode := none }

def lingala : Language :=
  { id := "lingala", name := "Lingala", glottocode := some "ling1263" }

def nandi : Language :=
  { id := "nandi", name := "Nandi", glottocode := none }

def sotho_northern : Language :=
  { id := "sotho_northern", name := "Sotho (Northern)", glottocode := some "pedi1238" }

def zulu : Language :=
  { id := "zulu", name := "Zulu", glottocode := some "zulu1248" }

def lango : Language :=
  { id := "lango", name := "Lango", glottocode := some "lang1324" }

def mbay : Language :=
  { id := "mbay", name := "Mbay", glottocode := some "mbay1241" }

def koroboro_seno : Language :=
  { id := "koroboro_seno", name := "Koroboro Seno", glottocode := some "koyr1242" }

def kanuri : Language :=
  { id := "kanuri", name := "Kanuri", glottocode := none }

def irish : Language :=
  { id := "irish", name := "Irish", glottocode := some "iris1253" }

def modern_greek : Language :=
  { id := "modern_greek", name := "Modern Greek", glottocode := some "mode1248" }

def kashmiri : Language :=
  { id := "kashmiri", name := "Kashmiri", glottocode := some "kash1277" }

def persian_farsi : Language :=
  { id := "persian_farsi", name := "Persian (Farsi)", glottocode := some "west2369" }

def czech : Language :=
  { id := "czech", name := "Czech", glottocode := some "czec1258" }

def finnish : Language :=
  { id := "finnish", name := "Finnish", glottocode := some "finn1318" }

def udmurt : Language :=
  { id := "udmurt", name := "Udmurt", glottocode := some "udmu1245" }

def nenets : Language :=
  { id := "nenets", name := "Nenets", glottocode := none }

def ket : Language :=
  { id := "ket", name := "Ket", glottocode := some "kett1243" }

def even : Language :=
  { id := "even", name := "Even", glottocode := some "even1260" }

def evenki : Language :=
  { id := "evenki", name := "Evenki", glottocode := some "even1259" }

def khalkha : Language :=
  { id := "khalkha", name := "Khalkha", glottocode := some "halh1238" }

def lezgian : Language :=
  { id := "lezgian", name := "Lezgian", glottocode := some "lezg1247" }

def hunzib : Language :=
  { id := "hunzib", name := "Hunzib", glottocode := some "hunz1247" }

def abkhaz : Language :=
  { id := "abkhaz", name := "Abkhaz", glottocode := some "abkh1244" }

def bashkir : Language :=
  { id := "bashkir", name := "Bashkir", glottocode := some "bash1264" }

def khakas : Language :=
  { id := "khakas", name := "Khakas", glottocode := some "khak1248" }

def tyvan : Language :=
  { id := "tyvan", name := "Tyvan", glottocode := some "tuvi1240" }

def itelmen : Language :=
  { id := "itelmen", name := "Itelmen", glottocode := some "itel1242" }

def chukchi : Language :=
  { id := "chukchi", name := "Chukchi", glottocode := some "chuk1273" }

def malayalam : Language :=
  { id := "malayalam", name := "Malayalam", glottocode := some "mala1464" }

def ainu : Language :=
  { id := "ainu", name := "Ainu", glottocode := some "ainu1240" }

def nivkh : Language :=
  { id := "nivkh", name := "Nivkh", glottocode := some "gily1242" }

def burushaski : Language :=
  { id := "burushaski", name := "Burushaski", glottocode := some "buru1296" }

def yukagir : Language :=
  { id := "yukagir", name := "Yukagir", glottocode := none }

def basque : Language :=
  { id := "basque", name := "Basque", glottocode := some "basq1248" }

def asl : Language :=
  { id := "asl", name := "ASL", glottocode := some "amer1248" }

def cantonese : Language :=
  { id := "cantonese", name := "Cantonese", glottocode := some "cant1236" }

def kunming : Language :=
  { id := "kunming", name := "Kunming", glottocode := some "kunm1234" }

def mandarin : Language :=
  { id := "mandarin", name := "Mandarin", glottocode := some "mand1415" }

def dzongkha : Language :=
  { id := "dzongkha", name := "Dzongkha", glottocode := some "dzon1239" }

def kham : Language :=
  { id := "kham", name := "Kham", glottocode := none }

def limbu : Language :=
  { id := "limbu", name := "Limbu", glottocode := some "limb1266" }

def newar_dolokha : Language :=
  { id := "newar_dolokha", name := "Newar (Dolokha)", glottocode := some "dola1240" }

def bisu : Language :=
  { id := "bisu", name := "Bisu", glottocode := some "bisu1244" }

def mongsen_ao : Language :=
  { id := "mongsen_ao", name := "Mongsen Ao", glottocode := some "mong1332" }

def mizo : Language :=
  { id := "mizo", name := "Mizo", glottocode := some "lush1249" }

def dumi : Language :=
  { id := "dumi", name := "Dumi", glottocode := some "dumi1241" }

def lao : Language :=
  { id := "lao", name := "Lao", glottocode := some "laoo1244" }

def thai : Language :=
  { id := "thai", name := "Thai", glottocode := some "thai1261" }

def japanese : Language :=
  { id := "japanese", name := "Japanese", glottocode := some "nucl1643" }

def korean : Language :=
  { id := "korean", name := "Korean", glottocode := some "kore1280" }

def mayali : Language :=
  { id := "mayali", name := "Mayali", glottocode := some "gunw1252" }

def nunggubuyu : Language :=
  { id := "nunggubuyu", name := "Nunggubuyu", glottocode := some "nung1290" }

def arrernte : Language :=
  { id := "arrernte", name := "Arrernte", glottocode := none }

def dyirbal : Language :=
  { id := "dyirbal", name := "Dyirbal", glottocode := some "dyir1250" }

def gumbaynggir : Language :=
  { id := "gumbaynggir", name := "Gumbaynggir", glottocode := some "kumb1268" }

def warlpiri : Language :=
  { id := "warlpiri", name := "Warlpiri", glottocode := some "warl1254" }

def yindjibarndi : Language :=
  { id := "yindjibarndi", name := "Yindjibarndi", glottocode := some "yind1247" }

def kayardild : Language :=
  { id := "kayardild", name := "Kayardild", glottocode := some "kaya1319" }

def jingulu : Language :=
  { id := "jingulu", name := "Jingulu", glottocode := some "djin1251" }

def amis : Language :=
  { id := "amis", name := "Amis", glottocode := some "amis1246" }

def paiwan : Language :=
  { id := "paiwan", name := "Paiwan", glottocode := some "paiw1248" }

def puyuma : Language :=
  { id := "puyuma", name := "Puyuma", glottocode := some "puyu1239" }

def rukai : Language :=
  { id := "rukai", name := "Rukai", glottocode := some "ruka1240" }

def seediq : Language :=
  { id := "seediq", name := "Seediq", glottocode := some "taro1264" }

def rapanui : Language :=
  { id := "rapanui", name := "Rapanui", glottocode := some "rapa1244" }

def maori : Language :=
  { id := "maori", name := "Maori", glottocode := some "maor1246" }

def muna : Language :=
  { id := "muna", name := "Muna", glottocode := some "muna1247" }

def pendau : Language :=
  { id := "pendau", name := "Pendau", glottocode := some "pend1242" }

def yapese : Language :=
  { id := "yapese", name := "Yapese", glottocode := some "yape1248" }

def palauan : Language :=
  { id := "palauan", name := "Palauan", glottocode := some "pala1344" }

def fijian_boumaa : Language :=
  { id := "fijian_boumaa", name := "Fijian (Boumaa)", glottocode := some "fiji1243" }

def tuvaluan : Language :=
  { id := "tuvaluan", name := "Tuvaluan", glottocode := some "tuva1244" }

def manam : Language :=
  { id := "manam", name := "Manam", glottocode := some "mana1295" }

def sinaugoro : Language :=
  { id := "sinaugoro", name := "Sinaugoro", glottocode := some "sina1266" }

def amele : Language :=
  { id := "amele", name := "Amele", glottocode := some "amel1241" }

def klon : Language :=
  { id := "klon", name := "Klon", glottocode := some "kelo1247" }

def teiwa : Language :=
  { id := "teiwa", name := "Teiwa", glottocode := some "teiw1235" }

def mian : Language :=
  { id := "mian", name := "Mian", glottocode := some "mian1256" }

def ekagi : Language :=
  { id := "ekagi", name := "Ekagi", glottocode := some "ekar1243" }

def koiari : Language :=
  { id := "koiari", name := "Koiari", glottocode := some "gras1249" }

def mauwake : Language :=
  { id := "mauwake", name := "Mauwake", glottocode := some "mauw1238" }

def arapesh : Language :=
  { id := "arapesh", name := "Arapesh", glottocode := none }

def skou : Language :=
  { id := "skou", name := "Skou", glottocode := some "nucl1634" }

def mundari : Language :=
  { id := "mundari", name := "Mundari", glottocode := some "mund1320" }

def santali : Language :=
  { id := "santali", name := "Santali", glottocode := some "sant1410" }

def remo : Language :=
  { id := "remo", name := "Remo", glottocode := some "bond1245" }

def semalai : Language :=
  { id := "semalai", name := "Semalai", glottocode := some "seme1247" }

def palaung : Language :=
  { id := "palaung", name := "Palaung", glottocode := none }

def vietnamese : Language :=
  { id := "vietnamese", name := "Vietnamese", glottocode := some "viet1252" }

def khmer : Language :=
  { id := "khmer", name := "Khmer", glottocode := some "cent1989" }

def sapuan : Language :=
  { id := "sapuan", name := "Sapuan", glottocode := some "sapu1248" }

def aleut : Language :=
  { id := "aleut", name := "Aleut", glottocode := some "aleu1260" }

def west_greenlandic : Language :=
  { id := "west_greenlandic", name := "West Greenlandic", glottocode := some "kala1399" }

def straits_salish : Language :=
  { id := "straits_salish", name := "Straits Salish", glottocode := some "stra1244" }

def navajo : Language :=
  { id := "navajo", name := "Navajo", glottocode := some "nava1243" }

def nishnaabemwin : Language :=
  { id := "nishnaabemwin", name := "Nishnaabemwin", glottocode := none }

def cherokee : Language :=
  { id := "cherokee", name := "Cherokee", glottocode := some "cher1273" }

def kiowa : Language :=
  { id := "kiowa", name := "Kiowa", glottocode := some "kiow1266" }

def chimariko : Language :=
  { id := "chimariko", name := "Chimariko", glottocode := some "chim1301" }

def kiliwa : Language :=
  { id := "kiliwa", name := "Kiliwa", glottocode := some "kili1268" }

def choctaw : Language :=
  { id := "choctaw", name := "Choctaw", glottocode := some "choc1276" }

def crow : Language :=
  { id := "crow", name := "Crow", glottocode := some "crow1244" }

def wappo : Language :=
  { id := "wappo", name := "Wappo", glottocode := some "wapp1239" }

def nahuatl : Language :=
  { id := "nahuatl", name := "Nahuatl", glottocode := none }

def comanche : Language :=
  { id := "comanche", name := "Comanche", glottocode := some "coma1245" }

def tumpisa_shoshone : Language :=
  { id := "tumpisa_shoshone", name := "Tümpisa Shoshone", glottocode := some "pana1305" }

def cupeno : Language :=
  { id := "cupeno", name := "Cupeño", glottocode := some "cupe1243" }

def sonora_yaqui : Language :=
  { id := "sonora_yaqui", name := "Sonora Yaqui", glottocode := some "yaqu1251" }

def tohono_oodham : Language :=
  { id := "tohono_oodham", name := "Tohono O’odham", glottocode := some "toho1245" }

def tarascan : Language :=
  { id := "tarascan", name := "Tarascan", glottocode := some "pure1242" }

def totonac : Language :=
  { id := "totonac", name := "Totonac", glottocode := none }

def miskitu : Language :=
  { id := "miskitu", name := "Miskitu", glottocode := some "misk1235" }

def mixtec : Language :=
  { id := "mixtec", name := "Mixtec", glottocode := none }

def wari : Language :=
  { id := "wari", name := "Wari’", glottocode := some "wari1268" }

def yagua : Language :=
  { id := "yagua", name := "Yagua", glottocode := some "yagu1244" }

def bare : Language :=
  { id := "bare", name := "Bare", glottocode := some "bare1276" }

def tariana : Language :=
  { id := "tariana", name := "Tariana", glottocode := some "tari1256" }

def warekena : Language :=
  { id := "warekena", name := "Warekena", glottocode := none }

def paumari : Language :=
  { id := "paumari", name := "Paumarí", glottocode := some "paum1247" }

def apalai : Language :=
  { id := "apalai", name := "Apalai", glottocode := some "apal1257" }

def hixkaryana : Language :=
  { id := "hixkaryana", name := "Hixkaryana", glottocode := some "hixk1239" }

def bororo : Language :=
  { id := "bororo", name := "Bororo", glottocode := some "boro1282" }

def kayapo : Language :=
  { id := "kayapo", name := "Kayapó", glottocode := some "kaya1330" }

def piraha : Language :=
  { id := "piraha", name := "Pirahã", glottocode := some "pira1253" }

def mbya_guarani : Language :=
  { id := "mbya_guarani", name := "Mbyá (Guaraní)", glottocode := some "mbya1239" }

def urubu_kaapor : Language :=
  { id := "urubu_kaapor", name := "Urubu-Kaapor", glottocode := some "urub1250" }

def andoke : Language :=
  { id := "andoke", name := "Andoke", glottocode := some "ando1256" }

def aymara : Language :=
  { id := "aymara", name := "Aymara", glottocode := none }

def mapuche : Language :=
  { id := "mapuche", name := "Mapuche", glottocode := some "mapu1245" }

def moseten : Language :=
  { id := "moseten", name := "Mosetén", glottocode := some "mose1249" }

def urarina : Language :=
  { id := "urarina", name := "Urarina", glottocode := some "urar1246" }

def kwaza : Language :=
  { id := "kwaza", name := "Kwaza", glottocode := some "kwaz1243" }

/-- Every row of the sample, in the order of the source (bobaljik-2012, Table A.1). -/
def rows : List Row := [
  { language := tamashek,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.definite, false, false⟩],
    suppl := [⟨.verb, false, false⟩] },
  { language := hausa,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := lele,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mina,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := qimant,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := somali,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := arabic_std,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.definite, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := neo_aramaic,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.definite, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := hebrew,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.more, false, false⟩] },
  { language := khoekhoe_nama,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := khwe,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.positive, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := koromfe,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := ijo,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kana,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := ogbronuagum,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := banda,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := lingala,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := nandi,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := sotho_northern,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := zulu,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩, ⟨.morphological, true, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := lango,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mbay,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := koroboro_seno,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kanuri,
    region := [⟨.africa, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.morphological, false, true⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := irish,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.comparative, false, false⟩],
    suppl := [⟨.yes, false, false⟩] },
  { language := modern_greek,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.definite, false, false⟩],
    suppl := [⟨.yes, false, false⟩] },
  { language := kashmiri,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := persian_farsi,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.yes, false, false⟩] },
  { language := czech,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.yes, false, false⟩] },
  { language := finnish,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.yes, false, false⟩] },
  { language := udmurt,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, true⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := nenets,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.unclear, false, false⟩] },
  { language := ket,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := even,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := evenki,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, true, false⟩],
    sprl := [⟨.morphological, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := khalkha,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := lezgian,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.more, true, false⟩] },
  { language := hunzib,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := abkhaz,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := bashkir,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, true⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := khakas,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := tyvan,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := itelmen,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := chukchi,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := malayalam,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.intensified, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := ainu,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.periphrastic, false, true⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := nivkh,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, true⟩],
    sprl := [⟨.intensified, true, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := burushaski,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := yukagir,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := basque,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.yes, false, false⟩] },
  { language := asl,
    region := [⟨.eurasia, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := cantonese,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := kunming,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.morphological, false, true⟩],
    sprl := [⟨.morphological, false, true⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mandarin,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := dzongkha,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, true, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kham,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := limbu,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := newar_dolokha,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := bisu,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := mongsen_ao,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.intensified, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mizo,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := dumi,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := lao,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := thai,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := japanese,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, true⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := korean,
    region := [⟨.eAsia, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.periphrastic, false, true⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := mayali,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.comparative, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := nunggubuyu,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.no, true, false⟩] },
  { language := arrernte,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := dyirbal,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := gumbaynggir,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := warlpiri,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := yindjibarndi,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kayardild,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := jingulu,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := amis,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := paiwan,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := puyuma,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, true, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, true, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := rukai,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, true, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := seediq,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.comparative, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := rapanui,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := maori,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.intensified, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := muna,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := pendau,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := yapese,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := palauan,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := fijian_boumaa,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := tuvaluan,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.positive, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := manam,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := sinaugoro,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := amele,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩, ⟨.standard, true, false⟩],
    cmpr := [⟨.periphrastic, true, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := klon,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.comparative, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := teiwa,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.positive, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mian,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, true, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := ekagi,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := koiari,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mauwake,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := arapesh,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, true, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := skou,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mundari,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := santali,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := remo,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := semalai,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := palaung,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, true, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := vietnamese,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.other, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := khmer,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := sapuan,
    region := [⟨.pacific, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := aleut,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := west_greenlandic,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.comparative, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := straits_salish,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := navajo,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := nishnaabemwin,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := cherokee,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kiowa,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.comparative, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := chimariko,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, true, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.morphological, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kiliwa,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, true, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := choctaw,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := crow,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.other, false, false⟩],
    cmpr := [⟨.morphological, true, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := wappo,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := nahuatl,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := comanche,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, true, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := tumpisa_shoshone,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := cupeno,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.universal, false, true⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := sonora_yaqui,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := tohono_oodham,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.intensified, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := tarascan,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.other, false, false⟩],
    cmpr := [⟨.morphological, true, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := totonac,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.comparative, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := miskitu,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.absolute, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mixtec,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.definite, false, false⟩],
    suppl := [⟨.no, true, false⟩] },
  { language := wari,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := yagua,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := bare,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, true⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := tariana,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := warekena,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := paumari,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := apalai,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := hixkaryana,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.other, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := bororo,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kayapo,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.absolute, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := piraha,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mbya_guarani,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.morphological, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.no, false, false⟩] },
  { language := urubu_kaapor,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.noInformation, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := andoke,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.absolute, false, false⟩, ⟨.periphrastic, false, true⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := aymara,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩, ⟨.exceed, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.periphrastic, false, false⟩, ⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := mapuche,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.standard, false, false⟩],
    cmpr := [⟨.periphrastic, false, false⟩],
    sprl := [⟨.universal, true, false⟩],
    suppl := [] },
  { language := moseten,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.absolute, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := urarina,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.exceed, false, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.universal, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] },
  { language := kwaza,
    region := [⟨.americas, false, false⟩],
    cmprTyp := [⟨.conjoined, true, false⟩],
    cmpr := [⟨.zero, false, false⟩],
    sprl := [⟨.none, false, false⟩],
    suppl := [⟨.notIndicated, false, false⟩] }]

end Bobaljik2012.Structures
