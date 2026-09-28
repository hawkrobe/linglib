module

/-!
# WALS Feature 101A: Expression of Pronominal Subjects
[wals-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 101A`.

Chapter 101, 711 languages.
-/

@[expose] public section

namespace Data.WALS.F101A

/-- WALS 101A values. -/
inductive ExpressionOfPronominalSubjects where
  /-- Obligatory pronouns in subject position (82 languages). -/
  | obligatoryPronounsInSubjectPosition
  /-- Subject affixes on verb (437 languages). -/
  | subjectAffixesOnVerb
  /-- Subject clitics on variable host (32 languages). -/
  | subjectCliticsOnVariableHost
  /-- Subject pronouns in different position (67 languages). -/
  | subjectPronounsInDifferentPosition
  /-- Optional pronouns in subject position (61 languages). -/
  | optionalPronounsInSubjectPosition
  /-- Mixed (32 languages). -/
  | mixed
  deriving DecidableEq, Repr

/-- Rows 1 to 500 of `allData`. -/
def allData_0 : List (String × ExpressionOfPronominalSubjects) :=
  [ ("aar", .subjectAffixesOnVerb) -- Aari
  , ("abk", .subjectAffixesOnVerb) -- Abkhaz
  , ("abu", .obligatoryPronounsInSubjectPosition) -- Abun
  , ("abv", .subjectPronounsInDifferentPosition) -- Abui
  , ("acg", .subjectAffixesOnVerb) -- Achagua
  , ("acl", .subjectAffixesOnVerb) -- Acholi
  , ("aco", .subjectAffixesOnVerb) -- Acoma
  , ("aeg", .subjectAffixesOnVerb) -- Arabic (Egyptian)
  , ("aga", .subjectAffixesOnVerb) -- Agarabi
  , ("agt", .obligatoryPronounsInSubjectPosition) -- Anguthimri
  , ("ain", .subjectAffixesOnVerb) -- Ainu
  , ("aja", .subjectAffixesOnVerb) -- Aja
  , ("ala", .subjectAffixesOnVerb) -- Alamblak
  , ("alb", .subjectAffixesOnVerb) -- Albanian
  , ("all", .subjectAffixesOnVerb) -- Ala'ala
  , ("aln", .mixed) -- Alune
  , ("amb", .obligatoryPronounsInSubjectPosition) -- Ambulas
  , ("amh", .subjectAffixesOnVerb) -- Amharic
  , ("aml", .subjectPronounsInDifferentPosition) -- Ambae (Lolovoli Northeast)
  , ("amp", .obligatoryPronounsInSubjectPosition) -- Arrernte (Mparntwe)
  , ("amq", .subjectAffixesOnVerb) -- Ambai
  , ("amr", .subjectAffixesOnVerb) -- Arabic (Moroccan)
  , ("amx", .subjectAffixesOnVerb) -- Anamuxra
  , ("ane", .subjectAffixesOnVerb) -- Anêm
  , ("ang", .subjectAffixesOnVerb) -- Anggor
  , ("anj", .obligatoryPronounsInSubjectPosition) -- Anejom
  , ("any", .subjectAffixesOnVerb) -- Anywa
  , ("ao", .obligatoryPronounsInSubjectPosition) -- Ao
  , ("aoj", .subjectAffixesOnVerb) -- Mufian
  , ("apl", .subjectAffixesOnVerb) -- Apalaí
  , ("apu", .subjectAffixesOnVerb) -- Apurinã
  , ("apw", .subjectAffixesOnVerb) -- Apache (Western)
  , ("ara", .subjectAffixesOnVerb) -- Lokono
  , ("arg", .subjectAffixesOnVerb) -- Arabic (Gulf)
  , ("arm", .subjectAffixesOnVerb) -- Armenian (Eastern)
  , ("arp", .subjectAffixesOnVerb) -- Arapesh (Mountain)
  , ("arq", .subjectAffixesOnVerb) -- Arabic (Iraqi)
  , ("arw", .subjectAffixesOnVerb) -- Armenian (Western)
  , ("asm", .subjectAffixesOnVerb) -- Asmat
  , ("ass", .subjectAffixesOnVerb) -- Assamese
  , ("asy", .subjectAffixesOnVerb) -- Arabic (Syrian)
  , ("ata", .subjectCliticsOnVariableHost) -- Atayal
  , ("ath", .subjectAffixesOnVerb) -- Athpare
  , ("awa", .subjectAffixesOnVerb) -- Awa
  , ("awp", .subjectAffixesOnVerb) -- Awa Pit
  , ("awt", .optionalPronounsInSubjectPosition) -- Awtuw
  , ("aym", .subjectAffixesOnVerb) -- Aymara (Central)
  , ("ayr", .subjectAffixesOnVerb) -- Ayoreo
  , ("bab", .obligatoryPronounsInSubjectPosition) -- Babungo
  , ("bae", .subjectAffixesOnVerb) -- Baré
  , ("bas", .obligatoryPronounsInSubjectPosition) -- Basaá
  , ("baw", .subjectPronounsInDifferentPosition) -- Bawm
  , ("bbl", .subjectAffixesOnVerb) -- Babole
  , ("bbw", .subjectAffixesOnVerb) -- Bininj Gun-Wok
  , ("bco", .subjectAffixesOnVerb) -- Bella Coola
  , ("bej", .subjectAffixesOnVerb) -- Beja
  , ("bel", .subjectAffixesOnVerb) -- Belhare
  , ("bem", .subjectAffixesOnVerb) -- Bemba
  , ("bfg", .subjectAffixesOnVerb) -- Berber (Figuig)
  , ("bgr", .subjectAffixesOnVerb) -- Bagiro
  , ("bid", .mixed) -- Bidiya
  , ("big", .subjectAffixesOnVerb) -- Binga
  , ("bii", .subjectAffixesOnVerb) -- Biri
  , ("bik", .subjectAffixesOnVerb) -- Biak
  , ("bil", .subjectCliticsOnVariableHost) -- Bilua
  , ("bin", .subjectAffixesOnVerb) -- Binandere
  , ("bio", .subjectAffixesOnVerb) -- Nai
  , ("bir", .subjectAffixesOnVerb) -- Birom
  , ("bkr", .mixed) -- Batak (Karo)
  , ("bku", .subjectAffixesOnVerb) -- Bakueri
  , ("bla", .subjectCliticsOnVariableHost) -- Blackfoot
  , ("ble", .subjectPronounsInDifferentPosition) -- Baoulé
  , ("bln", .subjectAffixesOnVerb) -- Bilin
  , ("blx", .subjectAffixesOnVerb) -- Biloxi
  , ("blz", .subjectAffixesOnVerb) -- Balanta
  , ("bma", .subjectAffixesOnVerb) -- Berber (Middle Atlas)
  , ("bmb", .obligatoryPronounsInSubjectPosition) -- Bimoba
  , ("bnb", .subjectAffixesOnVerb) -- Bunuba
  , ("bnn", .subjectPronounsInDifferentPosition) -- Banoni
  , ("bob", .subjectAffixesOnVerb) -- Bobangi
  , ("bol", .subjectAffixesOnVerb) -- Bolia
  , ("bre", .subjectAffixesOnVerb) -- Breton
  , ("brf", .subjectAffixesOnVerb) -- Berber (Rif)
  , ("brh", .subjectAffixesOnVerb) -- Brahui
  , ("brm", .optionalPronounsInSubjectPosition) -- Burmese
  , ("brn", .subjectPronounsInDifferentPosition) -- Burunge
  , ("brp", .subjectAffixesOnVerb) -- Barupu
  , ("brr", .subjectAffixesOnVerb) -- Bororo
  , ("brs", .subjectAffixesOnVerb) -- Barasano
  , ("bsh", .subjectAffixesOnVerb) -- Bushoong
  , ("bsk", .subjectAffixesOnVerb) -- Bashkir
  , ("bsq", .subjectAffixesOnVerb) -- Basque
  , ("bsr", .subjectAffixesOnVerb) -- Basari
  , ("bud", .mixed) -- Buduma
  , ("bul", .subjectAffixesOnVerb) -- Bulgarian
  , ("bum", .subjectAffixesOnVerb) -- Buma
  , ("bur", .subjectAffixesOnVerb) -- Burushaski
  , ("bus", .obligatoryPronounsInSubjectPosition) -- Busa
  , ("buw", .subjectPronounsInDifferentPosition) -- Bulu
  , ("bvi", .subjectPronounsInDifferentPosition) -- Bali-Vitu
  , ("bya", .obligatoryPronounsInSubjectPosition) -- Byansi
  , ("cah", .subjectAffixesOnVerb) -- Cahuilla
  , ("cai", .subjectAffixesOnVerb) -- Chai
  , ("cav", .mixed) -- Cavineña
  , ("cax", .subjectAffixesOnVerb) -- Campa (Axininca)
  , ("cba", .subjectAffixesOnVerb) -- Chumash (Barbareño)
  , ("cct", .subjectAffixesOnVerb) -- Choctaw
  , ("cde", .subjectAffixesOnVerb) -- Carib (De'kwana)
  , ("cea", .subjectCliticsOnVariableHost) -- Cree (Swampy)
  , ("cem", .subjectPronounsInDifferentPosition) -- Cèmuhî
  , ("chc", .obligatoryPronounsInSubjectPosition) -- Chechen
  , ("che", .subjectAffixesOnVerb) -- Cherokee
  , ("chg", .optionalPronounsInSubjectPosition) -- Chang
  , ("chh", .subjectAffixesOnVerb) -- Chaha
  , ("chi", .subjectAffixesOnVerb) -- Chimariko
  , ("chk", .subjectAffixesOnVerb) -- Chukchi
  , ("chn", .optionalPronounsInSubjectPosition) -- Chantyal
  , ("chs", .subjectPronounsInDifferentPosition) -- Chin (Siyin)
  , ("chx", .subjectAffixesOnVerb) -- Chontal (Huamelultec Oaxaca)
  , ("cic", .subjectAffixesOnVerb) -- Chichewa
  , ("cld", .subjectAffixesOnVerb) -- Chaldean (Modern)
  , ("cle", .subjectAffixesOnVerb) -- Chinantec (Lealao)
  , ("cln", .subjectAffixesOnVerb) -- Cholón
  , ("cmh", .subjectCliticsOnVariableHost) -- Chemehuevi
  , ("cmn", .subjectCliticsOnVariableHost) -- Comanche
  , ("cmy", .subjectAffixesOnVerb) -- Chontal Maya
  , ("coo", .subjectAffixesOnVerb) -- Coos (Hanis)
  , ("cre", .subjectCliticsOnVariableHost) -- Cree (Plains)
  , ("crn", .subjectAffixesOnVerb) -- Cornish
  , ("cro", .subjectAffixesOnVerb) -- Crow
  , ("cti", .mixed) -- Chin (Tiddim)
  , ("ctl", .subjectAffixesOnVerb) -- Catalan
  , ("cub", .subjectAffixesOnVerb) -- Cubeo
  , ("cup", .mixed) -- Cupeño
  , ("cyv", .subjectAffixesOnVerb) -- Cayuvava
  , ("cze", .subjectAffixesOnVerb) -- Czech
  , ("dag", .subjectAffixesOnVerb) -- Daga
  , ("dds", .subjectAffixesOnVerb) -- Donno So
  , ("des", .subjectAffixesOnVerb) -- Desano
  , ("dga", .obligatoryPronounsInSubjectPosition) -- Dagaare
  , ("dgb", .obligatoryPronounsInSubjectPosition) -- Dagbani
  , ("dha", .mixed) -- Dhaasanac
  , ("dhi", .subjectAffixesOnVerb) -- Dhivehi
  , ("die", .subjectAffixesOnVerb) -- Diegueño (Mesa Grande)
  , ("dig", .subjectAffixesOnVerb) -- Digaro
  , ("dim", .subjectAffixesOnVerb) -- Dime
  , ("din", .mixed) -- Dinka
  , ("dio", .subjectAffixesOnVerb) -- Diola-Fogny
  , ("djp", .optionalPronounsInSubjectPosition) -- Djapu
  , ("dlm", .subjectAffixesOnVerb) -- Dla (Menggwa)
  , ("dni", .subjectAffixesOnVerb) -- Dani (Lower Grand Valley)
  , ("dom", .subjectAffixesOnVerb) -- Domari
  , ("doy", .mixed) -- Doyayo
  , ("dre", .obligatoryPronounsInSubjectPosition) -- Drehu
  , ("dsh", .obligatoryPronounsInSubjectPosition) -- Danish
  , ("dum", .obligatoryPronounsInSubjectPosition) -- Dumo
  , ("dun", .optionalPronounsInSubjectPosition) -- Duna
  , ("dut", .obligatoryPronounsInSubjectPosition) -- Dutch
  , ("ebi", .subjectPronounsInDifferentPosition) -- Ebira
  , ("efi", .subjectAffixesOnVerb) -- Efik
  , ("egn", .obligatoryPronounsInSubjectPosition) -- Engenni
  , ("eip", .subjectAffixesOnVerb) -- Eipo
  , ("eko", .subjectAffixesOnVerb) -- Ekoti
  , ("emb", .subjectAffixesOnVerb) -- Emberá (Northern)
  , ("eme", .subjectAffixesOnVerb) -- Émérillon
  , ("ene", .subjectAffixesOnVerb) -- Enets
  , ("eng", .obligatoryPronounsInSubjectPosition) -- English
  , ("epe", .optionalPronounsInSubjectPosition) -- Epena Pedee
  , ("err", .subjectAffixesOnVerb) -- Erromangan
  , ("esm", .subjectAffixesOnVerb) -- Esmeraldeño
  , ("est", .subjectAffixesOnVerb) -- Estonian
  , ("eve", .obligatoryPronounsInSubjectPosition) -- Evenki
  , ("ewe", .subjectAffixesOnVerb) -- Ewe
  , ("ewo", .subjectAffixesOnVerb) -- Ewondo
  , ("fij", .subjectPronounsInDifferentPosition) -- Fijian
  , ("fin", .mixed) -- Finnish
  , ("fre", .obligatoryPronounsInSubjectPosition) -- French
  , ("fri", .obligatoryPronounsInSubjectPosition) -- Frisian
  , ("fua", .subjectAffixesOnVerb) -- Fulfulde (Adamawa)
  , ("fur", .subjectAffixesOnVerb) -- Fur
  , ("fut", .subjectPronounsInDifferentPosition) -- Futuna-Aniwa
  , ("fye", .subjectPronounsInDifferentPosition) -- Fyem
  , ("ga", .subjectAffixesOnVerb) -- Gã
  , ("gaa", .subjectAffixesOnVerb) -- Gaagudju
  , ("gae", .obligatoryPronounsInSubjectPosition) -- Gaelic (Scots)
  , ("gah", .subjectAffixesOnVerb) -- Gahuku
  , ("gar", .optionalPronounsInSubjectPosition) -- Garo
  , ("gds", .subjectAffixesOnVerb) -- Gadsup
  , ("geo", .subjectPronounsInDifferentPosition) -- Georgian
  , ("ger", .obligatoryPronounsInSubjectPosition) -- German
  , ("gim", .subjectPronounsInDifferentPosition) -- Gimira
  , ("gjj", .subjectAffixesOnVerb) -- Guajajara
  , ("gln", .subjectAffixesOnVerb) -- Golin
  , ("gmw", .subjectAffixesOnVerb) -- Gumawana
  , ("gmz", .subjectAffixesOnVerb) -- Gumuz
  , ("goe", .optionalPronounsInSubjectPosition) -- Goemai
  , ("goo", .subjectAffixesOnVerb) -- Gooniyandi
  , ("grb", .subjectPronounsInDifferentPosition) -- Grebo
  , ("grg", .subjectAffixesOnVerb) -- Gurr-goni
  , ("grj", .subjectCliticsOnVariableHost) -- Guarijío
  , ("grk", .subjectAffixesOnVerb) -- Greek (Modern)
  , ("grw", .subjectAffixesOnVerb) -- Greenlandic (West)
  , ("gua", .subjectAffixesOnVerb) -- Guaraní
  , ("gud", .obligatoryPronounsInSubjectPosition) -- Gude
  , ("gul", .subjectAffixesOnVerb) -- Gula (in Central African Republic)
  , ("gum", .optionalPronounsInSubjectPosition) -- Gumbaynggir
  , ("gur", .optionalPronounsInSubjectPosition) -- Gurung
  , ("guu", .optionalPronounsInSubjectPosition) -- Guugu Yimidhirr
  , ("gwa", .obligatoryPronounsInSubjectPosition) -- Gwari
  , ("gwo", .subjectPronounsInDifferentPosition) -- Gworok
  , ("gyc", .subjectAffixesOnVerb) -- Gyarong (Cogtse)
  , ("hai", .obligatoryPronounsInSubjectPosition) -- Haida
  , ("ham", .subjectAffixesOnVerb) -- Hamtai
  , ("hat", .subjectAffixesOnVerb) -- Hatam
  , ("hau", .subjectPronounsInDifferentPosition) -- Hausa
  , ("haw", .optionalPronounsInSubjectPosition) -- Hawaiian
  , ("hay", .subjectAffixesOnVerb) -- Hayu
  , ("heb", .mixed) -- Hebrew (Modern)
  , ("heh", .subjectAffixesOnVerb) -- Hehe
  , ("hei", .subjectCliticsOnVariableHost) -- Heiltsuk
  , ("hix", .subjectAffixesOnVerb) -- Hixkaryana
  , ("hlu", .subjectAffixesOnVerb) -- Halkomelem (Upriver)
  , ("hma", .subjectPronounsInDifferentPosition) -- Hmar
  , ("hmi", .subjectAffixesOnVerb) -- Huitoto (Minica)
  , ("hmo", .obligatoryPronounsInSubjectPosition) -- Hmong Njua
  , ("hnd", .subjectAffixesOnVerb) -- Hunde
  , ("hua", .subjectAffixesOnVerb) -- Hua
  , ("hun", .subjectAffixesOnVerb) -- Hungarian
  , ("hya", .subjectAffixesOnVerb) -- Haya
  , ("iaa", .subjectPronounsInDifferentPosition) -- Iaai
  , ("iba", .obligatoryPronounsInSubjectPosition) -- Iban
  , ("ice", .obligatoryPronounsInSubjectPosition) -- Icelandic
  , ("ifu", .subjectAffixesOnVerb) -- Ifugao (Batad)
  , ("igb", .subjectPronounsInDifferentPosition) -- Igbo
  , ("ige", .subjectAffixesOnVerb) -- Igede
  , ("ik", .subjectAffixesOnVerb) -- Ik
  , ("ika", .subjectAffixesOnVerb) -- Ika
  , ("ila", .subjectAffixesOnVerb) -- Ila
  , ("imo", .optionalPronounsInSubjectPosition) -- Imonda
  , ("ina", .subjectAffixesOnVerb) -- Inanwatan
  , ("ind", .obligatoryPronounsInSubjectPosition) -- Indonesian
  , ("ing", .obligatoryPronounsInSubjectPosition) -- Ingush
  , ("iri", .mixed) -- Irish
  , ("irq", .subjectAffixesOnVerb) -- Iraqw
  , ("isa", .subjectAffixesOnVerb) -- I'saka
  , ("ita", .subjectAffixesOnVerb) -- Italian
  , ("ite", .subjectAffixesOnVerb) -- Itelmen
  , ("ito", .subjectAffixesOnVerb) -- Itonama
  , ("izi", .subjectAffixesOnVerb) -- Izi
  , ("jab", .subjectAffixesOnVerb) -- Jabêm
  , ("jak", .mixed) -- Jakaltek
  , ("jam", .subjectAffixesOnVerb) -- Jaminjung
  , ("jmo", .subjectAffixesOnVerb) -- Jur Mödö
  , ("jng", .optionalPronounsInSubjectPosition) -- Jingpho
  , ("jpn", .optionalPronounsInSubjectPosition) -- Japanese
  , ("juh", .obligatoryPronounsInSubjectPosition) -- Ju|'hoan
  , ("juk", .obligatoryPronounsInSubjectPosition) -- Jukun
  , ("jwr", .mixed) -- Jarawara
  , ("kaa", .mixed) -- Karó (Arára)
  , ("kab", .subjectAffixesOnVerb) -- Kabardian
  , ("kae", .subjectAffixesOnVerb) -- Kaki Ae
  , ("kam", .subjectAffixesOnVerb) -- Kambera
  , ("kan", .subjectAffixesOnVerb) -- Kana
  , ("kas", .subjectPronounsInDifferentPosition) -- Kashmiri
  , ("kau", .mixed) -- Kaulong
  , ("kay", .optionalPronounsInSubjectPosition) -- Kayardild
  , ("kba", .subjectAffixesOnVerb) -- Kamba
  , ("kby", .optionalPronounsInSubjectPosition) -- Kabiyé
  , ("kch", .obligatoryPronounsInSubjectPosition) -- Koyra Chiini
  , ("kdw", .subjectAffixesOnVerb) -- Kadiwéu
  , ("kel", .obligatoryPronounsInSubjectPosition) -- Kele
  , ("ken", .mixed) -- Kenga
  , ("kew", .subjectAffixesOnVerb) -- Kewa
  , ("kfe", .subjectAffixesOnVerb) -- Koromfe
  , ("kga", .subjectAffixesOnVerb) -- Kinga
  , ("kgr", .subjectAffixesOnVerb) -- Kagulu
  , ("kgz", .subjectAffixesOnVerb) -- Kirghiz
  , ("kha", .optionalPronounsInSubjectPosition) -- Khalkha
  , ("kho", .obligatoryPronounsInSubjectPosition) -- Nama
  , ("khs", .obligatoryPronounsInSubjectPosition) -- Khasi
  , ("kik", .subjectAffixesOnVerb) -- Kikuyu
  , ("kio", .subjectAffixesOnVerb) -- Kiowa
  , ("kis", .subjectPronounsInDifferentPosition) -- Kisi
  , ("kkt", .subjectPronounsInDifferentPosition) -- Kokota
  , ("kku", .optionalPronounsInSubjectPosition) -- Korku
  , ("kkv", .subjectAffixesOnVerb) -- Lusi
  , ("klm", .optionalPronounsInSubjectPosition) -- Klamath
  , ("klv", .subjectAffixesOnVerb) -- Kilivila
  , ("kma", .subjectAffixesOnVerb) -- Kamaiurá
  , ("kmb", .subjectAffixesOnVerb) -- Kombai
  , ("kmh", .subjectAffixesOnVerb) -- Kham
  , ("kmj", .subjectAffixesOnVerb) -- Karimojong
  , ("kmp", .subjectAffixesOnVerb) -- Kunimaipa
  , ("kms", .subjectAffixesOnVerb) -- Kamass
  , ("kmu", .optionalPronounsInSubjectPosition) -- Khmu'
  , ("kmz", .subjectAffixesOnVerb) -- Kamasau
  , ("knc", .mixed) -- Kugu Nganhcara
  , ("knd", .subjectAffixesOnVerb) -- Kannada
  , ("knm", .subjectAffixesOnVerb) -- Kunama
  , ("kno", .subjectAffixesOnVerb) -- Kanoê
  , ("knr", .subjectAffixesOnVerb) -- Kanuri
  , ("knw", .subjectCliticsOnVariableHost) -- Konkow
  , ("koa", .subjectAffixesOnVerb) -- Koasati
  , ("kob", .subjectAffixesOnVerb) -- Kobon
  , ("koe", .subjectAffixesOnVerb) -- Koegu
  , ("kon", .subjectAffixesOnVerb) -- Kongo
  , ("kor", .optionalPronounsInSubjectPosition) -- Korean
  , ("krb", .subjectPronounsInDifferentPosition) -- Kiribati
  , ("krc", .subjectAffixesOnVerb) -- Karachay-Balkar
  , ("krd", .subjectAffixesOnVerb) -- Kurdish (Central)
  , ("kre", .subjectAffixesOnVerb) -- Kresh
  , ("krk", .subjectAffixesOnVerb) -- Karok
  , ("krn", .subjectCliticsOnVariableHost) -- Korana
  , ("kro", .mixed) -- Krongo
  , ("krr", .subjectAffixesOnVerb) -- Kairiru
  , ("krw", .subjectAffixesOnVerb) -- Korowai
  , ("ksa", .subjectAffixesOnVerb) -- Keresan (Santa Ana)
  , ("kse", .obligatoryPronounsInSubjectPosition) -- Koyraboro Senni
  , ("kty", .subjectAffixesOnVerb) -- Khanty
  , ("kut", .subjectPronounsInDifferentPosition) -- Kutenai
  , ("kwa", .subjectPronounsInDifferentPosition) -- Kwaio
  , ("kwk", .subjectAffixesOnVerb) -- Kwakw'ala
  , ("kwn", .subjectAffixesOnVerb) -- Kwangali
  , ("kwt", .subjectAffixesOnVerb) -- Kwomtari
  , ("kwz", .subjectAffixesOnVerb) -- Kwaza
  , ("kxo", .optionalPronounsInSubjectPosition) -- Kxoe
  , ("kyk", .subjectAffixesOnVerb) -- Kyaka
  , ("kyl", .optionalPronounsInSubjectPosition) -- Kayah Li (Eastern)
  , ("kyr", .obligatoryPronounsInSubjectPosition) -- Karkar-Yuri
  , ("laa", .obligatoryPronounsInSubjectPosition) -- Laal
  , ("lad", .optionalPronounsInSubjectPosition) -- Ladakhi
  , ("lah", .optionalPronounsInSubjectPosition) -- Lahu
  , ("lai", .subjectPronounsInDifferentPosition) -- Lai
  , ("lal", .optionalPronounsInSubjectPosition) -- Lalo
  , ("lan", .subjectAffixesOnVerb) -- Lango
  , ("lat", .obligatoryPronounsInSubjectPosition) -- Latvian
  , ("lav", .subjectAffixesOnVerb) -- Lavukaleve
  , ("lbu", .subjectAffixesOnVerb) -- Lunda
  , ("lda", .subjectAffixesOnVerb) -- Luganda
  , ("ldo", .subjectAffixesOnVerb) -- Londo
  , ("leg", .subjectAffixesOnVerb) -- Lega
  , ("lel", .subjectPronounsInDifferentPosition) -- Lele
  , ("len", .subjectAffixesOnVerb) -- Lenakel
  , ("lep", .obligatoryPronounsInSubjectPosition) -- Lepcha
  , ("let", .subjectAffixesOnVerb) -- Leti
  , ("lez", .optionalPronounsInSubjectPosition) -- Lezgian
  , ("lgi", .subjectAffixesOnVerb) -- Langi
  , ("lgu", .subjectPronounsInDifferentPosition) -- Longgu
  , ("lil", .subjectAffixesOnVerb) -- Lillooet
  , ("lim", .subjectAffixesOnVerb) -- Limbu
  , ("lin", .subjectAffixesOnVerb) -- Lingala
  , ("lit", .subjectAffixesOnVerb) -- Lithuanian
  , ("lkt", .subjectAffixesOnVerb) -- Lakhota
  , ("llm", .subjectAffixesOnVerb) -- Lelemi
  , ("lmb", .subjectPronounsInDifferentPosition) -- Lamba
  , ("lml", .subjectAffixesOnVerb) -- Limilngan
  , ("lmn", .mixed) -- Lamani
  , ("lmp", .optionalPronounsInSubjectPosition) -- Lampung
  , ("lon", .subjectPronounsInDifferentPosition) -- Loniu
  , ("lou", .subjectPronounsInDifferentPosition) -- Lou
  , ("luc", .subjectAffixesOnVerb) -- Lucazi
  , ("lul", .subjectAffixesOnVerb) -- Lule
  , ("luo", .subjectAffixesOnVerb) -- Luo
  , ("luv", .subjectAffixesOnVerb) -- Luvale
  , ("luy", .subjectAffixesOnVerb) -- Luyia
  , ("maa", .subjectAffixesOnVerb) -- Maasai
  , ("mab", .subjectAffixesOnVerb) -- Maba
  , ("mac", .subjectAffixesOnVerb) -- Macushi
  , ("mad", .subjectPronounsInDifferentPosition) -- Ma'di
  , ("mae", .subjectPronounsInDifferentPosition) -- Mae
  , ("maj", .subjectAffixesOnVerb) -- Majang
  , ("mak", .subjectCliticsOnVariableHost) -- Makah
  , ("mal", .obligatoryPronounsInSubjectPosition) -- Malagasy
  , ("mao", .optionalPronounsInSubjectPosition) -- Maori
  , ("map", .subjectAffixesOnVerb) -- Mapudungun
  , ("mar", .subjectAffixesOnVerb) -- Maricopa
  , ("mas", .optionalPronounsInSubjectPosition) -- Masa
  , ("mau", .subjectAffixesOnVerb) -- Maung
  , ("may", .optionalPronounsInSubjectPosition) -- Maybrat
  , ("mbl", .subjectAffixesOnVerb) -- Mbole
  , ("mbo", .subjectAffixesOnVerb) -- Monumbo
  , ("mbr", .subjectPronounsInDifferentPosition) -- Mbara
  , ("mbt", .subjectAffixesOnVerb) -- Mangbetu
  , ("mby", .subjectAffixesOnVerb) -- Mbay
  , ("mcc", .subjectAffixesOnVerb) -- Mochica
  , ("mcv", .subjectAffixesOnVerb) -- Mocoví
  , ("mdn", .subjectAffixesOnVerb) -- Mandan
  , ("mea", .subjectAffixesOnVerb) -- Meyah
  , ("mee", .subjectAffixesOnVerb) -- Me'en
  , ("meh", .subjectAffixesOnVerb) -- Mehri
  , ("mei", .optionalPronounsInSubjectPosition) -- Meithei
  , ("mek", .mixed) -- Mekens
  , ("men", .subjectCliticsOnVariableHost) -- Menomini
  , ("mgg", .optionalPronounsInSubjectPosition) -- Mangghuer
  , ("mgu", .subjectPronounsInDifferentPosition) -- Musgu
  , ("mhu", .subjectPronounsInDifferentPosition) -- Mbalanhu
  , ("min", .optionalPronounsInSubjectPosition) -- Minangkabau
  , ("mir", .subjectAffixesOnVerb) -- Miriwung
  , ("miy", .subjectPronounsInDifferentPosition) -- Miya
  , ("miz", .subjectPronounsInDifferentPosition) -- Mizo
  , ("mka", .obligatoryPronounsInSubjectPosition) -- Mauka
  , ("mkd", .subjectAffixesOnVerb) -- Makonde
  , ("mki", .subjectAffixesOnVerb) -- Mikasuki
  , ("mku", .subjectAffixesOnVerb) -- Maranungku
  , ("mlg", .mixed) -- Malgwa
  , ("mlm", .optionalPronounsInSubjectPosition) -- Mlabri (Minor)
  , ("mlu", .subjectAffixesOnVerb) -- Maleu
  , ("mme", .subjectAffixesOnVerb) -- Mari (Meadow)
  , ("mmw", .subjectAffixesOnVerb) -- Mambwe
  , ("mna", .subjectAffixesOnVerb) -- Muna
  , ("mnd", .optionalPronounsInSubjectPosition) -- Mandarin
  , ("mne", .subjectAffixesOnVerb) -- Maidu (Northeast)
  , ("mnm", .subjectAffixesOnVerb) -- Manam
  , ("mns", .subjectAffixesOnVerb) -- Mansi
  , ("mny", .obligatoryPronounsInSubjectPosition) -- Margany
  , ("moe", .subjectAffixesOnVerb) -- Mordvin (Erzya)
  , ("mof", .subjectPronounsInDifferentPosition) -- Mofu-Gudur
  , ("moh", .subjectAffixesOnVerb) -- Mohawk
  , ("mok", .optionalPronounsInSubjectPosition) -- Mokilese
  , ("mon", .optionalPronounsInSubjectPosition) -- Mon
  , ("moo", .obligatoryPronounsInSubjectPosition) -- Mooré
  , ("mou", .subjectAffixesOnVerb) -- Moru
  , ("mpr", .subjectAffixesOnVerb) -- Maipure
  , ("mpt", .subjectAffixesOnVerb) -- Mian
  , ("mpu", .subjectAffixesOnVerb) -- Mpur
  , ("mra", .subjectAffixesOnVerb) -- Mara
  , ("mrl", .subjectAffixesOnVerb) -- Murle
  , ("mro", .subjectAffixesOnVerb) -- Moro
  , ("mrt", .optionalPronounsInSubjectPosition) -- Martuthunira
  , ("msc", .subjectAffixesOnVerb) -- Muisca
  , ("msl", .subjectAffixesOnVerb) -- Masalit
  , ("mss", .subjectAffixesOnVerb) -- Miwok (Southern Sierra)
  , ("mtb", .subjectAffixesOnVerb) -- Matuumbi
  , ("mua", .subjectAffixesOnVerb) -- Makua
  , ("mum", .subjectPronounsInDifferentPosition) -- Mumuye
  , ("mun", .subjectCliticsOnVariableHost) -- Mundari
  , ("mup", .obligatoryPronounsInSubjectPosition) -- Mupun
  , ("mus", .subjectPronounsInDifferentPosition) -- Mussau
  , ("mut", .subjectCliticsOnVariableHost) -- Mutsun
  , ("mwb", .obligatoryPronounsInSubjectPosition) -- Manobo (Western Bukidnon)
  , ("mxc", .mixed) -- Mixtec (Chalcatongo)
  , ("myi", .subjectAffixesOnVerb) -- Mangarrayi
  , ("mym", .optionalPronounsInSubjectPosition) -- Malayalam
  , ("mzh", .subjectAffixesOnVerb) -- Mazatec (Huautla)
  , ("nab", .subjectAffixesOnVerb) -- Nabak
  , ("nag", .subjectAffixesOnVerb) -- Nagatman
  , ("naj", .subjectAffixesOnVerb) -- Neo-Aramaic (Arbel Jewish)
  , ("nak", .optionalPronounsInSubjectPosition) -- Nakanai
  , ("nal", .subjectPronounsInDifferentPosition) -- Nalik
  , ("nam", .obligatoryPronounsInSubjectPosition) -- Namia
  , ("nan", .subjectAffixesOnVerb) -- Nandi
  , ("nav", .subjectAffixesOnVerb) -- Navajo
  , ("nbd", .subjectAffixesOnVerb) -- Nubian (Dongolese)
  , ("nbm", .obligatoryPronounsInSubjectPosition) -- Ngbaka (Ma'bo)
  , ("ndb", .subjectAffixesOnVerb) -- Ndebele
  , ("ndj", .subjectAffixesOnVerb) -- Ndjébbana
  , ("ndo", .obligatoryPronounsInSubjectPosition) -- Ndonga
  , ("ndt", .obligatoryPronounsInSubjectPosition) -- Ndut
  , ("ndy", .obligatoryPronounsInSubjectPosition) -- Ndyuka
  , ("nez", .subjectAffixesOnVerb) -- Nez Perce
  , ("nga", .subjectAffixesOnVerb) -- Nganasan
  , ("ngi", .subjectCliticsOnVariableHost) -- Ngiyambaa
  , ("ngj", .obligatoryPronounsInSubjectPosition) -- Ngadjumaja
  , ("ngo", .subjectAffixesOnVerb) -- Ngoni
  , ("ngz", .subjectPronounsInDifferentPosition) -- Ngizim
  , ("nha", .subjectCliticsOnVariableHost) -- Nhanda
  , ("nhh", .subjectAffixesOnVerb) -- Nahuatl (Huasteca)
  , ("nhm", .subjectAffixesOnVerb) -- Nahuatl (Michoacán)
  , ("nhn", .subjectAffixesOnVerb) -- Nahuatl (North Puebla)
  , ("nht", .subjectAffixesOnVerb) -- Nahuatl (Tetelcingo)
  , ("nia", .mixed) -- Nias
  , ("nis", .optionalPronounsInSubjectPosition) -- Nyishi
  , ("niu", .optionalPronounsInSubjectPosition) -- Niuean
  , ("niv", .optionalPronounsInSubjectPosition) -- Nivkh
  , ("nke", .subjectPronounsInDifferentPosition) -- Nkem
  , ("nko", .subjectAffixesOnVerb) -- Nkore-Kiga
  , ("nmb", .subjectAffixesOnVerb) -- Nambikuára (Southern)
  , ("nnd", .subjectAffixesOnVerb) -- Nend
  , ("non", .obligatoryPronounsInSubjectPosition) -- Noni
  , ("nor", .obligatoryPronounsInSubjectPosition) -- Norwegian
  , ("nph", .optionalPronounsInSubjectPosition) -- Nar-Phu
  , ("nse", .subjectAffixesOnVerb) -- Nsenga
  , ("nsg", .subjectPronounsInDifferentPosition) -- Nisgha
  , ("nsn", .mixed) -- Nisenan
  , ("nti", .subjectAffixesOnVerb) -- Ngiti
  , ("ntj", .mixed) -- Ngaanyatjarra
  , ("ntu", .subjectAffixesOnVerb) -- Nenets
  , ("nua", .subjectAffixesOnVerb) -- Nuaulu
  , ("nue", .subjectAffixesOnVerb) -- Nuer
  , ("nug", .subjectAffixesOnVerb) -- Nunggubuyu
  , ("nuu", .subjectCliticsOnVariableHost) -- Nuuchahnulth
  , ("nwd", .subjectAffixesOnVerb) -- Newar (Dolakha)
  , ("nya", .obligatoryPronounsInSubjectPosition) -- Nyawaygi
  , ("nym", .subjectAffixesOnVerb) -- Nyamwezi
  , ("nyn", .subjectAffixesOnVerb) -- Nyigina
  , ("nyu", .subjectAffixesOnVerb) -- Nyulnyul
  , ("obg", .subjectAffixesOnVerb) -- Ogbronuagum
  , ("obo", .subjectAffixesOnVerb) -- Obolo
  , ("ocu", .subjectAffixesOnVerb) -- Ocuilteco
  , ("oji", .subjectCliticsOnVariableHost) -- Ojibwa (Eastern)
  ]

/-- Rows 501 to 711 of `allData`. -/
def allData_1 : List (String × ExpressionOfPronominalSubjects) :=
  [ ("olo", .subjectAffixesOnVerb) -- Olo
  , ("ond", .subjectAffixesOnVerb) -- Oneida
  , ("ood", .subjectCliticsOnVariableHost) -- O'odham
  , ("orh", .subjectAffixesOnVerb) -- Oromo (Harar)
  , ("oro", .subjectAffixesOnVerb) -- Orokaiva
  , ("ory", .subjectPronounsInDifferentPosition) -- Orya
  , ("osa", .subjectAffixesOnVerb) -- Osage
  , ("otm", .subjectAffixesOnVerb) -- Otomí (Mezquital)
  , ("pae", .subjectCliticsOnVariableHost) -- Páez
  , ("pai", .subjectAffixesOnVerb) -- Paiwan
  , ("pam", .obligatoryPronounsInSubjectPosition) -- Pame
  , ("pan", .subjectAffixesOnVerb) -- Panjabi
  , ("pau", .subjectAffixesOnVerb) -- Paumarí
  , ("pga", .subjectAffixesOnVerb) -- Pilagá
  , ("pkn", .subjectAffixesOnVerb) -- Paakantyi
  , ("pkt", .subjectAffixesOnVerb) -- Pokot
  , ("plh", .subjectAffixesOnVerb) -- Paulohi
  , ("plk", .obligatoryPronounsInSubjectPosition) -- Palikur
  , ("pms", .subjectAffixesOnVerb) -- Paamese
  , ("pno", .obligatoryPronounsInSubjectPosition) -- Paiute (Northern)
  , ("pog", .subjectAffixesOnVerb) -- Pogoro
  , ("pol", .subjectCliticsOnVariableHost) -- Polish
  , ("por", .subjectAffixesOnVerb) -- Portuguese
  , ("pra", .subjectAffixesOnVerb) -- Prasuni
  , ("pre", .subjectAffixesOnVerb) -- Pare
  , ("prs", .subjectAffixesOnVerb) -- Persian
  , ("psm", .subjectCliticsOnVariableHost) -- Passamaquoddy-Maliseet
  , ("pso", .obligatoryPronounsInSubjectPosition) -- Pomo (Southeastern)
  , ("pul", .subjectPronounsInDifferentPosition) -- Puluwat
  , ("pwn", .subjectAffixesOnVerb) -- Pawnee
  , ("qim", .subjectAffixesOnVerb) -- Quechua (Imbabura)
  , ("qum", .subjectAffixesOnVerb) -- Sipakapense
  , ("ram", .subjectAffixesOnVerb) -- Rama
  , ("rap", .optionalPronounsInSubjectPosition) -- Rapanui
  , ("rem", .subjectAffixesOnVerb) -- Remo
  , ("rim", .subjectAffixesOnVerb) -- Rimi
  , ("rit", .subjectCliticsOnVariableHost) -- Ritharngu
  , ("rny", .subjectAffixesOnVerb) -- Runyankore
  , ("ron", .subjectPronounsInDifferentPosition) -- Ron
  , ("rov", .obligatoryPronounsInSubjectPosition) -- Roviana
  , ("rru", .subjectAffixesOnVerb) -- Runyoro-Rutooro
  , ("ruk", .subjectAffixesOnVerb) -- Rukai (Tanan)
  , ("rum", .optionalPronounsInSubjectPosition) -- Rumu
  , ("run", .subjectAffixesOnVerb) -- Runga
  , ("rus", .obligatoryPronounsInSubjectPosition) -- Russian
  , ("rut", .subjectAffixesOnVerb) -- Rutul
  , ("sah", .obligatoryPronounsInSubjectPosition) -- Sahu
  , ("sak", .subjectAffixesOnVerb) -- Sakao
  , ("san", .subjectAffixesOnVerb) -- Sango
  , ("sap", .optionalPronounsInSubjectPosition) -- Sapuan
  , ("sar", .subjectAffixesOnVerb) -- Sare
  , ("scr", .subjectAffixesOnVerb) -- Serbian-Croatian
  , ("sdw", .obligatoryPronounsInSubjectPosition) -- Sandawe
  , ("ser", .subjectAffixesOnVerb) -- Seri
  , ("ses", .subjectPronounsInDifferentPosition) -- Sesotho
  , ("sgb", .subjectAffixesOnVerb) -- Sougb
  , ("sgl", .subjectAffixesOnVerb) -- Sengele
  , ("sgu", .subjectAffixesOnVerb) -- Sangu
  , ("shm", .subjectAffixesOnVerb) -- Shambala
  , ("shp", .mixed) -- Klikitat
  , ("shu", .subjectAffixesOnVerb) -- Shuswap
  , ("sid", .subjectAffixesOnVerb) -- Sidaama
  , ("sio", .subjectAffixesOnVerb) -- Sio
  , ("sis", .obligatoryPronounsInSubjectPosition) -- Sisiqa
  , ("siu", .subjectAffixesOnVerb) -- Siuslaw
  , ("skm", .subjectAffixesOnVerb) -- Sukuma
  , ("skp", .subjectAffixesOnVerb) -- Selkup
  , ("sla", .subjectAffixesOnVerb) -- Slave
  , ("slb", .subjectAffixesOnVerb) -- Saliba (in Papua New Guinea)
  , ("slo", .subjectAffixesOnVerb) -- Slovene
  , ("sml", .subjectAffixesOnVerb) -- Semelai
  , ("snm", .obligatoryPronounsInSubjectPosition) -- Sanuma
  , ("snn", .obligatoryPronounsInSubjectPosition) -- Soninke
  , ("so", .subjectAffixesOnVerb) -- So
  , ("sob", .subjectAffixesOnVerb) -- Sobei
  , ("som", .subjectPronounsInDifferentPosition) -- Somali
  , ("spa", .subjectAffixesOnVerb) -- Spanish
  , ("squ", .subjectAffixesOnVerb) -- Squamish
  , ("srb", .subjectAffixesOnVerb) -- Sorbian
  , ("src", .subjectAffixesOnVerb) -- Sarcee
  , ("sro", .subjectAffixesOnVerb) -- Siroi
  , ("stn", .subjectAffixesOnVerb) -- Sotho (Northern)
  , ("sue", .optionalPronounsInSubjectPosition) -- Suena
  , ("sul", .subjectAffixesOnVerb) -- Sulka
  , ("sup", .obligatoryPronounsInSubjectPosition) -- Supyire
  , ("swa", .subjectAffixesOnVerb) -- Swahili
  , ("swe", .obligatoryPronounsInSubjectPosition) -- Swedish
  , ("tab", .obligatoryPronounsInSubjectPosition) -- Taba
  , ("taf", .obligatoryPronounsInSubjectPosition) -- Taiof
  , ("taj", .subjectAffixesOnVerb) -- Tajik
  , ("tar", .subjectAffixesOnVerb) -- Tariana
  , ("tau", .subjectAffixesOnVerb) -- Tauya
  , ("tbl", .obligatoryPronounsInSubjectPosition) -- Tabla
  , ("tbw", .subjectAffixesOnVerb) -- Tabwa
  , ("ten", .subjectAffixesOnVerb) -- Tennet
  , ("tep", .subjectAffixesOnVerb) -- Tepehua (Tlachichilco)
  , ("tes", .subjectAffixesOnVerb) -- Teso
  , ("tet", .subjectAffixesOnVerb) -- Tetela
  , ("tgh", .subjectAffixesOnVerb) -- Tuareg (Ghat)
  , ("tgk", .subjectPronounsInDifferentPosition) -- Tigak
  , ("tgn", .subjectAffixesOnVerb) -- Tugun
  , ("tgr", .subjectAffixesOnVerb) -- Tigré
  , ("tha", .optionalPronounsInSubjectPosition) -- Thai
  , ("thy", .obligatoryPronounsInSubjectPosition) -- Kuuk Thaayorre
  , ("tid", .mixed) -- Tidore
  , ("tim", .optionalPronounsInSubjectPosition) -- Timugon
  , ("tin", .subjectPronounsInDifferentPosition) -- Tinrin
  , ("tiv", .subjectPronounsInDifferentPosition) -- Tiv
  , ("tiw", .subjectAffixesOnVerb) -- Tiwi
  , ("tja", .subjectAffixesOnVerb) -- Tiipay (Jamul)
  , ("tki", .subjectAffixesOnVerb) -- Tuki
  , ("tkl", .subjectAffixesOnVerb) -- Takelma
  , ("tkm", .subjectAffixesOnVerb) -- Turkmen
  , ("tla", .subjectPronounsInDifferentPosition) -- Tolai
  , ("tli", .subjectAffixesOnVerb) -- Tlingit
  , ("tlo", .subjectAffixesOnVerb) -- Tobelo
  , ("tmc", .subjectAffixesOnVerb) -- Timucua
  , ("tmr", .subjectAffixesOnVerb) -- Temiar
  , ("tna", .subjectAffixesOnVerb) -- Turkana
  , ("tnc", .subjectAffixesOnVerb) -- Tanacross
  , ("tnk", .subjectPronounsInDifferentPosition) -- Tungak
  , ("tob", .subjectAffixesOnVerb) -- Toba
  , ("ton", .subjectAffixesOnVerb) -- Tonkawa
  , ("toz", .subjectAffixesOnVerb) -- Tonga (in Zambia)
  , ("tpn", .mixed) -- Tepehuan (Northern)
  , ("tps", .subjectAffixesOnVerb) -- Tepehuan (Southeastern)
  , ("trb", .subjectAffixesOnVerb) -- Teribe
  , ("trr", .subjectAffixesOnVerb) -- Tairora
  , ("tru", .obligatoryPronounsInSubjectPosition) -- Trumai
  , ("tsi", .subjectPronounsInDifferentPosition) -- Tsimshian (Coast)
  , ("tsk", .subjectAffixesOnVerb) -- Tamashek
  , ("tsn", .subjectPronounsInDifferentPosition) -- Tsonga
  , ("tsz", .subjectAffixesOnVerb) -- Tsez
  , ("tte", .subjectAffixesOnVerb) -- Tutelo
  , ("tuk", .subjectAffixesOnVerb) -- Tukang Besi
  , ("tun", .subjectAffixesOnVerb) -- Tunica
  , ("tur", .subjectAffixesOnVerb) -- Turkish
  , ("tus", .subjectAffixesOnVerb) -- Tuscarora
  , ("tuv", .subjectAffixesOnVerb) -- Tuvan
  , ("tvo", .subjectAffixesOnVerb) -- Tatar
  , ("tvt", .obligatoryPronounsInSubjectPosition) -- Tutsa
  , ("uby", .subjectAffixesOnVerb) -- Ubykh
  , ("udm", .subjectAffixesOnVerb) -- Udmurt
  , ("uhi", .obligatoryPronounsInSubjectPosition) -- Uradhi
  , ("ukr", .obligatoryPronounsInSubjectPosition) -- Ukrainian
  , ("uld", .subjectAffixesOnVerb) -- Uldeme
  , ("una", .subjectAffixesOnVerb) -- Una
  , ("ung", .subjectAffixesOnVerb) -- Ungarinjin
  , ("ura", .subjectAffixesOnVerb) -- Ura
  , ("urk", .subjectAffixesOnVerb) -- Urubú-Kaapor
  , ("url", .optionalPronounsInSubjectPosition) -- Urak Lawoi'
  , ("urn", .subjectAffixesOnVerb) -- Urarina
  , ("usa", .subjectAffixesOnVerb) -- Usan
  , ("usr", .subjectAffixesOnVerb) -- Usarufa
  , ("ute", .subjectCliticsOnVariableHost) -- Ute
  , ("uyg", .obligatoryPronounsInSubjectPosition) -- Uyghur
  , ("uzb", .subjectAffixesOnVerb) -- Uzbek
  , ("vai", .obligatoryPronounsInSubjectPosition) -- Vai
  , ("ven", .subjectAffixesOnVerb) -- Venda
  , ("vie", .optionalPronounsInSubjectPosition) -- Vietnamese
  , ("wai", .subjectAffixesOnVerb) -- Wai Wai
  , ("wal", .subjectAffixesOnVerb) -- Walman
  , ("wam", .subjectPronounsInDifferentPosition) -- Wambaya
  , ("war", .subjectPronounsInDifferentPosition) -- Wari'
  , ("was", .subjectAffixesOnVerb) -- Washo
  , ("wat", .subjectCliticsOnVariableHost) -- Watjarri
  , ("way", .subjectAffixesOnVerb) -- Wayampi
  , ("wed", .subjectPronounsInDifferentPosition) -- Wedau
  , ("wic", .subjectAffixesOnVerb) -- Wichita
  , ("wir", .optionalPronounsInSubjectPosition) -- Wirangu
  , ("wiy", .subjectAffixesOnVerb) -- Wiyot
  , ("wlf", .subjectPronounsInDifferentPosition) -- Wolof
  , ("wlm", .subjectPronounsInDifferentPosition) -- Walmatjari
  , ("wma", .subjectAffixesOnVerb) -- West Makian
  , ("wol", .subjectPronounsInDifferentPosition) -- Woleaian
  , ("wrb", .subjectCliticsOnVariableHost) -- Warrnambool
  , ("wrd", .subjectAffixesOnVerb) -- Wardaman
  , ("wrg", .optionalPronounsInSubjectPosition) -- Warrgamay
  , ("wrk", .subjectAffixesOnVerb) -- Warekena
  , ("wrl", .subjectCliticsOnVariableHost) -- Warlpiri
  , ("wrm", .subjectAffixesOnVerb) -- Warembori
  , ("wrw", .subjectAffixesOnVerb) -- Warrwa
  , ("wry", .subjectAffixesOnVerb) -- Waray (in Australia)
  , ("wth", .subjectCliticsOnVariableHost) -- Wathawurrung
  , ("wya", .subjectAffixesOnVerb) -- Wyandot
  , ("xho", .subjectPronounsInDifferentPosition) -- Xhosa
  , ("yag", .subjectCliticsOnVariableHost) -- Yagua
  , ("yah", .mixed) -- Yahgan
  , ("yal", .subjectAffixesOnVerb) -- Yale (Kosarek)
  , ("yao", .subjectAffixesOnVerb) -- Yao (in Malawi)
  , ("yaq", .mixed) -- Yaqui
  , ("yar", .subjectAffixesOnVerb) -- Yareba
  , ("yel", .subjectAffixesOnVerb) -- Yelî Dnye
  , ("ygr", .subjectAffixesOnVerb) -- Yagaria
  , ("yid", .optionalPronounsInSubjectPosition) -- Yidiny
  , ("yim", .subjectAffixesOnVerb) -- Yimas
  , ("yin", .optionalPronounsInSubjectPosition) -- Yindjibarndi
  , ("yko", .subjectAffixesOnVerb) -- Yukaghir (Kolyma)
  , ("yng", .subjectCliticsOnVariableHost) -- Yingkarta
  , ("yor", .optionalPronounsInSubjectPosition) -- Yoruba
  , ("ypk", .subjectAffixesOnVerb) -- Yup'ik (Central)
  , ("yuc", .subjectAffixesOnVerb) -- Yuchi
  , ("yuk", .subjectCliticsOnVariableHost) -- Yukulta
  , ("yur", .subjectAffixesOnVerb) -- Yurok
  , ("yuw", .optionalPronounsInSubjectPosition) -- Yuwaalaraay
  , ("ywl", .subjectAffixesOnVerb) -- Yawelmani
  , ("zai", .subjectAffixesOnVerb) -- Zapotec (Isthmus)
  , ("zap", .subjectAffixesOnVerb) -- Zapotec (Mitla)
  , ("zay", .subjectAffixesOnVerb) -- Zayse
  , ("zqc", .subjectAffixesOnVerb) -- Zoque (Copainalá)
  , ("zul", .subjectAffixesOnVerb) -- Zulu
  ]

/-- The WALS 101A coding: each language's value, keyed by its WALS code (711 languages). -/
def allData : List (String × ExpressionOfPronominalSubjects) := allData_0 ++ allData_1

/-- Rows 1 to 500 of `sources`. -/
def sources_0 : List (String × List String) :=
  [ ("aar", ["Hayward-1990a[474]"]) -- Aari
  , ("abk", ["Hewitt-1979[102]"]) -- Abkhaz
  , ("abu", ["Berry-1995b[35]"]) -- Abun
  , ("abv", ["Kratochvil-2007[10]"]) -- Abui
  , ("acg", ["Wilson-and-Levinsohn-1992[6]"]) -- Achagua
  , ("acl", ["Crazzolara-1955[65]"]) -- Acholi
  , ("aco", ["Maring-1967[43, 113]"]) -- Acoma
  , ("aeg", ["Gary-and-Gamal-Eldin-1982[60, 100-101]"]) -- Arabic (Egyptian)
  , ("aga", ["Goddard-1967[19]"]) -- Agarabi
  , ("agt", ["Crowley-1981[passim]"]) -- Anguthimri
  , ("ain", ["Shibatani-1990[30]", "Refsing-1986[212]"]) -- Ainu
  , ("aja", ["Santandrea-1976[146]"]) -- Aja
  , ("ala", ["Bruce-1984[131]"]) -- Alamblak
  , ("alb", ["Newmark-et-al-1982[264]"]) -- Albanian
  , ("all", ["Symonds-1989[17]"]) -- Ala'ala
  , ("aln", ["Niggemeyer-1951[56]"]) -- Alune
  , ("amb", ["Wilson-1980[passim]"]) -- Ambulas
  , ("amh", ["Cotterell-1964[11]"]) -- Amharic
  , ("aml", ["Hyslop-2001[passim]"]) -- Ambae (Lolovoli Northeast)
  , ("amp", ["Wilkins-1989[226]"]) -- Arrernte (Mparntwe)
  , ("amq", ["Silzer-1983[141]"]) -- Ambai
  , ("amr", ["Harrell-1962[41, 46]"]) -- Arabic (Moroccan)
  , ("amx", ["Ingram-2001"]) -- Anamuxra
  , ("ane", ["Thurston-1982[41-42]"]) -- Anêm
  , ("ang", ["Litteral-1980[53-61]"]) -- Anggor
  , ("anj", ["Lynch-2000[114]"]) -- Anejom
  , ("any", ["Lusted-1976[505-506]"]) -- Anywa
  , ("ao", ["Gowda-1975[63]"]) -- Ao
  , ("aoj", ["Alungum-et-al-1978[94]"]) -- Mufian
  , ("apl", ["Koehn-and-Koehn-1986[108, 107]"]) -- Apalaí
  , ("apu", ["Polak-1894[7]", "Facundes-2000[146, 386]"]) -- Apurinã
  , ("apw", ["Edgerton-1963[103]"]) -- Apache (Western)
  , ("ara", ["Pet-1987[57-58, 23-24]"]) -- Lokono
  , ("arg", ["Holes-1990[77, 160]"]) -- Arabic (Gulf)
  , ("arp", ["Conrad-and-Wogiga-1991[14-15]"]) -- Arapesh (Mountain)
  , ("arq", ["Erwin-1963[84]"]) -- Arabic (Iraqi)
  , ("arw", ["Gulian-1965[50-51]"]) -- Armenian (Western)
  , ("asm", ["Voorhoeve-1965[85-86]"]) -- Asmat
  , ("ass", ["Goswami-and-Tamuli-2003[422]"]) -- Assamese
  , ("asy", ["Cowell-1964[418, 548]"]) -- Arabic (Syrian)
  , ("ata", ["Rau-1992[passim]"]) -- Atayal
  , ("ath", ["Ebert-1997b[23ff., 160ff.]"]) -- Athpare
  , ("awa", ["Loving-and-McKaughan-1973[37, 39]"]) -- Awa
  , ("awp", ["Curnow-1997[181, 182, 184, 193, 200]"]) -- Awa Pit
  , ("awt", ["Feldman-1986[53]"]) -- Awtuw
  , ("aym", ["Wexler-1967[60, 74, 95]", "Ebbing-1965[120-122]"]) -- Aymara (Central)
  , ("ayr", ["Adelaar-2004[passim]"]) -- Ayoreo
  , ("bab", ["Schaub-1985[107]"]) -- Babungo
  , ("bae", ["Aikhenvald-1996[27]"]) -- Baré
  , ("bas", ["Schurle-1912[passim]"]) -- Basaá
  , ("baw", ["Reichle-1981[55]"]) -- Bawm
  , ("bbl", ["Leitch-1994[191]"]) -- Babole
  , ("bbw", ["Evans-2004"]) -- Bininj Gun-Wok
  , ("bco", ["Davis-and-Saunders-1997[24]", "Davis-and-Saunders-1978[63, 38]"]) -- Bella Coola
  , ("bej", ["Almkvist-1881[85, 130]", "Reinisch-1893[141, 146, 183]"]) -- Beja
  , ("bel", ["Bickel-2003[551]"]) -- Belhare
  , ("bem", ["van-Sambeek-1955[43]"]) -- Bemba
  , ("bfg", ["Kossmann-1997[125]"]) -- Berber (Figuig)
  , ("bgr", ["Boyeldieu-2000[155, 159-167]"]) -- Bagiro
  , ("bid", ["Alio-1986[195]"]) -- Bidiya
  , ("big", ["Santandrea-1956[29-30]"]) -- Binga
  , ("bii", ["Terrill-1998[25]"]) -- Biri
  , ("bik", ["van-den-Heuvel-2006[106]"]) -- Biak
  , ("bil", ["Obata-2003"]) -- Bilua
  , ("bin", ["Wilson-1996[passim]"]) -- Binandere
  , ("bio", ["Hamlin-1998[12, 16]"]) -- Nai
  , ("bir", ["Bouquiaux-1970[299ff]"]) -- Birom
  , ("bkr", ["Woollams-1996[108]"]) -- Batak (Karo)
  , ("bku", ["Kagaya-1992[31]"]) -- Bakueri
  , ("bla", ["Taylor-1969b[259-269]"]) -- Blackfoot
  , ("ble", ["Carteron-1972[41]"]) -- Baoulé
  , ("bln", ["Reinisch-1882[105]"]) -- Bilin
  , ("blx", ["Einaudi-1976[68]"]) -- Biloxi
  , ("blz", ["Fudemann-1999[55]"]) -- Balanta
  , ("bma", ["Penchoen-1973b[56]"]) -- Berber (Middle Atlas)
  , ("bmb", ["Jacobs-1970[198]"]) -- Bimoba
  , ("bnb", ["Rumsey-2000[50]"]) -- Bunuba
  , ("bnn", ["Lincoln-1976[74]"]) -- Banoni
  , ("bob", ["Whitehead-1899[60]"]) -- Bobangi
  , ("bol", ["Mamet-1960[43]"]) -- Bolia
  , ("bre", ["Ternes-1970[252, 254, 260, 269-272]"]) -- Breton
  , ("brf", ["Kossmann-2000[54]"]) -- Berber (Rif)
  , ("brh", ["Bray-1909[76]"]) -- Brahui
  , ("brm", ["Okell-1969[passim]"]) -- Burmese
  , ("brn", ["Kiessling-1994[122]"]) -- Burunge
  , ("brp", ["Corris-2005[66, 72, 79, 84]"]) -- Barupu
  , ("brr", ["Huestis-1963[passim]"]) -- Bororo
  , ("brs", ["Jones-and-Jones-1991[166]"]) -- Barasano
  , ("bsh", ["Edmiston-1932[183]"]) -- Bushoong
  , ("bsk", ["Poppe-1964[44]"]) -- Bashkir
  , ("bsq", ["Saltarelli-et-al-1988[205]"]) -- Basque
  , ("bsr", ["Ferry-1981[58]"]) -- Basari
  , ("bud", ["Lukas-and-Nachtigal-1939[50-55]"]) -- Buduma
  , ("bul", ["Scatton-1993[234]"]) -- Bulgarian
  , ("bum", ["Tryon-2002[582]"]) -- Buma
  , ("bur", ["Tiffou-and-Pesot-1989[54-55, 39]", "Lorimer-1935[244ff]"]) -- Burushaski
  , ("bus", ["Wedekind-1972[passim]"]) -- Busa
  , ("buw", ["Bates-1904[passim]"]) -- Bulu
  , ("bvi", ["Ross-2002c[374]"]) -- Bali-Vitu
  , ("bya", ["Trivedi-1991[82ff]"]) -- Byansi
  , ("cah", ["Seiler-1977[133]"]) -- Cahuilla
  , ("cai", ["Last-and-Lucassen-1998[396]"]) -- Chai
  , ("cav", ["Guillaume-2004[76-79]"]) -- Cavineña
  , ("cax", ["Payne-1981[13-14, 23]"]) -- Campa (Axininca)
  , ("cba", ["Beeler-1976[255]"]) -- Chumash (Barbareño)
  , ("cct", ["Davies-1981c[32]"]) -- Choctaw
  , ("cde", ["Hall-1988[passim]"]) -- Carib (De'kwana)
  , ("cea", ["Ellis-1975[passim]"]) -- Cree (Swampy)
  , ("cem", ["Lynch-2002c[passim]"]) -- Cèmuhî
  -- Cherokee
  , ("che", ["Cook-1979[13, 22, 24, 41-44]", "Foley-1980[30]", "Scancarelli-1987[35-37]",
      "Holmes-and-Smith-1976[294-296]"])
  , ("chg", ["Hutton-1987[passim]"]) -- Chang
  , ("chh", ["Leslau-1950[28-29]"]) -- Chaha
  , ("chi", ["Dixon-1910[passim]"]) -- Chimariko
  , ("chk", ["Dunn-1999[120]"]) -- Chukchi
  , ("chn", ["Noonan-2003b[334]"]) -- Chantyal
  , ("chs", ["Naylor-1925[passim]"]) -- Chin (Siyin)
  , ("chx", ["Waterhouse-1967[359]"]) -- Chontal (Huamelultec Oaxaca)
  , ("cic", ["Bentley-and-Kulemeka-2001[14]"]) -- Chichewa
  , ("cld", ["Sara-1974[68]"]) -- Chaldean (Modern)
  , ("cle", ["Rupp-1989[passim]"]) -- Chinantec (Lealao)
  , ("cln", ["Alexander-Bakkerus-2005[197ff]"]) -- Cholón
  , ("cmh", ["Press-1979[77]"]) -- Chemehuevi
  , ("cmn", ["Wistrand-Robinson-and-Armagost-1990[311]"]) -- Comanche
  , ("cmy", ["Knowles-1984[76-82]"]) -- Chontal Maya
  , ("coo", ["Frachtenberg-1922a[321]"]) -- Coos (Hanis)
  , ("cre", ["Wolfart-1973[passim]"]) -- Cree (Plains)
  , ("crn", ["Jenner-1904[118-119, 135, 137]"]) -- Cornish
  , ("cro", ["Lowie-1941[34]"]) -- Crow
  , ("cti", ["Henderson-1965[32, 109]"]) -- Chin (Tiddim)
  , ("ctl", ["Hualde-1992[passim]"]) -- Catalan
  , ("cub", ["Morse-and-Maxwell-1999a[38-54]"]) -- Cubeo
  , ("cup", ["Hill-2005[77]"]) -- Cupeño
  , ("cyv", ["Key-1967[28-30]"]) -- Cayuvava
  , ("cze", ["Short-1993b[34]"]) -- Czech
  , ("dag", ["Murane-1974[39]"]) -- Daga
  , ("dds", ["Kervran-and-Prost-1969[43, 106]"]) -- Donno So
  , ("des", ["Miller-1999[64]"]) -- Desano
  , ("dga", ["Bodomo-1997[passim]"]) -- Dagaare
  , ("dgb", ["Olawsky-1999[21]"]) -- Dagbani
  , ("dha", ["Tosco-2001[258-266]"]) -- Dhaasanac
  , ("dhi", ["Cain-and-Gair-2000[37]"]) -- Dhivehi
  , ("die", ["Langdon-1970[146]"]) -- Diegueño (Mesa Grande)
  , ("dig", ["Sastry-1984[182]"]) -- Digaro
  , ("dim", ["Fleming-1990[522]"]) -- Dime
  , ("din", ["Nebel-1948[53]"]) -- Dinka
  , ("dio", ["Sapir-1965[90-91]"]) -- Diola-Fogny
  , ("djp", ["Morphy-1983[passim]"]) -- Djapu
  , ("dlm", ["de-Sousa-2006[passim]"]) -- Dla (Menggwa)
  , ("dni", ["Bromley-1981[passim]"]) -- Dani (Lower Grand Valley)
  , ("dom", ["Macalister-1914[27, 29]"]) -- Domari
  , ("doy", ["Wiering-and-Wiering-1994[passim]"]) -- Doyayo
  , ("dre", ["Moyse-Faurie-1983[143]"]) -- Drehu
  , ("dsh", ["Bredsdorff-1958[97, 99]", "Allan-et-al-1995[244]"]) -- Danish
  , ("dum", ["Ross-1980[93]"]) -- Dumo
  , ("dut", ["Shetter-1958[28-29]"]) -- Dutch
  , ("ebi", ["Adive-1989[77ff]"]) -- Ebira
  , ("efi", ["Welmers-1968a[7]"]) -- Efik
  , ("egn", ["Thomas-1978[65]"]) -- Engenni
  , ("eip", ["Heeschen-1998[149, 223]"]) -- Eipo
  , ("eko", ["Schadeberg-and-Mucanheia-2000[passim]"]) -- Ekoti
  , ("emb", ["Loewen-1958[passim]"]) -- Emberá (Northern)
  , ("eme", ["Rose-2003b[79, 151, passim]"]) -- Émérillon
  , ("ene", ["Kunnap-1999a[37]"]) -- Enets
  , ("epe", ["Harms-1994[10]"]) -- Epena Pedee
  , ("err", ["Crowley-1998a[158]"]) -- Erromangan
  , ("esm", ["Adelaar-2004[156]"]) -- Esmeraldeño
  , ("est", ["de-Sivers-1969[47-48]"]) -- Estonian
  , ("eve", ["Nedjalkov-1997[195]"]) -- Evenki
  , ("ewe", ["Warburton-et-al-1968[5]"]) -- Ewe
  , ("ewo", ["Redden-1979[20, 81]"]) -- Ewondo
  , ("fij", ["Dixon-1988[passim]"]) -- Fijian
  , ("fin", ["Sulkala-and-Karjalainen-1992[120, 272]"]) -- Finnish
  , ("fri", ["Tiersma-1985[69]"]) -- Frisian
  , ("fua", ["Stennes-1967[106-107]"]) -- Fulfulde (Adamawa)
  , ("fur", ["Tucker-and-Bryan-1966[passim]"]) -- Fur
  , ("fut", ["Dougherty-1983[passim]"]) -- Futuna-Aniwa
  , ("fye", ["Nettle-1998[passim]"]) -- Fyem
  , ("ga", ["Ablorh-Odjidja-1968[passim]"]) -- Gã
  , ("gaa", ["Harvey-2002[207]"]) -- Gaagudju
  , ("gae", ["Calder-1923[221]"]) -- Gaelic (Scots)
  , ("gah", ["Deibler-1976[8]"]) -- Gahuku
  , ("gar", ["Burling-2003[390]"]) -- Garo
  , ("gds", ["Frantz-and-McKaughan-1973[440]"]) -- Gadsup
  , ("geo", ["Aronson-1991[242]"]) -- Georgian
  , ("ger", ["Lederer-1969[46, 48]"]) -- German
  , ("gim", ["Breeze-1990[30-31]"]) -- Gimira
  , ("gjj", ["Bendor-Samuel-1972[83, 86-90]"]) -- Guajajara
  , ("gln", ["Bunn-1974[21]"]) -- Golin
  , ("gmw", ["Olson-1988[58]"]) -- Gumawana
  , ("gmz", ["Bender-1979[49]", "Uzar-1989[371-373, 376]"]) -- Gumuz
  , ("goe", ["Hellwig-2003[41]"]) -- Goemai
  , ("goo", ["McGregor-1990[passim]"]) -- Gooniyandi
  , ("grb", ["Innes-1966[50, 101]"]) -- Grebo
  , ("grg", ["Green-1995[162-169]"]) -- Gurr-goni
  , ("grj", ["Miller-1996a[76]"]) -- Guarijío
  , ("grk", ["Joseph-and-Philippaki-Warburton-1987[36]"]) -- Greek (Modern)
  , ("grw", ["Schultz-Lorentzen-1945[53]", "Fortescue-1984[289]"]) -- Greenlandic (West)
  , ("gua", ["Gregores-and-Suarez-1967[131-132]"]) -- Guaraní
  , ("gud", ["Hoskison-1983[passim]"]) -- Gude
  , ("gul", ["Nougayrol-1999[124]"]) -- Gula (in Central African Republic)
  , ("gum", ["Eades-1979[passim]"]) -- Gumbaynggir
  , ("gur", ["Glover-1974[passim]"]) -- Gurung
  , ("guu", ["Haviland-1979[101]"]) -- Guugu Yimidhirr
  , ("gwa", ["Hyman-and-Magaji-1970[passim]"]) -- Gwari
  , ("gwo", ["Adwiraah-1989[passim]"]) -- Gworok
  , ("gyc", ["Lin-1993[358]"]) -- Gyarong (Cogtse)
  , ("hai", ["Enrico-2003[passim]"]) -- Haida
  , ("ham", ["Oates-and-Oates-1968[29]"]) -- Hamtai
  , ("hat", ["Reesink-1999[passim]"]) -- Hatam
  , ("hau", ["Newman-2000[passim]"]) -- Hausa
  , ("haw", ["Elbert-and-Pukui-1979[108]"]) -- Hawaiian
  , ("hay", ["Michailovsky-1988[200]"]) -- Hayu
  , ("heb", ["Glinert-1989[53]"]) -- Hebrew (Modern)
  , ("heh", ["Velten-1899a[179]"]) -- Hehe
  , ("hei", ["Rath-1981[passim]"]) -- Heiltsuk
  , ("hix", ["Derbyshire-1985[32]", "Derbyshire-1979[37]"]) -- Hixkaryana
  , ("hlu", ["Galloway-1993[243]"]) -- Halkomelem (Upriver)
  , ("hma", ["Dutta-Baruah-and-Bapui-1996[passim]"]) -- Hmar
  , ("hmi", ["Minor-et-al-1982[15]"]) -- Huitoto (Minica)
  , ("hmo", ["Lyman-1979[passim]"]) -- Hmong Njua
  , ("hnd", ["Kahombo-1992[45-48]"]) -- Hunde
  , ("hua", ["Haiman-1980[passim]"]) -- Hua
  , ("hun", ["Kenesei-et-al-1998[263]"]) -- Hungarian
  , ("hya", ["Byarushengo-1977[11]"]) -- Haya
  , ("iaa", ["Tryon-1968[52-53]"]) -- Iaai
  , ("iba", ["Omar-1981[passim]"]) -- Iban
  , ("ice", ["Thrainsson-1994[168]"]) -- Icelandic
  , ("ifu", ["Newell-1993[passim]"]) -- Ifugao (Batad)
  , ("igb", ["Emenanjo-1978[passim]"]) -- Igbo
  , ("ige", ["Bergman-1981[9]"]) -- Igede
  , ("ik", ["Tucker-1972[184]"]) -- Ik
  , ("ika", ["Frank-1990[51]"]) -- Ika
  , ("ila", ["Smith-1907[80]"]) -- Ila
  , ("imo", ["Seiler-1985[passim]"]) -- Imonda
  , ("ina", ["de-Vries-1996[36]"]) -- Inanwatan
  , ("ind", ["Sneddon-1996a[passim]"]) -- Indonesian
  , ("iri", ["Dillon-and-O-Croinin-1961[32]", "O-Siadhail-1989[179-184]"]) -- Irish
  , ("irq", ["Nordbustad-1988[30]"]) -- Iraqw
  , ("isa", ["Donohue-and-San-Roque-2002[52]"]) -- I'saka
  , ("ita", ["Maiden-and-Robustelli-2000[93]"]) -- Italian
  , ("ite", ["Georg-and-Volodin-1999[142-143]", "Volodin-1976[220-236]"]) -- Itelmen
  , ("ito", ["Camp-and-Liccardi-1967[passim]"]) -- Itonama
  , ("izi", ["Meier-et-al-1975[236]"]) -- Izi
  , ("jab", ["Dempwolff-1939[57]"]) -- Jabêm
  , ("jak", ["Craig-1977[119]"]) -- Jakaltek
  , ("jam", ["Schultze-Berndt-2000[85]"]) -- Jaminjung
  , ("jmo", ["Persson-and-Persson-1991[13]", "Persson-1981[111]"]) -- Jur Mödö
  , ("jng", ["Hertz-1917[4]"]) -- Jingpho
  , ("jpn", ["Hinds-1986[75, 108]"]) -- Japanese
  , ("juh", ["Dickens-1992[passim]"]) -- Ju|'hoan
  , ("juk", ["Shimuzu-1980[passim]"]) -- Jukun
  , ("jwr", ["Dixon-2003[165-167]"]) -- Jarawara
  , ("kaa", ["Gabas-1999[passim]"]) -- Karó (Arára)
  , ("kab", ["Colarusso-1989[302]"]) -- Kabardian
  , ("kae", ["Clifton-1997[34]"]) -- Kaki Ae
  , ("kam", ["Klamer-1998[62]"]) -- Kambera
  , ("kan", ["Ikoro-1996[117-118]"]) -- Kana
  , ("kas", ["Wali-and-Koul-1997[249]"]) -- Kashmiri
  , ("kau", ["Ross-2002i[389]"]) -- Kaulong
  , ("kay", ["Evans-1995[passim]"]) -- Kayardild
  , ("kba", ["Whiteley-and-Muli-1962[18]"]) -- Kamba
  , ("kby", ["Lebikaza-1999[456]"]) -- Kabiyé
  , ("kch", ["Heath-1999b[passim]"]) -- Koyra Chiini
  , ("kdw", ["Sandalo-1997[36]"]) -- Kadiwéu
  , ("kel", ["Ross-2002k[142]"]) -- Kele
  , ("ken", ["Vandame-1968[35]"]) -- Kenga
  , ("kew", ["Franklin-1971[39, 40]"]) -- Kewa
  , ("kfe", ["Rennison-1997[312]"]) -- Koromfe
  , ("kga", ["Wolff-1905[passim]"]) -- Kinga
  , ("kgr", ["Last-1886[57]"]) -- Kagulu
  , ("kgz", ["Hebert-and-Poppe-1963[15]"]) -- Kirghiz
  , ("kha", ["Poppe-1970[155]"]) -- Khalkha
  , ("kho", ["Hagman-1977[passim]"]) -- Nama
  , ("khs", ["Nagaraja-1985[87]"]) -- Khasi
  , ("kik", ["Barlow-1960[70]"]) -- Kikuyu
  , ("kio", ["Watkins-1984[110ff]"]) -- Kiowa
  , ("kis", ["Childs-1995[passim]"]) -- Kisi
  , ("kkt", ["Palmer-2002[passim]"]) -- Kokota
  , ("kku", ["Drake-1903[63-64]"]) -- Korku
  , ("kkv", ["Counts-1969[69]"]) -- Lusi
  , ("klm", ["Gatschet-1890[417, 433]"]) -- Klamath
  , ("klv", ["Senft-1986[47]"]) -- Kilivila
  , ("kma", ["Seki-2000[137-139]"]) -- Kamaiurá
  , ("kmb", ["de-Vries-1989[145-147]"]) -- Kombai
  , ("kmh", ["Watters-1998[328]"]) -- Kham
  , ("kmj", ["Novelli-1985[200, 231]"]) -- Karimojong
  , ("kmp", ["Geary-1977[25-26]"]) -- Kunimaipa
  , ("kms", ["Kunnap-1999b[21]"]) -- Kamass
  , ("kmu", ["Smalley-1961[passim]"]) -- Khmu'
  , ("kmz", ["Sanders-and-Sanders-1994[15]"]) -- Kamasau
  , ("knc", ["Smith-and-Johnson-2000[passim]"]) -- Kugu Nganhcara
  , ("knd", ["Schiffman-1983[56, passim]", "Sridhar-1990[221-222]"]) -- Kannada
  , ("knm", ["Tucker-and-Bryan-1966[341]"]) -- Kunama
  , ("kno", ["Bacelar-2004[187, 232]"]) -- Kanoê
  , ("knr", ["Hutchison-1976[passim]", "Hutchison-1981[96-97]"]) -- Kanuri
  , ("knw", ["Ultan-1967[102-105]"]) -- Konkow
  , ("koa", ["Kimball-1991[58-87]"]) -- Koasati
  , ("kob", ["Davies-1981b[108-109, 166]"]) -- Kobon
  , ("koe", ["Hieda-1998[360]"]) -- Koegu
  , ("kon", ["Bentley-1887[647]"]) -- Kongo
  , ("kor", ["Sohn-1999[passim]"]) -- Korean
  , ("krb", ["Cowell-1951[57, 108]"]) -- Kiribati
  , ("krc", ["Seegmiller-1996[30]"]) -- Karachay-Balkar
  , ("krd", ["Abdulla-and-McCarus-1967[179]"]) -- Kurdish (Central)
  , ("kre", ["Santandrea-1976[59, 100]"]) -- Kresh
  , ("krk", ["Bright-1957[58]"]) -- Karok
  , ("krn", ["Meinhof-1930[passim]"]) -- Korana
  , ("kro", ["Reh-1985[164]"]) -- Krongo
  , ("krr", ["Wivell-1981[95]"]) -- Kairiru
  , ("krw", ["van-Enk-and-de-Vries-1997[90]"]) -- Korowai
  , ("ksa", ["Davis-1960[118]", "Davis-1964[128]"]) -- Keresan (Santa Ana)
  , ("kse", ["Heath-1999a[10]"]) -- Koyraboro Senni
  , ("kty", ["Honti-1988[185-186]"]) -- Khanty
  , ("kwa", ["Keesing-1985[passim]"]) -- Kwaio
  , ("kwk", ["Boas-1911a[535]"]) -- Kwakw'ala
  , ("kwn", ["Dammann-1957[51-59]"]) -- Kwangali
  , ("kwt", ["Spencer-2008[107]"]) -- Kwomtari
  , ("kwz", ["van-der-Voort-2004[passim]"]) -- Kwaza
  , ("kxo", ["Kohler-1981[546]"]) -- Kxoe
  , ("kyk", ["Draper-and-Draper-2002[9]"]) -- Kyaka
  , ("kyl", ["Solnit-1986[44]"]) -- Kayah Li (Eastern)
  , ("kyr", ["Rigden-nd-a[passim]"]) -- Karkar-Yuri
  , ("laa", ["Boyeldieu-1982[passim]"]) -- Laal
  , ("lad", ["Koshal-1979[passim]"]) -- Ladakhi
  , ("lah", ["Matisoff-1973[passim]"]) -- Lahu
  , ("lai", ["Hay-Neave-1953[passim]"]) -- Lai
  , ("lal", ["Bjorverud-1998[passim]"]) -- Lalo
  , ("lan", ["Noonan-1992[119]"]) -- Lango
  , ("lat", ["Mathiassen-1997[197]"]) -- Latvian
  , ("lav", ["Terrill-1999"]) -- Lavukaleve
  , ("lbu", ["Kawasha-2003[147]"]) -- Lunda
  , ("lda", ["Ashton-et-al-1954[32, 90-91]"]) -- Luganda
  , ("ldo", ["Kuperus-1985[129]"]) -- Londo
  , ("leg", ["Meeussen-1971[438]"]) -- Lega
  , ("lel", ["Frajzyngier-2001[100]"]) -- Lele
  , ("len", ["Lynch-1978[45, 54]"]) -- Lenakel
  , ("lep", ["Mainwaring-1876[passim]"]) -- Lepcha
  , ("let", ["van-Engelenhoven-1995[127]"]) -- Leti
  , ("lez", ["Haspelmath-1993[402]"]) -- Lezgian
  , ("lgi", ["Seidel-1898[399]"]) -- Langi
  , ("lgu", ["Hill-2002[passim]"]) -- Longgu
  , ("lil", ["van-Eijk-1997[163]"]) -- Lillooet
  , ("lim", ["van-Driem-1987[25]"]) -- Limbu
  , ("lin", ["Meeuwis-1998[41]"]) -- Lingala
  , ("lit", ["Ambrazas-1997[599]"]) -- Lithuanian
  , ("lkt", ["Buechel-1939[passim]"]) -- Lakhota
  , ("llm", ["Hoftmann-1971[47]"]) -- Lelemi
  , ("lmb", ["Doke-1922[43]"]) -- Lamba
  , ("lml", ["Harvey-2001[80]"]) -- Limilngan
  , ("lmn", ["Trail-1970[102, 145]"]) -- Lamani
  , ("lmp", ["Walker-1976[12]"]) -- Lampung
  , ("lon", ["Hamel-1985[166]"]) -- Loniu
  , ("lou", ["Stutzman-1997[passim]"]) -- Lou
  , ("luc", ["Fleisch-2001[117]"]) -- Lucazi
  , ("lul", ["Adelaar-2004[passim]"]) -- Lule
  , ("luo", ["Omondi-1982[35-39, 102-103, 358-359]"]) -- Luo
  , ("luv", ["Horton-1949[64]"]) -- Luvale
  , ("luy", ["Appleby-1961[passim]"]) -- Luyia
  , ("maa", ["Tucker-and-Mpaayei-1955[15]"]) -- Maasai
  , ("mab", ["Trenga-1947[130]"]) -- Maba
  , ("mac", ["Carson-1982[94-103, 127-129]", "Abbott-1991[101, 83, 123]"]) -- Macushi
  , ("mad", ["Tucker-and-Bryan-1966[42]", "Tucker-1967[137]"]) -- Ma'di
  , ("mae", ["Capell-1962a[25]"]) -- Mae
  , ("maj", ["Unseth-1989[102]"]) -- Majang
  , ("mal", ["Domenichini-Ramiaramanana-1977[61]"]) -- Malagasy
  , ("mao", ["Bauer-1993[148ff., 366]"]) -- Maori
  , ("map", ["Augusta-1903[9, 28]"]) -- Mapudungun
  , ("mar", ["Gordon-1986[16]"]) -- Maricopa
  , ("mas", ["Caitucoli-1986[passim]"]) -- Masa
  , ("mau", ["Capell-and-Hinch-1970[66]"]) -- Maung
  , ("may", ["Brown-1990[passim]"]) -- Maybrat
  , ("mbl", ["De-Rop-1971[56]"]) -- Mbole
  , ("mbo", ["Vormann-and-Scharfenberger-1914[50]"]) -- Monumbo
  , ("mbr", ["Tourneux-et-al-1986[passim]"]) -- Mbara
  , ("mbt", ["Tucker-and-Bryan-1966[33]"]) -- Mangbetu
  , ("mby", ["Fortier-1971[30]"]) -- Mbay
  , ("mcc", ["Adelaar-2004[337]"]) -- Mochica
  , ("mcv", ["Grondona-1998[96ff]"]) -- Mocoví
  , ("mdn", ["Kennard-1936[9]"]) -- Mandan
  , ("mea", ["Gravelle-2004[70]"]) -- Meyah
  , ("mee", ["Will-1989[140-141]"]) -- Me'en
  , ("meh", ["Simeone-Senelle-1997[402]"]) -- Mehri
  , ("mei", ["Chelliah-1997[passim]"]) -- Meithei
  , ("mek", ["Galucio-2001[80]"]) -- Mekens
  , ("men", ["Bloomfield-1962[36ff., 57, 103, 104, 148]"]) -- Menomini
  , ("mgg", ["Slater-2003[115]"]) -- Mangghuer
  , ("mgu", ["Meyer-Bahlburg-1972[113-115]"]) -- Musgu
  , ("mhu", ["Fourie-1993[passim]"]) -- Mbalanhu
  , ("min", ["Moussay-1981[91]"]) -- Minangkabau
  , ("mir", ["Kofod-1978[178, 179, 194]"]) -- Miriwung
  , ("miy", ["Schuh-1998[188]"]) -- Miya
  , ("miz", ["Chhangte-1989[passim]"]) -- Mizo
  , ("mka", ["Ebermann-1986a[passim]"]) -- Mauka
  , ("mkd", ["Harries-1940[106]"]) -- Makonde
  , ("mki", ["Boynton-1982[113]"]) -- Mikasuki
  , ("mku", ["Tryon-1970b[passim]"]) -- Maranungku
  , ("mlg", ["Lohr-2002[121]"]) -- Malgwa
  , ("mlm", ["Rischel-1995[171]"]) -- Mlabri (Minor)
  , ("mlu", ["Haywood-1996[150]"]) -- Maleu
  , ("mme", ["Sebeok-and-Ingemann-1961[14, 18]", "Kangasmaa-Minn-1998[230]"]) -- Mari (Meadow)
  , ("mmw", ["London-Missionary-Society-1962[12]"]) -- Mambwe
  , ("mna", ["van-den-Berg-1989b[50, 82, 162]"]) -- Muna
  , ("mnd", ["Li-and-Thompson-1981[657ff]"]) -- Mandarin
  , ("mne", ["Shipley-1964[45-46]"]) -- Maidu (Northeast)
  , ("mnm", ["Gregersen-1976[101]", "Lichtenberk-1983[111]"]) -- Manam
  , ("mns", ["Murphy-1968[78]"]) -- Mansi
  , ("mny", ["Breen-1981a[passim]"]) -- Margany
  , ("moe", ["Zaicz-1998[198-199]"]) -- Mordvin (Erzya)
  , ("mof", ["Barreteau-1988[50]"]) -- Mofu-Gudur
  , ("moh", ["Bonvillain-1973[66]"]) -- Mohawk
  , ("mok", ["Harrison-and-Albert-1976[91]"]) -- Mokilese
  , ("mon", ["Bauer-1982a[passim]"]) -- Mon
  , ("moo", ["Lehr-et-al-1966[passim]"]) -- Mooré
  , ("mou", ["Tucker-and-Bryan-1966[47]"]) -- Moru
  , ("mpr", ["Zamponi-2003a[23]"]) -- Maipure
  , ("mpt", ["Fedden-2007[248]"]) -- Mian
  , ("mpu", ["Ode-2002[52]"]) -- Mpur
  , ("mra", ["Heath-1981[197-199, 206ff]"]) -- Mara
  , ("mrl", ["Lyth-1971[55]", "Tucker-and-Bryan-1966[383]"]) -- Murle
  , ("mro", ["Black-and-Black-1971[8]"]) -- Moro
  , ("mrt", ["Dench-1995[passim]"]) -- Martuthunira
  , ("msc", ["Adelaar-2004[passim]"]) -- Muisca
  , ("msl", ["Edgar-1989[74]"]) -- Masalit
  , ("mss", ["Broadbent-1964[92]"]) -- Miwok (Southern Sierra)
  , ("mtb", ["Odden-1996[71]"]) -- Matuumbi
  , ("mua", ["Woodward-1926[281]"]) -- Makua
  , ("mum", ["Shimizu-1983[passim]"]) -- Mumuye
  , ("mun", ["Sinha-1975[passim]"]) -- Mundari
  , ("mup", ["Frajzyngier-1993[passim]"]) -- Mupun
  , ("mus", ["Ross-2002b[161]"]) -- Mussau
  , ("mut", ["Okrand-1977[passim]"]) -- Mutsun
  , ("mwb", ["Elkins-1970[66-67]"]) -- Manobo (Western Bukidnon)
  , ("mxc", ["Macaulay-1996[73]"]) -- Mixtec (Chalcatongo)
  , ("myi", ["Merlan-1982[41, 99]"]) -- Mangarrayi
  , ("mym", ["Asher-and-Kumari-1997[156]"]) -- Malayalam
  , ("mzh", ["Pike-1967[324]"]) -- Mazatec (Huautla)
  , ("nab", ["Fabian-et-al-1998[40]"]) -- Nabak
  , ("nag", ["Campbell-and-Campbell-1987[37]"]) -- Nagatman
  , ("naj", ["Khan-1999[313, 330]"]) -- Neo-Aramaic (Arbel Jewish)
  , ("nak", ["Johnston-1980[passim]"]) -- Nakanai
  , ("nal", ["Volker-1998[46]"]) -- Nalik
  , ("nam", ["Feldpausch-and-Feldpausch-1992[passim]"]) -- Namia
  , ("nan", ["Creider-and-Creider-1989[167-168]", "Hollis-1909[191]"]) -- Nandi
  , ("nav", ["Young-and-Morgan-1980[22]"]) -- Navajo
  , ("nbd", ["Armbruster-1960[346]"]) -- Nubian (Dongolese)
  , ("nbm", ["Thomas-1963[73]"]) -- Ngbaka (Ma'bo)
  , ("ndb", ["Bowern-and-Lotridge-2002[32]", "Ziervogel-1959[133]"]) -- Ndebele
  , ("ndj", ["McKay-2000[218]"]) -- Ndjébbana
  , ("ndo", ["Fivaz-1986[141-142]"]) -- Ndonga
  , ("ndt", ["Morgan-1996[passim]"]) -- Ndut
  , ("ndy", ["Huttar-and-Huttar-1994[521]"]) -- Ndyuka
  , ("nez", ["Aoki-1970[105]"]) -- Nez Perce
  , ("nga", ["Helimski-1998a[502]"]) -- Nganasan
  , ("ngi", ["Donaldson-1980[passim]"]) -- Ngiyambaa
  , ("ngj", ["von-Brandenstein-1980[16]"]) -- Ngadjumaja
  , ("ngo", ["Ngonyani-2003[52]"]) -- Ngoni
  , ("ngz", ["Schuh-1972[passim]"]) -- Ngizim
  , ("nha", ["Blevins-2001[passim]"]) -- Nhanda
  , ("nhh", ["Beller-and-Beller-1979[269]"]) -- Nahuatl (Huasteca)
  , ("nhm", ["Sischo-1979[351]"]) -- Nahuatl (Michoacán)
  , ("nhn", ["Brockway-1979[170]"]) -- Nahuatl (North Puebla)
  , ("nht", ["Tuggy-1979[81]"]) -- Nahuatl (Tetelcingo)
  , ("nia", ["Brown-2001"]) -- Nias
  , ("nis", ["Tayeng-1990a[11]"]) -- Nyishi
  , ("niu", ["Seiter-1980[51]"]) -- Niuean
  , ("niv", ["Panfilov-1962[7]"]) -- Nivkh
  , ("nke", ["Sibomana-1986[271]"]) -- Nkem
  , ("nko", ["Taylor-1985[150, 170]"]) -- Nkore-Kiga
  , ("nmb", ["Lowe-1999[passim]"]) -- Nambikuára (Southern)
  , ("nnd", ["Harris-1990[119]"]) -- Nend
  , ("non", ["Hyman-1981b[77]"]) -- Noni
  , ("nor", ["Olson-1901[59]"]) -- Norwegian
  , ("nph", ["Noonan-2003a[passim]"]) -- Nar-Phu
  , ("nse", ["Ranger-1928[63]"]) -- Nsenga
  , ("nsg", ["Tarpent-1987[334, 336]"]) -- Nisgha
  , ("nsn", ["Eatough-1999[passim]"]) -- Nisenan
  , ("nti", ["Kutsch-Lojenga-1994[190ff., 233]"]) -- Ngiti
  , ("ntj", ["Douglas-1964[passim]"]) -- Ngaanyatjarra
  , ("ntu", ["Collinder-1957[448ff]"]) -- Nenets
  , ("nua", ["Bolton-1990[36]"]) -- Nuaulu
  , ("nue", ["Crazzolara-1933[102]"]) -- Nuer
  , ("nug", ["Hughes-and-Healy-1971[47]", "Heath-1984[347]"]) -- Nunggubuyu
  , ("nuu", ["Davidson-2002"]) -- Nuuchahnulth
  , ("nya", ["Dixon-1983[passim]"]) -- Nyawaygi
  , ("nym", ["Maganga-and-Schadeberg-1992[97]"]) -- Nyamwezi
  , ("nyn", ["Stokes-1982[39, 233]"]) -- Nyigina
  , ("nyu", ["McGregor-1996[40]"]) -- Nyulnyul
  , ("obg", ["Kari-2000[passim]"]) -- Ogbronuagum
  , ("obo", ["Faraclas-1984[9, 12]"]) -- Obolo
  , ("ocu", ["Muntzel-1986[138]"]) -- Ocuilteco
  , ("oji", ["Valentine-2001[pp.142-pp.143]"]) -- Ojibwa (Eastern)
  , ("olo", ["Staley-1995[16]"]) -- Olo
  , ("ood", ["Saxton-1982[109]"]) -- O'odham
  , ("orh", ["Owens-1985[60, 66]"]) -- Oromo (Harar)
  , ("oro", ["Healey-et-al-1969[35, 40]"]) -- Orokaiva
  , ("ory", ["Fields-1997[263]"]) -- Orya
  , ("otm", ["Hess-1968[21]"]) -- Otomí (Mezquital)
  , ("pae", ["Slocum-1986[58-61, 66-68, 74-78]"]) -- Páez
  , ("pai", ["Egli-1990[passim]"]) -- Paiwan
  , ("pam", ["Manrique-1967[344, 347]"]) -- Pame
  ]

/-- Rows 501 to 696 of `sources`. -/
def sources_1 : List (String × List String) :=
  [ ("pan", ["Gill-and-Gleason-1963[229, 294]"]) -- Panjabi
  , ("pau", ["Chapman-and-Derbyshire-1991[286-287]"]) -- Paumarí
  , ("pga", ["Vidal-2001[132]"]) -- Pilagá
  , ("pkn", ["Hercus-1982[159]"]) -- Paakantyi
  , ("pkt", ["Crazzolara-1978[77-78, 81]", "Tucker-and-Bryan-1966[469-470]"]) -- Pokot
  , ("plh", ["Stresemann-1918[28]"]) -- Paulohi
  , ("plk", ["Green-and-Green-1972[passim]"]) -- Palikur
  , ("pms", ["Crowley-1982[129]"]) -- Paamese
  , ("pno", ["Snapp-et-al-1982[74-77]"]) -- Paiute (Northern)
  , ("pog", ["Hendle-1907[35]"]) -- Pogoro
  , ("pol", ["Stone-1980[13, 34ff]"]) -- Polish
  , ("por", ["Hutchinson-and-Lloyd-1996[35]"]) -- Portuguese
  , ("pra", ["Morgenstierne-1949[234, 236]"]) -- Prasuni
  , ("pre", ["Kotz-1964[7-9]", "Kagaya-1989[26]"]) -- Pare
  , ("prs", ["Lambton-1967[11]", "Rastorgueva-1964[34]"]) -- Persian
  , ("psm", ["Ng-2002"]) -- Passamaquoddy-Maliseet
  , ("pso", ["Moshinsky-1974[passim]"]) -- Pomo (Southeastern)
  , ("pul", ["Elbert-1974[passim]"]) -- Puluwat
  , ("pwn", ["Parks-1976[164]"]) -- Pawnee
  , ("qim", ["Cole-1982[69, 88, 129]"]) -- Quechua (Imbabura)
  , ("qum", ["Barrett-1999[76]"]) -- Sipakapense
  , ("ram", ["Grinevald-1988[104]"]) -- Rama
  , ("rap", ["Chapin-1978[140]"]) -- Rapanui
  , ("rem", ["Fernandez-1967[112]"]) -- Remo
  , ("rim", ["Olson-1964[96]"]) -- Rimi
  , ("rit", ["Heath-1980a[88]"]) -- Ritharngu
  , ("rny", ["Morris-and-Kirwan-1972[128]"]) -- Runyankore
  , ("ron", ["Seibert-1998[passim]"]) -- Ron
  , ("rov", ["Corston-Oliver-2002[passim]"]) -- Roviana
  , ("rru", ["Rubongoya-1999[passim]"]) -- Runyoro-Rutooro
  , ("ruk", ["Li-1973[78, 161]"]) -- Rukai (Tanan)
  , ("rum", ["Petterson-1999[passim]"]) -- Rumu
  , ("run", ["Nougayrol-1989[53-55]"]) -- Runga
  , ("rus", ["Stilman-and-Harkins-1964[338-343]"]) -- Russian
  , ("rut", ["Alekseev-1994b[240]"]) -- Rutul
  , ("sah", ["Visser-and-Voorhoeve-1987[23, 27]"]) -- Sahu
  , ("sak", ["Guy-1974a[45-46]"]) -- Sakao
  , ("san", ["Samarin-1967b[140-146]"]) -- Sango
  , ("sap", ["Jacq-and-Sidwell-1999[16]"]) -- Sapuan
  , ("sar", ["Sumbuk-2002"]) -- Sare
  , ("scr", ["Partridge-1964[35]"]) -- Serbian-Croatian
  , ("sdw", ["Eaton-2008[127]"]) -- Sandawe
  , ("ser", ["Marlett-1981[57-58]"]) -- Seri
  , ("ses", ["Paroz-1946[passim]"]) -- Sesotho
  , ("sgb", ["Reesink-2002[203, 206-207]"]) -- Sougb
  , ("sgl", ["Mangulu-2001[passim]"]) -- Sengele
  , ("sgu", ["Idiata-1998[passim]"]) -- Sangu
  , ("shm", ["Besha-1993[passim]"]) -- Shambala
  , ("shp", ["Jacobs-1931[142, 143-144]"]) -- Klikitat
  , ("shu", ["Kuipers-1974[46]"]) -- Shuswap
  , ("sid", ["Kawachi-2007[414]"]) -- Sidaama
  , ("sio", ["Clark-and-Clark-1987[53]"]) -- Sio
  , ("sis", ["Ross-2002l[462]"]) -- Sisiqa
  , ("siu", ["Frachtenberg-1914[459, 468]"]) -- Siuslaw
  , ("skm", ["Batibo-1985[passim]"]) -- Sukuma
  , ("skp", ["Helimski-1998b[567]"]) -- Selkup
  , ("sla", ["Rice-1989[253]"]) -- Slave
  , ("slb", ["Margetts-1999b[24]"]) -- Saliba (in Papua New Guinea)
  , ("slo", ["Herrity-2000[90]", "Priestly-1993[437]"]) -- Slovene
  , ("sml", ["Kruspe-1999[423]"]) -- Semelai
  , ("snm", ["Borgman-1990[197]"]) -- Sanuma
  , ("snn", ["Diagana-1995[passim]"]) -- Soninke
  , ("so", ["Serzisko-1989[390]"]) -- So
  , ("sob", ["Sterner-and-Ross-2002[178]"]) -- Sobei
  , ("som", ["Saeed-1987[27-28, 30, 58, 59]", "Kirk-1905[44]"]) -- Somali
  , ("squ", ["Kuipers-1967[85]"]) -- Squamish
  , ("srb", ["Stone-1993[656]"]) -- Sorbian
  , ("src", ["Cook-1984[126]"]) -- Sarcee
  , ("sro", ["Wells-1979[passim]"]) -- Siroi
  , ("stn", ["Louwrens-et-al-1995[44]"]) -- Sotho (Northern)
  , ("sue", ["Wilson-1974[passim]"]) -- Suena
  , ("sul", ["Tharp-1996[90]"]) -- Sulka
  , ("sup", ["Carlson-1994[passim]"]) -- Supyire
  , ("swa", ["Ashton-1947[42]"]) -- Swahili
  , ("swe", ["Holmes-and-Hinchliffe-1994[493]"]) -- Swedish
  , ("tab", ["Bowden-1997a[109]"]) -- Taba
  , ("taf", ["Ross-2002g[436]"]) -- Taiof
  , ("taj", ["Rastorgueva-1963[56]"]) -- Tajik
  , ("tar", ["Aikhenvald-2003"]) -- Tariana
  , ("tau", ["MacDonald-1990[171, 206]"]) -- Tauya
  , ("tbl", ["Abisay-et-al-1983[11]"]) -- Tabla
  , ("tbw", ["de-Beerst-1896[300-302]"]) -- Tabwa
  , ("ten", ["Randal-1998[231]"]) -- Tennet
  , ("tep", ["Watters-1988[289]"]) -- Tepehua (Tlachichilco)
  , ("tes", ["Hilders-and-Lawrance-1956[9-11]"]) -- Teso
  , ("tet", ["Wetshemongo-1996[412]"]) -- Tetela
  , ("tgh", ["Nehlil-1909[41]"]) -- Tuareg (Ghat)
  , ("tgk", ["Beaumont-1979[96]"]) -- Tigak
  , ("tgn", ["Hinton-1991[76]"]) -- Tugun
  , ("tgr", ["Raz-1983[38-39]"]) -- Tigré
  , ("tid", ["van-Staden-2000[77]"]) -- Tidore
  , ("tim", ["Prentice-1971[passim]"]) -- Timugon
  , ("tin", ["Osumi-1995[passim]"]) -- Tinrin
  , ("tiv", ["Abraham-1940[25]"]) -- Tiv
  , ("tiw", ["Osborne-1974[24]"]) -- Tiwi
  , ("tja", ["Miller-2001[135, 140]"]) -- Tiipay (Jamul)
  , ("tki", ["Biloa-1997[26]"]) -- Tuki
  , ("tkl", ["Sapir-1922b[56, 117, 161]"]) -- Takelma
  , ("tkm", ["Clark-1998b[214]"]) -- Turkmen
  , ("tla", ["Franklin-et-al-1974[passim]"]) -- Tolai
  , ("tli", ["Boas-1917[22]"]) -- Tlingit
  , ("tlo", ["Holton-2003[37]"]) -- Tobelo
  , ("tmc", ["Granberry-1993[84]"]) -- Timucua
  , ("tmr", ["Benjamin-1976[158-159, 183]"]) -- Temiar
  , ("tna", ["Dimmendaal-1983a[71, 207]"]) -- Turkana
  , ("tnc", ["Holton-2000[206, 278]"]) -- Tanacross
  , ("tnk", ["Fast-1990[passim]"]) -- Tungak
  , ("tob", ["Klein-2001[30]", "Klein-1973[81, 111-114]"]) -- Toba
  , ("ton", ["Hoijer-1933-1938[72]", "Troike-1967[329]"]) -- Tonkawa
  , ("toz", ["Collins-1962[32]"]) -- Tonga (in Zambia)
  , ("tpn", ["Bascom-1982[349, 370]"]) -- Tepehuan (Northern)
  , ("tps", ["Willett-1991[190]"]) -- Tepehuan (Southeastern)
  , ("trb", ["Quesada-2000[60, 83]"]) -- Teribe
  , ("trr", ["Vincent-1973a[535]", "Vincent-1973b[563]"]) -- Tairora
  , ("tru", ["Guirardello-1999a[passim]"]) -- Trumai
  , ("tsi", ["Mulder-1994[50]"]) -- Tsimshian (Coast)
  , ("tsk", ["Heath-2005[429-430]"]) -- Tamashek
  , ("tsn", ["Baumbach-1987[160]"]) -- Tsonga
  , ("tsz", ["Alekseev-and-Radzhabov-2004[149]"]) -- Tsez
  , ("tte", ["Oliverio-1996[63]"]) -- Tutelo
  , ("tuk", ["Donohue-1999a[51, 113, 152]"]) -- Tukang Besi
  , ("tun", ["Haas-1940[47, 56-57]"]) -- Tunica
  , ("tur", ["Lewis-1967[68]", "Kornfilt-1997[281]"]) -- Turkish
  , ("tus", ["Williams-1976[39]"]) -- Tuscarora
  , ("tuv", ["Anderson-and-Harrison-1999[39]"]) -- Tuvan
  , ("tvo", ["Poppe-1968[122]"]) -- Tatar
  , ("tvt", ["Rekhung-1992[22-24]"]) -- Tutsa
  , ("uby", ["Charachidze-1989[384]"]) -- Ubykh
  , ("udm", ["Tepljashina-1966[270-272]"]) -- Udmurt
  , ("uhi", ["Crowley-1983[passim]"]) -- Uradhi
  , ("ukr", ["Pugh-and-Press-1999[173]"]) -- Ukrainian
  , ("uld", ["de-Colombel-1997[51]"]) -- Uldeme
  , ("una", ["Louwerse-1988[37-45]"]) -- Una
  , ("ung", ["Rumsey-1982[31, 32]"]) -- Ungarinjin
  , ("ura", ["Crowley-1999[184]"]) -- Ura
  , ("urk", ["Kakumasu-1986[392]"]) -- Urubú-Kaapor
  , ("url", ["Hogan-1988[passim]"]) -- Urak Lawoi'
  , ("urn", ["Olawsky-2006[652]"]) -- Urarina
  , ("usa", ["Reesink-1987[94ff]"]) -- Usan
  , ("usr", ["Bee-1973[253]"]) -- Usarufa
  , ("ute", ["Southern-Ute-Tribe-1980[308]"]) -- Ute
  , ("uyg", ["Hahn-1998[394]"]) -- Uyghur
  , ("uzb", ["Sjoberg-1963[66]"]) -- Uzbek
  , ("vai", ["Welmers-1976[passim]"]) -- Vai
  , ("ven", ["Poulos-1990[98]"]) -- Venda
  , ("vie", ["Thompson-1965[248]"]) -- Vietnamese
  , ("wai", ["Hawkins-1998[81ff.]"]) -- Wai Wai
  , ("wam", ["Nordlinger-1993[162]"]) -- Wambaya
  , ("war", ["Everett-and-Kern-1997[passim]"]) -- Wari'
  , ("was", ["Kroeber-1906[301]", "Jacobsen-1964[449]"]) -- Washo
  , ("wat", ["Douglas-1981[passim]"]) -- Watjarri
  , ("way", ["Grenand-1980[68]"]) -- Wayampi
  , ("wed", ["King-1901a[11]"]) -- Wedau
  , ("wic", ["Rood-1976[19]"]) -- Wichita
  , ("wir", ["Hercus-1999a[96]"]) -- Wirangu
  , ("wiy", ["Teeter-1964[44]"]) -- Wiyot
  , ("wlf", ["Njie-1982[passim]"]) -- Wolof
  , ("wlm", ["Hudson-1978[56]"]) -- Walmatjari
  , ("wma", ["Voorhoeve-1982[12]"]) -- West Makian
  , ("wol", ["Sohn-1975[passim]"]) -- Woleaian
  , ("wrb", ["Blake-2003[38]"]) -- Warrnambool
  , ("wrd", ["Merlan-1994[125-127]"]) -- Wardaman
  , ("wrg", ["Dixon-1981[passim]"]) -- Warrgamay
  , ("wrk", ["Aikhenvald-1998[293]"]) -- Warekena
  , ("wrl", ["Capell-1962b[passim]"]) -- Warlpiri
  , ("wrm", ["Donohue-1999b[11]"]) -- Warembori
  , ("wrw", ["McGregor-1994[41]"]) -- Warrwa
  , ("wry", ["Harvey-1986[140, 167]"]) -- Waray (in Australia)
  , ("wth", ["Blake-et-al-1998a[77]"]) -- Wathawurrung
  , ("wya", ["Kopris-2001[147]"]) -- Wyandot
  , ("xho", ["McLaren-1939[40, 42]"]) -- Xhosa
  , ("yag", ["Payne-1990a[passim]"]) -- Yagua
  , ("yah", ["Adelaar-2004[575]"]) -- Yahgan
  , ("yal", ["Heeschen-1992[24, 27]"]) -- Yale (Kosarek)
  , ("yao", ["Whiteley-1966[56]"]) -- Yao (in Malawi)
  , ("yaq", ["Lindenfeld-1973[passim]"]) -- Yaqui
  , ("yar", ["Weimer-and-Weimer-1975[675]"]) -- Yareba
  , ("yel", ["Henderson-1975[825]"]) -- Yelî Dnye
  , ("ygr", ["Renck-1975[18, 85-86]"]) -- Yagaria
  , ("yid", ["Dixon-1977a[204]"]) -- Yidiny
  , ("yim", ["Foley-1991[193ff]"]) -- Yimas
  , ("yin", ["Wordick-1982[104, 129, 80]"]) -- Yindjibarndi
  , ("yko", ["Maslova-1999[625]"]) -- Yukaghir (Kolyma)
  , ("yng", ["Dench-1998[passim]"]) -- Yingkarta
  , ("yor", ["Awobuluyi-1978[22-24]"]) -- Yoruba
  , ("ypk", ["Reed-et-al-1977[127-128, 139]"]) -- Yup'ik (Central)
  , ("yuc", ["Wagner-1934[313-314]"]) -- Yuchi
  , ("yuk", ["Keen-1983[216]"]) -- Yukulta
  , ("yur", ["Robins-1958[passim]"]) -- Yurok
  , ("yuw", ["Williams-1980a[passim]"]) -- Yuwaalaraay
  , ("ywl", ["Newman-1944[passim]"]) -- Yawelmani
  , ("zai", ["Pickett-et-al-1998[29]"]) -- Zapotec (Isthmus)
  , ("zap", ["Briggs-1961[63-65]"]) -- Zapotec (Mitla)
  , ("zay", ["Hayward-1990b[270, 302-308]"]) -- Zayse
  , ("zqc", ["Harrison-et-al-1981[415]"]) -- Zoque (Copainalá)
  , ("zul", ["Ziervogel-et-al-1981[38]"]) -- Zulu
  ]

/-- The sources WALS cites for each language's 101A value, keyed by its WALS code: WALS reference
  keys, with pages in brackets (696 languages). -/
def sources : List (String × List String) := sources_0 ++ sources_1

end Data.WALS.F101A
