module

/-!
# WALS Feature 111A: Nonperiphrastic Causative Constructions
[song-2013-nonperiphrastic]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 111A`.

Chapter 111, 310 languages.
-/

@[expose] public section

namespace Data.WALS.F111A

/-- WALS 111A values. -/
inductive NonperiphrCausativeType where
  /-- Neither (23 languages). -/
  | neither
  /-- Morphological but no compound (254 languages). -/
  | morphologicalOnly
  /-- Compound but no morphological (9 languages). -/
  | compoundOnly
  /-- Both (24 languages). -/
  | both
  deriving DecidableEq, Repr

/-- The WALS 111A coding: each language's value, keyed by its WALS code (310 languages). -/
def allData : List (String × NonperiphrCausativeType) :=
  [ ("abi", .morphologicalOnly) -- Abipón
  , ("abk", .morphologicalOnly) -- Abkhaz
  , ("ace", .morphologicalOnly) -- Acehnese
  , ("aeg", .morphologicalOnly) -- Arabic (Egyptian)
  , ("ain", .morphologicalOnly) -- Ainu
  , ("aji", .morphologicalOnly) -- Ajië
  , ("ala", .both) -- Alamblak
  , ("aly", .morphologicalOnly) -- Alyawarra
  , ("ame", .morphologicalOnly) -- Amele
  , ("amh", .morphologicalOnly) -- Amharic
  , ("ana", .morphologicalOnly) -- Araona
  , ("apu", .morphologicalOnly) -- Apurinã
  , ("arm", .morphologicalOnly) -- Armenian (Eastern)
  , ("aro", .morphologicalOnly) -- Arosi
  , ("asm", .morphologicalOnly) -- Asmat
  , ("atc", .morphologicalOnly) -- Atchin
  , ("awn", .morphologicalOnly) -- Awngi
  , ("awp", .morphologicalOnly) -- Awa Pit
  , ("aym", .morphologicalOnly) -- Aymara (Central)
  , ("bab", .morphologicalOnly) -- Babungo
  , ("bag", .neither) -- Bagirmi
  , ("baj", .morphologicalOnly) -- Bajau (Sama)
  , ("bal", .morphologicalOnly) -- Balinese
  , ("bam", .morphologicalOnly) -- Bambara
  , ("baw", .both) -- Bawm
  , ("bej", .morphologicalOnly) -- Beja
  , ("bkr", .morphologicalOnly) -- Batak (Karo)
  , ("bla", .morphologicalOnly) -- Blackfoot
  , ("blx", .both) -- Biloxi
  , ("bma", .morphologicalOnly) -- Berber (Middle Atlas)
  , ("brh", .morphologicalOnly) -- Brahui
  , ("brm", .both) -- Burmese
  , ("brr", .morphologicalOnly) -- Bororo
  , ("brs", .morphologicalOnly) -- Barasano
  , ("bsq", .morphologicalOnly) -- Basque
  , ("bur", .morphologicalOnly) -- Burushaski
  , ("but", .morphologicalOnly) -- Buriat
  , ("cah", .morphologicalOnly) -- Cahuilla
  , ("car", .morphologicalOnly) -- Carib
  , ("cax", .morphologicalOnly) -- Campa (Axininca)
  , ("cct", .morphologicalOnly) -- Choctaw
  , ("ceb", .morphologicalOnly) -- Cebuano
  , ("cha", .morphologicalOnly) -- Chamorro
  , ("chk", .morphologicalOnly) -- Chukchi
  , ("chv", .morphologicalOnly) -- Chuvash
  , ("cld", .morphologicalOnly) -- Chaldean (Modern)
  , ("cle", .morphologicalOnly) -- Chinantec (Lealao)
  , ("cmn", .morphologicalOnly) -- Comanche
  , ("coa", .morphologicalOnly) -- Coahuilteco
  , ("coo", .morphologicalOnly) -- Coos (Hanis)
  , ("cor", .morphologicalOnly) -- Cora
  , ("cre", .morphologicalOnly) -- Cree (Plains)
  , ("crq", .both) -- Carrier
  , ("cui", .morphologicalOnly) -- Cuiba
  , ("dgr", .morphologicalOnly) -- Dagur
  , ("die", .morphologicalOnly) -- Diegueño (Mesa Grande)
  , ("dio", .morphologicalOnly) -- Diola-Fogny
  , ("diy", .morphologicalOnly) -- Diyari
  , ("djr", .neither) -- Djaru
  , ("doy", .morphologicalOnly) -- Doyayo
  , ("dre", .morphologicalOnly) -- Drehu
  , ("eng", .morphologicalOnly) -- English
  , ("epe", .morphologicalOnly) -- Epena Pedee
  , ("eve", .morphologicalOnly) -- Evenki
  , ("ewe", .neither) -- Ewe
  , ("fij", .morphologicalOnly) -- Fijian
  , ("fin", .morphologicalOnly) -- Finnish
  , ("fre", .both) -- French
  , ("fut", .morphologicalOnly) -- Futuna-Aniwa
  , ("gar", .morphologicalOnly) -- Garo
  , ("geo", .morphologicalOnly) -- Georgian
  , ("ger", .morphologicalOnly) -- German
  , ("goo", .neither) -- Gooniyandi
  , ("grb", .morphologicalOnly) -- Grebo
  , ("grk", .neither) -- Greek (Modern)
  , ("grw", .morphologicalOnly) -- Greenlandic (West)
  , ("gua", .morphologicalOnly) -- Guaraní
  , ("guj", .morphologicalOnly) -- Gujarati
  , ("guu", .morphologicalOnly) -- Guugu Yimidhirr
  , ("hai", .morphologicalOnly) -- Haida
  , ("hau", .morphologicalOnly) -- Hausa
  , ("haw", .morphologicalOnly) -- Hawaiian
  , ("heb", .morphologicalOnly) -- Hebrew (Modern)
  , ("hin", .morphologicalOnly) -- Hindi
  , ("hix", .morphologicalOnly) -- Hixkaryana
  , ("hmi", .morphologicalOnly) -- Huitoto (Minica)
  , ("hmo", .neither) -- Hmong Njua
  , ("hun", .morphologicalOnly) -- Hungarian
  , ("hzb", .morphologicalOnly) -- Hunzib
  , ("iaa", .morphologicalOnly) -- Iaai
  , ("igb", .morphologicalOnly) -- Igbo
  , ("ika", .morphologicalOnly) -- Ika
  , ("ila", .morphologicalOnly) -- Ila
  , ("ind", .morphologicalOnly) -- Indonesian
  , ("ing", .morphologicalOnly) -- Ingush
  , ("iri", .neither) -- Irish
  , ("irq", .morphologicalOnly) -- Iraqw
  , ("jak", .morphologicalOnly) -- Jakaltek
  , ("jaq", .morphologicalOnly) -- Jaqaru
  , ("jpn", .morphologicalOnly) -- Japanese
  , ("juh", .compoundOnly) -- Ju|'hoan
  , ("kam", .morphologicalOnly) -- Kambera
  , ("kas", .morphologicalOnly) -- Kashmiri
  , ("kay", .morphologicalOnly) -- Kayardild
  , ("kdz", .morphologicalOnly) -- Kadazan
  , ("kem", .morphologicalOnly) -- Kemant
  , ("ket", .morphologicalOnly) -- Ket
  , ("kew", .morphologicalOnly) -- Kewa
  , ("kfe", .morphologicalOnly) -- Koromfe
  , ("kgu", .morphologicalOnly) -- Kalkatungu
  , ("kha", .morphologicalOnly) -- Khalkha
  , ("khm", .morphologicalOnly) -- Khmer
  , ("kho", .both) -- Nama
  , ("khs", .morphologicalOnly) -- Khasi
  , ("kin", .morphologicalOnly) -- Kinyarwanda
  , ("kio", .morphologicalOnly) -- Kiowa
  , ("kis", .morphologicalOnly) -- Kisi
  , ("kls", .morphologicalOnly) -- Kalispel
  , ("klv", .neither) -- Kilivila
  , ("kmk", .morphologicalOnly) -- Kalmyk
  , ("kmu", .both) -- Khmu'
  , ("knd", .morphologicalOnly) -- Kannada
  , ("knm", .morphologicalOnly) -- Kunama
  , ("knr", .morphologicalOnly) -- Kanuri
  , ("koa", .both) -- Koasati
  , ("kob", .compoundOnly) -- Kobon
  , ("kol", .morphologicalOnly) -- Kolami
  , ("kon", .morphologicalOnly) -- Kongo
  , ("kor", .morphologicalOnly) -- Korean
  , ("kos", .morphologicalOnly) -- Kosraean
  , ("krb", .morphologicalOnly) -- Kiribati
  , ("krk", .morphologicalOnly) -- Karok
  , ("krn", .morphologicalOnly) -- Korana
  , ("kro", .neither) -- Krongo
  , ("kse", .both) -- Koyraboro Senni
  , ("kut", .morphologicalOnly) -- Kutenai
  , ("kwa", .morphologicalOnly) -- Kwaio
  , ("kyl", .compoundOnly) -- Kayah Li (Eastern)
  , ("lad", .morphologicalOnly) -- Ladakhi
  , ("lah", .both) -- Lahu
  , ("lal", .both) -- Lalo
  , ("lan", .morphologicalOnly) -- Lango
  , ("lat", .morphologicalOnly) -- Latvian
  , ("lav", .morphologicalOnly) -- Lavukaleve
  , ("lep", .morphologicalOnly) -- Lepcha
  , ("let", .morphologicalOnly) -- Leti
  , ("lez", .morphologicalOnly) -- Lezgian
  , ("lim", .morphologicalOnly) -- Limbu
  , ("lkt", .both) -- Lakhota
  , ("lmp", .morphologicalOnly) -- Lampung
  , ("luv", .morphologicalOnly) -- Luvale
  , ("maa", .morphologicalOnly) -- Maasai
  , ("mab", .morphologicalOnly) -- Maba
  , ("mac", .morphologicalOnly) -- Macushi
  , ("mak", .morphologicalOnly) -- Makah
  , ("mal", .morphologicalOnly) -- Malagasy
  , ("mao", .morphologicalOnly) -- Maori
  , ("map", .morphologicalOnly) -- Mapudungun
  , ("mar", .both) -- Maricopa
  , ("mau", .morphologicalOnly) -- Maung
  , ("may", .neither) -- Maybrat
  , ("mei", .morphologicalOnly) -- Meithei
  , ("men", .morphologicalOnly) -- Menomini
  , ("mhi", .morphologicalOnly) -- Marathi
  , ("mna", .morphologicalOnly) -- Muna
  , ("mnd", .compoundOnly) -- Mandarin
  , ("mnm", .morphologicalOnly) -- Manam
  , ("mns", .morphologicalOnly) -- Mansi
  , ("mny", .morphologicalOnly) -- Margany
  , ("mrl", .morphologicalOnly) -- Murle
  , ("mrt", .morphologicalOnly) -- Martuthunira
  , ("mss", .morphologicalOnly) -- Miwok (Southern Sierra)
  , ("mul", .neither) -- Mulao
  , ("mun", .both) -- Mundari
  , ("mwb", .morphologicalOnly) -- Manobo (Western Bukidnon)
  , ("mxc", .morphologicalOnly) -- Mixtec (Chalcatongo)
  , ("myi", .both) -- Mangarrayi
  , ("mym", .morphologicalOnly) -- Malayalam
  , ("nav", .neither) -- Navajo
  , ("nbd", .morphologicalOnly) -- Nubian (Dongolese)
  , ("nca", .morphologicalOnly) -- Nicobarese (Car)
  , ("ndo", .morphologicalOnly) -- Ndonga
  , ("ndy", .neither) -- Ndyuka
  , ("neh", .morphologicalOnly) -- Nehan
  , ("nez", .morphologicalOnly) -- Nez Perce
  , ("ngi", .morphologicalOnly) -- Ngiyambaa
  , ("ngl", .morphologicalOnly) -- Ngalakan
  , ("nht", .morphologicalOnly) -- Nahuatl (Tetelcingo)
  , ("niu", .morphologicalOnly) -- Niuean
  , ("niv", .morphologicalOnly) -- Nivkh
  , ("nko", .morphologicalOnly) -- Nkore-Kiga
  , ("nti", .morphologicalOnly) -- Ngiti
  , ("ntu", .morphologicalOnly) -- Nenets
  , ("nug", .morphologicalOnly) -- Nunggubuyu
  , ("nym", .morphologicalOnly) -- Nyamwezi
  , ("oji", .morphologicalOnly) -- Ojibwa (Eastern)
  , ("ond", .morphologicalOnly) -- Oneida
  , ("orh", .morphologicalOnly) -- Oromo (Harar)
  , ("orw", .morphologicalOnly) -- Oromo (Waata)
  , ("otm", .neither) -- Otomí (Mezquital)
  , ("pai", .morphologicalOnly) -- Paiwan
  , ("pal", .morphologicalOnly) -- Palauan
  , ("pan", .morphologicalOnly) -- Panjabi
  , ("pau", .morphologicalOnly) -- Paumarí
  , ("pip", .morphologicalOnly) -- Pipil
  , ("pit", .both) -- Pitjantjatjara
  , ("pkn", .morphologicalOnly) -- Paakantyi
  , ("pms", .neither) -- Paamese
  , ("pny", .morphologicalOnly) -- Panyjima
  , ("ppi", .morphologicalOnly) -- Pitta Pitta
  , ("prh", .morphologicalOnly) -- Pirahã
  , ("prs", .morphologicalOnly) -- Persian
  , ("psh", .morphologicalOnly) -- Pashto
  , ("psm", .morphologicalOnly) -- Passamaquoddy-Maliseet
  , ("pso", .morphologicalOnly) -- Pomo (Southeastern)
  , ("pul", .morphologicalOnly) -- Puluwat
  , ("pwn", .morphologicalOnly) -- Pawnee
  , ("qim", .morphologicalOnly) -- Quechua (Imbabura)
  , ("ram", .both) -- Rama
  , ("rap", .morphologicalOnly) -- Rapanui
  , ("rej", .neither) -- Rejang
  , ("ret", .morphologicalOnly) -- Retuarã
  , ("rot", .morphologicalOnly) -- Rotuman
  , ("ruk", .morphologicalOnly) -- Rukai (Tanan)
  , ("rus", .morphologicalOnly) -- Russian
  , ("sam", .morphologicalOnly) -- Samoan
  , ("saw", .morphologicalOnly) -- Sawu
  , ("sel", .morphologicalOnly) -- Selknam
  , ("shk", .both) -- Shipibo-Konibo
  , ("shn", .morphologicalOnly) -- Shona
  , ("shp", .morphologicalOnly) -- Klikitat
  , ("shu", .morphologicalOnly) -- Shuswap
  , ("sla", .morphologicalOnly) -- Slave
  , ("sml", .morphologicalOnly) -- Semelai
  , ("snh", .morphologicalOnly) -- Sinhala
  , ("snm", .morphologicalOnly) -- Sanuma
  , ("son", .morphologicalOnly) -- Sonsorol-Tobi
  , ("sor", .morphologicalOnly) -- Sora
  , ("spa", .both) -- Spanish
  , ("squ", .morphologicalOnly) -- Squamish
  , ("src", .neither) -- Sarcee
  , ("srn", .morphologicalOnly) -- Sirionó
  , ("sun", .morphologicalOnly) -- Sundanese
  , ("sup", .morphologicalOnly) -- Supyire
  , ("swa", .morphologicalOnly) -- Swahili
  , ("swt", .morphologicalOnly) -- Swati
  , ("tab", .morphologicalOnly) -- Taba
  , ("tag", .morphologicalOnly) -- Tagalog
  , ("tah", .morphologicalOnly) -- Tahitian
  , ("tas", .morphologicalOnly) -- Tashlhiyt
  , ("tel", .morphologicalOnly) -- Telugu
  , ("tgk", .both) -- Tigak
  , ("tha", .neither) -- Thai
  , ("tib", .neither) -- Tibetan (Standard Spoken)
  , ("tim", .morphologicalOnly) -- Timugon
  , ("tiw", .morphologicalOnly) -- Tiwi
  , ("tli", .morphologicalOnly) -- Tlingit
  , ("tml", .morphologicalOnly) -- Tamil
  , ("tmr", .morphologicalOnly) -- Temiar
  , ("tna", .morphologicalOnly) -- Turkana
  , ("tng", .morphologicalOnly) -- Tongan
  , ("tno", .morphologicalOnly) -- Tondano
  , ("ton", .morphologicalOnly) -- Tonkawa
  , ("tru", .compoundOnly) -- Trumai
  , ("tsh", .both) -- Tümpisa Shoshone
  , ("tsi", .morphologicalOnly) -- Tsimshian (Coast)
  , ("tsw", .morphologicalOnly) -- Tswana
  , ("tuk", .morphologicalOnly) -- Tukang Besi
  , ("tun", .both) -- Tunica
  , ("tur", .morphologicalOnly) -- Turkish
  , ("tus", .morphologicalOnly) -- Tuscarora
  , ("tvl", .morphologicalOnly) -- Tuvaluan
  , ("tzo", .morphologicalOnly) -- Tzotzil
  , ("uhi", .morphologicalOnly) -- Uradhi
  , ("uli", .morphologicalOnly) -- Ulithian
  , ("una", .morphologicalOnly) -- Una
  , ("ung", .neither) -- Ungarinjin
  , ("urk", .morphologicalOnly) -- Urubú-Kaapor
  , ("usa", .morphologicalOnly) -- Usan
  , ("ute", .morphologicalOnly) -- Ute
  , ("uzb", .morphologicalOnly) -- Uzbek
  , ("vai", .neither) -- Vai
  , ("vie", .compoundOnly) -- Vietnamese
  , ("wam", .morphologicalOnly) -- Wambaya
  , ("war", .compoundOnly) -- Wari'
  , ("wat", .morphologicalOnly) -- Watjarri
  , ("wch", .morphologicalOnly) -- Wichí
  , ("wic", .morphologicalOnly) -- Wichita
  , ("wma", .morphologicalOnly) -- West Makian
  , ("wol", .morphologicalOnly) -- Woleaian
  , ("wra", .morphologicalOnly) -- Warao
  , ("wrd", .compoundOnly) -- Wardaman
  , ("wrl", .morphologicalOnly) -- Warlpiri
  , ("yag", .morphologicalOnly) -- Yagua
  , ("yap", .morphologicalOnly) -- Yapese
  , ("yaq", .morphologicalOnly) -- Yaqui
  , ("yay", .neither) -- Yay
  , ("yel", .morphologicalOnly) -- Yelî Dnye
  , ("yid", .morphologicalOnly) -- Yidiny
  , ("yim", .both) -- Yimas
  , ("yko", .morphologicalOnly) -- Yukaghir (Kolyma)
  , ("ykt", .morphologicalOnly) -- Yakut
  , ("ynk", .morphologicalOnly) -- Yankuntjatjara
  , ("yor", .neither) -- Yoruba
  , ("ypk", .morphologicalOnly) -- Yup'ik (Central)
  , ("yuc", .compoundOnly) -- Yuchi
  , ("yus", .morphologicalOnly) -- Yupik (Siberian)
  , ("yuw", .morphologicalOnly) -- Yuwaalaraay
  , ("zul", .morphologicalOnly) -- Zulu
  , ("zun", .morphologicalOnly) -- Zuni
  ]

end Data.WALS.F111A
