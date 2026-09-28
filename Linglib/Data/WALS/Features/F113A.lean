module

/-!
# WALS Feature 113A: Symmetric and Asymmetric Standard Negation
[miestamo-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 113A`.

Chapter 113, 297 languages.
-/

@[expose] public section

namespace Data.WALS.F113A

/-- WALS 113A values. -/
inductive NegationSymmetry where
  /-- Symmetric (114 languages). -/
  | symmetric
  /-- Asymmetric (53 languages). -/
  | asymmetric
  /-- Both (130 languages). -/
  | both
  deriving DecidableEq, Repr

/-- The WALS 113A coding: each language's value, keyed by its WALS code (297 languages). -/
def allData : List (String × NegationSymmetry) :=
  [ ("abi", .both) -- Abipón
  , ("abk", .both) -- Abkhaz
  , ("acm", .asymmetric) -- Achumawi
  , ("aco", .both) -- Acoma
  , ("adk", .symmetric) -- Andoke
  , ("aeg", .symmetric) -- Arabic (Egyptian)
  , ("ain", .symmetric) -- Ainu
  , ("ala", .both) -- Alamblak
  , ("alb", .symmetric) -- Albanian
  , ("ame", .both) -- Amele
  , ("ana", .asymmetric) -- Araona
  , ("apl", .asymmetric) -- Apalaí
  , ("apu", .symmetric) -- Apurinã
  , ("arm", .both) -- Armenian (Eastern)
  , ("arp", .both) -- Arapesh (Mountain)
  , ("asm", .both) -- Asmat
  , ("awp", .both) -- Awa Pit
  , ("aym", .asymmetric) -- Aymara (Central)
  , ("bae", .asymmetric) -- Baré
  , ("baf", .both) -- Bafut
  , ("bag", .both) -- Bagirmi
  , ("bam", .both) -- Bambara
  , ("baw", .both) -- Bawm
  , ("bco", .both) -- Bella Coola
  , ("bej", .both) -- Beja
  , ("bir", .symmetric) -- Birom
  , ("bkr", .symmetric) -- Batak (Karo)
  , ("bma", .asymmetric) -- Berber (Middle Atlas)
  , ("bok", .both) -- Boko
  , ("brh", .both) -- Brahui
  , ("brm", .asymmetric) -- Burmese
  , ("brr", .both) -- Bororo
  , ("brs", .symmetric) -- Barasano
  , ("bsq", .asymmetric) -- Basque
  , ("bua", .both) -- Burarra
  , ("bur", .symmetric) -- Burushaski
  , ("can", .both) -- Candoshi
  , ("car", .asymmetric) -- Carib
  , ("cba", .symmetric) -- Chumash (Barbareño)
  , ("cha", .symmetric) -- Chamorro
  , ("chk", .both) -- Chukchi
  , ("chl", .both) -- Chehalis (Upper)
  , ("ckl", .symmetric) -- Chinook (Lower)
  , ("cle", .symmetric) -- Chinantec (Lealao)
  , ("cmn", .both) -- Comanche
  , ("cnl", .symmetric) -- Canela
  , ("cnm", .symmetric) -- Canamarí
  , ("cnt", .both) -- Cantonese
  , ("coo", .symmetric) -- Coos (Hanis)
  , ("cre", .symmetric) -- Cree (Plains)
  , ("crt", .symmetric) -- Chorote
  , ("cui", .both) -- Cuiba
  , ("cyv", .symmetric) -- Cayuvava
  , ("dag", .symmetric) -- Daga
  , ("deg", .asymmetric) -- Degema
  , ("dio", .both) -- Diola-Fogny
  , ("dni", .both) -- Dani (Lower Grand Valley)
  , ("dre", .symmetric) -- Drehu
  , ("duk", .asymmetric) -- Duka
  , ("dum", .symmetric) -- Dumo
  , ("ebi", .asymmetric) -- Ebira
  , ("eng", .both) -- English
  , ("epe", .asymmetric) -- Epena Pedee
  , ("eve", .asymmetric) -- Evenki
  , ("ewe", .both) -- Ewe
  , ("fij", .asymmetric) -- Fijian
  , ("fin", .asymmetric) -- Finnish
  , ("fre", .symmetric) -- French
  , ("fur", .symmetric) -- Fur
  , ("gar", .both) -- Garo
  , ("gbb", .both) -- Gbeya Bossangoa
  , ("geo", .symmetric) -- Georgian
  , ("ger", .symmetric) -- German
  , ("gku", .symmetric) -- Gününa Küne
  , ("gnn", .symmetric) -- Gunin
  , ("god", .both) -- Godoberi
  , ("gol", .both) -- Gola
  , ("goo", .symmetric) -- Gooniyandi
  , ("grb", .asymmetric) -- Grebo
  , ("grk", .symmetric) -- Greek (Modern)
  , ("grr", .symmetric) -- Garrwa
  , ("grw", .asymmetric) -- Greenlandic (West)
  , ("gua", .both) -- Guaraní
  , ("hai", .symmetric) -- Haida
  , ("ham", .asymmetric) -- Hamtai
  , ("har", .both) -- Haruai
  , ("hau", .both) -- Hausa
  , ("hcr", .both) -- Haitian Creole
  , ("heb", .both) -- Hebrew (Modern)
  , ("hin", .both) -- Hindi
  , ("hix", .asymmetric) -- Hixkaryana
  , ("hlu", .asymmetric) -- Halkomelem (Upriver)
  , ("hmo", .symmetric) -- Hmong Njua
  , ("hui", .symmetric) -- Huichol
  , ("hun", .symmetric) -- Hungarian
  , ("hve", .both) -- Huave (San Mateo del Mar)
  , ("hzb", .both) -- Hunzib
  , ("ice", .symmetric) -- Icelandic
  , ("igb", .asymmetric) -- Igbo
  , ("ige", .both) -- Igede
  , ("ijo", .both) -- Ijo (Kolokuma)
  , ("ika", .asymmetric) -- Ika
  , ("imo", .both) -- Imonda
  , ("ina", .both) -- Inanwatan
  , ("ind", .symmetric) -- Indonesian
  , ("ing", .symmetric) -- Ingush
  , ("iri", .both) -- Irish
  , ("irq", .asymmetric) -- Iraqw
  , ("ita", .symmetric) -- Italian
  , ("jak", .both) -- Jakaltek
  , ("jaq", .asymmetric) -- Jaqaru
  , ("jeb", .symmetric) -- Jebero
  , ("jpn", .asymmetric) -- Japanese
  , ("juh", .symmetric) -- Ju|'hoan
  , ("kab", .both) -- Kabardian
  , ("kae", .both) -- Kaki Ae
  , ("kay", .both) -- Kayardild
  , ("kem", .asymmetric) -- Kemant
  , ("ker", .both) -- Kera
  , ("ket", .symmetric) -- Ket
  , ("kew", .symmetric) -- Kewa
  , ("kfe", .symmetric) -- Koromfe
  , ("kha", .both) -- Khalkha
  , ("khm", .symmetric) -- Khmer
  , ("kho", .both) -- Nama
  , ("khr", .asymmetric) -- Kharia
  , ("khs", .both) -- Khasi
  , ("kio", .both) -- Kiowa
  , ("klm", .symmetric) -- Klamath
  , ("klv", .symmetric) -- Kilivila
  , ("kmu", .symmetric) -- Khmu'
  , ("knd", .asymmetric) -- Kannada
  , ("knm", .both) -- Kunama
  , ("knr", .both) -- Kanuri
  , ("koa", .both) -- Koasati
  , ("kob", .symmetric) -- Kobon
  , ("koi", .both) -- Koiari
  , ("kon", .symmetric) -- Kongo
  , ("kor", .both) -- Korean
  , ("kre", .both) -- Kresh
  , ("krk", .asymmetric) -- Karok
  , ("kro", .both) -- Krongo
  , ("kse", .both) -- Koyraboro Senni
  , ("kun", .symmetric) -- Kuna
  , ("kut", .symmetric) -- Kutenai
  , ("kwz", .symmetric) -- Kwaza
  , ("kyl", .both) -- Kayah Li (Eastern)
  , ("lad", .both) -- Ladakhi
  , ("lah", .both) -- Lahu
  , ("lan", .symmetric) -- Lango
  , ("lar", .both) -- Laragia
  , ("lat", .both) -- Latvian
  , ("lav", .both) -- Lavukaleve
  , ("lew", .asymmetric) -- Lewo
  , ("lez", .both) -- Lezgian
  , ("lkt", .symmetric) -- Lakhota
  , ("lug", .both) -- Lugbara
  , ("luv", .both) -- Luvale
  , ("maa", .both) -- Maasai
  , ("mab", .both) -- Maba
  , ("mak", .asymmetric) -- Makah
  , ("mal", .symmetric) -- Malagasy
  , ("mam", .both) -- Mam
  , ("mao", .asymmetric) -- Maori
  , ("map", .symmetric) -- Mapudungun
  , ("mar", .symmetric) -- Maricopa
  , ("mas", .symmetric) -- Masa
  , ("mau", .both) -- Maung
  , ("may", .symmetric) -- Maybrat
  , ("mei", .both) -- Meithei
  , ("miy", .both) -- Miya
  , ("mku", .symmetric) -- Maranungku
  , ("mnd", .both) -- Mandarin
  , ("mne", .symmetric) -- Maidu (Northeast)
  , ("mns", .symmetric) -- Mansi
  , ("mos", .symmetric) -- Mosetén
  , ("mrl", .symmetric) -- Murle
  , ("mrt", .symmetric) -- Martuthunira
  , ("mss", .symmetric) -- Miwok (Southern Sierra)
  , ("mun", .symmetric) -- Mundari
  , ("mxc", .symmetric) -- Mixtec (Chalcatongo)
  , ("myi", .both) -- Mangarrayi
  , ("mym", .both) -- Malayalam
  , ("nad", .asymmetric) -- Nadëb
  , ("nah", .asymmetric) -- Nahali
  , ("nas", .both) -- Nasioi
  , ("nav", .asymmetric) -- Navajo
  , ("nbd", .asymmetric) -- Nubian (Dongolese)
  , ("nca", .symmetric) -- Nicobarese (Car)
  , ("ndy", .symmetric) -- Ndyuka
  , ("nez", .symmetric) -- Nez Perce
  , ("ngi", .symmetric) -- Ngiyambaa
  , ("nht", .symmetric) -- Nahuatl (Tetelcingo)
  , ("niv", .both) -- Nivkh
  , ("nko", .both) -- Nkore-Kiga
  , ("nti", .symmetric) -- Ngiti
  , ("ntu", .asymmetric) -- Nenets
  , ("nug", .both) -- Nunggubuyu
  , ("nyu", .both) -- Nyulnyul
  , ("obg", .asymmetric) -- Ogbronuagum
  , ("ond", .both) -- Oneida
  , ("ono", .symmetric) -- Ono
  , ("orh", .both) -- Oromo (Harar)
  , ("otm", .both) -- Otomí (Mezquital)
  , ("pae", .both) -- Páez
  , ("pai", .both) -- Paiwan
  , ("pau", .symmetric) -- Paumarí
  , ("pba", .symmetric) -- Pima Bajo
  , ("pec", .both) -- Pech
  , ("pit", .both) -- Pitjantjatjara
  , ("pms", .both) -- Paamese
  , ("prh", .symmetric) -- Pirahã
  , ("prs", .symmetric) -- Persian
  , ("psj", .symmetric) -- Popoloca (San Juan Atzingo)
  , ("psm", .both) -- Passamaquoddy-Maliseet
  , ("pso", .both) -- Pomo (Southeastern)
  , ("pur", .symmetric) -- Purépecha
  , ("qaw", .symmetric) -- Qawasqar
  , ("qim", .both) -- Quechua (Imbabura)
  , ("qui", .asymmetric) -- Quileute
  , ("ram", .both) -- Rama
  , ("rap", .both) -- Rapanui
  , ("rus", .symmetric) -- Russian
  , ("san", .symmetric) -- Sango
  , ("sap", .symmetric) -- Sapuan
  , ("saw", .symmetric) -- Sawu
  , ("see", .both) -- Seediq
  , ("sel", .asymmetric) -- Selknam
  , ("shk", .symmetric) -- Shipibo-Konibo
  , ("shu", .asymmetric) -- Shuswap
  , ("siu", .symmetric) -- Siuslaw
  , ("sla", .symmetric) -- Slave
  , ("sml", .both) -- Semelai
  , ("snm", .both) -- Sanuma
  , ("snt", .asymmetric) -- Sentani
  , ("so", .both) -- So
  , ("som", .asymmetric) -- Somali
  , ("spa", .symmetric) -- Spanish
  , ("squ", .asymmetric) -- Squamish
  , ("sue", .both) -- Suena
  , ("sup", .both) -- Supyire
  , ("swa", .both) -- Swahili
  , ("tab", .symmetric) -- Taba
  , ("tag", .symmetric) -- Tagalog
  , ("tau", .symmetric) -- Tauya
  , ("ter", .both) -- Tera
  , ("tha", .symmetric) -- Thai
  , ("tib", .both) -- Tibetan (Standard Spoken)
  , ("tiw", .both) -- Tiwi
  , ("tkl", .both) -- Takelma
  , ("tli", .both) -- Tlingit
  , ("tms", .asymmetric) -- Tommo So
  , ("tol", .symmetric) -- Tol
  , ("ton", .symmetric) -- Tonkawa
  , ("tpa", .symmetric) -- Totonac (Papantla)
  , ("tru", .both) -- Trumai
  , ("tsi", .both) -- Tsimshian (Coast)
  , ("tuk", .symmetric) -- Tukang Besi
  , ("tun", .both) -- Tunica
  , ("tur", .both) -- Turkish
  , ("tuy", .symmetric) -- Tuyuca
  , ("ukr", .symmetric) -- Ukrainian
  , ("una", .symmetric) -- Una
  , ("ung", .both) -- Ungarinjin
  , ("urk", .symmetric) -- Urubú-Kaapor
  , ("usa", .both) -- Usan
  , ("uzb", .both) -- Uzbek
  , ("vie", .symmetric) -- Vietnamese
  , ("wam", .both) -- Wambaya
  , ("wao", .both) -- Waorani
  , ("war", .asymmetric) -- Wari'
  , ("was", .symmetric) -- Washo
  , ("way", .both) -- Wayampi
  , ("wch", .both) -- Wichí
  , ("wic", .both) -- Wichita
  , ("win", .asymmetric) -- Wintu
  , ("wiy", .both) -- Wiyot
  , ("wra", .asymmetric) -- Warao
  , ("wrd", .symmetric) -- Wardaman
  , ("wrm", .symmetric) -- Warembori
  , ("wrn", .asymmetric) -- Warndarang
  , ("yag", .symmetric) -- Yagua
  , ("yaq", .symmetric) -- Yaqui
  , ("yar", .both) -- Yareba
  , ("yid", .symmetric) -- Yidiny
  , ("yim", .asymmetric) -- Yimas
  , ("yko", .both) -- Yukaghir (Kolyma)
  , ("yor", .both) -- Yoruba
  , ("yrr", .symmetric) -- Yaruro
  , ("yuc", .symmetric) -- Yuchi
  , ("yur", .both) -- Yurok
  , ("yus", .both) -- Yupik (Siberian)
  , ("ywl", .symmetric) -- Yawelmani
  , ("zap", .asymmetric) -- Zapotec (Mitla)
  , ("zaz", .symmetric) -- Zazaki
  , ("zqc", .asymmetric) -- Zoque (Copainalá)
  , ("zul", .both) -- Zulu
  ]

end Data.WALS.F113A
