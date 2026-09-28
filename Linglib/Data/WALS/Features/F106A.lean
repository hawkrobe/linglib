module

/-!
# WALS Feature 106A: Reciprocal Constructions
[maslova-nedjalkov-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 106A`.

Chapter 106, 175 languages.
-/

@[expose] public section

namespace Data.WALS.F106A

/-- WALS 106A values. -/
inductive ReciprocalType where
  /-- No reciprocal construction (16 languages). -/
  | noReciprocalConstruction
  /-- Distinct from reflexive (99 languages). -/
  | distinctFromReflexive
  /-- Mixed (16 languages). -/
  | mixed
  /-- Identical to reflexive (44 languages). -/
  | identicalToReflexive
  deriving DecidableEq, Repr

/-- The WALS 106A coding: each language's value, keyed by its WALS code (175 languages). -/
def allData : List (String × ReciprocalType) :=
  [ ("abk", .distinctFromReflexive) -- Abkhaz
  , ("acg", .distinctFromReflexive) -- Achagua
  , ("aeg", .distinctFromReflexive) -- Arabic (Egyptian)
  , ("ain", .distinctFromReflexive) -- Ainu
  , ("ame", .noReciprocalConstruction) -- Amele
  , ("amu", .distinctFromReflexive) -- Amuesha
  , ("anc", .distinctFromReflexive) -- Angas
  , ("apu", .distinctFromReflexive) -- Apurinã
  , ("arp", .noReciprocalConstruction) -- Arapesh (Mountain)
  , ("asm", .distinctFromReflexive) -- Asmat
  , ("bae", .identicalToReflexive) -- Baré
  , ("bag", .distinctFromReflexive) -- Bagirmi
  , ("bam", .distinctFromReflexive) -- Bambara
  , ("bma", .distinctFromReflexive) -- Berber (Middle Atlas)
  , ("bnw", .identicalToReflexive) -- Baniwa
  , ("brm", .noReciprocalConstruction) -- Burmese
  , ("bsq", .distinctFromReflexive) -- Basque
  , ("bul", .mixed) -- Bulgarian
  , ("bur", .distinctFromReflexive) -- Burushaski
  , ("but", .distinctFromReflexive) -- Buriat
  , ("cah", .identicalToReflexive) -- Cahuilla
  , ("cea", .distinctFromReflexive) -- Cree (Swampy)
  , ("cha", .distinctFromReflexive) -- Chamorro
  , ("chc", .noReciprocalConstruction) -- Chechen
  , ("chk", .distinctFromReflexive) -- Chukchi
  , ("cnt", .distinctFromReflexive) -- Cantonese
  , ("cor", .identicalToReflexive) -- Cora
  , ("csh", .distinctFromReflexive) -- Cashinahua
  , ("cup", .identicalToReflexive) -- Cupeño
  , ("djr", .identicalToReflexive) -- Djaru
  , ("dni", .noReciprocalConstruction) -- Dani (Lower Grand Valley)
  , ("eng", .distinctFromReflexive) -- English
  , ("eve", .distinctFromReflexive) -- Evenki
  , ("evn", .distinctFromReflexive) -- Even
  , ("fij", .distinctFromReflexive) -- Fijian
  , ("fin", .distinctFromReflexive) -- Finnish
  , ("fre", .mixed) -- French
  , ("fue", .distinctFromReflexive) -- Futuna (East)
  , ("gbb", .distinctFromReflexive) -- Gbeya Bossangoa
  , ("gdi", .noReciprocalConstruction) -- Godié
  , ("geo", .distinctFromReflexive) -- Georgian
  , ("ger", .mixed) -- German
  , ("gim", .identicalToReflexive) -- Gimira
  , ("goa", .distinctFromReflexive) -- Goajiro
  , ("goo", .identicalToReflexive) -- Gooniyandi
  , ("grb", .distinctFromReflexive) -- Grebo
  , ("grk", .mixed) -- Greek (Modern)
  , ("grw", .identicalToReflexive) -- Greenlandic (West)
  , ("gua", .distinctFromReflexive) -- Guaraní
  , ("hau", .distinctFromReflexive) -- Hausa
  , ("heb", .mixed) -- Hebrew (Modern)
  , ("hin", .distinctFromReflexive) -- Hindi
  , ("hix", .mixed) -- Hixkaryana
  , ("hmo", .distinctFromReflexive) -- Hmong Njua
  , ("hop", .mixed) -- Hopi
  , ("hui", .identicalToReflexive) -- Huichol
  , ("ign", .distinctFromReflexive) -- Ignaciano
  , ("ika", .identicalToReflexive) -- Ika
  , ("imo", .identicalToReflexive) -- Imonda
  , ("ind", .distinctFromReflexive) -- Indonesian
  , ("ite", .distinctFromReflexive) -- Itelmen
  , ("jak", .identicalToReflexive) -- Jakaltek
  , ("jpn", .distinctFromReflexive) -- Japanese
  , ("jva", .distinctFromReflexive) -- Karajá
  , ("kab", .distinctFromReflexive) -- Kabardian
  , ("kay", .distinctFromReflexive) -- Kayardild
  , ("kew", .noReciprocalConstruction) -- Kewa
  , ("kgz", .distinctFromReflexive) -- Kirghiz
  , ("kha", .distinctFromReflexive) -- Khalkha
  , ("kho", .distinctFromReflexive) -- Nama
  , ("kio", .identicalToReflexive) -- Kiowa
  , ("knd", .distinctFromReflexive) -- Kannada
  , ("kng", .identicalToReflexive) -- Kaingang
  , ("koa", .distinctFromReflexive) -- Koasati
  , ("kor", .distinctFromReflexive) -- Korean
  , ("krc", .distinctFromReflexive) -- Karachay-Balkar
  , ("krk", .distinctFromReflexive) -- Karok
  , ("kro", .identicalToReflexive) -- Krongo
  , ("kse", .distinctFromReflexive) -- Koyraboro Senni
  , ("kut", .distinctFromReflexive) -- Kutenai
  , ("kws", .identicalToReflexive) -- Kawaiisu
  , ("kyp", .distinctFromReflexive) -- Kayapó
  , ("lan", .identicalToReflexive) -- Lango
  , ("lit", .mixed) -- Lithuanian
  , ("lkt", .distinctFromReflexive) -- Lakhota
  , ("lrd", .distinctFromReflexive) -- Lardil
  , ("lui", .identicalToReflexive) -- Luiseño
  , ("luv", .identicalToReflexive) -- Luvale
  , ("lye", .distinctFromReflexive) -- Lyele
  , ("mal", .distinctFromReflexive) -- Malagasy
  , ("mam", .noReciprocalConstruction) -- Mam
  , ("map", .identicalToReflexive) -- Mapudungun
  , ("mar", .identicalToReflexive) -- Maricopa
  , ("mau", .identicalToReflexive) -- Maung
  , ("max", .identicalToReflexive) -- Maxakalí
  , ("may", .noReciprocalConstruction) -- Maybrat
  , ("mei", .distinctFromReflexive) -- Meithei
  , ("mku", .distinctFromReflexive) -- Maranungku
  , ("mnd", .distinctFromReflexive) -- Mandarin
  , ("mne", .distinctFromReflexive) -- Maidu (Northeast)
  , ("mno", .distinctFromReflexive) -- Mono (in United States)
  , ("mrt", .distinctFromReflexive) -- Martuthunira
  , ("mud", .identicalToReflexive) -- Mundani
  , ("mun", .distinctFromReflexive) -- Mundari
  , ("myi", .identicalToReflexive) -- Mangarrayi
  , ("nel", .distinctFromReflexive) -- Nelemwa
  , ("ngi", .distinctFromReflexive) -- Ngiyambaa
  , ("niv", .distinctFromReflexive) -- Nivkh
  , ("nko", .distinctFromReflexive) -- Nkore-Kiga
  , ("nom", .distinctFromReflexive) -- Nomatsiguenga
  , ("nug", .distinctFromReflexive) -- Nunggubuyu
  , ("ojm", .distinctFromReflexive) -- Ojibwe (Minnesota)
  , ("ond", .identicalToReflexive) -- Oneida
  , ("ood", .mixed) -- O'odham
  , ("orh", .distinctFromReflexive) -- Oromo (Harar)
  , ("otm", .noReciprocalConstruction) -- Otomí (Mezquital)
  , ("pir", .distinctFromReflexive) -- Piro
  , ("pno", .mixed) -- Paiute (Northern)
  , ("pol", .mixed) -- Polish
  , ("prh", .noReciprocalConstruction) -- Pirahã
  , ("prs", .distinctFromReflexive) -- Persian
  , ("pso", .distinctFromReflexive) -- Pomo (Southeastern)
  , ("put", .identicalToReflexive) -- Paiute (Southern)
  , ("qbo", .distinctFromReflexive) -- Quechua (Bolivian)
  , ("qcu", .distinctFromReflexive) -- Quechua (Cuzco)
  , ("qhu", .identicalToReflexive) -- Quechua (Huallaga)
  , ("qim", .mixed) -- Quechua (Imbabura)
  , ("ram", .noReciprocalConstruction) -- Rama
  , ("rap", .identicalToReflexive) -- Rapanui
  , ("rus", .mixed) -- Russian
  , ("san", .noReciprocalConstruction) -- Sango
  , ("sho", .identicalToReflexive) -- Shoshone
  , ("sla", .distinctFromReflexive) -- Slave
  , ("snm", .distinctFromReflexive) -- Sanuma
  , ("spa", .mixed) -- Spanish
  , ("srr", .identicalToReflexive) -- Serrano
  , ("sup", .identicalToReflexive) -- Supyire
  , ("sur", .mixed) -- Sursurunga
  , ("swa", .distinctFromReflexive) -- Swahili
  , ("tag", .distinctFromReflexive) -- Tagalog
  , ("tar", .mixed) -- Tariana
  , ("tbb", .distinctFromReflexive) -- Tübatulabal
  , ("tce", .distinctFromReflexive) -- Tarahumara (Central)
  , ("tha", .distinctFromReflexive) -- Thai
  , ("tiw", .distinctFromReflexive) -- Tiwi
  , ("tml", .distinctFromReflexive) -- Tamil
  , ("toq", .identicalToReflexive) -- Toqabaqita
  , ("tpc", .noReciprocalConstruction) -- Tepecano
  , ("tuc", .distinctFromReflexive) -- Tucano
  , ("tuk", .distinctFromReflexive) -- Tukang Besi
  , ("tur", .distinctFromReflexive) -- Turkish
  , ("tuv", .distinctFromReflexive) -- Tuvan
  , ("vie", .distinctFromReflexive) -- Vietnamese
  , ("wam", .identicalToReflexive) -- Wambaya
  , ("war", .identicalToReflexive) -- Wari'
  , ("wch", .identicalToReflexive) -- Wichí
  , ("wgu", .distinctFromReflexive) -- Warrongo
  , ("wic", .noReciprocalConstruction) -- Wichita
  , ("win", .distinctFromReflexive) -- Wintu
  , ("wra", .identicalToReflexive) -- Warao
  , ("wrk", .identicalToReflexive) -- Warekena
  , ("wur", .distinctFromReflexive) -- Waurá
  , ("xer", .identicalToReflexive) -- Xerénte
  , ("xok", .distinctFromReflexive) -- Xokleng
  , ("yag", .identicalToReflexive) -- Yagua
  , ("yaq", .identicalToReflexive) -- Yaqui
  , ("ygd", .distinctFromReflexive) -- Dii
  , ("yid", .noReciprocalConstruction) -- Yidiny
  , ("yko", .distinctFromReflexive) -- Yukaghir (Kolyma)
  , ("ykt", .distinctFromReflexive) -- Yakut
  , ("ynk", .identicalToReflexive) -- Yankuntjatjara
  , ("yor", .identicalToReflexive) -- Yoruba
  , ("ytu", .distinctFromReflexive) -- Yukaghir (Tundra)
  , ("yuk", .distinctFromReflexive) -- Yukulta
  , ("zul", .distinctFromReflexive) -- Zulu
  ]

end Data.WALS.F106A
