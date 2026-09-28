module

/-!
# WALS Feature 121A: Comparative Constructions
[stassen-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 121A`.

Chapter 121, 167 languages.
-/

@[expose] public section

namespace Data.WALS.F121A

/-- WALS 121A values. -/
inductive ComparativeType where
  /-- Locational (78 languages). -/
  | locational
  /-- Exceed (33 languages). -/
  | exceed
  /-- Conjoined (34 languages). -/
  | conjoined
  /-- Particle (22 languages). -/
  | particle
  deriving DecidableEq, Repr

/-- The WALS 121A coding: each language's value, keyed by its WALS code (167 languages). -/
def allData : List (String × ComparativeType) :=
  [ ("abi", .conjoined) -- Abipón
  , ("adk", .locational) -- Andoke
  , ("alb", .particle) -- Albanian
  , ("ale", .locational) -- Aleut
  , ("ame", .exceed) -- Amele
  , ("amh", .locational) -- Amharic
  , ("amp", .locational) -- Arrernte (Mparntwe)
  , ("amr", .locational) -- Arabic (Moroccan)
  , ("ams", .locational) -- Arabic (Modern Standard)
  , ("apl", .conjoined) -- Apalaí
  , ("arg", .locational) -- Arabic (Gulf)
  , ("arp", .conjoined) -- Arapesh (Mountain)
  , ("aym", .locational) -- Aymara (Central)
  , ("bae", .locational) -- Baré
  , ("bar", .exceed) -- Bari
  , ("bgi", .locational) -- Bagri
  , ("biu", .conjoined) -- Bisu
  , ("bln", .locational) -- Bilin
  , ("bma", .locational) -- Berber (Middle Atlas)
  , ("bre", .locational) -- Breton
  , ("brm", .locational) -- Burmese
  , ("bsq", .particle) -- Basque
  , ("bto", .particle) -- Batak (Toba)
  , ("bur", .locational) -- Burushaski
  , ("car", .locational) -- Carib
  , ("ceb", .locational) -- Cebuano
  , ("chk", .locational) -- Chukchi
  , ("cic", .exceed) -- Chichewa
  , ("cmn", .particle) -- Comanche
  , ("coe", .locational) -- Coeur d'Alene
  , ("dga", .exceed) -- Dagaare
  , ("dgb", .exceed) -- Dagbani
  , ("dua", .exceed) -- Duala
  , ("dut", .particle) -- Dutch
  , ("eka", .conjoined) -- Ekari
  , ("eng", .particle) -- English
  , ("eve", .locational) -- Evenki
  , ("evn", .locational) -- Even
  , ("fin", .particle) -- Finnish
  , ("fre", .particle) -- French
  , ("fus", .exceed) -- Fula (Senegal)
  , ("gae", .particle) -- Gaelic (Scots)
  , ("gbb", .exceed) -- Gbeya Bossangoa
  , ("geo", .locational) -- Georgian
  , ("goa", .particle) -- Goajiro
  , ("grk", .particle) -- Greek (Modern)
  , ("grw", .locational) -- Greenlandic (West)
  , ("gua", .locational) -- Guaraní
  , ("gum", .conjoined) -- Gumbaynggir
  , ("hau", .exceed) -- Hausa
  , ("heb", .locational) -- Hebrew (Modern)
  , ("hin", .locational) -- Hindi
  , ("hix", .conjoined) -- Hixkaryana
  , ("hun", .particle) -- Hungarian
  , ("hzb", .locational) -- Hunzib
  , ("igb", .exceed) -- Igbo
  , ("ilo", .particle) -- Ilocano
  , ("iri", .particle) -- Irish
  , ("jab", .conjoined) -- Jabêm
  , ("jak", .locational) -- Jakaltek
  , ("jav", .particle) -- Javanese
  , ("jpn", .locational) -- Japanese
  , ("kan", .exceed) -- Kana
  , ("kas", .locational) -- Kashmiri
  , ("kbl", .locational) -- Kabyle
  , ("kem", .locational) -- Kemant
  , ("kfe", .exceed) -- Koromfe
  , ("kha", .locational) -- Khalkha
  , ("khk", .locational) -- Khakas
  , ("khm", .exceed) -- Khmer
  , ("kho", .locational) -- Nama
  , ("klw", .conjoined) -- Kiliwa
  , ("kms", .locational) -- Kamass
  , ("knr", .locational) -- Kanuri
  , ("kob", .conjoined) -- Kobon
  , ("koi", .conjoined) -- Koiari
  , ("kor", .locational) -- Korean
  , ("kro", .locational) -- Krongo
  , ("kug", .exceed) -- Kunming
  , ("kyp", .conjoined) -- Kayapó
  , ("lat", .particle) -- Latvian
  , ("laz", .locational) -- Laz
  , ("lez", .locational) -- Lezgian
  , ("lim", .locational) -- Limbu
  , ("lin", .exceed) -- Lingala
  , ("lkt", .conjoined) -- Lakhota
  , ("lnd", .exceed) -- Linda
  , ("maa", .locational) -- Maasai
  , ("mal", .particle) -- Malagasy
  , ("mao", .conjoined) -- Maori
  , ("map", .locational) -- Mapudungun
  , ("maw", .locational) -- Maninka (Western)
  , ("mbo", .conjoined) -- Monumbo
  , ("mby", .exceed) -- Mbay
  , ("men", .conjoined) -- Menomini
  , ("mhi", .locational) -- Marathi
  , ("mis", .conjoined) -- Miskito
  , ("mlt", .locational) -- Maltese
  , ("mna", .conjoined) -- Muna
  , ("mnc", .locational) -- Manchu
  , ("mnd", .exceed) -- Mandarin
  , ("mrg", .exceed) -- Margi
  , ("mss", .locational) -- Miwok (Southern Sierra)
  , ("mtu", .conjoined) -- Motu
  , ("mun", .locational) -- Mundari
  , ("mxa", .conjoined) -- Mixtec (Atatlahuca)
  , ("myi", .conjoined) -- Mangarrayi
  , ("nan", .exceed) -- Nandi
  , ("nav", .locational) -- Navajo
  , ("ngt", .locational) -- Naga (Tangkhul)
  , ("ngu", .exceed) -- Nguna
  , ("ntu", .locational) -- Nenets
  , ("nue", .locational) -- Nuer
  , ("nug", .conjoined) -- Nunggubuyu
  , ("obg", .exceed) -- Ogbronuagum
  , ("ood", .particle) -- O'odham
  , ("pal", .locational) -- Palauan
  , ("pau", .conjoined) -- Paumarí
  , ("pir", .locational) -- Piro
  , ("prh", .conjoined) -- Pirahã
  , ("ptp", .conjoined) -- Patpatar
  , ("pur", .locational) -- Purépecha
  , ("qcu", .locational) -- Quechua (Cuzco)
  , ("qim", .locational) -- Quechua (Imbabura)
  , ("rap", .locational) -- Rapanui
  , ("rem", .locational) -- Remo
  , ("rnd", .exceed) -- Rundi
  , ("rus", .particle) -- Russian
  , ("sal", .locational) -- Salinan
  , ("sam", .conjoined) -- Samoan
  , ("sap", .exceed) -- Sapuan
  , ("shk", .conjoined) -- Shipibo-Konibo
  , ("shn", .exceed) -- Shona
  , ("sik", .conjoined) -- Sika
  , ("siu", .locational) -- Siuslaw
  , ("spa", .particle) -- Spanish
  , ("sra", .particle) -- Sranan
  , ("stl", .locational) -- Santali
  , ("stn", .exceed) -- Sotho (Northern)
  , ("swa", .exceed) -- Swahili
  , ("taj", .locational) -- Tajik
  , ("taz", .locational) -- Talysh (Azerbaijan)
  , ("tbu", .locational) -- Tubu
  , ("tel", .locational) -- Telugu
  , ("tha", .exceed) -- Thai
  , ("tml", .locational) -- Tamil
  , ("tsh", .particle) -- Tümpisa Shoshone
  , ("tug", .locational) -- Tuareg (Ahaggar)
  , ("tup", .locational) -- Tupi
  , ("tur", .locational) -- Turkish
  , ("tuv", .locational) -- Tuvan
  , ("tvl", .locational) -- Tuvaluan
  , ("uby", .locational) -- Ubykh
  , ("udm", .locational) -- Udmurt
  , ("urk", .conjoined) -- Urubú-Kaapor
  , ("uzb", .locational) -- Uzbek
  , ("vie", .exceed) -- Vietnamese
  , ("war", .conjoined) -- Wari'
  , ("wlf", .exceed) -- Wolof
  , ("wrk", .conjoined) -- Warekena
  , ("yag", .conjoined) -- Yagua
  , ("yah", .exceed) -- Yahgan
  , ("yap", .locational) -- Yapese
  , ("yav", .conjoined) -- Yavapai
  , ("yin", .conjoined) -- Yindjibarndi
  , ("yor", .exceed) -- Yoruba
  , ("zul", .exceed) -- Zulu
  ]

end Data.WALS.F121A
