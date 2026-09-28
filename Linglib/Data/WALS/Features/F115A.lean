module

/-!
# WALS Feature 115A: Negative Indefinite Pronouns and Predicate Negation
[haspelmath-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 115A`.

Chapter 115, 206 languages.
-/

@[expose] public section

namespace Data.WALS.F115A

/-- WALS 115A values. -/
inductive NegativeIndefiniteType where
  /-- Predicate negation also present (170 languages). -/
  | predicateNegationAlsoPresent
  /-- No predicate negation (11 languages). -/
  | noPredicateNegation
  /-- Mixed behaviour (13 languages). -/
  | mixedBehaviour
  /-- Negative existential construction (12 languages). -/
  | negativeExistentialConstruction
  deriving DecidableEq, Repr

/-- The WALS 115A coding: each language's value, keyed by its WALS code (206 languages). -/
def allData : List (String × NegativeIndefiniteType) :=
  [ ("abk", .predicateNegationAlsoPresent) -- Abkhaz
  , ("abu", .predicateNegationAlsoPresent) -- Abun
  , ("ace", .predicateNegationAlsoPresent) -- Acehnese
  , ("ady", .predicateNegationAlsoPresent) -- Adyghe (Abzakh)
  , ("aeg", .predicateNegationAlsoPresent) -- Arabic (Egyptian)
  , ("ain", .predicateNegationAlsoPresent) -- Ainu
  , ("ana", .predicateNegationAlsoPresent) -- Araona
  , ("ano", .predicateNegationAlsoPresent) -- Anong
  , ("ass", .predicateNegationAlsoPresent) -- Assamese
  , ("awp", .predicateNegationAlsoPresent) -- Awa Pit
  , ("bab", .predicateNegationAlsoPresent) -- Babungo
  , ("bae", .predicateNegationAlsoPresent) -- Baré
  , ("bag", .predicateNegationAlsoPresent) -- Bagirmi
  , ("baw", .predicateNegationAlsoPresent) -- Bawm
  , ("bbw", .predicateNegationAlsoPresent) -- Bininj Gun-Wok
  , ("biu", .predicateNegationAlsoPresent) -- Bisu
  , ("bkr", .predicateNegationAlsoPresent) -- Batak (Karo)
  , ("bma", .predicateNegationAlsoPresent) -- Berber (Middle Atlas)
  , ("boz", .predicateNegationAlsoPresent) -- Bozo (Tigemaxo)
  , ("brh", .predicateNegationAlsoPresent) -- Brahui
  , ("brm", .predicateNegationAlsoPresent) -- Burmese
  , ("brs", .negativeExistentialConstruction) -- Barasano
  , ("bsq", .predicateNegationAlsoPresent) -- Basque
  , ("bud", .predicateNegationAlsoPresent) -- Buduma
  , ("bul", .predicateNegationAlsoPresent) -- Bulgarian
  , ("cch", .noPredicateNegation) -- Chocho
  , ("cha", .noPredicateNegation) -- Chamorro
  , ("chk", .predicateNegationAlsoPresent) -- Chukchi
  , ("chn", .predicateNegationAlsoPresent) -- Chantyal
  , ("cnl", .predicateNegationAlsoPresent) -- Canela
  , ("cnt", .predicateNegationAlsoPresent) -- Cantonese
  , ("coo", .predicateNegationAlsoPresent) -- Coos (Hanis)
  , ("cop", .predicateNegationAlsoPresent) -- Coptic
  , ("ctl", .predicateNegationAlsoPresent) -- Catalan
  , ("dgr", .predicateNegationAlsoPresent) -- Dagur
  , ("dji", .predicateNegationAlsoPresent) -- Djingili
  , ("dut", .noPredicateNegation) -- Dutch
  , ("eng", .mixedBehaviour) -- English
  , ("epe", .predicateNegationAlsoPresent) -- Epena Pedee
  , ("eve", .predicateNegationAlsoPresent) -- Evenki
  , ("fin", .predicateNegationAlsoPresent) -- Finnish
  , ("fon", .predicateNegationAlsoPresent) -- Fongbe
  , ("fre", .mixedBehaviour) -- French
  , ("fue", .negativeExistentialConstruction) -- Futuna (East)
  , ("geo", .mixedBehaviour) -- Georgian
  , ("ger", .noPredicateNegation) -- German
  , ("goo", .predicateNegationAlsoPresent) -- Gooniyandi
  , ("grg", .predicateNegationAlsoPresent) -- Gurr-goni
  , ("grk", .predicateNegationAlsoPresent) -- Greek (Modern)
  , ("grw", .predicateNegationAlsoPresent) -- Greenlandic (West)
  , ("gua", .predicateNegationAlsoPresent) -- Guaraní
  , ("guj", .predicateNegationAlsoPresent) -- Gujarati
  , ("hai", .predicateNegationAlsoPresent) -- Haida
  , ("hau", .predicateNegationAlsoPresent) -- Hausa
  , ("heb", .predicateNegationAlsoPresent) -- Hebrew (Modern)
  , ("hin", .predicateNegationAlsoPresent) -- Hindi
  , ("hmo", .predicateNegationAlsoPresent) -- Hmong Njua
  , ("hun", .predicateNegationAlsoPresent) -- Hungarian
  , ("hzb", .predicateNegationAlsoPresent) -- Hunzib
  , ("ice", .mixedBehaviour) -- Icelandic
  , ("ind", .predicateNegationAlsoPresent) -- Indonesian
  , ("iri", .predicateNegationAlsoPresent) -- Irish
  , ("irq", .negativeExistentialConstruction) -- Iraqw
  , ("ita", .mixedBehaviour) -- Italian
  , ("itz", .mixedBehaviour) -- Itzaj
  , ("jam", .predicateNegationAlsoPresent) -- Jaminjung
  , ("jel", .predicateNegationAlsoPresent) -- Jeli
  , ("jpn", .predicateNegationAlsoPresent) -- Japanese
  , ("kan", .predicateNegationAlsoPresent) -- Kana
  , ("kas", .predicateNegationAlsoPresent) -- Kashmiri
  , ("kaz", .predicateNegationAlsoPresent) -- Kazakh
  , ("ker", .predicateNegationAlsoPresent) -- Kera
  , ("ket", .predicateNegationAlsoPresent) -- Ket
  , ("kfe", .predicateNegationAlsoPresent) -- Koromfe
  , ("khm", .predicateNegationAlsoPresent) -- Khmer
  , ("khs", .predicateNegationAlsoPresent) -- Khasi
  , ("kio", .predicateNegationAlsoPresent) -- Kiowa
  , ("kkp", .predicateNegationAlsoPresent) -- Karakalpak
  , ("kku", .predicateNegationAlsoPresent) -- Korku
  , ("klv", .predicateNegationAlsoPresent) -- Kilivila
  , ("kma", .predicateNegationAlsoPresent) -- Kamaiurá
  , ("kmh", .predicateNegationAlsoPresent) -- Kham
  , ("kmu", .predicateNegationAlsoPresent) -- Khmu'
  , ("knd", .predicateNegationAlsoPresent) -- Kannada
  , ("knr", .predicateNegationAlsoPresent) -- Kanuri
  , ("koa", .predicateNegationAlsoPresent) -- Koasati
  , ("kob", .predicateNegationAlsoPresent) -- Kobon
  , ("kod", .predicateNegationAlsoPresent) -- Kodava
  , ("kor", .predicateNegationAlsoPresent) -- Korean
  , ("kse", .predicateNegationAlsoPresent) -- Koyraboro Senni
  , ("kty", .predicateNegationAlsoPresent) -- Khanty
  , ("kug", .predicateNegationAlsoPresent) -- Kunming
  , ("kzy", .predicateNegationAlsoPresent) -- Komi-Zyrian
  , ("lak", .predicateNegationAlsoPresent) -- Lak
  , ("lan", .negativeExistentialConstruction) -- Lango
  , ("lat", .predicateNegationAlsoPresent) -- Latvian
  , ("lav", .predicateNegationAlsoPresent) -- Lavukaleve
  , ("lel", .predicateNegationAlsoPresent) -- Lele
  , ("lez", .predicateNegationAlsoPresent) -- Lezgian
  , ("lil", .predicateNegationAlsoPresent) -- Lillooet
  , ("lin", .predicateNegationAlsoPresent) -- Lingala
  , ("lit", .predicateNegationAlsoPresent) -- Lithuanian
  , ("lkt", .predicateNegationAlsoPresent) -- Lakhota
  , ("mac", .predicateNegationAlsoPresent) -- Macushi
  , ("mad", .predicateNegationAlsoPresent) -- Ma'di
  , ("mao", .predicateNegationAlsoPresent) -- Maori
  , ("map", .predicateNegationAlsoPresent) -- Mapudungun
  , ("may", .predicateNegationAlsoPresent) -- Maybrat
  , ("mbi", .predicateNegationAlsoPresent) -- Mbili
  , ("mby", .predicateNegationAlsoPresent) -- Mbay
  , ("mcv", .negativeExistentialConstruction) -- Mocoví
  , ("mdg", .predicateNegationAlsoPresent) -- Mundang
  , ("mgu", .predicateNegationAlsoPresent) -- Musgu
  , ("mhi", .predicateNegationAlsoPresent) -- Marathi
  , ("miy", .predicateNegationAlsoPresent) -- Miya
  , ("mle", .predicateNegationAlsoPresent) -- Maale
  , ("mlg", .mixedBehaviour) -- Malgwa
  , ("mlt", .mixedBehaviour) -- Maltese
  , ("mme", .predicateNegationAlsoPresent) -- Mari (Meadow)
  , ("mnd", .predicateNegationAlsoPresent) -- Mandarin
  , ("moe", .predicateNegationAlsoPresent) -- Mordvin (Erzya)
  , ("mos", .predicateNegationAlsoPresent) -- Mosetén
  , ("mto", .predicateNegationAlsoPresent) -- Malto
  , ("mun", .predicateNegationAlsoPresent) -- Mundari
  , ("mxc", .noPredicateNegation) -- Mixtec (Chalcatongo)
  , ("myi", .noPredicateNegation) -- Mangarrayi
  , ("mym", .predicateNegationAlsoPresent) -- Malayalam
  , ("nai", .predicateNegationAlsoPresent) -- Nanai
  , ("nav", .predicateNegationAlsoPresent) -- Navajo
  , ("ndj", .predicateNegationAlsoPresent) -- Ndjébbana
  , ("nel", .negativeExistentialConstruction) -- Nelemwa
  , ("nep", .predicateNegationAlsoPresent) -- Nepali
  , ("ngi", .predicateNegationAlsoPresent) -- Ngiyambaa
  , ("nht", .noPredicateNegation) -- Nahuatl (Tetelcingo)
  , ("niu", .predicateNegationAlsoPresent) -- Niuean
  , ("niv", .predicateNegationAlsoPresent) -- Nivkh
  , ("nko", .negativeExistentialConstruction) -- Nkore-Kiga
  , ("nti", .predicateNegationAlsoPresent) -- Ngiti
  , ("nua", .predicateNegationAlsoPresent) -- Nuaulu
  , ("nwd", .predicateNegationAlsoPresent) -- Newar (Dolakha)
  , ("oji", .predicateNegationAlsoPresent) -- Ojibwa (Eastern)
  , ("ood", .predicateNegationAlsoPresent) -- O'odham
  , ("orh", .predicateNegationAlsoPresent) -- Oromo (Harar)
  , ("oss", .noPredicateNegation) -- Ossetic
  , ("pae", .predicateNegationAlsoPresent) -- Páez
  , ("pai", .predicateNegationAlsoPresent) -- Paiwan
  , ("pms", .predicateNegationAlsoPresent) -- Paamese
  , ("pno", .predicateNegationAlsoPresent) -- Paiute (Northern)
  , ("pol", .predicateNegationAlsoPresent) -- Polish
  , ("pop", .predicateNegationAlsoPresent) -- Popoloca (Metzontla)
  , ("por", .mixedBehaviour) -- Portuguese
  , ("prs", .predicateNegationAlsoPresent) -- Persian
  , ("pur", .noPredicateNegation) -- Purépecha
  , ("qhu", .predicateNegationAlsoPresent) -- Quechua (Huallaga)
  , ("qia", .predicateNegationAlsoPresent) -- Qiang
  , ("qim", .predicateNegationAlsoPresent) -- Quechua (Imbabura)
  , ("raw", .predicateNegationAlsoPresent) -- Rawang
  , ("ret", .predicateNegationAlsoPresent) -- Retuarã
  , ("rom", .predicateNegationAlsoPresent) -- Romanian
  , ("rus", .predicateNegationAlsoPresent) -- Russian
  , ("scr", .predicateNegationAlsoPresent) -- Serbian-Croatian
  , ("shk", .predicateNegationAlsoPresent) -- Shipibo-Konibo
  , ("skp", .predicateNegationAlsoPresent) -- Selkup
  , ("sla", .predicateNegationAlsoPresent) -- Slave
  , ("sno", .predicateNegationAlsoPresent) -- Saami (Northern)
  , ("som", .predicateNegationAlsoPresent) -- Somali
  , ("spa", .mixedBehaviour) -- Spanish
  , ("squ", .predicateNegationAlsoPresent) -- Squamish
  , ("sup", .predicateNegationAlsoPresent) -- Supyire
  , ("swa", .predicateNegationAlsoPresent) -- Swahili
  , ("swe", .mixedBehaviour) -- Swedish
  , ("tab", .mixedBehaviour) -- Taba
  , ("tag", .predicateNegationAlsoPresent) -- Tagalog
  , ("tah", .negativeExistentialConstruction) -- Tahitian
  , ("tam", .predicateNegationAlsoPresent) -- Tamang (Eastern)
  , ("teo", .negativeExistentialConstruction) -- Teop
  , ("tha", .predicateNegationAlsoPresent) -- Thai
  , ("tid", .predicateNegationAlsoPresent) -- Tidore
  , ("tiw", .noPredicateNegation) -- Tiwi
  , ("tja", .predicateNegationAlsoPresent) -- Tiipay (Jamul)
  , ("tke", .negativeExistentialConstruction) -- Tokelauan
  , ("tml", .predicateNegationAlsoPresent) -- Tamil
  , ("tms", .predicateNegationAlsoPresent) -- Tommo So
  , ("tpn", .predicateNegationAlsoPresent) -- Tepehuan (Northern)
  , ("trb", .predicateNegationAlsoPresent) -- Teribe
  , ("tru", .predicateNegationAlsoPresent) -- Trumai
  , ("ttn", .predicateNegationAlsoPresent) -- Tetun
  , ("tur", .predicateNegationAlsoPresent) -- Turkish
  , ("tuv", .predicateNegationAlsoPresent) -- Tuvan
  , ("tvl", .negativeExistentialConstruction) -- Tuvaluan
  , ("tzu", .noPredicateNegation) -- Tzutujil
  , ("udh", .predicateNegationAlsoPresent) -- Udihe
  , ("udm", .predicateNegationAlsoPresent) -- Udmurt
  , ("uku", .negativeExistentialConstruction) -- Upper Kuskokwim
  , ("urk", .predicateNegationAlsoPresent) -- Urubú-Kaapor
  , ("vie", .predicateNegationAlsoPresent) -- Vietnamese
  , ("wch", .predicateNegationAlsoPresent) -- Wichí
  , ("wlf", .predicateNegationAlsoPresent) -- Wolof
  , ("yaq", .mixedBehaviour) -- Yaqui
  , ("yko", .predicateNegationAlsoPresent) -- Yukaghir (Kolyma)
  , ("ykt", .predicateNegationAlsoPresent) -- Yakut
  , ("ytu", .predicateNegationAlsoPresent) -- Yukaghir (Tundra)
  , ("zaq", .predicateNegationAlsoPresent) -- Zapotec (Quiegolani)
  , ("zaz", .predicateNegationAlsoPresent) -- Zazaki
  , ("zul", .predicateNegationAlsoPresent) -- Zulu
  , ("zun", .predicateNegationAlsoPresent) -- Zuni
  ]

end Data.WALS.F115A
