module

/-!
# WALS Feature 110A: Periphrastic Causative Constructions
[song-2013-periphrastic]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 110A`.

Chapter 110, 118 languages.
-/

@[expose] public section

namespace Data.WALS.F110A

/-- WALS 110A values. -/
inductive PeriphrasticCausativeType where
  /-- Sequential but no purposive (35 languages). -/
  | sequentialOnly
  /-- Purposive but no sequential (68 languages). -/
  | purposiveOnly
  /-- Both (15 languages). -/
  | both
  deriving DecidableEq, Repr

/-- The WALS 110A coding: each language's value, keyed by its WALS code (118 languages). -/
def allData : List (String × PeriphrasticCausativeType) :=
  [ ("abk", .purposiveOnly) -- Abkhaz
  , ("aeg", .purposiveOnly) -- Arabic (Egyptian)
  , ("aji", .purposiveOnly) -- Ajië
  , ("ame", .sequentialOnly) -- Amele
  , ("arm", .purposiveOnly) -- Armenian (Eastern)
  , ("atc", .sequentialOnly) -- Atchin
  , ("awn", .purposiveOnly) -- Awngi
  , ("bab", .sequentialOnly) -- Babungo
  , ("bag", .sequentialOnly) -- Bagirmi
  , ("bkr", .purposiveOnly) -- Batak (Karo)
  , ("brm", .purposiveOnly) -- Burmese
  , ("bsq", .purposiveOnly) -- Basque
  , ("cha", .purposiveOnly) -- Chamorro
  , ("die", .sequentialOnly) -- Diegueño (Mesa Grande)
  , ("diy", .sequentialOnly) -- Diyari
  , ("djr", .purposiveOnly) -- Djaru
  , ("eng", .sequentialOnly) -- English
  , ("epe", .sequentialOnly) -- Epena Pedee
  , ("ewe", .sequentialOnly) -- Ewe
  , ("fij", .purposiveOnly) -- Fijian
  , ("fin", .purposiveOnly) -- Finnish
  , ("geo", .purposiveOnly) -- Georgian
  , ("ger", .sequentialOnly) -- German
  , ("goo", .purposiveOnly) -- Gooniyandi
  , ("grk", .purposiveOnly) -- Greek (Modern)
  , ("hau", .sequentialOnly) -- Hausa
  , ("heb", .purposiveOnly) -- Hebrew (Modern)
  , ("hin", .purposiveOnly) -- Hindi
  , ("hmo", .sequentialOnly) -- Hmong Njua
  , ("hun", .both) -- Hungarian
  , ("igb", .sequentialOnly) -- Igbo
  , ("ika", .purposiveOnly) -- Ika
  , ("ind", .sequentialOnly) -- Indonesian
  , ("iri", .purposiveOnly) -- Irish
  , ("jak", .both) -- Jakaltek
  , ("kay", .purposiveOnly) -- Kayardild
  , ("kfe", .sequentialOnly) -- Koromfe
  , ("khm", .both) -- Khmer
  , ("kin", .both) -- Kinyarwanda
  , ("klv", .sequentialOnly) -- Kilivila
  , ("kmu", .sequentialOnly) -- Khmu'
  , ("knd", .purposiveOnly) -- Kannada
  , ("knm", .both) -- Kunama
  , ("knr", .sequentialOnly) -- Kanuri
  , ("kob", .sequentialOnly) -- Kobon
  , ("kol", .purposiveOnly) -- Kolami
  , ("kor", .purposiveOnly) -- Korean
  , ("krb", .purposiveOnly) -- Kiribati
  , ("kro", .purposiveOnly) -- Krongo
  , ("kse", .both) -- Koyraboro Senni
  , ("lah", .purposiveOnly) -- Lahu
  , ("lan", .both) -- Lango
  , ("lat", .purposiveOnly) -- Latvian
  , ("lav", .sequentialOnly) -- Lavukaleve
  , ("lep", .purposiveOnly) -- Lepcha
  , ("let", .sequentialOnly) -- Leti
  , ("lez", .purposiveOnly) -- Lezgian
  , ("lim", .purposiveOnly) -- Limbu
  , ("maa", .purposiveOnly) -- Maasai
  , ("mal", .purposiveOnly) -- Malagasy
  , ("mao", .purposiveOnly) -- Maori
  , ("may", .sequentialOnly) -- Maybrat
  , ("mhi", .purposiveOnly) -- Marathi
  , ("mnm", .sequentialOnly) -- Manam
  , ("mrl", .purposiveOnly) -- Murle
  , ("mrt", .purposiveOnly) -- Martuthunira
  , ("mul", .sequentialOnly) -- Mulao
  , ("mxc", .sequentialOnly) -- Mixtec (Chalcatongo)
  , ("nav", .sequentialOnly) -- Navajo
  , ("ndy", .sequentialOnly) -- Ndyuka
  , ("ngi", .purposiveOnly) -- Ngiyambaa
  , ("nht", .purposiveOnly) -- Nahuatl (Tetelcingo)
  , ("nym", .purposiveOnly) -- Nyamwezi
  , ("ond", .purposiveOnly) -- Oneida
  , ("orh", .purposiveOnly) -- Oromo (Harar)
  , ("otm", .purposiveOnly) -- Otomí (Mezquital)
  , ("pau", .purposiveOnly) -- Paumarí
  , ("pms", .sequentialOnly) -- Paamese
  , ("prh", .purposiveOnly) -- Pirahã
  , ("prs", .purposiveOnly) -- Persian
  , ("psm", .sequentialOnly) -- Passamaquoddy-Maliseet
  , ("ram", .purposiveOnly) -- Rama
  , ("rej", .sequentialOnly) -- Rejang
  , ("ret", .purposiveOnly) -- Retuarã
  , ("rus", .purposiveOnly) -- Russian
  , ("shk", .purposiveOnly) -- Shipibo-Konibo
  , ("shn", .purposiveOnly) -- Shona
  , ("shu", .purposiveOnly) -- Shuswap
  , ("spa", .both) -- Spanish
  , ("src", .purposiveOnly) -- Sarcee
  , ("sup", .both) -- Supyire
  , ("swa", .purposiveOnly) -- Swahili
  , ("tab", .sequentialOnly) -- Taba
  , ("tag", .purposiveOnly) -- Tagalog
  , ("tha", .both) -- Thai
  , ("tib", .purposiveOnly) -- Tibetan (Standard Spoken)
  , ("tml", .purposiveOnly) -- Tamil
  , ("tna", .sequentialOnly) -- Turkana
  , ("tuk", .both) -- Tukang Besi
  , ("tur", .purposiveOnly) -- Turkish
  , ("tvl", .both) -- Tuvaluan
  , ("tzo", .purposiveOnly) -- Tzotzil
  , ("ung", .purposiveOnly) -- Ungarinjin
  , ("vai", .purposiveOnly) -- Vai
  , ("vie", .both) -- Vietnamese
  , ("wam", .purposiveOnly) -- Wambaya
  , ("war", .purposiveOnly) -- Wari'
  , ("wch", .sequentialOnly) -- Wichí
  , ("wic", .purposiveOnly) -- Wichita
  , ("wrl", .purposiveOnly) -- Warlpiri
  , ("yap", .sequentialOnly) -- Yapese
  , ("yaq", .purposiveOnly) -- Yaqui
  , ("yay", .sequentialOnly) -- Yay
  , ("yid", .purposiveOnly) -- Yidiny
  , ("yim", .both) -- Yimas
  , ("yor", .both) -- Yoruba
  , ("yuw", .purposiveOnly) -- Yuwaalaraay
  , ("zul", .purposiveOnly) -- Zulu
  ]

end Data.WALS.F110A
