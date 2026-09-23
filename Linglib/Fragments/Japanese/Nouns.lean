module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Japanese.Classifiers
public import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Japanese nouns

The Japanese noun as a lexical entry: the root `Noun` with its romanization, the classifier it
counts with, and the optional plural in *-tachi* where the entry records one; a name is the root
`ProperName` with its romanization. Japanese is [+arg, −pred] ([chierchia-1998]): nouns denote
kinds, and with no articles no covert shift is blocked, so every bare noun is an argument. The
classifiers are `Japanese.Classifier`.

## References

* [chierchia-1998]
* [downing-1996]
-/

@[expose] public section

namespace Japanese.Nouns

open Japanese (Classifier)
open Genericity

/-- A Japanese noun: the root entry with its romanization, the classifier it counts with, if any,
and its optional plural. -/
structure Noun extends _root_.Noun where
  /-- The romanization. -/
  romaji : String
  /-- The classifier the noun counts with; none for a mass noun. -/
  classifier : Option Classifier := some .tsu
  /-- The optional plural in *-tachi*. -/
  plural : Option String := none
  deriving DecidableEq, Repr

/-! ### Common nouns -/

def inu : Noun := { form := "犬", gloss := "dog", romaji := "inu", classifier := some .hiki }
def neko : Noun := { form := "猫", gloss := "cat", romaji := "neko", classifier := some .hiki }
def hito : Noun :=
  { form := "人", gloss := "person", romaji := "hito", classifier := some .nin,
    plural := "人たち" }
def hon : Noun := { form := "本", gloss := "book", romaji := "hon", classifier := some .satsu }
def kuruma : Noun := { form := "車", gloss := "car", romaji := "kuruma", classifier := some .dai }
def tori : Noun := { form := "鳥", gloss := "bird", romaji := "tori", classifier := some .wa }
def hana : Noun := { form := "花", gloss := "flower", romaji := "hana", classifier := some .hon }
def mizu : Noun := { form := "水", gloss := "water", romaji := "mizu", classifier := none }
def gohan : Noun :=
  { form := "ご飯", gloss := "cooked rice", romaji := "gohan", classifier := none }
def musume : Noun :=
  { form := "娘", gloss := "daughter", romaji := "musume", classifier := some .nin,
    plural := "娘たち" }
def musuko : Noun :=
  { form := "息子", gloss := "son", romaji := "musuko", classifier := some .nin,
    plural := "息子たち" }
def gakusei : Noun :=
  { form := "学生", gloss := "student", romaji := "gakusei", classifier := some .nin,
    plural := "学生たち" }
def sensei : Noun :=
  { form := "先生", gloss := "teacher", romaji := "sensei", classifier := some .nin,
    plural := "先生たち" }
def tomodachi : Noun :=
  { form := "友達", gloss := "friend", romaji := "tomodachi", classifier := some .nin }

/-! ### Proper names -/

/-- A Japanese name: the root name with its romanization. -/
structure ProperName extends _root_.ProperName where
  /-- The romanization. -/
  romaji : String
  deriving DecidableEq, Repr

/-- A personal name glossed by its romanization. -/
def name (form romaji : String) (gender : Option Gender := none) : ProperName :=
  { form, gloss := romaji, romaji, gender }

def taro : ProperName := name "太郎" "Tarō" (some .masculine)
def hanako : ProperName := name "花子" "Hanako" (some .feminine)
def yamada : ProperName := name "山田" "Yamada"
def tanaka : ProperName := name "田中" "Tanaka"

/-! ### The Nominal Mapping Parameter -/

/-- Japanese is [+arg, −pred]: nouns denote kinds, and with no articles
(`Japanese.Determiners.inventory`) no covert shift is blocked ([chierchia-1998]). -/
def nominalMapping : NominalMapping := .argOnly

end Japanese.Nouns
