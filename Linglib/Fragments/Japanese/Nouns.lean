module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Japanese.Classifiers

/-!
# Japanese nouns

The Japanese noun as a lexical entry: the root entry with its romanization as citation form,
its spelling, the classifiers it is counted with, and the optional plural in *-tachi* where the
entry records one; a name is the root `ProperName` with its spelling. Japanese has no articles,
and a bare noun can be an argument. A mass noun such as *mizu* 'water' takes no classifier.

## References

* [downing-1996]
-/

@[expose] public section

namespace Japanese.Nouns

/-- A Japanese noun: the root entry with its romanization as citation form, its spelling, the
classifiers it is counted with, and its optional plural. -/
structure Noun extends ClassifiedNoun Classifier where
  /-- The spelling in kanji and kana. -/
  script : String
  /-- The optional plural in *-tachi*, romanized. -/
  plural : Option String := none
  deriving DecidableEq

/-! ### Common nouns -/

/-- 犬 *inu* 'dog'. -/
def inu : Noun :=
  { form := "inu", script := "犬", gloss := "dog", classifiers := {Classifiers.hiki} }

/-- 猫 *neko* 'cat'. -/
def neko : Noun :=
  { form := "neko", script := "猫", gloss := "cat", classifiers := {Classifiers.hiki} }

/-- 人 *hito* 'person'. -/
def hito : Noun :=
  { form := "hito", script := "人", gloss := "person", classifiers := {Classifiers.nin},
    plural := "hitotachi" }

/-- 本 *hon* 'book'. -/
def hon : Noun :=
  { form := "hon", script := "本", gloss := "book", classifiers := {Classifiers.satsu} }

/-- 車 *kuruma* 'car'. -/
def kuruma : Noun :=
  { form := "kuruma", script := "車", gloss := "car", classifiers := {Classifiers.dai} }

/-- 鳥 *tori* 'bird'. -/
def tori : Noun :=
  { form := "tori", script := "鳥", gloss := "bird", classifiers := {Classifiers.wa} }

/-- 花 *hana* 'flower'. -/
def hana : Noun :=
  { form := "hana", script := "花", gloss := "flower", classifiers := {Classifiers.hon} }

/-- 水 *mizu* 'water'. -/
def mizu : Noun := { form := "mizu", script := "水", gloss := "water", classifiers := ∅ }

/-- ご飯 *gohan* 'cooked rice'. -/
def gohan : Noun := { form := "gohan", script := "ご飯", gloss := "cooked rice", classifiers := ∅ }

/-- 娘 *musume* 'daughter'. -/
def musume : Noun :=
  { form := "musume", script := "娘", gloss := "daughter", classifiers := {Classifiers.nin},
    plural := "musumetachi" }

/-- 息子 *musuko* 'son'. -/
def musuko : Noun :=
  { form := "musuko", script := "息子", gloss := "son", classifiers := {Classifiers.nin},
    plural := "musukotachi" }

/-- 学生 *gakusei* 'student'. -/
def gakusei : Noun :=
  { form := "gakusei", script := "学生", gloss := "student", classifiers := {Classifiers.nin},
    plural := "gakuseitachi" }

/-- 先生 *sensei* 'teacher'. -/
def sensei : Noun :=
  { form := "sensei", script := "先生", gloss := "teacher", classifiers := {Classifiers.nin},
    plural := "senseitachi" }

/-- 友達 *tomodachi* 'friend'. -/
def tomodachi : Noun :=
  { form := "tomodachi", script := "友達", gloss := "friend", classifiers := {Classifiers.nin} }

/-! ### Proper names -/

/-- A Japanese name: the root name with its romanization as citation form, and its spelling. -/
structure ProperName extends _root_.ProperName where
  /-- The spelling in kanji and kana. -/
  script : String
  deriving DecidableEq, Repr

/-- A personal name glossed by its romanization. -/
def name (form script : String) (gender : Option Gender := none) : ProperName :=
  { form, gloss := form, script, gender }

def taro : ProperName := name "Tarō" "太郎" (some .masculine)
def hanako : ProperName := name "Hanako" "花子" (some .feminine)
def yamada : ProperName := name "Yamada" "山田"
def tanaka : ProperName := name "Tanaka" "田中"

end Japanese.Nouns
