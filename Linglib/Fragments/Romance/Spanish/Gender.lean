module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Spanish noun gender

Spanish nouns are masculine or feminine. A noun for a human being or one of a few well-known
animals takes the gender of the referent's sex, *el hombre* 'man' and *la mujer* 'woman', in a
special form for each sex, *el rey*, *la reina*, or with feminine *-a* for masculine *-o*, *el
gato*, *la gata*; some such nouns have one form for either sex, *el* or *la estudiante*, and a few
have one gender whatever the referent's sex, *la persona* 'person' and *el ángel* 'angel'. The
gender of every other noun, for things, plants and the remaining animals, has nothing to do with
sex and must be learned: *la mesa* 'table', *el libro* 'book'. The article and adjectives agree:
*-o* with a masculine, *-a* with a feminine ([butt-benjamin-2019]).

## Main definitions

* `Spanish.Gender.Value` — the two genders, with their comparative labels
* `Spanish.Gender.Noun`, `Spanish.Gender.allNouns` — nouns with a fixed gender
* `Spanish.Gender.eitherGender` — nouns with one form for either sex

## References

* [butt-benjamin-2019]
-/

@[expose] public section

namespace Spanish.Gender

/-- The two genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine

/-- A noun with its gender and the gender of its referents where the gender is the referent's. -/
abbrev Noun := GenderedNoun Value

/-! ### Nouns taking the referent's gender -/

/-- *hombre* 'man'. -/
def hombre : Noun := ⟨⟨"hombre", "man"⟩, .masc, some .masculine⟩

/-- *mujer* 'woman'. -/
def mujer : Noun := ⟨⟨"mujer", "woman"⟩, .fem, some .feminine⟩

/-- *niño* 'boy'. -/
def niño : Noun := ⟨⟨"niño", "boy"⟩, .masc, some .masculine⟩

/-- *niña* 'girl'. -/
def niña : Noun := ⟨⟨"niña", "girl"⟩, .fem, some .feminine⟩

/-- *rey* 'king'. -/
def rey : Noun := ⟨⟨"rey", "king"⟩, .masc, some .masculine⟩

/-- *reina* 'queen'. -/
def reina : Noun := ⟨⟨"reina", "queen"⟩, .fem, some .feminine⟩

/-- *gato* 'cat', also for the species. -/
def gato : Noun := ⟨⟨"gato", "cat"⟩, .masc, some .masculine⟩

/-- *gata* 'she-cat'. -/
def gata : Noun := ⟨⟨"gata", "she-cat"⟩, .fem, some .feminine⟩

/-! ### Nouns of one gender for either sex -/

/-- *persona* 'person', feminine whatever the referent's sex. -/
def persona : Noun := ⟨⟨"persona", "person"⟩, .fem, none⟩

/-- *ángel* 'angel', masculine whatever the referent's sex. -/
def ángel : Noun := ⟨⟨"ángel", "angel"⟩, .masc, none⟩

/-! ### Nouns of arbitrary gender -/

/-- *mesa* 'table'. -/
def mesa : Noun := ⟨⟨"mesa", "table"⟩, .fem, none⟩

/-- *silla* 'chair'. -/
def silla : Noun := ⟨⟨"silla", "chair"⟩, .fem, none⟩

/-- *casa* 'house'. -/
def casa : Noun := ⟨⟨"casa", "house"⟩, .fem, none⟩

/-- *puerta* 'door'. -/
def puerta : Noun := ⟨⟨"puerta", "door"⟩, .fem, none⟩

/-- *ventana* 'window'. -/
def ventana : Noun := ⟨⟨"ventana", "window"⟩, .fem, none⟩

/-- *cama* 'bed'. -/
def cama : Noun := ⟨⟨"cama", "bed"⟩, .fem, none⟩

/-- *libro* 'book'. -/
def libro : Noun := ⟨⟨"libro", "book"⟩, .masc, none⟩

/-- *zapato* 'shoe'. -/
def zapato : Noun := ⟨⟨"zapato", "shoe"⟩, .masc, none⟩

/-- *coche* 'car'. -/
def coche : Noun := ⟨⟨"coche", "car"⟩, .masc, none⟩

/-- *árbol* 'tree'. -/
def árbol : Noun := ⟨⟨"árbol", "tree"⟩, .masc, none⟩

/-- *cielo* 'sky'. -/
def cielo : Noun := ⟨⟨"cielo", "sky"⟩, .masc, none⟩

/-- *vaso* 'glass'. -/
def vaso : Noun := ⟨⟨"vaso", "glass"⟩, .masc, none⟩

/-- The nouns with a fixed gender. -/
def allNouns : List Noun :=
  [hombre, mujer, niño, niña, rey, reina, gato, gata, persona, ángel, mesa, silla, casa, puerta,
    ventana, cama, libro, zapato, coche, árbol, cielo, vaso]

/-! ### Nouns of either gender -/

/-- *soldado* 'soldier': *un soldado*, *una soldado*. -/
def soldado : _root_.Noun := ⟨"soldado", "soldier"⟩

/-- *estudiante* 'student': *el estudiante*, *la estudiante*. -/
def estudiante : _root_.Noun := ⟨"estudiante", "student"⟩

/-- *artista* 'artist': *el artista*, *la artista*. -/
def artista : _root_.Noun := ⟨"artista", "artist"⟩

/-- The nouns with one form for either sex, masculine of a male referent and feminine of a
female one. -/
def eitherGender : List _root_.Noun := [soldado, estudiante, artista]

/-! ### Agreement -/

/-- The endings of an agreeing adjective. -/
inductive Concord where
  | o
  | a
  deriving DecidableEq, Repr

/-- The ending an adjective takes in agreement with a gender. -/
def Value.concord : Value → Concord
  | .masc => .o
  | .fem => .a

/-- The genders are told apart by adjectival agreement. -/
theorem faithful_concord : Function.Injective Value.concord := by decide

end Spanish.Gender
