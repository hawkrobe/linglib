module

public import Linglib.Fragments.Romance.Spanish.Gender

/-!
# Spanish binominal nouns

Spanish binominals join a first noun to a second by *de*, and fall into three types by the class
of the first noun. A group noun heads a pseudo-partitive, *un grupo de estudiantes* 'a group of
students'; a quantity noun heads a quantificational binominal, *un montón de estudiantes* 'a lot
of students'; and an expressive noun heads a qualitative binominal, in which it evaluates the
referent of the second noun, *una mierda de departamento* 'a shit of an apartment'. Group and
quantity nouns also have a descriptive reading in which they head the phrase, as *una pila de
libros* is 'a pile of books' beside 'a lot of books'. *Bocha* and *pila* are the Rioplatense
quantity nouns ([saab-2026]).

## Main definitions

* `Spanish.Binominals.BinominalType` — the three types
* `Spanish.Binominals.BinominalNoun` — a noun with the type of binominal it heads

## References

* [saab-2026]
-/

@[expose] public section

namespace Spanish.Binominals

open Spanish.Gender (Value)

/-- The types of binominal, by the class of the first noun. -/
inductive BinominalType where
  /-- A group noun and the set it groups. -/
  | pseudoPartitive
  /-- A quantity noun and what it quantifies. -/
  | quantificational
  /-- An expressive noun and what it evaluates. -/
  | qualitative
  deriving DecidableEq, Repr

/-- A noun with its gender and the type of binominal it heads. -/
structure BinominalNoun extends Spanish.Gender.Noun where
  binominalType : BinominalType

/-- *grupo* 'group'. -/
def grupo : BinominalNoun := ⟨⟨⟨"grupo", "group"⟩, .masc, none⟩, .pseudoPartitive⟩

/-- *parte* 'part'. -/
def parte : BinominalNoun := ⟨⟨⟨"parte", "part"⟩, .fem, none⟩, .pseudoPartitive⟩

/-- *mayoría* 'most'. -/
def mayoría : BinominalNoun := ⟨⟨⟨"mayoría", "most"⟩, .fem, none⟩, .pseudoPartitive⟩

/-- *montón* 'lot'. -/
def montón : BinominalNoun := ⟨⟨⟨"montón", "lot"⟩, .masc, none⟩, .quantificational⟩

/-- *pila* 'pile', Rioplatense. -/
def pila : BinominalNoun := ⟨⟨⟨"pila", "pile"⟩, .fem, none⟩, .quantificational⟩

/-- *bocha* 'ball', Rioplatense. -/
def bocha : BinominalNoun := ⟨⟨⟨"bocha", "ball"⟩, .fem, none⟩, .quantificational⟩

/-- *mierda* 'shit'. -/
def mierda : BinominalNoun := ⟨⟨⟨"mierda", "shit"⟩, .fem, none⟩, .qualitative⟩

/-- The binominal nouns. -/
def allNouns : List BinominalNoun := [grupo, parte, mayoría, montón, pila, bocha, mierda]

/-- The entry with a given form. -/
def lookup (form : String) : Option BinominalNoun := allNouns.find? (·.form == form)

end Spanish.Binominals
