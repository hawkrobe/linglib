import Linglib.Morphology.DistributedMorphology.Categorizer.Gender

/-!
# Spanish binominal nouns

Spanish binominals join a first noun to a second by *de*. They fall into three types by the
class of the first noun. Group nouns (*grupo*, *conjunto*, *serie*) head pseudo-partitives,
quantity nouns (*montón*, *pila*, *cantidad*) head quantificational binominals, which also have a
descriptive reading in which the noun keeps its literal meaning, and expressive nouns (*mierda*,
*maravilla*, *desastre*) head qualitative binominals, in which the first noun evaluates the
referent of the second.

## References

* [saab-2026]
* [kramer-2015]
-/

namespace Spanish.Binominals

open DistributedMorphology
open DistributedMorphology.Categorizer (Head)

/-- The types of Spanish binominal, by the class of the first noun. -/
inductive BinominalType where
  /-- A group noun and the set it groups, as in *un grupo de estudiantes*. -/
  | pseudoPartitive
  /-- A quantity noun and what it quantifies, as in *un montón de estudiantes*. -/
  | quantificational
  /-- An expressive noun and what it evaluates, as in *una mierda de departamento*. -/
  | qualitative
  deriving DecidableEq, Repr

/-- A Spanish binominal noun entry, with gender encoded via the DM
    categorizing head on n ([kramer-2015]). -/
structure BinominalNoun where
  /-- The noun form -/
  form : String
  /-- Categorizing head (encodes gender structurally) -/
  nHead : Head
  /-- Binominal class -/
  binominalType : BinominalType
  /-- Gloss in English -/
  gloss : String
  deriving Repr

-- Group nouns (pseudo-partitive)
def grupo     : BinominalNoun := ⟨"grupo",     Head.n_plain, .pseudoPartitive,  "group"⟩
def conjunto  : BinominalNoun := ⟨"conjunto",  Head.n_plain, .pseudoPartitive,  "set"⟩
def serie     : BinominalNoun := ⟨"serie",     Head.n_uFem,  .pseudoPartitive,  "series"⟩

-- Quantity nouns (quantificational)
def montón    : BinominalNoun := ⟨"montón",    Head.n_plain, .quantificational, "heap/lot"⟩
def pila      : BinominalNoun := ⟨"pila",      Head.n_uFem,  .quantificational, "pile"⟩
def cantidad  : BinominalNoun := ⟨"cantidad",  Head.n_uFem,  .quantificational, "quantity"⟩
/-- Rioplatense *bocha* 'ball', a quantificational noun. -/
def bocha     : BinominalNoun := ⟨"bocha",     Head.n_uFem,  .quantificational, "ball/lot"⟩

-- Expressive nouns (qualitative)
def mierda    : BinominalNoun := ⟨"mierda",    Head.n_uFem,  .qualitative,      "shit"⟩
def maravilla : BinominalNoun := ⟨"maravilla", Head.n_uFem,  .qualitative,      "wonder"⟩
def desastre  : BinominalNoun := ⟨"desastre",  Head.n_plain, .qualitative,      "disaster"⟩

/-- All binominal noun entries. -/
def allNouns : List BinominalNoun :=
  [grupo, conjunto, serie, montón, pila, cantidad, bocha, mierda, maravilla, desastre]

/-- The entry with a given form. -/
def lookup (form : String) : Option BinominalNoun := allNouns.find? (·.form == form)

end Spanish.Binominals
