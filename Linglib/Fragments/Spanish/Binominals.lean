import Linglib.Semantics.Quantification.BinominalDefs
import Linglib.Morphology.DistributedMorphology.Categorizer.Gender

/-!
# Spanish Binominal Nouns [saab-2026]

Lexical entries for Spanish nouns appearing in binominal constructions,
classified by their structural type.

## Noun Classes

- **Group nouns** (pseudo-partitive): *grupo*, *conjunto*, *serie*
- **Quantity nouns** (quantificational): *montón*, *pila*, *cantidad*
- **Expressive nouns** (qualitative): *mierda*, *maravilla*, *desastre*

Each class determines the internal structure of the binominal DP
and thereby the availability of NP-ellipsis.
-/

namespace Spanish.Binominals

open Quantifier.Binominal
open DistributedMorphology
open DistributedMorphology.Categorizer (Head)

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
