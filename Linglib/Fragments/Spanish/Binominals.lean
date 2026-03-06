import Linglib.Core.Lexical.Binominal

/-!
# Spanish Binominal Nouns @cite{saab-2026}

Lexical entries for Spanish nouns appearing in binominal constructions,
classified by their structural type.

## Noun Classes

- **Group nouns** (pseudo-partitive): *grupo*, *conjunto*, *serie*
- **Quantity nouns** (quantificational): *montón*, *pila*, *cantidad*
- **Expressive nouns** (qualitative): *mierda*, *maravilla*, *desastre*

Each class determines the internal structure of the binominal DP
and thereby the availability of NP-ellipsis.
-/

namespace Fragments.Spanish.Binominals

open Core.Lexical.Binominal

/-- A Spanish binominal noun entry. -/
structure BinominalNoun where
  /-- The noun form -/
  form : String
  /-- Grammatical gender (true = feminine) -/
  feminine : Bool
  /-- Binominal class -/
  binominalType : BinominalType
  /-- Gloss in English -/
  gloss : String
  deriving Repr

-- Group nouns (pseudo-partitive)
def grupo     : BinominalNoun := ⟨"grupo",     false, .pseudoPartitive,  "group"⟩
def conjunto  : BinominalNoun := ⟨"conjunto",  false, .pseudoPartitive,  "set"⟩
def serie     : BinominalNoun := ⟨"serie",     true,  .pseudoPartitive,  "series"⟩

-- Quantity nouns (quantificational)
def montón    : BinominalNoun := ⟨"montón",    false, .quantificational, "heap/lot"⟩
def pila      : BinominalNoun := ⟨"pila",      true,  .quantificational, "pile"⟩
def cantidad  : BinominalNoun := ⟨"cantidad",  true,  .quantificational, "quantity"⟩

-- Expressive nouns (qualitative)
def mierda    : BinominalNoun := ⟨"mierda",    true,  .qualitative,      "shit"⟩
def maravilla : BinominalNoun := ⟨"maravilla", true,  .qualitative,      "wonder"⟩
def desastre  : BinominalNoun := ⟨"desastre",  false, .qualitative,      "disaster"⟩

/-- All binominal noun entries. -/
def allNouns : List BinominalNoun :=
  [grupo, conjunto, serie, montón, pila, cantidad, mierda, maravilla, desastre]

/-- Group and quantity nouns license NP-ellipsis; expressive nouns do not. -/
theorem grupo_licenses_npe : grupo.binominalType.licensesNPE = true := rfl
theorem monton_licenses_npe : montón.binominalType.licensesNPE = true := rfl
theorem mierda_blocks_npe : mierda.binominalType.licensesNPE = false := rfl

/-- Every noun's NPE licensing is determined by its binominal type. -/
theorem all_nouns_npe_from_type :
    allNouns.all (λ n => n.binominalType.licensesNPE = n.binominalType.hasNumE) = true := by
  native_decide

end Fragments.Spanish.Binominals
