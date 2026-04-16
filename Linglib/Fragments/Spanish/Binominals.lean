import Linglib.Core.Lexical.Binominal
import Linglib.Theories.Morphology.DM.Categorizer

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
open Morphology.DM

/-- A Spanish binominal noun entry, with gender encoded via the DM
    categorizing head on n (@cite{kramer-2015}). -/
structure BinominalNoun where
  /-- The noun form -/
  form : String
  /-- Categorizing head (encodes gender structurally) -/
  nHead : CatHead
  /-- Binominal class -/
  binominalType : BinominalType
  /-- Gloss in English -/
  gloss : String
  deriving Repr

-- Group nouns (pseudo-partitive)
def grupo     : BinominalNoun := ⟨"grupo",     CatHead.n_plain, .pseudoPartitive,  "group"⟩
def conjunto  : BinominalNoun := ⟨"conjunto",  CatHead.n_plain, .pseudoPartitive,  "set"⟩
def serie     : BinominalNoun := ⟨"serie",     CatHead.n_uFem,  .pseudoPartitive,  "series"⟩

-- Quantity nouns (quantificational)
def montón    : BinominalNoun := ⟨"montón",    CatHead.n_plain, .quantificational, "heap/lot"⟩
def pila      : BinominalNoun := ⟨"pila",      CatHead.n_uFem,  .quantificational, "pile"⟩
def cantidad  : BinominalNoun := ⟨"cantidad",  CatHead.n_uFem,  .quantificational, "quantity"⟩

-- Expressive nouns (qualitative)
def mierda    : BinominalNoun := ⟨"mierda",    CatHead.n_uFem,  .qualitative,      "shit"⟩
def maravilla : BinominalNoun := ⟨"maravilla", CatHead.n_uFem,  .qualitative,      "wonder"⟩
def desastre  : BinominalNoun := ⟨"desastre",  CatHead.n_plain, .qualitative,      "disaster"⟩

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
