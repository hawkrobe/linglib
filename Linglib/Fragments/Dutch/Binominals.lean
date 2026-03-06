import Linglib.Core.Lexical.Binominal

/-!
# Dutch Binominal Nouns

Lexical entries for Dutch nouns appearing in *van*-binominal constructions,
classified by the shared `OfBinominalType` taxonomy.

Dutch uses *van* as the linking element. Like English, Dutch has
productive evaluative BNPs (*een beer van een man* 'a bear of a man')
and pseudo-partitives (*een glas water* / *een glas van water*).

The Den Dikken (2006) comparative QBNP analysis was originally based
on Dutch data.

## Examples

- Pseudo-partitive: *een glas water* 'a glass of water'
- EBNP: *een beer van een man* 'a bear of a man'
- EBNP: *een schat van een kind* 'a treasure of a child'
-/

namespace Fragments.Dutch.Binominals

open Core.Lexical.Binominal

/-- A Dutch binominal N₁ noun entry. -/
structure BinominalN₁Entry where
  /-- Surface form. -/
  form : String
  /-- Grammatical gender (de/het). True = neuter (het-word). -/
  neuter : Bool
  /-- Which *van*-binominal constructions this noun appears in. -/
  constructions : List OfBinominalType
  /-- English gloss. -/
  gloss : String
  deriving Repr, BEq

-- Pseudo-partitive N₁ nouns

def glas : BinominalN₁Entry :=
  ⟨"glas", true, [.pseudoPartitive], "glass"⟩

def stuk : BinominalN₁Entry :=
  ⟨"stuk", true, [.pseudoPartitive], "piece"⟩

def groep : BinominalN₁Entry :=
  ⟨"groep", false, [.pseudoPartitive], "group"⟩

def hoop : BinominalN₁Entry :=
  ⟨"hoop", false, [.pseudoPartitive], "heap/lot"⟩

-- Evaluative N₁ nouns

def beer : BinominalN₁Entry :=
  ⟨"beer", false, [.nPP, .evaluative], "bear"⟩

def schat : BinominalN₁Entry :=
  ⟨"schat", false, [.evaluative], "treasure"⟩

def ramp : BinominalN₁Entry :=
  ⟨"ramp", false, [.evaluative], "disaster"⟩

def allN₁Entries : List BinominalN₁Entry :=
  [glas, stuk, groep, hoop, beer, schat, ramp]

/-- Dutch evaluative BNPs are N₂-headed. -/
theorem beer_n₂_headed :
    (OfBinominalType.evaluative).head = .n₂ := rfl

end Fragments.Dutch.Binominals
