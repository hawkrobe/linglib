import Linglib.Core.Lexical.Binominal

/-!
# French Binominal Nouns @cite{ten-wolde-2023}

Lexical entries for French nouns appearing in *de*-binominal constructions,
classified by the shared `OfBinominalType` taxonomy.

French has all six *of*-binominal types, using *de* as the linking element.
The evaluative BNP may have entered English from French or Latin
(@cite{ten-wolde-2023}).

## Examples

- N+PP: *la bête du champ* 'the beast of the field'
- Head-classifier: *un gâteau de seigle* 'a cake of rye'
- Pseudo-partitive: *un verre d'eau* 'a glass of water'
- EBNP: *cet idiot de médecin* 'that idiot of a doctor'
- EM: *un sacré de boulot* 'a hell of a job' (informal)
-/

namespace Fragments.French.Binominals

open Core.Lexical.Binominal

/-- A French binominal N₁ noun entry. -/
structure BinominalN₁Entry where
  /-- Surface form. -/
  form : String
  /-- Grammatical gender (true = feminine). -/
  feminine : Bool
  /-- Which *de*-binominal constructions this noun appears in. -/
  constructions : List OfBinominalType
  /-- English gloss. -/
  gloss : String
  deriving Repr, BEq

-- Pseudo-partitive N₁ nouns

def verre : BinominalN₁Entry :=
  ⟨"verre", false, [.pseudoPartitive], "glass"⟩

def morceau : BinominalN₁Entry :=
  ⟨"morceau", false, [.pseudoPartitive], "piece"⟩

def tas : BinominalN₁Entry :=
  ⟨"tas", false, [.pseudoPartitive], "heap/lot"⟩

def groupe : BinominalN₁Entry :=
  ⟨"groupe", false, [.pseudoPartitive], "group"⟩

-- Evaluative N₁ nouns

def idiot : BinominalN₁Entry :=
  ⟨"idiot", false, [.evaluative], "idiot"⟩

def imbécile : BinominalN₁Entry :=
  ⟨"imbécile", false, [.evaluative], "imbecile"⟩

def monstre : BinominalN₁Entry :=
  ⟨"monstre", false, [.nPP, .headClassifier, .evaluative], "monster"⟩

def allN₁Entries : List BinominalN₁Entry :=
  [verre, morceau, tas, groupe, idiot, imbécile, monstre]

/-- French pseudo-partitives are N₂-headed. -/
theorem verre_n₂_headed :
    (OfBinominalType.pseudoPartitive).head = .n₂ := rfl

/-- French evaluative BNPs are N₂-headed. -/
theorem idiot_n₂_headed :
    (OfBinominalType.evaluative).head = .n₂ := rfl

end Fragments.French.Binominals
