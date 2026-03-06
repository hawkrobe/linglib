import Linglib.Core.Lexical.Binominal

/-!
# Italian Binominal Nouns

Lexical entries for Italian nouns appearing in *di*-binominal constructions,
classified by the shared `OfBinominalType` taxonomy.

Italian binominals use *di* as the linking element and follow the same
structural patterns as other Romance languages. The EBNP construction
(*quell'idiota di un dottore*) is attested in Italian and may represent
the Latin source for both French and English evaluative BNPs.

## Examples

- N+PP: *la bestia del campo* 'the beast of the field'
- Head-classifier: *una torta di segale* 'a cake of rye'
- Pseudo-partitive: *un bicchiere d'acqua* 'a glass of water'
- EBNP: *quell'idiota di un dottore* 'that idiot of a doctor'
-/

namespace Fragments.Italian.Binominals

open Core.Lexical.Binominal

/-- An Italian binominal N₁ noun entry. -/
structure BinominalN₁Entry where
  /-- Surface form. -/
  form : String
  /-- Grammatical gender (true = feminine). -/
  feminine : Bool
  /-- Which *di*-binominal constructions this noun appears in. -/
  constructions : List OfBinominalType
  /-- English gloss. -/
  gloss : String
  deriving Repr, BEq

-- Pseudo-partitive N₁ nouns

def bicchiere : BinominalN₁Entry :=
  ⟨"bicchiere", false, [.pseudoPartitive], "glass"⟩

def pezzo : BinominalN₁Entry :=
  ⟨"pezzo", false, [.pseudoPartitive], "piece"⟩

def gruppo : BinominalN₁Entry :=
  ⟨"gruppo", false, [.pseudoPartitive], "group"⟩

def mucchio : BinominalN₁Entry :=
  ⟨"mucchio", false, [.pseudoPartitive], "heap/lot"⟩

-- Evaluative N₁ nouns

def idiota : BinominalN₁Entry :=
  ⟨"idiota", false, [.evaluative], "idiot"⟩

def mostro : BinominalN₁Entry :=
  ⟨"mostro", false, [.nPP, .headClassifier, .evaluative], "monster"⟩

def tesoro : BinominalN₁Entry :=
  ⟨"tesoro", false, [.evaluative], "treasure"⟩

def allN₁Entries : List BinominalN₁Entry :=
  [bicchiere, pezzo, gruppo, mucchio, idiota, mostro, tesoro]

/-- Italian pseudo-partitives are N₂-headed, like all Romance pseudo-partitives. -/
theorem bicchiere_n₂_headed :
    (OfBinominalType.pseudoPartitive).head = .n₂ := rfl

end Fragments.Italian.Binominals
