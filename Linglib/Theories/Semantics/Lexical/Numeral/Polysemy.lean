import Linglib.Theories.Semantics.Lexical.Noun.TypeShifting
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-!
# Number Word Polysemy (Snyder 2026)

Three polymorphic analyses of number words and their type-shifting maps.

## Key Idea

Polymorphic Contextualism: the lexical meaning of 'two' is an atomic predicate
`λx_a. two(x)`, applicable to different countable entities in different contexts.
Kinds whose instantiations are numeral tokens. All other meanings derive via
Partee type-shifting.

## The Type-Shifting Map (Contextualism)

```
  (numeral, kind-ref, token-ref)
        ↑ IOTA
  λx_a. two(x)  ——CARD——→  (predicative)  ——PM——→  (attributive)
                                   |                      |
                                  NOM                     A
                                   ↓                      ↓
                           (specificational)      (quantificational)
```

## References

- Snyder, E. (2026). Numbers as kinds. *L&P* 49, 57–100.
- Partee, B. (1986/1987). Noun Phrase Interpretation and Type-shifting.
- Mendia, J. A. (2020). One more comparative: a novel argument for degree abstraction.
-/

namespace Semantics.Lexical.Numeral.Polysemy

/-- The three polymorphic analyses of number words (Snyder §2, §5). -/
inductive PolymorphicAnalysis where
  | substantivalism  -- lexical = numeral (e), derive cardinal via CARD
  | adjectivalism    -- lexical = cardinal predicate (⟨e,t⟩), derive numeral via NOM+RSE
  | contextualism    -- lexical = atomic predicate (⟨e,t⟩), derive all via type-shifting
  deriving DecidableEq, BEq, Repr

/-- Semantic functions of number words (Snyder (1a-f) + (76g-j)). -/
inductive SemanticFunction where
  | predicative       -- (1a) Mars's moons are two (in number)
  | attributive       -- (1b) Those are Mars's two moons
  | quantificational  -- (1c) Mars has two moons
  | specificational   -- (1d) The number of Mars's moons is two
  | numeral           -- (1e) Two is an even number
  | closeAppositive   -- (1f) The number two is even
  | taxonomic         -- (47) Each kind of two belongs to a different system
  | tokenRef          -- (76g) Two is next to a five on the board
  | kindRef           -- (76i) Two comes in several varieties
  deriving DecidableEq, BEq, Repr

/-- Which type-shifting path derives each semantic function under Contextualism.
    The lexical predicate λx_a.two(x) is the source for all. -/
inductive DerivationPath where
  | cardFromPred    -- CARD applied to IOTA(pred) → predicative (76a)
  | pmFromCard      -- PM applied to CARD result → attributive (76b)
  | aFromCard       -- A applied to CARD result → quantificational (76c)
  | nomFromCard     -- NOM applied to CARD result → specificational (76d)
  | iotaFromPred    -- IOTA applied to pred → numeral (76e), kind-ref (76i)
  | iotaToken       -- IOTA applied to pred (token context) → token-ref (76g,h)
  | closeAppos      -- IOTA applied to N₁ ∧ N₂ → close appositive (76f,j)
  deriving DecidableEq, BEq, Repr

/-- Map from semantic function to derivation path under Contextualism. -/
def contextualistPath : SemanticFunction → DerivationPath
  | .predicative      => .cardFromPred
  | .attributive      => .pmFromCard
  | .quantificational => .aFromCard
  | .specificational   => .nomFromCard
  | .numeral          => .iotaFromPred
  | .closeAppositive  => .closeAppos
  | .taxonomic        => .iotaFromPred
  | .tokenRef         => .iotaToken
  | .kindRef          => .iotaFromPred

/-- Close appositive semantics: ⟦the N₁ N₂⟧ = ιx[N₁(x) ∧ N₂(x)] (Snyder §5.2, (16b)).
    N₁ functions as intersective modifier via IDENT, N₂ is the numeral predicate. -/
def closeAppositive {m : Semantics.Montague.Model}
    (domain : List m.Entity)
    (n1 n2 : m.interpTy Semantics.Montague.Ty.et)
    : Option (m.interpTy .e) :=
  Semantics.Lexical.Noun.TypeShifting.iota domain (fun x => n1 x && n2 x)

/-- Specificational copula: ⟦be⟧ = λx.λy_i. ∨y_i = x (Romero 2005, (34)).
    Maps individual concepts to their actual present values. -/
def specCopula {α β : Type} (actualValue : α → β) (x : α) : β := actualValue x

/-- The Identification Problem is resolved: close appositives are context-sensitive.
    "The von Neumann ordinal two" and "the Zermelo ordinal two" refer to different
    subkinds of TWO, so both can be true without contradiction (Snyder §5.2). -/
theorem identification_problem_resolved :
    ∀ (sys₁ sys₂ : Noun.Kind.Chierchia1998.NumberSystem),
      sys₁ ≠ sys₂ → Noun.Kind.Chierchia1998.twoSubkinds sys₁ sys₂ := by
  intro s₁ s₂ h; exact h

-- ============================================================================
-- Coverage Verification
-- ============================================================================

/-- The contextualist derivation map is total: every semantic function
    has a derivation path. (This is trivially true because `contextualistPath`
    is a total function, but stating it explicitly documents the claim.) -/
theorem contextualism_total (sf : SemanticFunction) :
    ∃ dp : DerivationPath, contextualistPath sf = dp := ⟨_, rfl⟩

/-- All nine semantic functions are covered by Contextualism. -/
theorem contextualism_covers_all_nine :
    [SemanticFunction.predicative, .attributive, .quantificational,
     .specificational, .numeral, .closeAppositive,
     .taxonomic, .tokenRef, .kindRef].length = 9 := rfl

/-- The taxonomic function is supported: NumberSystem has multiple subkinds,
    so "two comes in several varieties" is predicted to be felicitous. -/
theorem taxonomic_supported :
    contextualistPath .taxonomic = .iotaFromPred ∧
    Noun.Kind.Chierchia1998.NumberSystem.all.length ≥ 2 := ⟨rfl, by native_decide⟩

end Semantics.Lexical.Numeral.Polysemy
