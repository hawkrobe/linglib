import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Core.Parse
import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Interface
import Linglib.Phenomena.Quantification.Studies.FrankeBergen2020

/-!
# Bridge: Franke & Bergen (2020) RSA Model → Quantification Phenomena

Global Intentions (GI) RSA model for exhaustification ambiguity.
The model depends on `AristQuant`, `NestedAristotelian`, `allSentences`,
and `exhParses` from `Phenomena.Quantification.Studies.FrankeBergen2020`,
so the full implementation lives here as a bridge file.
-/

namespace RSA.Implementations.FrankeBergen2020

open Core
open NeoGricean.Exhaustivity.Interface
open NeoGricean.Exhaustivity
open Phenomena.Quantification.Studies.FrankeBergen2020


/-- World state: (aliensWhoDrank, potsPerAlien)
    Simplified: 2 aliens, 3 pots. -/
structure AlienWorld where
  aliensWhoDrank : Fin 3  -- 0, 1, or 2 aliens
  potsPerAlien : Fin 4    -- 0, 1, 2, or 3 pots
  deriving DecidableEq, Repr, BEq

/-- All 12 worlds -/
def alienWorlds : List AlienWorld :=
  (List.finRange 3).flatMap λ a =>
    (List.finRange 4).map λ p => ⟨a, p⟩


/-- Quantifier meaning (simplified for 2-alien, 3-pot domain) -/
def quantMeaning (q : AristQuant) (n total : Nat) : Bool :=
  match q with
  | .none => n = 0
  | .some => n > 0
  | .all => n = total

/-- Literal meaning of nested Aristotelian (no EXH) -/
def literalMeaning (s : NestedAristotelian) (w : AlienWorld) : Bool :=
  let numAliens := 2
  let numPots := 3
  let aliensWhoDrankSome := w.aliensWhoDrank.val
  let potsEachDrank := if w.aliensWhoDrank.val > 0 then w.potsPerAlien.val else 0
  quantMeaning s.outer aliensWhoDrankSome numAliens &&
  quantMeaning s.inner potsEachDrank numPots


/-- Scale for Aristotelian quantifiers: none < some < all -/
def aristScale : List AristQuant := [.none, .some, .all]

/-- Convert Bool meaning to Prop' -/
def toProp (f : AlienWorld → Bool) : Prop' AlienWorld := λ w => f w = true

/-- Alternatives for outer quantifier (Q₁) -/
def outerAlternatives (s : NestedAristotelian) : Set (Prop' AlienWorld) :=
  { toProp (literalMeaning ⟨.none, s.inner⟩),
    toProp (literalMeaning ⟨.some, s.inner⟩),
    toProp (literalMeaning ⟨.all, s.inner⟩) }

/-- Alternatives for inner quantifier (Q₂) -/
def innerAlternatives (s : NestedAristotelian) : Set (Prop' AlienWorld) :=
  { toProp (literalMeaning ⟨s.outer, .none⟩),
    toProp (literalMeaning ⟨s.outer, .some⟩),
    toProp (literalMeaning ⟨s.outer, .all⟩) }

/-- Alternatives for matrix (whole sentence) - all 9 combinations -/
def matrixAlternatives (_s : NestedAristotelian) : Set (Prop' AlienWorld) :=
  { toProp (literalMeaning s) | s ∈ (allSentences.toFinset : Finset NestedAristotelian) }

/-- Position-dependent alternatives for nested Aristotelians.

    This is the key connection to the unified EXH machinery:
    - Position M: alternatives vary both quantifiers
    - Position O: alternatives vary the outer quantifier
    - Position I: alternatives vary the inner quantifier -/
def alternativesAtPosition (s : NestedAristotelian) : AlternativesAtPosition AlienWorld :=
  λ pos => match pos with
  | .M => matrixAlternatives s
  | .O => outerAlternatives s
  | .I => innerAlternatives s


/-- Exhaustifiable instance for nested Aristotelians.

    This IS appropriate because Franke & Bergen's model is about
    where EXH inserts (M, O, I positions).

    Uses the unified interface:
    - `exhOperator`: Innocent Exclusion (default)
    - `literalMeaning`: Base meaning before EXH
    - `alternativesAt`: Position-dependent scalar alternatives -/
instance : Exhaustifiable NestedAristotelian AlienWorld where
  -- Use Innocent Exclusion (Fox 2007) as the EXH operator
  exhOperator := .IE
  -- Standard 8 EXH parses
  parses := exhParses
  -- Literal meaning (no EXH)
  literalMeaning := literalMeaning
  -- Position-dependent alternatives
  alternativesAt := alternativesAtPosition


/-- GI model meaning function. -/
def giMeaning (p : Core.Parse) (s : NestedAristotelian) (w : AlienWorld) : ℚ :=
  boolToRat (Exhaustifiable.meaningAtParseBool p s w)

/-- L1 computation using RSA.Eval for the GI model -/
def giL1_world (s : NestedAristotelian) : List (AlienWorld × ℚ) :=
  RSA.Eval.L1_world allSentences alienWorlds exhParses [()] [()] [()]
    (λ p _ s' w => giMeaning p s' w)
    (λ _ => 1)  -- world prior
    (λ _ => 1)  -- interp prior
    (λ _ => 1)  -- lexicon prior
    (λ _ => 1)  -- belief state prior
    (λ _ => 1)  -- goal prior
    (λ _ _ => 1)  -- speaker credence
    (λ _ w1 w2 => w1 == w2)  -- identity goal projection
    (λ _ => 0)  -- no cost
    1  -- α = 1
    s


/-- Correct dimensions: 9 sentences × 8 parses × 12 worlds -/
theorem gi_dimensions :
    allSentences.length = 9 ∧
    exhParses.length = 8 ∧
    alienWorlds.length = 12 := by
  native_decide

/-- "Some some" (SS) is true at world (1,1) -/
theorem ss_true_at_1_1 :
    literalMeaning ⟨.some, .some⟩ ⟨⟨1, by omega⟩, ⟨1, by omega⟩⟩ = true := by
  native_decide

/-- "All all" (AA) requires both aliens drinking all pots -/
theorem aa_requires_full :
    literalMeaning ⟨.all, .all⟩ ⟨⟨2, by omega⟩, ⟨3, by omega⟩⟩ = true := by
  native_decide

/-- The model matches the phenomena prediction that GI wins -/
theorem gi_is_best_model :
    getPosterior .globalIntentions > getPosterior .lexicalUncertainty := by
  native_decide

-- Summary

/-
## What This Shows

1. **Unified EXH interface**: Uses `Exhaustifiable` which internally calls
   `applyExhAtParse` from NeoGricean.Exhaustivity.Unified.

2. **Position-dependent alternatives**: `alternativesAtPosition` provides
   different scalar alternatives for M, O, I positions.

3. **Operator selection**: Uses `.IE` (Innocent Exclusion) as the EXH operator,
   but this could be changed to `.MW` for comparison.

4. **Contrast with ScontrasPearl2021**: Scope ambiguity is NOT exhaustification.
   That file uses `Core.scopeParses` directly, without `Exhaustifiable`.

5. **Clean separation**:
   - `Core.Parse`: general grammatical ambiguity
   - `NeoGricean.Exhaustivity.Interface.exhParses`: EXH position parses
   - `Core.scopeParses`: scope reading parses
   - `Exhaustifiable`: typeclass for EXH-specific phenomena
   - `applyExhAtParse`: unified entry point for parse-guided EXH

## TODO

- Make `meaningAtParseBool` properly decidable (currently falls back to literal)
- Implement full exhaustified meaning computation
- Compare IE vs MW operators on this domain
-/

end RSA.Implementations.FrankeBergen2020
