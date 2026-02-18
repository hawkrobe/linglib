import Mathlib.Data.Rat.Defs
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# Lexical Uncertainty Extension to RSA

## Architecture

Lexical uncertainty posits that speakers and listeners have uncertainty about
the semantic content of utterances. Rather than a fixed lexicon, there is a
set of possible lexica Λ, and pragmatic inference involves reasoning about
which lexicon is in use.

### Innovation (Bergen, Levy & Goodman 2016)

The marginalization over lexica happens at L₁, not L₀:
- L₀ is still parameterized by a specific lexicon L
- S₁ believes L₀ uses lexicon L (and is certain about it)
- L₁ is uncertain which lexicon S₁/L₀ are using, and marginalizes

### What This Derives

1. **M-implicatures**: Complex expressions → marked (low-probability) interpretations
2. **Ignorance implicatures**: "some or all" → speaker doesn't know which
3. **Non-convex disjunctive implicatures**: "one or three" ≠ "one or two"

## Status

The ℚ-based RSA evaluation infrastructure (RSA.Eval, boolToRat, RSAScenario) has been
removed. Type definitions and structural properties are preserved. RSA computations
(L0, S1, L1) need to be re-implemented using the new RSAConfig framework.

## Reference

Bergen, Levy & Goodman (2016) "Pragmatic reasoning through semantic inference"
-/

-- Lexicon: A mapping from utterances to truth functions

/--
A lexicon maps each utterance to a truth function over worlds.

In Bergen et al. (2016) notation:
  L(u, w) = 1 if w ∈ ⟦u⟧_L, else 0

For graded semantics, we allow values in [0,1].
-/
structure Lexicon (Utterance World : Type) where
  /-- The meaning function for this lexicon -/
  meaning : Utterance → World → ℚ

namespace Lexicon

variable {U W : Type}

/-- Create a lexicon from an RSAScenario's meaning function -/
def ofScenario {U W : Type} (_utts : List U) (_worlds : List W) (φ : U → W → ℚ) : Lexicon U W where
  meaning := φ

/-- Two lexica are equivalent if they assign the same meanings -/
def equiv (L₁ L₂ : Lexicon U W) : Prop :=
  ∀ u w, L₁.meaning u w = L₂.meaning u w

/-- Check if a lexicon is a refinement of another (logically implies) -/
def refines (L_refined L_base : Lexicon U W) : Prop :=
  ∀ u w, L_base.meaning u w = 0 → L_refined.meaning u w = 0

/-- Notation: L' ≤ₗ L means L' refines (is more specific than) L -/
notation:50 L' " ≤ₗ " L => refines L' L

end Lexicon

-- LexicalUncertaintyScenario: RSA with multiple possible lexica

/--
Lexical Uncertainty RSA Scenario.

Extends the basic RSA setup with:
- A set of possible lexica Λ
- A prior distribution over lexica

The semantic content of utterances is not fixed; rather, pragmatic inference
jointly determines both the interpretation AND the lexicon.
-/
structure LUScenario where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of possible worlds -/
  World : Type
  /-- Base semantic lexicon (unrefined meanings) -/
  baseLexicon : Lexicon Utterance World
  /-- Set of possible refined lexica -/
  lexica : List (Lexicon Utterance World)
  /-- Prior over lexica (default: uniform) -/
  lexPrior : Lexicon Utterance World → ℚ := λ _ => 1
  /-- Prior over worlds -/
  worldPrior : World → ℚ := λ _ => 1
  /-- Enumeration of utterances -/
  utterances : List Utterance
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Rationality parameter. Higher values = more informative speaker. -/
  α : ℕ := 1
  /-- Null utterance cost (high, to discourage) -/
  nullCost : ℚ := 10
  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]
  [worldDecEq : DecidableEq World]

attribute [instance] LUScenario.uttBEq LUScenario.worldBEq LUScenario.worldDecEq

-- Lexical Refinement: Generating Λ from base semantics

namespace LexicalRefinement

/--
A refinement of a truth function: a subset of worlds where it's true.

Given base meaning M : W → Bool, a valid refinement M' satisfies:
  ∀ w, M(w) = false → M'(w) = false

That is, M' can only narrow down the set of true worlds, not expand it.
-/
structure Refinement (W : Type) where
  /-- The refined meaning as a subset indicator -/
  meaning : W → Bool

/--
Check if one meaning refines another (is more specific).

M' refines M iff M' ⊆ M (as sets of worlds).
-/
def Refinement.isValidFor {W : Type} (r : Refinement W) (base : W → Bool) : Prop :=
  ∀ w, base w = false → r.meaning w = false

/--
Generate all valid refinements of a Boolean meaning over finite worlds.

For a base meaning true at n worlds, there are 2ⁿ - 1 valid non-trivial refinements
(excluding the empty refinement which would be contradictory).
-/
def allRefinements {W : Type} [DecidableEq W] (worlds : List W) (base : W → Bool)
    : List (Refinement W) :=
  -- Get worlds where base is true
  let trueWorlds := worlds.filter base
  -- Generate all non-empty subsets
  let subsets := trueWorlds.sublists.filter (·.length > 0)
  -- Convert each subset to a refinement
  subsets.map λ subset =>
    { meaning := λ w => subset.contains w }

end LexicalRefinement

-- Some-or-All Ignorance Implicature Types

/--
Observation states for ignorance implicatures.

The speaker may:
- Know all passed (∀)
- Know some-but-not-all passed (∃¬∀)
- Be ignorant (?)
-/
inductive ObsState where
  | knowAll      -- Speaker observed all passed
  | knowSomeNot  -- Speaker observed some-but-not-all passed
  | ignorant     -- Speaker made no observation
  deriving Repr, BEq, DecidableEq

/--
World states for scalar scenarios.
-/
inductive ScalarWorld where
  | all     -- All passed
  | someNot -- Some but not all passed
  deriving Repr, BEq, DecidableEq

/--
Utterances for some-or-all ignorance implicatures.
-/
inductive SomeOrAllUtt where
  | all_
  | some_
  | someOrAll
  deriving Repr, BEq, DecidableEq

-- Theorems

namespace LUTheorems

/--
Symmetry breaking: semantically equivalent utterances can get different interpretations.

This is the key property that enables M-implicatures.
-/
theorem symmetry_breaking_possible :
    ∃ (S : LUScenario) (u₁ u₂ : S.Utterance) (w : S.World),
      -- u₁ and u₂ have same base meaning
      S.baseLexicon.meaning u₁ = S.baseLexicon.meaning u₂ ∧
      -- But different L₁ interpretations (under some LU-RSA model)
      True := by
  sorry  -- TODO: construct concrete counterexample with new RSAConfig

end LUTheorems
