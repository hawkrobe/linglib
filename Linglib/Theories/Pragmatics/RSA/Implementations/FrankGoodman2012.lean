/-
# Frank & Goodman (2012) @cite{frank-goodman-2012}

"Predicting Pragmatic Reasoning in Language Games"
Science 336(6084): 998

This paper introduced the RSA (Rational Speech Acts) framework, showing that
pragmatic inferences in reference games can be predicted by modeling listeners
as reasoning about rational, informative speakers.

## The Reference Game

Context: {blue_square, blue_circle, green_square}
Utterances: {blue, green, square, circle}

## Result

L1("square") assigns higher probability to blue_square than green_square.

Why? A speaker wanting green_square would say "green" (uniquely identifying).
Saying "square" signals they probably mean blue_square.

## Speaker Utility

The speaker utility is belief-based (informational):

    S1 score = L0(w|u)^α

Using rpow so that false utterances (L0 = 0) correctly get score 0.
When α = 1, S1(u|w) ∝ L0(w|u), which is the original F&G formulation.

## References

- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
  Science 336(6084): 998.
- Degen (2023). The Rational Speech Act Framework. §2.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSADecide
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RSA.FrankGoodman2012

open RSA Real

-- ============================================================================
-- Domain Types
-- ============================================================================

/-- The three objects in the classic Frank & Goodman context.

Previously modeled as Color × Shape (4 values), but the context only has
3 objects — the phantom green_circle made key theorems unprovable. -/
inductive Object where
  | blue_square | blue_circle | green_square
  deriving Repr, DecidableEq, BEq

instance : Fintype Object where
  elems := {.blue_square, .blue_circle, .green_square}
  complete := fun o => by cases o <;> decide

instance : Nonempty Object := ⟨.blue_square⟩

/-- A feature predicate: the four single-word utterances in the reference game. -/
inductive Feature where
  | blue | green | square | circle
  deriving Repr, DecidableEq, BEq

instance : Fintype Feature where
  elems := {.blue, .green, .square, .circle}
  complete := fun f => by cases f <;> decide

instance : Nonempty Feature := ⟨.blue⟩

/-- Montague meaning: ⟦feature⟧(object) = characteristic function. -/
def Feature.appliesTo (f : Feature) (o : Object) : Bool :=
  match f, o with
  | .blue, .blue_square => true
  | .blue, .blue_circle => true
  | .green, .green_square => true
  | .square, .blue_square => true
  | .square, .green_square => true
  | .circle, .blue_circle => true
  | _, _ => false

-- ============================================================================
-- Context
-- ============================================================================

/-- The four utterances. -/
def utt_blue : Feature := .blue
def utt_green : Feature := .green
def utt_square : Feature := .square
def utt_circle : Feature := .circle

-- ============================================================================
-- RSAConfig: The Reference Game
-- ============================================================================

/-- The Frank & Goodman (2012) reference game as an RSAConfig.

- Meaning: Boolean feature semantics (1 if feature applies, 0 otherwise)
- World prior: uniform
- α = 1 (standard rationality)
- S1 score: belief-based (rpow): score = L0(w|u)^α
- No latent variables (Unit) -/
noncomputable def cfg : RSAConfig Feature Object where
  meaning _ u w := if u.appliesTo w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- Derived Agents
-- ============================================================================

/-!
All RSA levels are derived from `cfg`:

- `cfg.L0agent ()` : `RationalAction Feature Object` — literal listener
- `cfg.S1agent ()` : `RationalAction Object Feature` — pragmatic speaker
- `cfg.L0 () u w` — L0 posterior P(w|u)
- `cfg.S1 () w u` — S1 policy P(u|w)
- `cfg.L1 u w` — L1 posterior P(w|u)
-/

-- ============================================================================
-- Main Theorems
-- ============================================================================

/-- **Reference Game Theorem**

L1("square") assigns higher probability to blue_square than green_square.

This captures the pragmatic inference: if speaker wanted green_square,
they would have said "green" (uniquely identifying). Saying "square"
signals they probably mean blue_square. -/
theorem reference_game_inference :
    cfg.L1 utt_square .blue_square > cfg.L1 utt_square .green_square := by
  rsa_decide

/-- At literal level L0, squares are equally likely. -/
theorem l0_squares_equal :
    cfg.L0 () utt_square .blue_square = cfg.L0 () utt_square .green_square := by
  rsa_decide

/-- Speaker in green_square world prefers "green" over "square". -/
theorem s1_green_prefers_green :
    cfg.S1 () .green_square utt_green > cfg.S1 () .green_square utt_square := by
  rsa_decide

/-- Speaker in blue_square world: "blue" and "square" are equally informative. -/
theorem s1_blue_square_equal :
    cfg.S1 () .blue_square utt_blue = cfg.S1 () .blue_square utt_square := by
  rsa_decide

-- ============================================================================
-- Structural Properties
-- ============================================================================

/-- "green" uniquely identifies green_square. -/
theorem green_unique_identifier :
    utt_green.appliesTo .green_square = true ∧
    utt_green.appliesTo .blue_square = false ∧
    utt_green.appliesTo .blue_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-- "circle" uniquely identifies blue_circle. -/
theorem circle_unique_identifier :
    utt_circle.appliesTo .blue_circle = true ∧
    utt_circle.appliesTo .blue_square = false ∧
    utt_circle.appliesTo .green_square = false :=
  ⟨rfl, rfl, rfl⟩

/-- "blue" applies to two objects (is ambiguous). -/
theorem blue_ambiguous :
    utt_blue.appliesTo .blue_square = true ∧
    utt_blue.appliesTo .blue_circle = true ∧
    utt_blue.appliesTo .green_square = false :=
  ⟨rfl, rfl, rfl⟩

/-- "square" applies to two objects (is ambiguous). -/
theorem square_ambiguous :
    utt_square.appliesTo .blue_square = true ∧
    utt_square.appliesTo .green_square = true ∧
    utt_square.appliesTo .blue_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-
## How RSA Derives the Reference Game Inference

1. **L0**: Literal listener
   - "square" → uniform over {blue_square, green_square}
   - "green" → only green_square

2. **S1**: Pragmatic speaker (score = L0^α)
   - In green_square world: L0(green_square|"green") = 1 > L0(green_square|"square") = 1/2
     Score: rpow(1, α) > rpow(1/2, α). Prefers "green"!
   - In blue_square world: L0(blue_square|"blue") = L0(blue_square|"square") = 1/2
     Equal scores. Indifferent.

3. **L1**: Pragmatic listener hearing "square"
   - Reasons: "If speaker meant green_square, they'd say 'green'"
   - Speaker said "square" → probably NOT green_square
   - Therefore: blue_square more likely than green_square

This is the core RSA insight: pragmatic listeners infer meaning by
reasoning about rational speaker behavior.
-/

end RSA.FrankGoodman2012
