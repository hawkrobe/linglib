/-
# Frank & Goodman (2012)

"Predicting Pragmatic Reasoning in Language Games"
Science 336(6084): 998

This paper introduced the RSA (Rational Speech Acts) framework, showing that
pragmatic inferences in reference games can be predicted by modeling listeners
as reasoning about rational, informative speakers.

## The Reference Game

Context: {blue_square, blue_circle, green_square}
Utterances: {blue, green, square, circle}

## Key Result

L1("square") assigns higher probability to blue_square than green_square.

Why? A speaker wanting green_square would say "green" (uniquely identifying).
Saying "square" signals they probably mean blue_square.

## Montague Grounding

This implementation derives its meaning function from Montague compositional
semantics via `Montague.Core.Features`. Feature predicates like "blue" and
"square" have type `e → t` in Montague's type system, where:

- ⟦blue⟧ = λx. color(x) = blue
- ⟦square⟧ = λx. shape(x) = square

The RSA meaning function φ is derived from these Montague meanings, not stipulated.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Model
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Domains.ReferenceGames
import Mathlib.Data.Rat.Defs

namespace RSA.FrankGoodman2012

open RSA.Domains.ReferenceGame RSA.Eval

-- ============================================================================
-- Domain: Objects and Utterances (from Montague-grounded infrastructure)
-- ============================================================================

/-- Objects in the reference game context (Color × Shape pairs) -/
abbrev Object := RSA.Domains.ReferenceGame.Object

/-- The three objects in the classic Frank & Goodman context -/
def blue_square : Object := ⟨.blue, .square⟩
def blue_circle : Object := ⟨.blue, .circle⟩
def green_square : Object := ⟨.green, .square⟩

/-- Utterances are feature predicates (from Montague) -/
abbrev Utterance := RSA.Domains.ReferenceGame.Feature

/-- The four utterances in the classic context -/
def utt_blue : Utterance := .color .blue
def utt_green : Utterance := .color .green
def utt_square : Utterance := .shape .square
def utt_circle : Utterance := .shape .circle

-- ============================================================================
-- Literal Semantics (derived from Montague)
-- ============================================================================

/--
Literal meaning: does utterance apply to object?

This is derived from Montague's compositional semantics via `featureMeaning`,
not stipulated directly.
-/
def meaning (u : Utterance) (o : Object) : Bool :=
  u.appliesTo o

/-- Grounding theorem: meaning is derived from compositional semantics -/
theorem meaning_from_compositional (u : Utterance) (o : Object) :
    meaning u o = RSA.Domains.ReferenceGame.featureMeaning u o := rfl

-- ============================================================================
-- RSAScenario Instance (using unified API)
-- ============================================================================

/-- The classic Frank & Goodman context as a TypedContext -/
def classicContext : TypedContext :=
  fromPairs [(.blue, .square), (.blue, .circle), (.green, .square)]

/-- Run L0 for the classic reference game -/
def runL0 (u : Utterance) : List (Object × ℚ) :=
  classicContext.runL0 u

/-- Run S1 for the classic reference game -/
def runS1 (o : Object) : List (Utterance × ℚ) :=
  classicContext.runS1 o

/-- Run L1 for the classic reference game -/
def runL1 (u : Utterance) : List (Object × ℚ) :=
  classicContext.runL1 u

-- ============================================================================
-- Compute RSA Distributions
-- ============================================================================

/-- L0 for "blue" - uniform over blue objects -/
def l0_blue : List (Object × ℚ) := runL0 utt_blue

/-- L0 for "green" - only green_square -/
def l0_green : List (Object × ℚ) := runL0 utt_green

/-- L0 for "square" - uniform over squares -/
def l0_square : List (Object × ℚ) := runL0 utt_square

/-- S1 in blue_square world -/
def s1_blue_square : List (Utterance × ℚ) := runS1 blue_square

/-- S1 in green_square world -/
def s1_green_square : List (Utterance × ℚ) := runS1 green_square

/-- L1 for "square" - the key pragmatic inference -/
def l1_square : List (Object × ℚ) := runL1 utt_square

/-- L1 for "blue" -/
def l1_blue : List (Object × ℚ) := runL1 utt_blue

-- ============================================================================
-- Evaluate
-- ============================================================================

#eval l0_blue      -- L0("blue"): 1/2 each for blue_square, blue_circle
#eval l0_green     -- L0("green"): 1 for green_square
#eval l0_square    -- L0("square"): 1/2 each for blue_square, green_square

#eval s1_blue_square   -- S1(blue_square): blue and square both informative
#eval s1_green_square  -- S1(green_square): green preferred over square!

#eval l1_square    -- L1("square"): blue_square > green_square (the inference!)
#eval l1_blue      -- L1("blue"): should be roughly uniform over blue objects

-- ============================================================================
-- Main Theorems
-- ============================================================================

/--
**Reference Game Theorem**

L1("square") assigns higher probability to blue_square than green_square.

This captures the pragmatic inference: if speaker wanted green_square,
they would have said "green" (uniquely identifying). Saying "square"
signals they probably mean blue_square.
-/
theorem reference_game_inference :
    RSA.Eval.getScore l1_square blue_square > RSA.Eval.getScore l1_square green_square := by
  native_decide

/-- At literal level L0, squares are equally likely -/
theorem l0_squares_equal :
    RSA.Eval.getScore l0_square blue_square = RSA.Eval.getScore l0_square green_square := by
  native_decide

/-- Speaker in green_square world prefers "green" over "square" -/
theorem s1_green_prefers_green :
    RSA.Eval.getScore s1_green_square utt_green > RSA.Eval.getScore s1_green_square utt_square := by
  native_decide

/-- Speaker in blue_square world: "blue" and "square" are equally informative -/
theorem s1_blue_square_equal :
    RSA.Eval.getScore s1_blue_square utt_blue = RSA.Eval.getScore s1_blue_square utt_square := by
  native_decide

-- ============================================================================
-- Additional: Unique Reference
-- ============================================================================

/-- "green" uniquely identifies green_square at L0 -/
theorem green_unique :
    (RSA.Eval.getScore l0_green green_square).num > 0 ∧
    (RSA.Eval.getScore l0_green blue_square).num = 0 ∧
    (RSA.Eval.getScore l0_green blue_circle).num = 0 := by
  native_decide

/-- "circle" uniquely identifies blue_circle at L0 -/
theorem circle_unique :
    (RSA.Eval.getScore (runL0 utt_circle) blue_circle).num > 0 ∧
    (RSA.Eval.getScore (runL0 utt_circle) blue_square).num = 0 := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## How RSA Derives the Reference Game Inference

1. **L0**: Literal listener
   - "square" → uniform over {blue_square, green_square}
   - "green" → only green_square

2. **S1**: Pragmatic speaker
   - In green_square world: "green" is maximally informative (1 referent)
     while "square" is less informative (2 referents). Prefers "green"!
   - In blue_square world: "blue" and "square" equally informative (2 each)

3. **L1**: Pragmatic listener hearing "square"
   - Reasons: "If speaker meant green_square, they'd say 'green'"
   - Speaker said "square" → probably NOT green_square
   - Therefore: blue_square more likely than green_square

This is the core RSA insight: pragmatic listeners infer meaning by
reasoning about rational speaker behavior.
-/

-- ============================================================================
-- Fintype-Based API (RSAScenario / RSA)
-- ============================================================================

/-!
## Fintype-Based RSA

The following demonstrates the new `RSAScenario` / `RSA` API which provides:
- Compile-time type safety via Fintype constraints
- Direct use of ExactDist for proper probability distributions
- No explicit List enumerations (derived from Fintype instances)
-/

/-- Reference game scenario using Fintype-based API -/
def refGameScenarioF : RSAScenario :=
  RSAScenario.basicBool
    (U := Feature)  -- Utterances are features
    (W := Object)   -- Worlds are objects
    (satisfies := fun o u => u.appliesTo o)  -- Satisfies relation from Montague
    (prior := fun _ => 1)
    (prior_nonneg := fun _ => le_refl 0 |> fun _ => by norm_num)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)
    (utterancePrior := fun _ => 1)
    (utterancePrior_nonneg := fun _ => le_refl 0 |> fun _ => by norm_num)

-- ============================================================================
-- RSAModel Instance: Convergence Guarantees
-- ============================================================================

/-!
## Zaslavsky et al. (2020) Convergence Guarantees

By converting `refGameScenarioF` to an `RSAModel` instance, we automatically
inherit the convergence and monotonicity theorems from Zaslavsky et al. (2020).

This demonstrates the architecture: prove theorems once for the abstract
`RSAModel` interface, then any concrete scenario gets them for free.
-/

/--
RSAModel instance for the Frank & Goodman reference game.

This enables:
- `G_α_monotone_generic`: G_α is monotonically non-decreasing
- `RSA_converges_generic`: RSA dynamics converge to a fixed point
- `eventually_εConverged_generic`: Can stop RSA recursion at finite depth

Note: We use the concrete Utterance type here since refGameScenarioF.Utterance
is definitionally equal to Feature (from RSAScenario.basicBool).
-/
noncomputable instance refGameModel : RSAModel Feature :=
  @RSAScenario.toModel refGameScenarioF
    (inferInstance : Fintype Feature)  -- Feature has Fintype
    (inferInstance : Fintype Object)      -- World = Object has Fintype
    ()  -- default Interp
    ()  -- default Lexicon

/-!
With this instance, the following theorems apply automatically:

```lean
-- G_α monotonicity for Frank & Goodman scenario
#check @G_α_monotone_generic Feature refGameModel

-- RSA convergence for Frank & Goodman scenario
#check @RSA_converges_generic Feature refGameModel
```

These theorems say:
1. **Monotonicity**: Each RSA iteration improves the objective G_α
2. **Convergence**: The RSA dynamics converge to a fixed point
3. **ε-Convergence**: We can stop at finite depth with bounded error

This justifies using L1 or S1 approximations instead of computing
the full infinite recursion L∞ / S∞.
-/

-- Compute distributions using RSAF

/-- L0 for "square" using Fintype API -/
def l0_square_F : Option (ExactDist Object) :=
  RSA.L0 refGameScenarioF utt_square () () () ()

/-- S1 in blue_square world using Fintype API -/
def s1_blue_square_F : Option (ExactDist Feature) :=
  RSA.S1 refGameScenarioF blue_square () () () ()

/-- L1 for "square" using Fintype API -/
def l1_square_F : Option (ExactDist Object) :=
  RSA.L1_world refGameScenarioF utt_square

-- Evaluate (compare with List-based versions above)
-- Note: Currently disabled due to sorry axioms in RSAF non-negativity proofs

-- #eval l0_square_F.map (fun d => (d.mass blue_square, d.mass green_square))
-- Should be (1/2, 1/2) - uniform over squares

-- #eval l1_square_F.map (fun d => (d.mass blue_square, d.mass green_square))
-- Should show blue_square > green_square (the pragmatic inference!)

/--
**Reference Game Theorem (Fintype version)**

Using ExactDist, we can directly compare probabilities.
-/
theorem reference_game_inference_F :
    ∀ d, l1_square_F = some d →
    d.mass blue_square > d.mass green_square := by
  intro d hd
  sorry  -- TODO: prove once sorries in RSAF are filled

end RSA.FrankGoodman2012
