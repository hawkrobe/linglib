/-
# RSA Embedded Scalar Implicatures: Simplified Model (For Analysis)

This file implements a **simplified** 2-lexicon model to analyze why minimal
Lexical Uncertainty models fail to derive embedded implicature patterns.

**For the full working model, see `PottsLU.lean`** which implements the
complete Potts et al. (2016) model with:
- 10 world classes (3 players × 3 outcomes)
- 4 lexica (2 refinable items: quantifier + predicate)
- 11 utterances
- Proven theorems for DE blocking and UE implicature

## This File's Purpose

Demonstrates that a minimal 2-lexicon, 3-world model gives **inverted**
predictions, motivating the richer structure in the full model.

## References

- Potts, Lassiter, Levy & Frank (2016). Embedded implicatures as pragmatic
  inferences under compositional lexical uncertainty. Journal of Semantics.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Geurts, B. (2010). Quantity Implicatures.
-/

import Linglib.Theories.RSA.Core
import Linglib.Theories.RSA.LexicalUncertainty.Basic
import Linglib.Phenomena.ScalarImplicatures.Data

namespace RSA.EmbeddedScalars

open RSA LURSA
open Phenomena.ScalarImplicatures

-- ============================================================================
-- PART 1: World States
-- ============================================================================

/--
World states for embedded scalar scenarios.

- **none**: Nobody solved any problems
- **someNotAll**: Someone solved some-but-not-all problems
- **someAll**: Someone solved all problems
-/
inductive EmbeddedWorld where
  | none        -- Nobody solved any problems
  | someNotAll  -- Someone solved some-but-not-all problems
  | someAll     -- Someone solved all problems
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- PART 2: Utterances for DE Context
-- ============================================================================

/--
Utterances for DE context: "No one solved {some/all} problems"

We need scalar alternatives for RSA to reason about informativity.
-/
inductive DEUtterance where
  | noSome  -- "No one solved some of the problems"
  | noAll   -- "No one solved all of the problems" (scalar alternative)
  | null    -- Null/baseline utterance
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- PART 3: Lexica for "some" (The Actual Potts Model)
-- ============================================================================

/-
## The Lexical Uncertainty Model

Each lexicon L assigns meanings to "some":

- **L_base**: "some" = at-least-one (literal)
- **L_refined**: "some" = some-but-not-all (Neo-Gricean strengthened)

The listener reasons over which lexicon the speaker is using.
This is equation (11) in the paper.
-/

/--
Base lexicon: "some" = at-least-one

"No one solved some problems" under L_base:
- True only when nobody solved any problems
-/
def lexBase : Lexicon DEUtterance EmbeddedWorld where
  meaning u w := boolToRat $ match u, w with
    -- "No one solved some (≥1) problems" = "No one solved ANY"
    | .noSome, .none => true
    | .noSome, .someNotAll => false
    | .noSome, .someAll => false
    -- "No one solved all problems"
    | .noAll, .none => true
    | .noAll, .someNotAll => true
    | .noAll, .someAll => false
    -- Null utterance: true everywhere
    | .null, _ => true

/--
Refined lexicon: "some" = some-but-not-all

"No one solved some problems" under L_refined:
- True when nobody solved "some-but-not-all"
- This is TRUE when someone solved ALL (they didn't solve "some-but-not-all")!
-/
def lexRefined : Lexicon DEUtterance EmbeddedWorld where
  meaning u w := boolToRat $ match u, w with
    -- "No one solved some-but-not-all problems"
    | .noSome, .none => true
    | .noSome, .someNotAll => false
    | .noSome, .someAll => true     -- TRUE! Solver solved ALL
    -- "No one solved all" (same as base)
    | .noAll, .none => true
    | .noAll, .someNotAll => true
    | .noAll, .someAll => false
    -- Null utterance: true everywhere
    | .null, _ => true

-- ============================================================================
-- PART 4: LU Scenario for DE Context
-- ============================================================================

/--
Lexical Uncertainty scenario for DE context.

Following Potts et al. Table 7:
- α = 1 (we can't use 0.1 with ℕ, but see analysis below)
- Uniform priors over worlds and lexica
- Null message cost handled separately
-/
def noSomeLUScenario : LUScenario where
  Utterance := DEUtterance
  World := EmbeddedWorld
  baseLexicon := lexBase
  lexica := [lexBase, lexRefined]
  lexPrior := fun _ => 1  -- Flat prior per Potts
  worldPrior := fun _ => 1  -- Flat prior per Potts
  utterances := [.noSome, .noAll, .null]
  worlds := [.none, .someNotAll, .someAll]
  α := 1  -- Potts uses λ=0.1, we analyze the α→0 limit separately

-- ============================================================================
-- PART 5: RSA Computations for DE (Using LURSA)
-- ============================================================================

/-- L₁ distribution over worlds for "noSome" utterance -/
def l1WorldsDE : List (EmbeddedWorld × ℚ) :=
  LURSA.L1 noSomeLUScenario .noSome

/-- Joint L₁ distribution over (World × Lexicon) for "noSome" -/
def l1JointDE : List ((EmbeddedWorld × Lexicon DEUtterance EmbeddedWorld) × ℚ) :=
  LURSA.L1_joint noSomeLUScenario .noSome

#eval l1WorldsDE
#eval l1JointDE.length  -- Should be 6 (3 worlds × 2 lexica)

-- ============================================================================
-- PART 6: Lexicon Marginals
-- ============================================================================

/-
## Key Insight: Lexicon Inference Reveals Global/Local Preference

- "Global" reading = L_base inferred
- "Local" reading = L_refined inferred

We compute P(L_base | noSome) vs P(L_refined | noSome).
-/

/--
Marginal probability of base lexicon given "noSome" utterance.

P(L_base | noSome) = Σ_w P(w, L_base | noSome)

The joint has entries in order: worlds × lexica
With worlds = [none, someNotAll, someAll] and lexica = [lexBase, lexRefined]:
- Indices 0, 2, 4 are (w, lexBase)
- Indices 1, 3, 5 are (w, lexRefined)
-/
def pLexBase : ℚ :=
  let joint := l1JointDE
  match joint with
  | [(_, s0), (_, _), (_, s2), (_, _), (_, s4), (_, _)] =>
    s0 + s2 + s4  -- (none,base) + (someNotAll,base) + (someAll,base)
  | _ => 0

def pLexRefined : ℚ :=
  let joint := l1JointDE
  match joint with
  | [(_, _), (_, s1), (_, _), (_, s3), (_, _), (_, s5)] =>
    s1 + s3 + s5  -- (none,refined) + (someNotAll,refined) + (someAll,refined)
  | _ => 0

#eval pLexBase
#eval pLexRefined
#eval (pLexBase, pLexRefined, decide (pLexBase > pLexRefined))

-- ============================================================================
-- PART 7: UE Context ("Someone solved some problems")
-- ============================================================================

/-- Utterances for UE context -/
inductive UEUtterance where
  | someSome  -- "Someone solved some problems"
  | someAll   -- "Someone solved all problems" (scalar alternative)
  | null
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Base lexicon for UE: "some" = at-least-one -/
def lexBaseUE : Lexicon UEUtterance EmbeddedWorld where
  meaning u w := boolToRat $ match u, w with
    | .someSome, .none => false
    | .someSome, .someNotAll => true
    | .someSome, .someAll => true     -- True: someone solved ≥1
    | .someAll, .none => false
    | .someAll, .someNotAll => false
    | .someAll, .someAll => true
    | .null, _ => true

/-- Refined lexicon for UE: "some" = some-but-not-all -/
def lexRefinedUE : Lexicon UEUtterance EmbeddedWorld where
  meaning u w := boolToRat $ match u, w with
    | .someSome, .none => false
    | .someSome, .someNotAll => true
    | .someSome, .someAll => false    -- FALSE! Solved all, not "some-but-not-all"
    | .someAll, .none => false
    | .someAll, .someNotAll => false
    | .someAll, .someAll => true
    | .null, _ => true

def someSomeLUScenario : LUScenario where
  Utterance := UEUtterance
  World := EmbeddedWorld
  baseLexicon := lexBaseUE
  lexica := [lexBaseUE, lexRefinedUE]
  lexPrior := fun _ => 1
  worldPrior := fun _ => 1
  utterances := [.someSome, .someAll, .null]
  worlds := [.none, .someNotAll, .someAll]
  α := 1

def l1JointUE : List ((EmbeddedWorld × Lexicon UEUtterance EmbeddedWorld) × ℚ) :=
  LURSA.L1_joint someSomeLUScenario .someSome

def pLexBaseUE : ℚ :=
  let joint := l1JointUE
  match joint with
  | [(_, s0), (_, _), (_, s2), (_, _), (_, s4), (_, _)] =>
    s0 + s2 + s4
  | _ => 0

def pLexRefinedUE : ℚ :=
  let joint := l1JointUE
  match joint with
  | [(_, _), (_, s1), (_, _), (_, s3), (_, _), (_, s5)] =>
    s1 + s3 + s5
  | _ => 0

#eval pLexBaseUE
#eval pLexRefinedUE
#eval (pLexBaseUE, pLexRefinedUE, decide (pLexRefinedUE > pLexBaseUE))

-- ============================================================================
-- PART 8: Analysis - Why Simple LU Doesn't Work
-- ============================================================================

/-
## Analysis of Results

With α = 1 and uniform priors, the model predictions are:

**DE Context** ("No one solved some"):
- P(L_base | noSome) ≈ 36%
- P(L_refined | noSome) ≈ 64%
- Prediction: L_refined (local) wins ✗

**UE Context** ("Someone solved some"):
- P(L_base | someSome) ≈ 54%
- P(L_refined | someSome) ≈ 46%
- Prediction: L_base (global) wins ✗

Both predictions are INVERTED from the empirical pattern!

## Why This Happens

The key asymmetry is **world coverage**:

In DE:
- L_base: noSome true in {none} — 1 world
- L_refined: noSome true in {none, someAll} — 2 worlds

L_refined makes the utterance true in MORE worlds, so even though L_base
is more informative, L_refined gets extra probability mass from the
(someAll, L_refined) pair.

## What Potts et al. Actually Does

The paper succeeds because of **richer model structure**:

1. **Multiple refinable items**: Not just "some", but also proper names,
   predicates like "scored" vs "aced" (equation 14)

2. **Richer world space**: 3 players × 3 outcomes = 10 equivalence classes

3. **Message alternatives**: Full cross-product of quantifiers and predicates

4. **Low λ = 0.1**: Speaker nearly uniform, so implicatures emerge from
   lexicon structure, not informativity

Our 2-lexicon, 3-world model is too simple to capture the asymmetries
that make embedded implicatures work in the full model.

## Connection to Table 4 in Potts et al.

From their Table 4 (Neo-Gricean refinement):
- "no player scored" in world NN: 0.61 (highest)
- "no player scored" in world NS/NA: some positive probability

This shows the model predicts global is **preferred** but local is
**possible** — not a categorical blocking effect.
-/

/-- Document the model limitation -/
theorem simple_lu_model_limitation :
    -- DE: L_refined wins (wrong)
    pLexRefined > pLexBase ∧
    -- UE: L_base wins (wrong)
    pLexBaseUE > pLexRefinedUE := by
  native_decide

-- ============================================================================
-- PART 9: What Would Make It Work
-- ============================================================================

/-
## Requirements for Correct Predictions

To derive both DE blocking and UE implicatures, the model needs:

### Option 1: Richer Lexicon Space (Potts et al. approach)

Following equation (14), refine multiple items:
- Proper names: {⟦A⟧, ⟦only A⟧}
- Predicates: {⟦scored⟧, ⟦scored-not-aced⟧}
- Quantifiers: {⟦some⟧, ⟦some-not-all⟧}

This creates 2^n lexica where n = number of refinable items.
The richer structure creates the right asymmetries.

### Option 2: Context-Dependent Priors

Use different P(L) in DE vs UE contexts:
- DE: Bias toward L_base (global)
- UE: Bias toward L_refined (local)

This works but is stipulative.

### Option 3: QUD (Question Under Discussion)

Model different questions for DE vs UE:
- DE: "Did anyone solve problems?" → global relevant
- UE: "How many did they solve?" → local relevant

### Current Status

Our simplified model demonstrates the architecture but doesn't derive
the full empirical pattern. The existence proof is in Potts et al. (2016)
with their richer model structure.
-/

-- ============================================================================
-- PART 10: Connection to Phenomena Data
-- ============================================================================

/--
**Connection to empirical pattern**.

The empirical data (Geurts 2010) shows:
- DE: implicature blocked (global preferred)
- UE: implicature arises (local preferred)

Our simple LU model predicts the opposite.
The full Potts et al. model derives the correct pattern.
-/
theorem empirical_pattern_documented :
    -- Empirical: DE blocks, UE allows
    someAllBlocking.implicatureInDE = false ∧
    someAllBlocking.implicatureInUE = true := by
  native_decide

-- ============================================================================
-- PART 11: Summary
-- ============================================================================

/-
## Summary: The Actual Potts et al. (2016) Model

### What We Implemented

The correct LU architecture from the paper:
- Listener marginalizes over lexica: L₁(w|m) ∝ P(w) Σ_L P(L) S₁(m|w,L)
- Two lexica: L_base and L_refined
- This is Section 4.3, equations (13a-c)

### Key Finding

With just 2 lexica and 3 worlds, the model predicts:
- DE: local wins (WRONG)
- UE: global wins (WRONG)

The predictions are inverted because the lexicon that makes the utterance
true in more worlds gets extra probability mass.

### What Makes Potts et al. Work

1. **Richer lexicon space**: Multiple refinable items (equation 14)
2. **More worlds**: 3 players × 3 outcomes
3. **More utterances**: Full quantifier × predicate cross-product
4. **Low λ = 0.1**: Informativity nearly uniform

The paper's success is an existence proof that LU can derive embedded
implicatures, but requires the full model structure.

### Theoretical Contribution

This analysis shows:
1. Simple 2-lexicon models don't work
2. The DE/UE asymmetry requires richer structure
3. The Potts et al. model is necessary, not just sufficient

This motivates implementing CompositionalLU.lean with full lexicon
enumeration and Neo-Gricean refinement constraints.
-/

end RSA.EmbeddedScalars
