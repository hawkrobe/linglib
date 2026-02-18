import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic

/-!
# RSA Embedded Scalar Implicatures: Simplified Model (For Analysis)

This file implements a **simplified** 2-lexicon model to analyze why minimal
Lexical Uncertainty models fail to derive embedded implicature patterns.

## Status

The ℚ-based RSA evaluation infrastructure (RSA.Eval, boolToRat, LURSA) has been
removed. Type definitions and the model limitation analysis are preserved.
RSA computations need to be re-implemented using the new RSAConfig framework.

## This File's Purpose

Demonstrates that a minimal 2-lexicon, 3-world model gives **inverted**
predictions, motivating the richer structure in the full model.

## References

- Potts, Lassiter, Levy & Frank (2016). Embedded implicatures as pragmatic
  inferences under compositional lexical uncertainty. Journal of Semantics.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Geurts, B. (2010). Quantity Implicatures.
-/

namespace RSA.EmbeddedScalars


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


/--
Utterances for DE context: "No one solved {some/all} problems"

We need scalar alternatives for RSA to reason about informativity.
-/
inductive DEUtterance where
  | noSome  -- "No one solved some of the problems"
  | noAll   -- "No one solved all of the problems" (scalar alternative)
  | null    -- Null/baseline utterance
  deriving DecidableEq, Repr, BEq, Inhabited


/-!
## The Lexical Uncertainty Model

Each lexicon L assigns meanings to "some":

- **L_base**: "some" = at-least-one (literal)
- **L_refined**: "some" = some-but-not-all (Neo-Gricean strengthened)

The listener reasons over which lexicon the speaker is using.
-/

/--
Base lexicon meaning: "some" = at-least-one

"No one solved some problems" under L_base:
- True only when nobody solved any problems
-/
def lexBaseMeaning : DEUtterance → EmbeddedWorld → Bool
  | .noSome, .none => true
  | .noSome, .someNotAll => false
  | .noSome, .someAll => false
  | .noAll, .none => true
  | .noAll, .someNotAll => true
  | .noAll, .someAll => false
  | .null, _ => true

/--
Refined lexicon meaning: "some" = some-but-not-all

"No one solved some problems" under L_refined:
- True when nobody solved "some-but-not-all"
- This is TRUE when someone solved ALL (they didn't solve "some-but-not-all")!
-/
def lexRefinedMeaning : DEUtterance → EmbeddedWorld → Bool
  | .noSome, .none => true
  | .noSome, .someNotAll => false
  | .noSome, .someAll => true     -- TRUE! Solver solved ALL
  | .noAll, .none => true
  | .noAll, .someNotAll => true
  | .noAll, .someAll => false
  | .null, _ => true


/-- Utterances for UE context -/
inductive UEUtterance where
  | someSome  -- "Someone solved some problems"
  | someAll   -- "Someone solved all problems" (scalar alternative)
  | null
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Base lexicon meaning for UE: "some" = at-least-one -/
def lexBaseUEMeaning : UEUtterance → EmbeddedWorld → Bool
  | .someSome, .none => false
  | .someSome, .someNotAll => true
  | .someSome, .someAll => true     -- True: someone solved ≥1
  | .someAll, .none => false
  | .someAll, .someNotAll => false
  | .someAll, .someAll => true
  | .null, _ => true

/-- Refined lexicon meaning for UE: "some" = some-but-not-all -/
def lexRefinedUEMeaning : UEUtterance → EmbeddedWorld → Bool
  | .someSome, .none => false
  | .someSome, .someNotAll => true
  | .someSome, .someAll => false    -- FALSE! Solved all, not "some-but-not-all"
  | .someAll, .none => false
  | .someAll, .someNotAll => false
  | .someAll, .someAll => true
  | .null, _ => true


/-!
## Analysis of Results

With α = 1 and uniform priors, the simplified 2-lexicon model gives INVERTED
predictions compared to the empirical pattern. This motivates the need for
richer model structure (Potts et al. 2016).

**DE Context** ("No one solved some"):
- The simple model predicts L_refined (local) wins -- WRONG

**UE Context** ("Someone solved some"):
- The simple model predicts L_base (global) wins -- WRONG

## Why This Happens

The key asymmetry is **world coverage**:

In DE:
- L_base: noSome true in {none} -- 1 world
- L_refined: noSome true in {none, someAll} -- 2 worlds

L_refined makes the utterance true in MORE worlds, so even though L_base
is more informative, L_refined gets extra probability mass.

## What Potts et al. Actually Does

The paper succeeds because of **richer model structure**:

1. **Multiple refinable items**: Not just "some", but also proper names,
   predicates like "scored" vs "aced" (equation 14)

2. **Richer world space**: 3 players × 3 outcomes = 10 equivalence classes

3. **Message alternatives**: Full cross-product of quantifiers and predicates

4. **Low λ = 0.1**: Speaker nearly uniform, so implicatures emerge from
   lexicon structure, not informativity
-/

end RSA.EmbeddedScalars
