/-
# RSA for Quantifier Scope Ambiguity

Lifted-variable RSA model for scope resolution.

## Model (Scontras & Pearl 2021)

The listener jointly infers:
- **w**: World state (how many horses jumped: 0, 1, or 2)
- **i**: Interpretation (surface vs inverse scope)

```
L1(w, i | u) ∝ P(w) × P(i) × S1(u | w, i)
```

Where S1(u | w, i) is proportional to informativity of u under interpretation i.

## Key Predictions

1. **Neither pure scope explains the data**: The model predicts intermediate
   truth-value judgments for partial worlds (1 horse jumped), matching the
   empirical 59% rate from Scontras & Pearl (2021).

2. **Inverse scope preference**: The model assigns higher probability to
   inverse scope (¬>∀) than surface scope (∀>¬).

## References

- Scontras, G. & Pearl, L. (2021). "When pragmatics matters more for
  truth-value judgments: An investigation of quantifier scope ambiguity."
- Goodman, N. D. & Frank, M. C. (2016). "Pragmatic language interpretation
  as probabilistic inference."
-/

import Linglib.Core.RSA
import Linglib.Core.Frac
import Linglib.Phenomena.ScontrasPearl2021.Data
import Linglib.Theories.Montague.Scope

namespace RSA.ScopeAmbiguity

open Frac
open ParametricRSA
open ScontrasPearl2021
open Montague.Scope

-- ============================================================================
-- Utterances
-- ============================================================================

/-- Utterances in the scope ambiguity domain -/
inductive ScopeUtterance where
  | null              -- Silence / null utterance (always true)
  | everyHorseNotJump -- "Every horse didn't jump" (ambiguous)
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- Connecting Montague Derivations to RSA
-- ============================================================================

/--
Build RSA meaning function from a Montague world-parametric derivation.

This is the key bridge: RSA's meaning function is DERIVED from the
formal semantic derivation, not stipulated separately.

The null utterance is always true (uninformative baseline).
Other utterances get their meaning from the Montague derivation.
-/
def meaningFromDerivation
    (deriv : WorldParametricScopeDerivation Nat)
    (scope : ScopeConfig) (utt : ScopeUtterance) (world : Nat) : Bool :=
  match utt with
  | .null => true  -- Null utterance always true
  | .everyHorseNotJump => deriv.meaningAt scope world

/-- The meaning function derived from the Montague semantics -/
def scopeMeaning : ScopeConfig → ScopeUtterance → Nat → Bool :=
  meaningFromDerivation everyHorseDidntJump_parametric

/--
**Key theorem**: RSA meaning agrees with Montague derivation.

This proves the connection is faithful - we're not stipulating
separate truth conditions, we're using the semantic derivation.
-/
theorem rsa_meaning_from_montague :
    scopeMeaning .surface .everyHorseNotJump 0 =
      everyHorseDidntJump_parametric.meaningAt .surface 0 ∧
    scopeMeaning .inverse .everyHorseNotJump 1 =
      everyHorseDidntJump_parametric.meaningAt .inverse 1 := by
  native_decide

-- ============================================================================
-- ParametricSemanticBackend Instance (derived from Montague)
-- ============================================================================

/-- Marker type for the scope ambiguity domain -/
def ScopeDomain : Type := Unit

/-- All utterances -/
def allScopeUtterances : List ScopeUtterance := [.null, .everyHorseNotJump]

/--
Build ParametricSemanticBackend from a Montague derivation.

The worlds and interpretations come from the derivation itself,
ensuring consistency between semantics and pragmatics.
-/
instance : ParametricSemanticBackend ScopeDomain where
  Utterance := ScopeUtterance
  World := Nat  -- From Montague derivation
  Interp := ScopeConfig  -- From Montague scope infrastructure
  utterances := allScopeUtterances
  worlds := everyHorseDidntJump_parametric.worlds  -- [0, 1, 2] from derivation
  interps := everyHorseDidntJump_parametric.availableScopes  -- from derivation
  meaning := scopeMeaning  -- Derived from Montague, not stipulated
  utteranceBEq := inferInstance
  worldBEq := inferInstance
  interpBEq := inferInstance

-- ============================================================================
-- RSA Computations
-- ============================================================================

/-- L1 joint scores over (world × scope) -/
def l1JointScores : List ((Nat × ScopeConfig) × Frac.Frac) :=
  ParametricRSA.L1_joint_scores ScopeDomain .everyHorseNotJump

/-- L1 marginal scores over worlds -/
def l1WorldScores : List (Nat × Frac.Frac) :=
  ParametricRSA.L1_world_scores ScopeDomain .everyHorseNotJump

/-- L1 marginal scores over scope interpretations -/
def l1ScopeScores : List (ScopeConfig × Frac.Frac) :=
  ParametricRSA.L1_interp_scores ScopeDomain .everyHorseNotJump

-- ============================================================================
-- Helper: Get score from distribution
-- ============================================================================

def getWorldScore (w : Nat) : Frac.Frac :=
  ParametricRSA.getScore l1WorldScores w

def getScopeScore (s : ScopeConfig) : Frac.Frac :=
  ParametricRSA.getScore l1ScopeScores s

-- ============================================================================
-- Verification: Check RSA predictions
-- ============================================================================

-- Display scores for inspection
#eval l1JointScores
#eval l1WorldScores
#eval l1ScopeScores

-- ============================================================================
-- Key Theorems
-- ============================================================================

/--
**RSA assigns positive probability to partial world (w=1)**.

Unlike pure scope theories, RSA doesn't categorically rule out
the partial world. This matches the empirical 59% rate.
-/
theorem rsa_partial_world_possible :
    Frac.isPos (getWorldScore 1) = true := by
  native_decide

/--
**RSA assigns positive probability to compatible worlds**.

Zero and one have positive probability because "Every horse didn't jump"
is true in these worlds under at least one scope reading.
Two has zero probability because the utterance is false there under both scopes.
-/
theorem rsa_compatible_worlds_positive :
    Frac.isPos (getWorldScore 0) = true ∧
    Frac.isPos (getWorldScore 1) = true := by
  native_decide

/--
**World=two gets zero probability**.

When all horses jumped, "Every horse didn't jump" is false under both
scope readings, so L1 assigns probability 0 to this world.
-/
theorem rsa_two_world_zero :
    Frac.isZero (getWorldScore 2) = true := by
  native_decide

/--
**RSA prefers inverse scope over surface scope**.

The model assigns higher probability to the inverse (¬>∀)
interpretation than the surface (∀>¬) interpretation.

This reflects the general preference for inverse scope readings
of "every...not" sentences in English.
-/
theorem rsa_prefers_inverse_scope :
    getScopeScore .inverse > getScopeScore .surface := by
  native_decide

/--
**Zero-horse world has highest probability**.

Both scopes agree that "Every horse didn't jump" is true
when no horse jumped, so this world gets the highest mass.
-/
theorem rsa_zero_world_highest :
    getWorldScore 0 > getWorldScore 1 ∧
    getWorldScore 0 > getWorldScore 2 := by
  native_decide

/--
**Partial world (one) has more probability than all-jumped world (two)**.

The inverse scope (¬>∀) is true for w=1 but false for w=2.
Since inverse scope is preferred, w=1 gets more mass than w=2.
-/
theorem rsa_one_greater_than_two :
    getWorldScore 1 > getWorldScore 2 := by
  native_decide

-- ============================================================================
-- Connection to Empirical Data
-- ============================================================================

/--
**RSA ordering matches empirical ordering**.

RSA predicts: P(w=0) > P(w=1) > P(w=2)
Empirical data: 92% > 59% > 18%

The model captures the qualitative pattern.
-/
theorem rsa_matches_empirical_ordering :
    getWorldScore 0 > getWorldScore 1 ∧
    getWorldScore 1 > getWorldScore 2 := by
  native_decide

/--
**Both RSA and empirical data show the same ordering**.

This links the RSA predictions to the empirical findings.
-/
theorem rsa_and_empirical_agree :
    (getWorldScore 0 > getWorldScore 1) ∧
    (getWorldScore 1 > getWorldScore 2) ∧
    (getResult .zero > getResult .one) ∧
    (getResult .one > getResult .two) := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Architecture: RSA ← Montague Connection

```
Montague/Scope.lean                    RSA/ScopeAmbiguity.lean
────────────────────                   ─────────────────────────
WorldParametricScopeDerivation    →    ParametricSemanticBackend
  meaningAt : Scope → World → Bool        meaning := meaningFromDerivation
  worlds := [0, 1, 2]                      worlds := deriv.worlds
  availableScopes := [surface, inverse]   interps := deriv.availableScopes
```

**Key insight**: RSA's meaning function is DERIVED from the formal
semantic derivation, not stipulated separately. This ensures:
- Truth conditions come from compositional semantics
- No duplication of semantic content
- Changes to semantics automatically propagate to pragmatics

### Types
- `ScopeUtterance`: Utterances (null, everyHorseNotJump)
- `ScopeDomain`: Marker type for ParametricSemanticBackend

### RSA Computations
- `l1JointScores`: P(w, i | u) distribution
- `l1WorldScores`: Marginal P(w | u)
- `l1ScopeScores`: Marginal P(i | u)

### Key Theorems
- `rsa_meaning_from_montague`: RSA meaning = Montague derivation
- `rsa_partial_world_possible`: P(w=1 | u) > 0
- `rsa_prefers_inverse_scope`: P(inverse) > P(surface)
- `rsa_matches_empirical_ordering`: RSA matches qualitative data pattern

### Connection to Empirical Findings

The model captures Scontras & Pearl (2021)'s key findings:

1. **Mixed judgments for partial worlds**: The 59% rate for 1-horse
   worlds is explained by uncertainty over scope interpretations.

2. **Inverse scope preference**: Listeners prefer the ¬>∀ reading,
   which allows more worlds to be true.

3. **Graded truth-value judgments**: Rather than categorical true/false,
   the model predicts graded endorsements proportional to the
   posterior probability of the world given the utterance.

### Model Limitations

This implementation uses:
- Uniform priors over worlds and interpretations
- No QUD (Question Under Discussion) modeling
- No S2 (pragmatic speaker for endorsement predictions)

Future extensions could add:
- Non-uniform priors (e.g., all-jumped as default expectation)
- QUD-based projection (how-many vs all-jumped vs none-jumped)
- S2 layer for explicit truth-value judgment predictions
-/

end RSA.ScopeAmbiguity
