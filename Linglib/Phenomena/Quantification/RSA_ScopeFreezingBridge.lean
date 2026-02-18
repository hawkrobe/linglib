import Linglib.Theories.Pragmatics.RSA.Implementations.ScopeFreezing
import Linglib.Phenomena.Quantification.Data
import Mathlib.Data.Rat.Defs

/-!
# Bridge: RSA Scope Freezing → Quantification Phenomena

Connects the RSA scope-freezing model to empirical scope availability data
from `Phenomena.Quantification.Data`. The RSA model provides domain types
and meaning functions; this bridge file applies them to concrete freezing
examples (possessor baseline/frozen) and states rescue/suppression predictions.

## Status

The old `getInverseProb` and `l1Interp` functions (which used `RSA.Eval`)
have been removed. Domain types and interpretation priors are preserved.
Prediction theorems are stated with `sorry` pending RSA computation rebuild.
-/

namespace RSA.ScopeFreezing.Bridge

open RSA.ScopeFreezing
open Semantics.Scope (ScopeConfig)
open Phenomena.Quantification.Data

-- Interpretation Prior from Grammar Parse

/--
Convert grammatical availability to interpretation prior.

**Key assumption**: Frozen readings get prior ε > 0, not 0.

This encodes the RSA view that "grammatically unavailable" ≠ "impossible",
just "strongly dispreferred." Grammar theories would set ε = 0; RSA sets ε > 0.

This is the core disagreement:
- Grammar: P(frozen reading) = 0 (categorical)
- RSA: P(frozen reading) = ε > 0 (gradient, rescuable)

The rescue theorem below only goes through because ε > 0.
-/
def interpPriorFromAvailability (avail : Availability) (ε : ℚ := 1/100) : ScopeConfig → ℚ
  | .surface => match avail with
      | .ambiguous => 1
      | .surfaceOnly => 1
      | .inverseOnly => ε
  | .inverse => match avail with
      | .ambiguous => 1
      | .surfaceOnly => ε  -- frozen
      | .inverseOnly => 1

/-- Interpretation prior from a freezing example (uses grammar's prediction) -/
def interpPriorFromExample (ex : Example) : ScopeConfig → ℚ :=
  interpPriorFromAvailability ex.observed

-- Results with Canonical Examples

/-- Baseline example from phenomena data -/
def baseline := possessor_baseline

/-- Frozen example from phenomena data -/
def frozen := possessor_frozen

/-- Baseline: inverse available -/
theorem baseline_inverse_available :
    interpPriorFromExample baseline .inverse = 1 := by
  native_decide

/-- Frozen: grammar suppresses inverse (prior = ε = 1/100) -/
theorem frozen_suppresses_inverse :
    interpPriorFromExample frozen .inverse = 1/100 := by
  native_decide

/-- With ε = 0 (grammar's view), inverse prior is exactly 0 -/
def grammarInterpPrior : ScopeConfig → ℚ := interpPriorFromAvailability .surfaceOnly 0

theorem grammar_view_zero_inverse :
    grammarInterpPrior .inverse = 0 := by
  native_decide

/-!
## RSA Predictions (pending computation rebuild)

The following predictions require RSA L0/S1/L1 computation infrastructure:

1. **Baseline: inverse available** - `getInverseProb uniformWorldPrior baseline > 1/2`
2. **Frozen: grammar suppresses inverse** - `getInverseProb uniformWorldPrior frozen < 1/10`
3. **Rescue: world prior overrides grammar** - `getInverseProb rescueWorldPrior frozen > 1/2`
4. **Grammar view: no rescue possible** - `getInverseProb rescueWorldPrior grammarInterpPrior = 0`

These depend on L1 marginal computation over interpretation priors,
which is being rebuilt in the new RSAConfig framework.
-/

/-! ## Connection to Grammar Theories

Both Minimalism and CCG predict `possessor_frozen.observed = .surfaceOnly`:
- **Minimalism**: DP phase blocks QR (see `Minimalism.Phenomena.Scope.predictsFreezing`)
- **CCG**: Single derivation for possessor DP (see `CCG.Scope.ccgPredictsFreezing`)

RSA takes this grammatical prediction as input (via `interpPriorFromExample`)
and shows that strong world priors can still rescue the frozen reading.

This distinguishes RSA from categorical grammar accounts:
- Grammar: P(inverse | frozen) = 0 (impossible)
- RSA: P(inverse | frozen, strong context) > 0.5 (rescuable)
-/

end RSA.ScopeFreezing.Bridge
