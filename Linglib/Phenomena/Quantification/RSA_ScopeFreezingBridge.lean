import Linglib.Theories.Pragmatics.RSA.Implementations.ScopeFreezing
import Linglib.Phenomena.Quantification.Data

/-!
# Bridge: RSA Scope Freezing → Quantification Phenomena

Connects the RSA scope-freezing model to empirical scope availability data
from `Phenomena.Quantification.Data`. The RSA model provides `l1Interp` and
`getInverseProb`; this bridge file applies them to concrete freezing examples
(possessor baseline/frozen) and proves rescue/suppression predictions.
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

#eval baseline.observed  -- ambiguous
#eval frozen.observed    -- surfaceOnly

#eval getInverseProb uniformWorldPrior (interpPriorFromExample baseline)
#eval getInverseProb uniformWorldPrior (interpPriorFromExample frozen)
#eval getInverseProb rescueWorldPrior (interpPriorFromExample frozen)

/-- Baseline: inverse available -/
theorem baseline_inverse_available :
    getInverseProb uniformWorldPrior (interpPriorFromExample baseline) > 1/2 := by
  native_decide

/-- Frozen: grammar suppresses inverse -/
theorem frozen_suppresses_inverse :
    getInverseProb uniformWorldPrior (interpPriorFromExample frozen) < 1/10 := by
  native_decide

/-- Rescue: world prior overrides grammar (requires ε > 0 assumption) -/
theorem rsa_can_rescue_frozen :
    getInverseProb rescueWorldPrior (interpPriorFromExample frozen) > 1/2 := by
  native_decide

/-- With ε = 0 (grammar's view), rescue is impossible -/
def grammarInterpPrior : ScopeConfig → ℚ := interpPriorFromAvailability .surfaceOnly 0

theorem grammar_view_no_rescue :
    getInverseProb rescueWorldPrior grammarInterpPrior = 0 := by
  native_decide

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
