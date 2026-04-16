import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Core.Semantics.CommonGround
import Mathlib.Data.Rat.Defs

/-!
# @cite{lauer-2013}: Probabilistic Assertion

@cite{lauer-2013}

Models assertion as a speech act governed by probabilistic thresholds.
A proposition is assertable when the speaker's credence exceeds a
context-dependent threshold. This bridges traditional assertion
theories to RSA's probabilistic pragmatic reasoning.

## Key Properties

- **Credence function**: the speaker's subjective probability over
  worlds (rational-valued, matching RSA's `worldPrior`)
- **Assertability threshold**: a credence threshold above which
  assertion is licensed (matching RSA's `alpha` parameter)
- **Bridge to RSA**: Lauer's credence maps to RSA's `worldPrior`,
  and the threshold maps to the rationality parameter

## Relation to Other Theories

Lauer's model is closest to Stalnaker in structure (no explicit
commitment/belief separation), but adds a probabilistic dimension
that the CG model lacks. The threshold mechanism provides a
quantitative handle on hedging and commitment strength that
Krifka's ComP layer models categorically.

-/

namespace Pragmatics.Assertion.Lauer

open Core.Discourse.Commitment (CommitmentSlate)
open Core.CommonGround (ContextSet)
open Core.Proposition (BProp)

-- ════════════════════════════════════════════════════
-- § 1. Credence Functions
-- ════════════════════════════════════════════════════

/-- A credence function: the speaker's subjective probability
    assignment to propositions.

    Rational-valued (ℚ) for exact computation, matching RSA convention.
    The function takes a proposition and returns a probability in [0,1]. -/
structure Credence (W : Type*) where
  /-- Probability assignment for a proposition (given as a list of
      proposition-probability pairs). -/
  prob : List (BProp W × ℚ)
  /-- Default credence for propositions not in the list. -/
  defaultProb : ℚ := 1/2

namespace Credence

variable {W : Type*}

/-- Look up the credence for a proposition. -/
def lookup (c : Credence W) (p : BProp W) [BEq (BProp W)] : ℚ :=
  match c.prob.find? (λ ⟨q, _⟩ => q == p) with
  | some ⟨_, v⟩ => v
  | none => c.defaultProb

/-- Uninformative credence: equal probability for everything. -/
def uniform : Credence W := ⟨[], 1/2⟩

end Credence

-- ════════════════════════════════════════════════════
-- § 2. Lauer State
-- ════════════════════════════════════════════════════

/-- Lauer's discourse state: speaker credence + assertability threshold
    + history of assertions.

    The threshold is context-dependent: formal contexts (courtrooms)
    have higher thresholds than casual conversation. -/
structure LauerState (W : Type*) where
  /-- Speaker's credence function -/
  credence : Credence W
  /-- Assertability threshold (credence must exceed this) -/
  threshold : ℚ := 9/10
  /-- List of asserted propositions (for tracking) -/
  asserted : CommitmentSlate W

namespace LauerState

variable {W : Type*}

/-- Initial state: uniform credence, default threshold, no assertions. -/
def empty : LauerState W :=
  ⟨Credence.uniform, 9/10, CommitmentSlate.empty⟩

/-- Assert a proposition: add it to the asserted list.

    Assertability is a precondition (the speaker SHOULD have credence ≥
    threshold), but the operation succeeds regardless — modeling that
    assertion can occur even when the norm is violated (as in lying). -/
def assert (s : LauerState W) (p : BProp W) : LauerState W :=
  { s with asserted := s.asserted.add p }

/-- Check if a proposition is assertable (credence ≥ threshold). -/
def assertable (s : LauerState W) (p : BProp W) [BEq (BProp W)] : Bool :=
  s.credence.lookup p ≥ s.threshold

/-- Context set: worlds compatible with all asserted propositions. -/
def contextSet (s : LauerState W) : ContextSet W :=
  λ w => s.asserted.toContextSet w = true

/-- Stability: always stable (no table mechanism). -/
def isStable (_ : LauerState W) : Bool := true

end LauerState

-- ════════════════════════════════════════════════════
-- § 3. Bridge to RSA
-- ════════════════════════════════════════════════════

/-!
## RSA Correspondence

Lauer's probabilistic model maps naturally to RSA parameters:

| Lauer | RSA | Role |
|-------|-----|------|
| `credence` | `worldPrior` | probability over worlds |
| `threshold` | `alpha` | rationality / commitment level |
| `asserted` | utterance history | discourse context |

The mapping is conceptual, not formal: RSA's `worldPrior` is a
distribution over worlds (P(w)), while Lauer's credence is a
probability over propositions (P(p)). The connection is:

    P_Lauer(p) = Σ_{w: p(w)} P_RSA(w)

This lifts RSA's world-level prior to Lauer's proposition-level credence.
-/

/-- Lauer is always stable (no pending issues mechanism). -/
theorem always_stable {W : Type*} (s : LauerState W) :
    LauerState.isStable s = true := rfl

end Pragmatics.Assertion.Lauer
