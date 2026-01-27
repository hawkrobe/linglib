/-
# RSA Theory: Basic Definitions

The cookie domain for scalar implicature:
- 3 people at a party, question: "How many ate cookies?"
- Worlds: 0, 1, 2, or 3 people ate cookies
- Utterances: "none", "some", "all"

Literal semantics (weak "some"):
- "none" true iff 0 ate
- "some" true iff ≥1 ate (including all!)
- "all" true iff 3 ate

Reference: Goodman & Frank (2016)
-/

import Linglib.Core.RSA

namespace RSA.Scalar

-- ============================================================================
-- Worlds
-- ============================================================================

/-- How many (out of 3) ate cookies -/
inductive CookieWorld where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- Utterances
-- ============================================================================

/-- Scalar utterances -/
inductive ScalarUtterance where
  | none_ | some_ | all
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- Literal Semantics
-- ============================================================================

/-- Literal meaning (weak "some" = at least one) -/
def meaning : ScalarUtterance → CookieWorld → Bool
  | .none_, .w0 => true
  | .none_, _ => false
  | .some_, .w0 => false
  | .some_, _ => true   -- true for w1, w2, w3 (including "all"!)
  | .all, .w3 => true
  | .all, _ => false

-- ============================================================================
-- RSAScenario Instance (replaces FiniteSemanticBackend)
-- ============================================================================

def allUtterances : List ScalarUtterance := [.none_, .some_, .all]
def allWorlds : List CookieWorld := [.w0, .w1, .w2, .w3]

/-- The scalar RSA scenario for cookie domain -/
def scalarScenario : SimpleRSAScenario ScalarUtterance CookieWorld :=
  SimpleRSAScenario.ofBool allUtterances allWorlds (fun w u => meaning u w)

/-- Legacy alias for backward compatibility -/
abbrev scalarBackend := scalarScenario

-- ============================================================================
-- Key Property: "some" is compatible with "all"
-- ============================================================================

/-- "some" is literally true when all 3 ate -/
theorem some_compatible_with_all : meaning .some_ .w3 = true := rfl

end RSA.Scalar
