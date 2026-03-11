import Linglib.Core.Semantics.CommonGround

/-!
# Stalnaker's Common Ground Model of Assertion

@cite{stalnaker-1978} @cite{stalnaker-2002}Assertion as context set update: to assert p is to propose eliminating
¬p-worlds from the common ground. This is the simplest assertion theory
and the baseline against which richer theories are compared.

## Key Properties

- **No commitment/belief separation**: assertion IS adding to shared beliefs.
  There is no intermediate "commitment" stage.
- **No retraction**: the CG is monotonically updated (worlds are eliminated,
  never restored).
- **No source marking**: all CG updates are symmetric between participants.

## Stalnaker's Norm

@cite{stalnaker-1978} identifies three norms on assertion:
1. The proposition expressed is true (sincerity)
2. The speaker believes the proposition (knowledge)
3. The proposition is not already in the common ground (informativity)

This module models the EFFECT of assertion (CG update), not the norms.
The norms are relevant to Krifka's separation of commitment from belief.

-/

namespace Theories.Pragmatics.Assertion.Stalnaker

open Core.CommonGround (CG ContextSet)
open Core.Proposition (BProp)

-- ════════════════════════════════════════════════════
-- § 1. State = Common Ground
-- ════════════════════════════════════════════════════

/-- Stalnaker's discourse state IS the common ground.
    No separate commitment layer; assertion directly updates shared beliefs. -/
abbrev StalnakerState (W : Type*) := CG W

/-- Initial state: empty common ground (all worlds possible). -/
def initial {W : Type*} : StalnakerState W := CG.empty

/-- Assert p: add it to the common ground.
    This IS the full effect of assertion — no intermediate step. -/
def assert {W : Type*} (s : StalnakerState W) (p : BProp W) : StalnakerState W :=
  s.add p

/-- Context set: directly from CG. -/
def contextSet {W : Type*} (s : StalnakerState W) : ContextSet W :=
  s.contextSet

/-- Stalnaker states are always stable: there is no "table" or
    pending issue mechanism. Assertion is immediate. -/
def isStable {W : Type*} (_ : StalnakerState W) : Bool := true

-- ════════════════════════════════════════════════════
-- § 2. Verification
-- ════════════════════════════════════════════════════

/-- Empty CG gives trivial context set. -/
theorem initial_trivial {W : Type*} :
    contextSet (initial (W := W)) = ContextSet.trivial := CG.empty_contextSet

/-- Assertion restricts the context set. -/
theorem assert_restricts {W : Type*} (s : StalnakerState W) (p : BProp W) (w : W) :
    contextSet (assert s p) w → contextSet s w :=
  CG.add_restricts s p w

/-- Stalnaker states are always stable. -/
theorem always_stable {W : Type*} (s : StalnakerState W) : isStable s = true := rfl

end Theories.Pragmatics.Assertion.Stalnaker
