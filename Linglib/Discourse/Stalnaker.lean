import Linglib.Discourse.CommonGround

/-!
# Stalnaker's Common Ground Model of Assertion

[stalnaker-1978] [stalnaker-2002]Assertion as context set update: to assert p is to propose eliminating
¬p-worlds from the common ground. This is the simplest assertion theory
and the baseline against which richer theories are compared.

## Key Properties

- **No commitment/belief separation**: assertion IS adding to shared beliefs.
  There is no intermediate "commitment" stage.
- **No retraction**: the CommonGround is monotonically updated (worlds are eliminated,
  never restored).
- **No source marking**: all CommonGround updates are symmetric between participants.

## Stalnaker's Norm

[stalnaker-1978] identifies three norms on assertion:
1. The proposition expressed is true (sincerity)
2. The speaker believes the proposition (knowledge)
3. The proposition is not already in the common ground (informativity)

This module models the EFFECT of assertion (CommonGround update), not the norms.
The norms are relevant to Krifka's separation of commitment from belief.

-/

namespace Discourse.Stalnaker

open CommonGround (ContextSet)

-- ════════════════════════════════════════════════════
-- § 1. State = Common Ground
-- ════════════════════════════════════════════════════

/-- Stalnaker's discourse state IS the common ground.
    No separate commitment layer; assertion directly updates shared beliefs. -/
abbrev StalnakerState (W : Type*) := CommonGround W

/-- Initial state: empty common ground (all worlds possible). -/
def initial {W : Type*} : StalnakerState W := CommonGround.empty

/-- Assert p: add it to the common ground.
    This IS the full effect of assertion — no intermediate step. -/
def assert {W : Type*} (s : StalnakerState W) (p : Set W) : StalnakerState W :=
  s.add p

/-- Context set: directly from CommonGround. -/
def contextSet {W : Type*} (s : StalnakerState W) : ContextSet W :=
  s.contextSet

/-- Stalnaker states are always stable: there is no "table" or
    pending issue mechanism. Assertion is immediate. -/
def isStable {W : Type*} (_ : StalnakerState W) : Prop := True

instance {W : Type*} (s : StalnakerState W) : Decidable (isStable s) :=
  inferInstanceAs (Decidable True)

-- ════════════════════════════════════════════════════
-- § 2. Verification
-- ════════════════════════════════════════════════════

/-- Empty CommonGround gives trivial context set. -/
theorem initial_trivial {W : Type*} :
    contextSet (initial (W := W)) = ContextSet.trivial := CommonGround.empty_contextSet

/-- Assertion restricts the context set. -/
theorem assert_restricts {W : Type*} (s : StalnakerState W) (p : Set W) :
    contextSet (assert s p) ⊆ contextSet s :=
  CommonGround.add_restricts s p

/-- Stalnaker states are always stable. -/
theorem always_stable {W : Type*} (s : StalnakerState W) : isStable s := trivial

-- ════════════════════════════════════════════════════
-- HasContextSet (re-export via abbrev)
-- ════════════════════════════════════════════════════

/-- Theorem (not instance — the `CommonGround W` instance from `CommonGround`
    already resolves through the `StalnakerState W := CommonGround W` abbrev): the
    `HasContextSet` projection on a Stalnaker state agrees with the
    local `Stalnaker.contextSet` def. Documents the bridge for grep. -/
theorem hasContextSet_eq_contextSet {W : Type*} (s : StalnakerState W) :
    CommonGround.HasContextSet.toContextSet s = Stalnaker.contextSet s := rfl

/-- Theorem (not instance — the `CommonGround W` instance of
    `CommonGround.HasAssertion` already resolves through the
    `StalnakerState W := CommonGround W` abbrev): the `HasAssertion`
    assertion on a Stalnaker state is the local `Stalnaker.assert`.
    Documents the bridge for grep. -/
theorem hasAssertion_eq_assert {W : Type*} (s : StalnakerState W) (p : Set W) :
    CommonGround.HasAssertion.assert s p = Stalnaker.assert s p := rfl

end Discourse.Stalnaker
