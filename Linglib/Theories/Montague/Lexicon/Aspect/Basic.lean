/-
# Aspectual Categories

Core types for aspectual classification following Vendler (1957) and subsequent work.

## Key Distinctions

1. **Telicity**: Does the event have a natural endpoint?
   - Telic: arrive, build, recognize (has endpoint)
   - Atelic: run, swim, love (no endpoint)

2. **Duration**: Does the event take time?
   - Durative: run, build, love (takes time)
   - Punctual: recognize, arrive, die (instantaneous)

3. **Dynamicity**: Does the event involve change?
   - Dynamic: run, build, die (involves change)
   - Stative: know, love, own (no change)

## Vendler Classification

| Class         | Telic? | Duration? | Dynamic? | Example          |
|---------------|--------|-----------|----------|------------------|
| State         | —      | durative  | stative  | know, love, own  |
| Activity      | atelic | durative  | dynamic  | run, swim, push  |
| Achievement   | telic  | punctual  | dynamic  | recognize, die   |
| Accomplishment| telic  | durative  | dynamic  | build, write     |

## References

- Vendler, Z. (1957). Verbs and times. *Philosophical Review* 66(2).
- Dowty, D. (1979). *Word Meaning and Montague Grammar*.
- Smith, C. (1991). *The Parameter of Aspect*.
-/

namespace Montague.Lexicon.Aspect

-- ============================================================================
-- Core Aspectual Features
-- ============================================================================

/--
Telicity: whether an event has a natural endpoint.

- **Telic**: Has a natural endpoint; the event culminates.
  Examples: arrive, build a house, recognize, die
  Test: "in an hour" ✓ ("built the house in an hour")

- **Atelic**: No natural endpoint; the event can continue indefinitely.
  Examples: run, swim, love, push the cart
  Test: "for an hour" ✓ ("ran for an hour")
-/
inductive Telicity where
  | telic   -- has natural endpoint (stop, build, arrive)
  | atelic  -- no natural endpoint (run, swim, love)
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Duration: whether an event takes time or is instantaneous.

- **Durative**: The event takes time to unfold.
  Examples: run, build, love, sleep

- **Punctual**: The event is instantaneous (or nearly so).
  Examples: recognize, arrive, die, find
-/
inductive Duration where
  | durative  -- takes time (run, build, love)
  | punctual  -- instantaneous (recognize, arrive, die)
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Dynamicity: whether the event involves change.

- **Dynamic**: The event involves change or action.
  Examples: run, build, die, arrive

- **Stative**: The event is a state with no change.
  Examples: know, love, own, be tall
-/
inductive Dynamicity where
  | dynamic  -- involves change (run, build, die)
  | stative  -- no change (know, love, own)
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- Vendler Classification
-- ============================================================================

/--
Vendler's four-way classification of eventualities.

This is the classic typology from Vendler (1957), refined by Dowty (1979):

- **State**: No change, durative. ("John knows French")
- **Activity**: Change, durative, no endpoint. ("John ran")
- **Achievement**: Change, punctual, has endpoint. ("John recognized Mary")
- **Accomplishment**: Change, durative, has endpoint. ("John built a house")
-/
inductive VendlerClass where
  | state         -- [-dynamic, +durative]  know, love
  | activity      -- [+dynamic, +durative, -telic]  run, swim
  | achievement   -- [+dynamic, -durative, +telic]  recognize, die
  | accomplishment -- [+dynamic, +durative, +telic]  build, write
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- Feature Extraction from Vendler Class
-- ============================================================================

/--
Get the telicity of a Vendler class.

States are neither telic nor atelic in the traditional sense; we treat them
as atelic since they can combine with "for X" adverbials.
-/
def VendlerClass.telicity : VendlerClass → Telicity
  | .state => .atelic         -- States can take "for an hour"
  | .activity => .atelic
  | .achievement => .telic
  | .accomplishment => .telic

/--
Get the duration of a Vendler class.
-/
def VendlerClass.duration : VendlerClass → Duration
  | .state => .durative
  | .activity => .durative
  | .achievement => .punctual
  | .accomplishment => .durative

/--
Get the dynamicity of a Vendler class.
-/
def VendlerClass.dynamicity : VendlerClass → Dynamicity
  | .state => .stative
  | .activity => .dynamic
  | .achievement => .dynamic
  | .accomplishment => .dynamic

-- ============================================================================
-- Theorems: Feature-Class Correspondence
-- ============================================================================

/-- States are stative (by definition). -/
theorem state_is_stative : VendlerClass.state.dynamicity = .stative := rfl

/-- Activities are atelic (by definition). -/
theorem activity_is_atelic : VendlerClass.activity.telicity = .atelic := rfl

/-- Activities are durative (by definition). -/
theorem activity_is_durative : VendlerClass.activity.duration = .durative := rfl

/-- Achievements are punctual (by definition). -/
theorem achievement_is_punctual : VendlerClass.achievement.duration = .punctual := rfl

/-- Achievements are telic (by definition). -/
theorem achievement_is_telic : VendlerClass.achievement.telicity = .telic := rfl

/-- Accomplishments are telic (by definition). -/
theorem accomplishment_is_telic : VendlerClass.accomplishment.telicity = .telic := rfl

/-- Accomplishments are durative (by definition). -/
theorem accomplishment_is_durative : VendlerClass.accomplishment.duration = .durative := rfl

/--
All dynamic classes involve change.
-/
theorem dynamic_classes_are_dynamic (c : VendlerClass) :
    c ≠ .state → c.dynamicity = .dynamic := by
  intro h
  cases c with
  | state => contradiction
  | activity => rfl
  | achievement => rfl
  | accomplishment => rfl

/--
All telic classes have endpoints.
-/
theorem telic_classes (c : VendlerClass) :
    c.telicity = .telic ↔ (c = .achievement ∨ c = .accomplishment) := by
  cases c <;> simp [VendlerClass.telicity]

end Montague.Lexicon.Aspect
