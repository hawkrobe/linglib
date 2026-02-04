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

namespace Montague.Verb.Aspect

-- Core Aspectual Features

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

-- Vendler Classification

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

-- Feature Extraction from Vendler Class

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

-- Theorems: Feature-Class Correspondence

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

-- Aspectual Profile and Classification Theory

/-!
## Aspectual Profile

An `AspectualProfile` bundles the three core aspectual features:
- Telicity (telic/atelic)
- Duration (durative/punctual)
- Dynamicity (dynamic/stative)

The profile determines (and is determined by) the Vendler class.

## Aspectual Coercion

Many aspectual shifts are possible compositionally:
- "John ran" (activity) → "John ran a mile" (accomplishment) [telic augmentation]
- "John built a house" (accomplishment) → "John was building a house" (activity) [progressive]
- "John coughed" (achievement) → "John was coughing" (activity) [iterative]
-/

/--
An aspectual profile bundles all three aspectual features.

This structure allows for complete specification of a predicate's aspectual
properties, from which the Vendler class can be derived.
-/
structure AspectualProfile where
  /-- Whether the eventuality has a natural endpoint -/
  telicity : Telicity
  /-- Whether the eventuality takes time -/
  duration : Duration
  /-- Whether the eventuality involves change -/
  dynamicity : Dynamicity
  deriving DecidableEq, Repr, BEq

-- Profile ↔ Vendler Class Mapping

/--
Convert an aspectual profile to a Vendler class.

Not all feature combinations are possible (e.g., stative + punctual is odd).
This function maps to the nearest sensible class.

| Dynamicity | Duration  | Telicity | Class          |
|------------|-----------|----------|----------------|
| stative    | *         | *        | state          |
| dynamic    | durative  | atelic   | activity       |
| dynamic    | punctual  | telic    | achievement    |
| dynamic    | durative  | telic    | accomplishment |
| dynamic    | punctual  | atelic   | semelfactive*  |

*Semelfactives (cough, knock, flash) are punctual atelics.
We assimilate them to activities following Dowty's treatment.
-/
def AspectualProfile.toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .activity  -- semelfactives → activity

/--
Convert a Vendler class to its canonical aspectual profile.
-/
def VendlerClass.toProfile (c : VendlerClass) : AspectualProfile :=
  { telicity := c.telicity
  , duration := c.duration
  , dynamicity := c.dynamicity }

-- Canonical Profiles

/-- Canonical profile for states -/
def stateProfile : AspectualProfile :=
  { telicity := .atelic, duration := .durative, dynamicity := .stative }

/-- Canonical profile for activities -/
def activityProfile : AspectualProfile :=
  { telicity := .atelic, duration := .durative, dynamicity := .dynamic }

/-- Canonical profile for achievements -/
def achievementProfile : AspectualProfile :=
  { telicity := .telic, duration := .punctual, dynamicity := .dynamic }

/-- Canonical profile for accomplishments -/
def accomplishmentProfile : AspectualProfile :=
  { telicity := .telic, duration := .durative, dynamicity := .dynamic }

-- Roundtrip Theorems

/--
Converting a Vendler class to a profile and back is identity.
-/
theorem vendler_profile_roundtrip (c : VendlerClass) :
    c.toProfile.toVendlerClass = c := by
  cases c <;> rfl

/--
The canonical state profile maps to the state class.
-/
theorem stateProfile_toClass : stateProfile.toVendlerClass = .state := rfl

/--
The canonical activity profile maps to the activity class.
-/
theorem activityProfile_toClass : activityProfile.toVendlerClass = .activity := rfl

/--
The canonical achievement profile maps to the achievement class.
-/
theorem achievementProfile_toClass : achievementProfile.toVendlerClass = .achievement := rfl

/--
The canonical accomplishment profile maps to the accomplishment class.
-/
theorem accomplishmentProfile_toClass : accomplishmentProfile.toVendlerClass = .accomplishment := rfl

-- Aspectual Shifts (Coercion)

/--
Telicize: Add a natural endpoint to an atelic predicate.

Example: "run" (activity) + "a mile" → "run a mile" (accomplishment)

This corresponds to compositional telicity from the object.
-/
def AspectualProfile.telicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .telic }

/--
Atelicize: Remove the natural endpoint (progressive effect).

Example: "build a house" (accomplishment) → "building a house" (activity)

The progressive removes the endpoint, making the event atelic.
-/
def AspectualProfile.atelicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .atelic }

/--
Duratize: Stretch a punctual event over time (iterative).

Example: "cough" (achievement/semelfactive) → "coughing" (activity)

Repeated instantaneous events become durative.
-/
def AspectualProfile.duratize (p : AspectualProfile) : AspectualProfile :=
  { p with duration := .durative }

/--
Statify: Convert to a stative reading.

Example: "The road winds through the hills" (stative use of motion verb)
-/
def AspectualProfile.statify (p : AspectualProfile) : AspectualProfile :=
  { p with dynamicity := .stative }

-- Shift Theorems

/--
Telicizing an activity yields an accomplishment.
-/
theorem telicize_activity :
    activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/--
Atelicizing an accomplishment yields an activity.
-/
theorem atelicize_accomplishment :
    accomplishmentProfile.atelicize.toVendlerClass = .activity := rfl

/--
Duratizing an achievement yields an accomplishment.
-/
theorem duratize_achievement :
    achievementProfile.duratize.toVendlerClass = .accomplishment := rfl

/--
Telicize is idempotent.
-/
theorem telicize_idempotent (p : AspectualProfile) :
    p.telicize.telicize = p.telicize := rfl

/--
Atelicize is idempotent.
-/
theorem atelicize_idempotent (p : AspectualProfile) :
    p.atelicize.atelicize = p.atelicize := rfl

-- Homogeneity (Subinterval Property)

/--
Whether a predicate is homogeneous (has the subinterval property).

Homogeneous predicates: any subinterval of the event is also an instance.
- States: "John is tall at t₁" → "John is tall at any t ⊆ t₁"
- Activities: "John ran from 2-3pm" → "John ran at 2:30"

Non-homogeneous predicates: subintervals may not satisfy the predicate.
- Accomplishments: "John built a house from 2-3pm" ↛ "John built a house at 2:30"
-/
def AspectualProfile.isHomogeneous (p : AspectualProfile) : Bool :=
  match p.toVendlerClass with
  | .state | .activity => true
  | .achievement | .accomplishment => false

/--
States are homogeneous.
-/
theorem state_is_homogeneous : stateProfile.isHomogeneous = true := rfl

/--
Activities are homogeneous.
-/
theorem activity_is_homogeneous : activityProfile.isHomogeneous = true := rfl

/--
Achievements are not homogeneous.
-/
theorem achievement_not_homogeneous : achievementProfile.isHomogeneous = false := rfl

/--
Accomplishments are not homogeneous.
-/
theorem accomplishment_not_homogeneous : accomplishmentProfile.isHomogeneous = false := rfl

/--
Homogeneous iff atelic.

This captures the observation that atelic predicates (states, activities)
have the subinterval property while telic predicates don't.
-/
theorem homogeneous_iff_atelic (p : AspectualProfile) :
    p.isHomogeneous = true ↔ p.toVendlerClass.telicity = .atelic := by
  simp only [AspectualProfile.isHomogeneous]
  cases h : p.toVendlerClass <;> simp [VendlerClass.telicity]

-- Summary

/-
## Summary: Aspectual Profile and Theory

### Key Types
- `AspectualProfile`: Bundle of (telicity, duration, dynamicity)
- Canonical profiles: `stateProfile`, `activityProfile`, etc.

### Profile ↔ Class
- `AspectualProfile.toVendlerClass`: Derive class from features
- `VendlerClass.toProfile`: Get canonical profile for class
- `vendler_profile_roundtrip`: Roundtrip theorem

### Aspectual Shifts
- `telicize`: Activity → Accomplishment (add endpoint)
- `atelicize`: Accomplishment → Activity (progressive)
- `duratize`: Achievement → Accomplishment (iterative)
- `statify`: Convert to stative

### Homogeneity
- `isHomogeneous`: Subinterval property
- States and activities are homogeneous
- Achievements and accomplishments are not

### Usage
Import this module to work with aspectual profiles. Use `toVendlerClass`
to classify predicates and the shift operations to model compositional
aspectual coercion.
-/

end Montague.Verb.Aspect
