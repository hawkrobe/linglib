/-
# Aspectual Profile and Classification Theory

This module defines `AspectualProfile` for bundling aspectual features,
and provides classification and compositional machinery.

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

We define operations that capture these shifts.

## References

- Dowty, D. (1979). *Word Meaning and Montague Grammar*.
- Krifka, M. (1998). The origins of telicity.
- Filip, H. (1999). *Aspect, Eventuality Types and Noun Phrase Semantics*.
-/

import Linglib.Theories.Montague.Lexicon.Aspect.Basic

namespace Montague.Lexicon.Aspect

-- ============================================================================
-- Aspectual Profile
-- ============================================================================

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

-- ============================================================================
-- Profile ↔ Vendler Class Mapping
-- ============================================================================

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

-- ============================================================================
-- Canonical Profiles
-- ============================================================================

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

-- ============================================================================
-- Roundtrip Theorems
-- ============================================================================

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

-- ============================================================================
-- Aspectual Shifts (Coercion)
-- ============================================================================

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

-- ============================================================================
-- Shift Theorems
-- ============================================================================

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

-- ============================================================================
-- Homogeneity (Subinterval Property)
-- ============================================================================

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

-- ============================================================================
-- Summary
-- ============================================================================

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

end Montague.Lexicon.Aspect
