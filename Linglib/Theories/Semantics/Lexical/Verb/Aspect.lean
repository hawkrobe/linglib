/-
Aspectual categories following Vendler (1957) and Dowty (1979).
Three binary features (telicity, duration, dynamicity) yield four Vendler classes.
Aspectual shifts (telicize, atelicize, duratize) model compositional coercion.

- Vendler, Z. (1957). Verbs and times.
- Dowty, D. (1979). Word Meaning and Montague Grammar.
- Smith, C. (1991). The Parameter of Aspect.
-/

namespace Semantics.Lexical.Verb.Aspect

section Features

/-- Telicity: whether an event has a natural endpoint. -/
inductive Telicity where
  | telic   -- has natural endpoint (stop, build, arrive)
  | atelic  -- no natural endpoint (run, swim, love)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Duration: whether an event takes time or is instantaneous. -/
inductive Duration where
  | durative  -- takes time (run, build, love)
  | punctual  -- instantaneous (recognize, arrive, die)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Dynamicity: whether the event involves change. -/
inductive Dynamicity where
  | dynamic  -- involves change (run, build, die)
  | stative  -- no change (know, love, own)
  deriving DecidableEq, Repr, BEq, Inhabited

end Features

section VendlerClassification

/-- Vendler's four-way classification of eventualities (Vendler 1957, Dowty 1979). -/
inductive VendlerClass where
  | state         -- [-dynamic, +durative]  know, love
  | activity      -- [+dynamic, +durative, -telic]  run, swim
  | achievement   -- [+dynamic, -durative, +telic]  recognize, die
  | accomplishment -- [+dynamic, +durative, +telic]  build, write
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Get the telicity of a Vendler class (states treated as atelic). -/
def VendlerClass.telicity : VendlerClass → Telicity
  | .state => .atelic         -- States can take "for an hour"
  | .activity => .atelic
  | .achievement => .telic
  | .accomplishment => .telic

/-- Get the duration of a Vendler class. -/
def VendlerClass.duration : VendlerClass → Duration
  | .state => .durative
  | .activity => .durative
  | .achievement => .punctual
  | .accomplishment => .durative

/-- Get the dynamicity of a Vendler class. -/
def VendlerClass.dynamicity : VendlerClass → Dynamicity
  | .state => .stative
  | .activity => .dynamic
  | .achievement => .dynamic
  | .accomplishment => .dynamic

/-- States are stative. -/
theorem state_is_stative : VendlerClass.state.dynamicity = .stative := rfl

/-- Activities are atelic. -/
theorem activity_is_atelic : VendlerClass.activity.telicity = .atelic := rfl

/-- Activities are durative. -/
theorem activity_is_durative : VendlerClass.activity.duration = .durative := rfl

/-- Achievements are punctual. -/
theorem achievement_is_punctual : VendlerClass.achievement.duration = .punctual := rfl

/-- Achievements are telic. -/
theorem achievement_is_telic : VendlerClass.achievement.telicity = .telic := rfl

/-- Accomplishments are telic. -/
theorem accomplishment_is_telic : VendlerClass.accomplishment.telicity = .telic := rfl

/-- Accomplishments are durative. -/
theorem accomplishment_is_durative : VendlerClass.accomplishment.duration = .durative := rfl

/-- All dynamic classes involve change. -/
theorem dynamic_classes_are_dynamic (c : VendlerClass) :
    c ≠ .state → c.dynamicity = .dynamic := by
  intro h
  cases c with
  | state => contradiction
  | activity => rfl
  | achievement => rfl
  | accomplishment => rfl

/-- All telic classes have endpoints. -/
theorem telic_classes (c : VendlerClass) :
    c.telicity = .telic ↔ (c = .achievement ∨ c = .accomplishment) := by
  cases c <;> simp [VendlerClass.telicity]

end VendlerClassification

section AspectualProfile

/-- An aspectual profile bundles telicity, duration, and dynamicity. -/
structure AspectualProfile where
  /-- Whether the eventuality has a natural endpoint -/
  telicity : Telicity
  /-- Whether the eventuality takes time -/
  duration : Duration
  /-- Whether the eventuality involves change -/
  dynamicity : Dynamicity
  deriving DecidableEq, Repr, BEq

/-- Convert an aspectual profile to a Vendler class (semelfactives mapped to activity). -/
def AspectualProfile.toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .activity

/-- Convert a Vendler class to its canonical aspectual profile. -/
def VendlerClass.toProfile (c : VendlerClass) : AspectualProfile :=
  { telicity := c.telicity
  , duration := c.duration
  , dynamicity := c.dynamicity }

/-- Canonical profile for states. -/
def stateProfile : AspectualProfile :=
  { telicity := .atelic, duration := .durative, dynamicity := .stative }

/-- Canonical profile for activities. -/
def activityProfile : AspectualProfile :=
  { telicity := .atelic, duration := .durative, dynamicity := .dynamic }

/-- Canonical profile for achievements. -/
def achievementProfile : AspectualProfile :=
  { telicity := .telic, duration := .punctual, dynamicity := .dynamic }

/-- Canonical profile for accomplishments. -/
def accomplishmentProfile : AspectualProfile :=
  { telicity := .telic, duration := .durative, dynamicity := .dynamic }

/-- Converting a Vendler class to a profile and back is identity. -/
theorem vendler_profile_roundtrip (c : VendlerClass) :
    c.toProfile.toVendlerClass = c := by
  cases c <;> rfl

/-- The canonical state profile maps to the state class. -/
theorem stateProfile_toClass : stateProfile.toVendlerClass = .state := rfl

/-- The canonical activity profile maps to the activity class. -/
theorem activityProfile_toClass : activityProfile.toVendlerClass = .activity := rfl

/-- The canonical achievement profile maps to the achievement class. -/
theorem achievementProfile_toClass : achievementProfile.toVendlerClass = .achievement := rfl

/-- The canonical accomplishment profile maps to the accomplishment class. -/
theorem accomplishmentProfile_toClass : accomplishmentProfile.toVendlerClass = .accomplishment := rfl

end AspectualProfile

section Shifts

/-- Telicize: add a natural endpoint to an atelic predicate. -/
def AspectualProfile.telicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .telic }

/-- Atelicize: remove the natural endpoint (progressive effect). -/
def AspectualProfile.atelicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .atelic }

/-- Duratize: stretch a punctual event over time (iterative). -/
def AspectualProfile.duratize (p : AspectualProfile) : AspectualProfile :=
  { p with duration := .durative }

/-- Statify: convert to a stative reading. -/
def AspectualProfile.statify (p : AspectualProfile) : AspectualProfile :=
  { p with dynamicity := .stative }

/-- Telicizing an activity yields an accomplishment. -/
theorem telicize_activity :
    activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/-- Atelicizing an accomplishment yields an activity. -/
theorem atelicize_accomplishment :
    accomplishmentProfile.atelicize.toVendlerClass = .activity := rfl

/-- Duratizing an achievement yields an accomplishment. -/
theorem duratize_achievement :
    achievementProfile.duratize.toVendlerClass = .accomplishment := rfl

/-- Telicize is idempotent. -/
theorem telicize_idempotent (p : AspectualProfile) :
    p.telicize.telicize = p.telicize := rfl

/-- Atelicize is idempotent. -/
theorem atelicize_idempotent (p : AspectualProfile) :
    p.atelicize.atelicize = p.atelicize := rfl

end Shifts

section Homogeneity

/-- Whether a predicate is homogeneous (has the subinterval property). -/
def AspectualProfile.isHomogeneous (p : AspectualProfile) : Bool :=
  match p.toVendlerClass with
  | .state | .activity => true
  | .achievement | .accomplishment => false

/-- States are homogeneous. -/
theorem state_is_homogeneous : stateProfile.isHomogeneous = true := rfl

/-- Activities are homogeneous. -/
theorem activity_is_homogeneous : activityProfile.isHomogeneous = true := rfl

/-- Achievements are not homogeneous. -/
theorem achievement_not_homogeneous : achievementProfile.isHomogeneous = false := rfl

/-- Accomplishments are not homogeneous. -/
theorem accomplishment_not_homogeneous : accomplishmentProfile.isHomogeneous = false := rfl

/-- Homogeneous iff atelic. -/
theorem homogeneous_iff_atelic (p : AspectualProfile) :
    p.isHomogeneous = true ↔ p.toVendlerClass.telicity = .atelic := by
  simp only [AspectualProfile.isHomogeneous]
  cases h : p.toVendlerClass <;> simp [VendlerClass.telicity]

end Homogeneity

end Semantics.Lexical.Verb.Aspect
