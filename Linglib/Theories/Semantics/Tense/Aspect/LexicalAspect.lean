import Linglib.Core.Scales.Scale

/-!
# Situation Type Classification

Five situation types classified by three binary features (telicity, duration,
dynamicity), following @cite{smith-1997} and @cite{vendler-1957}.
@cite{vendler-1957} identified four classes; @cite{smith-1997} added
semelfactives as a fifth, completing the feature space.

Aspectual shifts (telicize, atelicize, duratize) model compositional coercion.
-/

namespace Semantics.Tense.Aspect.LexicalAspect

section Features

/-- Telicity: whether an event has a natural endpoint. -/
inductive Telicity where
  | telic   -- has natural endpoint (stop, build, arrive)
  | atelic  -- no natural endpoint (run, swim, love)
  deriving DecidableEq, Repr, Inhabited

/-- Duration: whether an event takes time or is instantaneous. -/
inductive Duration where
  | durative  -- takes time (run, build, love)
  | punctual  -- instantaneous (recognize, arrive, die)
  deriving DecidableEq, Repr, Inhabited

/-- Dynamicity: whether the event involves change. -/
inductive Dynamicity where
  | dynamic  -- involves change (run, build, die)
  | stative  -- no change (know, love, own)
  deriving DecidableEq, Repr, Inhabited

end Features

/-- Telicity → MereoTag: telic = quantized.
    Telic predicates are QUA (no proper part of a telic event is telic);
    atelic predicates are CUM (the sum of two atelic events is atelic). -/
def Telicity.toMereoTag : Telicity → Core.Scale.MereoTag
  | .telic  => .qua
  | .atelic => .cum

section VendlerClassification

/-- Five-way situation type classification (@cite{smith-1997}).
    Three binary features [±dynamic, ±durative, ±telic] yield five classes.
    The name `VendlerClass` is retained for compatibility; @cite{vendler-1957}
    identified the first four, @cite{smith-1997} added semelfactives. -/
inductive VendlerClass where
  | state         -- [-dynamic, +durative]  know, love
  | activity      -- [+dynamic, +durative, -telic]  run, swim
  | achievement   -- [+dynamic, -durative, +telic]  recognize, die
  | accomplishment -- [+dynamic, +durative, +telic]  build, write
  | semelfactive  -- [+dynamic, -durative, -telic]  cough, tap, flash
  deriving DecidableEq, Repr, Inhabited

/-- Get the telicity of a Vendler class (states treated as atelic). -/
def VendlerClass.telicity : VendlerClass → Telicity
  | .state => .atelic         -- States can take "for an hour"
  | .activity => .atelic
  | .achievement => .telic
  | .accomplishment => .telic
  | .semelfactive => .atelic  -- No natural endpoint

/-- Get the duration of a Vendler class. -/
def VendlerClass.duration : VendlerClass → Duration
  | .state => .durative
  | .activity => .durative
  | .achievement => .punctual
  | .accomplishment => .durative
  | .semelfactive => .punctual  -- Instantaneous

/-- Get the dynamicity of a Vendler class. -/
def VendlerClass.dynamicity : VendlerClass → Dynamicity
  | .state => .stative
  | .activity => .dynamic
  | .achievement => .dynamic
  | .accomplishment => .dynamic
  | .semelfactive => .dynamic

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

/-- Semelfactives are atelic. -/
theorem semelfactive_is_atelic : VendlerClass.semelfactive.telicity = .atelic := rfl

/-- Semelfactives are punctual. -/
theorem semelfactive_is_punctual : VendlerClass.semelfactive.duration = .punctual := rfl

/-- Semelfactives are dynamic. -/
theorem semelfactive_is_dynamic : VendlerClass.semelfactive.dynamicity = .dynamic := rfl

/-- All dynamic classes involve change. -/
theorem dynamic_classes_are_dynamic (c : VendlerClass) :
    c ≠ .state → c.dynamicity = .dynamic := by
  intro h
  cases c with
  | state => contradiction
  | activity => rfl
  | achievement => rfl
  | accomplishment => rfl
  | semelfactive => rfl

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
  deriving DecidableEq, Repr

/-- Convert an aspectual profile to a situation type.
    All five [±dynamic, ±durative, ±telic] combinations are distinguished. -/
def AspectualProfile.toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .semelfactive

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

/-- Canonical profile for semelfactives. -/
def semelfactiveProfile : AspectualProfile :=
  { telicity := .atelic, duration := .punctual, dynamicity := .dynamic }

/-- Converting a situation type to a profile and back is identity. -/
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

/-- The canonical semelfactive profile maps to the semelfactive class. -/
theorem semelfactiveProfile_toClass : semelfactiveProfile.toVendlerClass = .semelfactive := rfl

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

/-- Duratizing a semelfactive yields an activity (iterative reading). -/
theorem duratize_semelfactive :
    semelfactiveProfile.duratize.toVendlerClass = .activity := rfl

/-- Telicizing a semelfactive yields an achievement. -/
theorem telicize_semelfactive :
    semelfactiveProfile.telicize.toVendlerClass = .achievement := rfl

/-- Telicize is idempotent. -/
theorem telicize_idempotent (p : AspectualProfile) :
    p.telicize.telicize = p.telicize := rfl

/-- Atelicize is idempotent. -/
theorem atelicize_idempotent (p : AspectualProfile) :
    p.atelicize.atelicize = p.atelicize := rfl

end Shifts

section Homogeneity

/-- Whether a predicate has the subinterval property (qualified).
    States and activities both have it, but with different strength:
    - **States** have the *full* SIP: every subinterval of a knowing event
      is a knowing event (@cite{smith-1997} p. 23).
    - **Activities** have a *qualified* SIP: subintervals down to a
      minimum size are activity events, but below that minimum they
      are not (you can't be "walking" in an interval smaller than a
      single stride). See `hasFullSubintervalProp` for the distinction. -/
def AspectualProfile.isHomogeneous (p : AspectualProfile) : Bool :=
  match p.toVendlerClass with
  | .state | .activity => true
  | .achievement | .accomplishment | .semelfactive => false

/-- Whether the situation type has the *full* (unqualified) subinterval
    property. Only states satisfy this: every subinterval of a state event
    is itself a state event, with no minimum-size qualification.
    Activities have a qualified SIP (above a minimum interval); all other
    types lack it entirely.

    This distinction is the semantic content behind @cite{zhao-2025}'s
    ATOM-DIST_t: states distribute over temporal atoms, activities do not.
    See `predictsAtomDist_iff_stative`. -/
def VendlerClass.hasFullSubintervalProp : VendlerClass → Bool
  | .state => true
  | .activity | .achievement | .accomplishment | .semelfactive => false

/-- States are homogeneous (full SIP). -/
theorem state_is_homogeneous : stateProfile.isHomogeneous = true := rfl

/-- Activities are homogeneous (qualified SIP — above minimum intervals). -/
theorem activity_is_homogeneous : activityProfile.isHomogeneous = true := rfl

/-- Achievements are not homogeneous. -/
theorem achievement_not_homogeneous : achievementProfile.isHomogeneous = false := rfl

/-- Accomplishments are not homogeneous. -/
theorem accomplishment_not_homogeneous : accomplishmentProfile.isHomogeneous = false := rfl

/-- Semelfactives are not homogeneous (punctual — no proper subintervals). -/
theorem semelfactive_not_homogeneous : semelfactiveProfile.isHomogeneous = false := rfl

/-- States have the full (unqualified) SIP. -/
theorem state_has_full_sip : VendlerClass.state.hasFullSubintervalProp = true := rfl

/-- Activities do NOT have the full SIP — only a qualified version. -/
theorem activity_lacks_full_sip : VendlerClass.activity.hasFullSubintervalProp = false := rfl

/-- Full SIP implies qualified SIP (homogeneity), but not vice versa. -/
theorem fullSIP_implies_homogeneous (c : VendlerClass)
    (h : c.hasFullSubintervalProp = true) :
    c.toProfile.isHomogeneous = true := by
  cases c <;> simp_all [VendlerClass.hasFullSubintervalProp]; rfl

/-- VendlerClass predicts the (qualified) subinterval property:
    states and activities have it, others don't.
    This matches `isHomogeneous` — see `sub_agrees_with_homogeneous`.

    Note: states have the *full* SIP (every subinterval, no minimum),
    while activities have a *qualified* SIP (subintervals above a
    minimum size). This predicate returns `true` for both — use
    `VendlerClass.hasFullSubintervalProp` to distinguish them. -/
def predictsSubintervalProp : VendlerClass → Bool
  | .state | .activity => true
  | .achievement | .accomplishment | .semelfactive => false

/-- SUB prediction agrees with homogeneity. -/
theorem sub_agrees_with_homogeneous (c : VendlerClass) :
    predictsSubintervalProp c = c.toProfile.isHomogeneous := by
  cases c <;> rfl

/-- Full SIP is strictly stronger than qualified SIP:
    states have full SIP, activities have only qualified SIP. -/
theorem fullSIP_strictly_stronger :
    VendlerClass.state.hasFullSubintervalProp = true ∧
    predictsSubintervalProp .state = true ∧
    VendlerClass.activity.hasFullSubintervalProp = false ∧
    predictsSubintervalProp .activity = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Homogeneous iff durative and atelic.
    Semelfactives are atelic but not homogeneous (punctual), so
    homogeneity requires both atelicity and duration. -/
theorem homogeneous_iff_durative_atelic (p : AspectualProfile) :
    p.isHomogeneous = true ↔
    (p.toVendlerClass = .state ∨ p.toVendlerClass = .activity) := by
  simp only [AspectualProfile.isHomogeneous]
  cases h : p.toVendlerClass <;> simp

end Homogeneity

section AtomicDistributivity

/-- Whether a VendlerClass predicts ATOM-DIST_t (@cite{zhao-2025}, Def. 5.3).
    States satisfy ATOM-DIST_t (distribute over temporal subintervals);
    dynamic classes do not. Stricter than `isHomogeneous`: activities are
    homogeneous but fail ATOM-DIST_t.

    - Zhao, Z. (2025). Cross-Linguistic and Cross-Domain Temporal Expressions.
      NYU dissertation, Ch. 5. -/
def VendlerClass.predictsAtomDist : VendlerClass → Bool
  | .state => true
  | .activity | .achievement | .accomplishment | .semelfactive => false

/-- ATOM-DIST_t prediction coincides with stative dynamicity. -/
theorem predictsAtomDist_iff_stative (c : VendlerClass) :
    c.predictsAtomDist = true ↔ c.dynamicity = .stative := by
  cases c <;> simp [VendlerClass.predictsAtomDist, VendlerClass.dynamicity]

/-- States predict ATOM-DIST_t holds. -/
theorem state_predictsAtomDist :
    VendlerClass.state.predictsAtomDist = true := rfl

/-- All dynamic classes predict ATOM-DIST_t failure. -/
theorem dynamic_predictsAtomDist_false (c : VendlerClass)
    (h : c.dynamicity = .dynamic) :
    c.predictsAtomDist = false := by
  cases c <;> simp_all [VendlerClass.dynamicity, VendlerClass.predictsAtomDist]

/-- ATOM-DIST_t implies homogeneity (but not vice versa).
    Activities are homogeneous but do NOT satisfy ATOM-DIST_t — this is
    Zhao's point: ATOM-DIST_t discriminates states from activities, while
    the classical subinterval property does not. -/
theorem atomDist_implies_homogeneous (c : VendlerClass)
    (h : c.predictsAtomDist = true) :
    c.toProfile.isHomogeneous = true := by
  cases c <;> simp_all [VendlerClass.predictsAtomDist]; rfl

/-- ATOM-DIST_t prediction is the negation of dynamicity =.dynamic. -/
theorem predictsAtomDist_iff_not_dynamic (c : VendlerClass) :
    (c.predictsAtomDist = false) ↔ (c.dynamicity = .dynamic) := by
  cases c <;> simp [VendlerClass.predictsAtomDist, VendlerClass.dynamicity]

/-- Full SIP coincides with ATOM-DIST_t — both pick out exactly states. -/
theorem fullSIP_iff_atomDist (c : VendlerClass) :
    c.hasFullSubintervalProp = c.predictsAtomDist := by
  cases c <;> rfl

end AtomicDistributivity

end Semantics.Tense.Aspect.LexicalAspect
