/-!
# Aspect: basic definitions

This file defines the classificatory vocabulary of aspect, following the two components of
Smith's theory. Situation type classifies an eventuality by three binary features: whether it
has a natural endpoint (`Telicity`), whether it takes time (`Duration`) and whether it involves
change (`Dynamicity`). The features are bundled as an `AspectualProfile` and projected onto the
four classes of Vendler together with Smith's semelfactives (`VendlerClass`). The aspectual
shifts of compositional coercion change one feature of a profile (`AspectualProfile.telicize`
and its siblings), and Dowty's adverbial and progressive diagnostics are functions of the
features (`forXPrediction`, `inXPrediction`, `progressivePrediction`). Viewpoint is the
presentation of a situation, Klein's four relations between the topic time and the situation
time together with Smith's neutral viewpoint (`ViewpointType`), and at its coarsest the
opposition of perfective and imperfective (`Perfectivity`). The operators that viewpoints
denote are in `Semantics/Aspect/Viewpoint.lean`.

## Main definitions

* `Aspect.VendlerClass`: the five situation types.
* `Aspect.AspectualProfile`: a bundle of the three features, with `toVendlerClass` its
  situation type.
* `Aspect.DiagnosticResult`: the outcome of a diagnostic, with the *for*-adverbial,
  *in*-adverbial and progressive tests as functions of a situation type.
* `Aspect.ViewpointType`, `Aspect.Perfectivity`: the viewpoints.

## References

* [smith-1997]
* [vendler-1957]
* [dowty-1979]
* [klein-1994]
-/

namespace Aspect

/-! ### Situation type -/

/-- Whether an eventuality has a natural endpoint. -/
inductive Telicity
  | telic
  | atelic
  deriving DecidableEq, Repr, Inhabited

/-- Whether an eventuality takes time or is instantaneous. -/
inductive Duration
  | durative
  | punctual
  deriving DecidableEq, Repr, Inhabited

/-- Whether an eventuality involves change. -/
inductive Dynamicity
  | dynamic
  | stative
  deriving DecidableEq, Repr, Inhabited

/-- The five situation types are the four classes of [vendler-1957] and the semelfactives of
[smith-1997]. -/
inductive VendlerClass
  | state
  | activity
  | achievement
  | accomplishment
  | semelfactive
  deriving DecidableEq, Repr, Inhabited

namespace VendlerClass

/-- The telicity of a situation type. -/
def telicity : VendlerClass → Telicity
  | state | activity | semelfactive => .atelic
  | achievement | accomplishment => .telic

/-- The duration of a situation type. -/
def duration : VendlerClass → Duration
  | state | activity | accomplishment => .durative
  | achievement | semelfactive => .punctual

/-- The dynamicity of a situation type. -/
def dynamicity : VendlerClass → Dynamicity
  | state => .stative
  | activity | achievement | accomplishment | semelfactive => .dynamic

end VendlerClass

/-- The three features of a situation type, bundled. -/
structure AspectualProfile where
  telicity : Telicity
  duration : Duration
  dynamicity : Dynamicity
  deriving DecidableEq, Repr

namespace AspectualProfile

/-- The situation type of a profile. -/
@[simp] def toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .semelfactive

/-- Add a natural endpoint. -/
def telicize (p : AspectualProfile) : AspectualProfile := { p with telicity := .telic }

/-- Remove the natural endpoint, the effect of the progressive. -/
def atelicize (p : AspectualProfile) : AspectualProfile := { p with telicity := .atelic }

/-- Stretch a punctual eventuality over time, the iterative reading. -/
def duratize (p : AspectualProfile) : AspectualProfile := { p with duration := .durative }

end AspectualProfile

/-- The canonical profile of a situation type. -/
@[simp] def VendlerClass.toProfile (c : VendlerClass) : AspectualProfile :=
  ⟨c.telicity, c.duration, c.dynamicity⟩

/-- The canonical profile of a state. -/
def stateProfile : AspectualProfile := ⟨.atelic, .durative, .stative⟩

/-- The canonical profile of an activity. -/
def activityProfile : AspectualProfile := ⟨.atelic, .durative, .dynamic⟩

/-- The canonical profile of an achievement. -/
def achievementProfile : AspectualProfile := ⟨.telic, .punctual, .dynamic⟩

/-- The canonical profile of an accomplishment. -/
def accomplishmentProfile : AspectualProfile := ⟨.telic, .durative, .dynamic⟩

/-- The canonical profile of a semelfactive. -/
def semelfactiveProfile : AspectualProfile := ⟨.atelic, .punctual, .dynamic⟩

@[simp] theorem VendlerClass.toProfile_toVendlerClass (c : VendlerClass) :
    c.toProfile.toVendlerClass = c := by
  cases c <;> rfl

/-- Telicizing an activity gives an accomplishment. -/
theorem telicize_activity : activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/-- Duratizing a semelfactive gives an activity, the iterative reading. -/
theorem duratize_semelfactive : semelfactiveProfile.duratize.toVendlerClass = .activity := rfl

/-! ### Diagnostics

The adverbial and progressive tests of [dowty-1979], as functions of the three features: a
*for*-adverbial measures an atelic durative eventuality and coerces a telic or punctual one into
repetition or iteration; an *in*-adverbial needs a culmination; the progressive needs internal
stages, reads an achievement through its preliminary stages and a semelfactive as iterated. -/

/-- The outcome of a diagnostic is acceptable, unacceptable, degraded, or acceptable under a
meaning shift. -/
inductive DiagnosticResult
  | accept
  | reject
  | marginal
  | coerced
  deriving DecidableEq, Repr

/-- The *for*-adverbial test. -/
def forXPrediction (c : VendlerClass) : DiagnosticResult :=
  match c.telicity, c.duration with
  | .atelic, .durative => .accept
  | .telic, .punctual => .reject
  | _, _ => .coerced

/-- The *in*-adverbial test. -/
def inXPrediction (c : VendlerClass) : DiagnosticResult :=
  if c.telicity = .telic then .accept else .reject

/-- The progressive test. -/
def progressivePrediction (c : VendlerClass) : DiagnosticResult :=
  match c.dynamicity, c.duration, c.telicity with
  | .stative, _, _ => .reject
  | .dynamic, .durative, _ => .accept
  | .dynamic, .punctual, .telic => .marginal
  | .dynamic, .punctual, .atelic => .coerced

theorem inXPrediction_eq_accept_iff (c : VendlerClass) :
    inXPrediction c = .accept ↔ c.telicity = .telic := by
  cases c <;> decide

theorem forXPrediction_eq_accept_iff (c : VendlerClass) :
    forXPrediction c = .accept ↔ c.telicity = .atelic ∧ c.duration = .durative := by
  cases c <;> decide

theorem progressivePrediction_eq_accept_iff (c : VendlerClass) :
    progressivePrediction c = .accept ↔ c.duration = .durative ∧ c.dynamicity = .dynamic := by
  cases c <;> decide

/-! ### Viewpoint -/

/-- The viewpoints are the four relations of [klein-1994] between the topic time and the situation
time, and the neutral viewpoint of [smith-1997], the default in the absence of aspect
morphology. -/
inductive ViewpointType
  | imperfective
  | perfective
  | perfect
  | prospective
  | neutral
  deriving DecidableEq, Repr, Inhabited

/-- The opposition of perfective and imperfective is viewpoint aspect at its coarsest, the right
granularity where the fact at issue is that the perfective requires actualization and the
imperfective does not, or where the opposition is lexically encoded, as on a `Verb.Stem`. -/
inductive Perfectivity
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

end Aspect
