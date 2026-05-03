import Linglib.Core.Scales.Scale

/-!
# Features.Aktionsart
@cite{vendler-1957} @cite{smith-1997}

Per-verb-entry feature taxonomy for lexical aspect: the three orthogonal
binary features (telicity, duration, dynamicity), the five-way Vendler
class projection, the bundled `AspectualProfile`, and aspectual-shift
operations modeling compositional coercion.

This file is **descriptive vocabulary** Fragment authors use to label
lexical entries (`verb.aspectualProfile = activityProfile`). Predictions
about how a labelled verb's denotation behaves live in `Theories/`
(consequence theorems) or framework-specific `Studies/` files, not here.

## Provenance

Moved from `Core/Lexical/VerbClass.lean` (the inductives + class theorems)
and `Theories/Semantics/Tense/Aspect/LexicalAspect.lean` (the shift
methods + `Telicity.toMereoTag`) in the cleanup that dissolved
`Core/Lexical/`. Per-verb-entry classifications belong with the other
feature taxonomies (Person, Number, Polarity, Definiteness…) — not in
`Core/` (substrate) and not in `Theories/` (which would imply
framework-specific theorem content). The shift methods co-locate with
the type definitions per the dot-notation rule (`(p : AspectualProfile).telicize`
must be declared in `namespace Features.AspectualProfile`).

## Framework commitment

The 5-way classification (`VendlerClass`) and the orthogonal-binary
parameterization (`AspectualProfile`) follow @cite{vendler-1957} as
extended by Smith 1991 *The Parameter of Aspect* (1st ed.; both the
binary-feature decomposition and the 5-cell map including semelfactives
appear there — the @cite{smith-1997} 2nd ed. cited here is a revision).
The semelfactive category predates Smith — it comes from Slavic
aspectology and was introduced into the typological literature by
Comrie 1976 *Aspect* (Cambridge UP; not currently in `references.bib`).

## Substrate primacy

`Telicity.toMereoTag` projects this file's binary `Telicity` onto
`Core.Scales.Scale.MereoTag`, the canonical cumulative/quantized tag.
The mereological algebra of CUM/QUA/DIV event predicates lives in
`Theories/Semantics/Events/Mereology.lean`; this file's `Telicity` is
the Smith-flavored derived label, not the primary notion. Reversing
the projection — defining `Telicity` as a quotient of the substrate —
is a follow-up.

## Sibling formalizations elsewhere in linglib

- @cite{vendler-1957}: the original 4-way is `VendlerClass` minus
  `.semelfactive`.
- @cite{bach-1986}: `EventSort = action | state` in
  `Theories/Semantics/Events/Basic.lean`, with `dynamicityToEventSort`
  round-trip against this file's `Dynamicity`.
- @cite{krifka-1989}, @cite{krifka-1998}: full CUM/QUA/DIV algebra in
  `Theories/Semantics/Events/Mereology.lean`, plus study files
  `Phenomena/TenseAspect/Studies/Krifka1989.lean` and `Krifka1998.lean`.
- @cite{dowty-1979}: subinterval property as `HasSubintervalProp` in
  `Theories/Semantics/Tense/Aspect/SubintervalProperty.lean`.
- @cite{rothstein-2004}: complex-event analysis of accomplishments —
  partial coverage in `Phenomena/ArgumentStructure/Studies/Dowty1991.lean`
  and `Theories/Semantics/Verb/Affectedness.lean`.
- @cite{filip-2012}: three-way CUM/QUA/neither classification in
  `Phenomena/TenseAspect/Studies/Filip2012.lean`, with a
  `three_way_exhaustive` theorem refuting the binary `Telicity` here
  for incremental verbs (no refutation theorem yet ties back to this file).

Bridges between this vocabulary and those substrate formalizations
(e.g., "a verb of class `.state` has a denotation satisfying
`HasSubintervalProp`") are not yet landed.
-/

namespace Features

-- ════════════════════════════════════════════════════
-- § 1. Three Orthogonal Binary Features
-- ════════════════════════════════════════════════════

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

namespace Telicity

/-- Telicity → MereoTag: telic = quantized.
    Telic predicates are QUA (no proper part of a telic event is telic);
    atelic predicates are CUM (the sum of two atelic events is atelic). -/
def toMereoTag : Telicity → Core.Scale.MereoTag
  | .telic  => .qua
  | .atelic => .cum

end Telicity

-- ════════════════════════════════════════════════════
-- § 2. Vendler Class (five-way projection)
-- ════════════════════════════════════════════════════

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

namespace VendlerClass

/-- Get the telicity of a Vendler class (states treated as atelic). -/
def telicity : VendlerClass → Telicity
  | .state => .atelic
  | .activity => .atelic
  | .achievement => .telic
  | .accomplishment => .telic
  | .semelfactive => .atelic

/-- Get the duration of a Vendler class. -/
def duration : VendlerClass → Duration
  | .state => .durative
  | .activity => .durative
  | .achievement => .punctual
  | .accomplishment => .durative
  | .semelfactive => .punctual

/-- Get the dynamicity of a Vendler class. -/
def dynamicity : VendlerClass → Dynamicity
  | .state => .stative
  | .activity => .dynamic
  | .achievement => .dynamic
  | .accomplishment => .dynamic
  | .semelfactive => .dynamic

end VendlerClass

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

-- ════════════════════════════════════════════════════
-- § 3. AspectualProfile (bundled binary features)
-- ════════════════════════════════════════════════════

/-- An aspectual profile bundles telicity, duration, and dynamicity. -/
structure AspectualProfile where
  /-- Whether the eventuality has a natural endpoint -/
  telicity : Telicity
  /-- Whether the eventuality takes time -/
  duration : Duration
  /-- Whether the eventuality involves change -/
  dynamicity : Dynamicity
  deriving DecidableEq, Repr

namespace AspectualProfile

/-- Convert an aspectual profile to a situation type.
    All five [±dynamic, ±durative, ±telic] combinations are distinguished. -/
def toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .semelfactive

/-- Telicize: add a natural endpoint to an atelic predicate. -/
def telicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .telic }

/-- Atelicize: remove the natural endpoint (progressive effect). -/
def atelicize (p : AspectualProfile) : AspectualProfile :=
  { p with telicity := .atelic }

/-- Duratize: stretch a punctual event over time (iterative). -/
def duratize (p : AspectualProfile) : AspectualProfile :=
  { p with duration := .durative }

/-- Statify: convert to a stative reading. -/
def statify (p : AspectualProfile) : AspectualProfile :=
  { p with dynamicity := .stative }

end AspectualProfile

namespace VendlerClass

/-- Convert a Vendler class to its canonical aspectual profile. -/
def toProfile (c : VendlerClass) : AspectualProfile :=
  { telicity := c.telicity
  , duration := c.duration
  , dynamicity := c.dynamicity }

end VendlerClass

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

-- ════════════════════════════════════════════════════
-- § 4. Aspectual shifts (compositional coercion)
-- ════════════════════════════════════════════════════

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

end Features
