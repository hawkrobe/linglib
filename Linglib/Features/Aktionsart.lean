import Linglib.Core.Order.Boundedness

/-!
# Features.Aktionsart
[vendler-1957] [smith-1997]

Per-verb-entry feature taxonomy for lexical aspect: three orthogonal
binary features (telicity, duration, dynamicity), the five-way Vendler
class projection, the bundled `AspectualProfile`, and aspectual-shift
operations modeling compositional coercion.

**Descriptive vocabulary** Fragment authors use to label lexical entries
(`verb.aspectualProfile = activityProfile`); predictions about how a
labelled verb's denotation behaves live in `Theories/` (consequence
theorems) or framework-specific `Studies/` files.

The 5-way classification follows the Vendler taxonomy as extended by
Smith 1991 / [smith-1997] (binary feature decomposition + 5-cell map
including semelfactives — both first appear in the 1991 1st ed., not the
1997 2nd ed. cited here). The semelfactive category itself comes from
Slavic aspectology (Comrie 1976 *Aspect*, not in `references.bib`).

`Telicity.toMereoTag` projects this file's binary `Telicity` onto
`Core.Scales.Scale.MereoTag`, the canonical cumulative/quantized tag.
The CUM/QUA/DIV algebra over event predicates lives in
`Semantics/Events/CEM.lean` — that is the substrate; the
`Telicity` here is the Smith-flavored derived label.

Sibling formalizations of competitor lexical-aspect frameworks:
[bach-1986]; the event-token sort is this `Dynamicity` feature (`Event.sort`);
[krifka-1989]/[krifka-1998] CUM/QUA/DIV in
`Semantics/Events/CEM.lean`; [dowty-1979] SIP in
`Semantics/Aspect/SubintervalProperty.lean`;
[filip-2012] three-way refutation of binary telicity in
`Studies/Filip2012.lean`.
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
@[simp]
def toMereoTag : Telicity → Core.Order.MereoTag
  | .telic  => .qua
  | .atelic => .cum

end Telicity

-- ════════════════════════════════════════════════════
-- § 2. Vendler Class (five-way projection)
-- ════════════════════════════════════════════════════

/-- Five-way situation type classification ([smith-1997]).
    Three binary features [±dynamic, ±durative, ±telic] yield five classes.
    The name `VendlerClass` is retained for compatibility; [vendler-1957]
    identified the first four, [smith-1997] added semelfactives. -/
inductive VendlerClass where
  | state         -- [-dynamic, +durative]  know, love
  | activity      -- [+dynamic, +durative, -telic]  run, swim
  | achievement   -- [+dynamic, -durative, +telic]  recognize, die
  | accomplishment -- [+dynamic, +durative, +telic]  build, write
  | semelfactive  -- [+dynamic, -durative, -telic]  cough, tap, flash
  deriving DecidableEq, Repr, Inhabited

namespace VendlerClass

/-- Get the telicity of a Vendler class (states treated as atelic). -/
@[simp]
def telicity : VendlerClass → Telicity
  | .state => .atelic
  | .activity => .atelic
  | .achievement => .telic
  | .accomplishment => .telic
  | .semelfactive => .atelic

/-- Get the duration of a Vendler class. -/
@[simp]
def duration : VendlerClass → Duration
  | .state => .durative
  | .activity => .durative
  | .achievement => .punctual
  | .accomplishment => .durative
  | .semelfactive => .punctual

/-- Get the dynamicity of a Vendler class. -/
@[simp]
def dynamicity : VendlerClass → Dynamicity
  | .state => .stative
  | .activity => .dynamic
  | .achievement => .dynamic
  | .accomplishment => .dynamic
  | .semelfactive => .dynamic

end VendlerClass

-- LicensingPipeline instances: per the convention noted in
-- `Core/Scales/Defs.lean` (LicensingPipeline class docstring), instances
-- live with the type they classify. Both compose via
-- `t.toMereoTag.toBoundedness`.

instance : Core.Order.LicensingPipeline Telicity where
  toBoundedness t := t.toMereoTag.toBoundedness

instance : Core.Order.LicensingPipeline VendlerClass where
  toBoundedness v := v.telicity.toMereoTag.toBoundedness

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

namespace VendlerClass

/-- A Vendler class has internal stages iff it is both dynamic and durative.
    [smith-1997] Ch. 4: the progressive focuses internal stages, so classes
    without them (states, punctuals) resist the progressive. -/
def HasInternalStages (c : VendlerClass) : Prop :=
  c.dynamicity = .dynamic ∧ c.duration = .durative

instance (c : VendlerClass) : Decidable c.HasInternalStages :=
  inferInstanceAs (Decidable (_ ∧ _))

end VendlerClass

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
@[simp]
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
@[simp]
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
@[simp]
theorem vendler_profile_roundtrip (c : VendlerClass) :
    c.toProfile.toVendlerClass = c := by
  cases c <;> rfl

/-- The canonical state profile maps to the state class. -/
@[simp]
theorem stateProfile_toClass : stateProfile.toVendlerClass = .state := rfl

/-- The canonical activity profile maps to the activity class. -/
@[simp]
theorem activityProfile_toClass : activityProfile.toVendlerClass = .activity := rfl

/-- The canonical achievement profile maps to the achievement class. -/
@[simp]
theorem achievementProfile_toClass : achievementProfile.toVendlerClass = .achievement := rfl

/-- The canonical accomplishment profile maps to the accomplishment class. -/
@[simp]
theorem accomplishmentProfile_toClass : accomplishmentProfile.toVendlerClass = .accomplishment := rfl

/-- The canonical semelfactive profile maps to the semelfactive class. -/
@[simp]
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

/-! ## Aspectual diagnostics
[vendler-1957] [dowty-1979]

The textbook test battery: *for*-X and *in*-X adverbials, the
progressive, *stop V-ing*, and the imperative. Each prediction is a
function of `VendlerClass`, and the derivation theorems show the
predictions are consequences of the three-feature decomposition
(telicity, duration, dynamicity), not independent stipulations. -/

/-- Result of applying an aspectual diagnostic: felicitous, infelicitous,
    degraded, or acceptable only under a meaning shift. -/
inductive DiagnosticResult where
  | accept    -- ✓ grammatical, acceptable
  | reject    -- ✗ ungrammatical, unacceptable
  | marginal  -- ? degraded, speaker variation
  | coerced   -- ~ acceptable with meaning shift
  deriving DecidableEq, Repr

/-- *for*-X adverbial: measures the duration of an atelic eventuality
    ("ran for an hour" ✓, \*"arrived for an hour"; "built houses for a
    year" coerces to repetition, "coughed for an hour" to iteration). -/
def forXPrediction : VendlerClass → DiagnosticResult
  | .state => .accept
  | .activity => .accept
  | .achievement => .reject
  | .accomplishment => .coerced
  | .semelfactive => .coerced

/-- *in*-X adverbial: measures time to a culmination point
    ("built the house in a year" ✓, \*"ran in an hour"). -/
def inXPrediction : VendlerClass → DiagnosticResult
  | .state => .reject
  | .activity => .reject
  | .achievement => .accept
  | .accomplishment => .accept
  | .semelfactive => .reject

/-- Progressive: requires ongoing, dynamic eventualities
    ("is running" ✓, \*"is knowing French"; "is arriving" marginal
    via preliminary stages, "is coughing" coerces to iteration). -/
def progressivePrediction : VendlerClass → DiagnosticResult
  | .state => .reject
  | .activity => .accept
  | .achievement => .marginal
  | .accomplishment => .accept
  | .semelfactive => .coerced

/-- *stop V-ing*: presupposes an ongoing eventuality that ceases
    ("stopped running" ✓; "stopped loving her" needs an inchoative
    reading, "stopped recognizing" an iterative one). -/
def stopVingPrediction : VendlerClass → DiagnosticResult
  | .state => .marginal
  | .activity => .accept
  | .achievement => .coerced
  | .accomplishment => .accept
  | .semelfactive => .coerced

/-- Imperative: requires agentive control
    ("Run!" ✓, \*"Know French!"; "Cough!" ✓). -/
def imperativePrediction : VendlerClass → DiagnosticResult
  | .state => .reject
  | .activity => .accept
  | .achievement => .marginal
  | .accomplishment => .accept
  | .semelfactive => .accept

/-- *in*-X acceptance is exactly telicity: the diagnostic follows from
    the telicity feature. -/
theorem inX_identifies_telic (c : VendlerClass) :
    inXPrediction c = .accept ↔ c.telicity = .telic := by
  cases c <;> simp [inXPrediction, VendlerClass.telicity]

/-- *for*-X acceptance is exactly atelicity plus duration: semelfactives
    are atelic but punctual, so they only accept *for*-X with iterative
    coercion. -/
theorem forX_from_features (c : VendlerClass) :
    forXPrediction c = .accept ↔
    (c.telicity = .atelic ∧ c.duration = .durative) := by
  cases c <;> simp [forXPrediction, VendlerClass.telicity, VendlerClass.duration]

/-- Semelfactive coercion under *for*-X derives from being atelic but
    punctual: atelicity licenses temporal modification, punctuality
    forces iterative reinterpretation. -/
theorem forX_semelfactive_coercion :
    forXPrediction .semelfactive = .coerced ∧
    VendlerClass.semelfactive.telicity = .atelic ∧
    VendlerClass.semelfactive.duration = .punctual := ⟨rfl, rfl, rfl⟩

/-- Progressive acceptance is exactly duration plus dynamicity: states
    fail (not dynamic), achievements and semelfactives fail (not
    durative). -/
theorem progressive_accepts_durative_dynamic (c : VendlerClass) :
    progressivePrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [progressivePrediction, VendlerClass.duration,
    VendlerClass.dynamicity]

end Features
