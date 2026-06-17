import Linglib.Semantics.Tense.Defs
import Linglib.Semantics.Tense.Domain
import Linglib.Semantics.Tense.System

/-!
# Reichenbach's Temporal Framework
[kiparsky-2002] [klein-1994] [reichenbach-1947]

[reichenbach-1947] / [klein-1994] tense–aspect parameters, extended with
[kiparsky-2002]'s perspective time P.

Three (four) distinguished times:
- **S** (Speech time): When the utterance occurs
- **P** (Perspective time): Origin of temporal deixis
- **R** (Reference/Topic time): The time being talked about
- **E** (Event time): When the event occurs

Tense relates R to P; Aspect relates E to R.

## Domain bridge

`ReichenbachFrame` is the four-slot point-time record used throughout
linglib's tense modules. The `toDomain` builder lifts it to a generic
`Tense.Domain` (central = S, sub-TOs = [P, R, E], all as point
intervals via `TO.pure`). The `*_iff_relatedByName` bridge theorems
re-express each predicate (`isPast`, `isPerfect`, …) as a
`Domain.relatedByName` query against named atom-sets from the Allen
algebra. This grounds the Reichenbach predicates in the Allen
projection function (`NonemptyInterval.allenRel`) without changing the
existing four-field record — downstream call sites continue to use
`f.referenceTime`, `f.isPast`, etc., while domain-level tooling can
work with `f.toDomain` and `relatedByName`.
-/

open Tense (Domain Orientation TO)
open AllenRelation (precedesSet equalSet)

namespace Time

/--
Reichenbach's temporal parameters for tense/aspect analysis,
extended with [kiparsky-2002]'s perspective time P.

- `speechTime`: When the utterance is made (S)
- `perspectiveTime`: Origin of temporal deixis (P, [kiparsky-2002])
- `referenceTime`: The time being talked about (R, Klein's "topic time")
- `eventTime`: When the described event occurs (E)

P = S in root clauses but diverges for flashbacks, free indirect discourse,
and embedded tenses. Tense locates R relative to P (not S).
-/
structure ReichenbachFrame (T : Type*) where
  /-- Speech time (S): when the utterance occurs -/
  speechTime : T
  /-- Perspective time (P): origin of temporal deixis.
      Equals S in root clauses; shifts in flashback, FID, embedded tenses. -/
  perspectiveTime : T
  /-- Reference time (R): the time under discussion -/
  referenceTime : T
  /-- Event time (E): when the described event occurs (E) -/
  eventTime : T

namespace ReichenbachFrame

variable {T : Type*} [LinearOrder T]

/-- PAST: R < P (reference time precedes perspective time) — a view of
    `Core.Order.holds Tense.past`. [kiparsky-2002]: tense locates R relative to P, not S. -/
def isPast (f : ReichenbachFrame T) : Prop :=
  Core.Order.holds Tense.past f.referenceTime f.perspectiveTime

/-- PRESENT: R = P (reference time equals perspective time). Present is the one tense that
    needs no ordering, so it stays the bare equality (frame predicates over unordered time keep
    typechecking); it is definitionally `Core.Order.holds Tense.present`. -/
def isPresent (f : ReichenbachFrame T) : Prop :=
  f.referenceTime = f.perspectiveTime

/-- FUTURE: P < R (perspective time precedes reference time). -/
def isFuture (f : ReichenbachFrame T) : Prop :=
  Core.Order.holds Tense.future f.referenceTime f.perspectiveTime

/-- NONPAST: P ≤ R (present or future) ([klecha-2016]) — the view of
    `Core.Order.holds Tense.nonpast`. Completes the four-way relation on frames. -/
def isNonpast (f : ReichenbachFrame T) : Prop :=
  Core.Order.holds Tense.nonpast f.referenceTime f.perspectiveTime

/-- Simple case: P = S (root clause, no perspective shift). -/
def isSimpleCase (f : ReichenbachFrame T) : Prop :=
  f.perspectiveTime = f.speechTime

/-- Kiparsky's unmarked P–R default: P ≤ R. -/
def defaultPR (f : ReichenbachFrame T) : Prop :=
  f.perspectiveTime ≤ f.referenceTime

/-- Kiparsky's unmarked E–R default: E ≤ R. -/
def defaultER (f : ReichenbachFrame T) : Prop :=
  f.eventTime ≤ f.referenceTime

/-- Perfective: E ⊆ R (event contained in reference).
    Simplified to E = R for point-based times.
    TODO: proper interval-based perfective/imperfective distinction
    lives in `Semantics/Aspect/Basic.lean` (`ViewpointAspectB`). -/
def isPerfective (f : ReichenbachFrame T) : Prop :=
  f.eventTime = f.referenceTime

/-- Perfect: E < R (event precedes reference) -/
def isPerfect (f : ReichenbachFrame T) : Prop :=
  f.eventTime < f.referenceTime

/-- Prospective: R < E (reference precedes event) -/
def isProspective (f : ReichenbachFrame T) : Prop :=
  f.referenceTime < f.eventTime

/-! ### Unfolding lemmas and decidability

One `_def` simp lemma and one `Decidable` instance per predicate, so
consumers can close concrete goals with `decide` and rewrite with
`simp only [isPast_def]` instead of unfolding definitions by hand. -/

@[simp] theorem isPast_def (f : ReichenbachFrame T) :
    f.isPast ↔ f.referenceTime < f.perspectiveTime :=
  Core.Order.holds_before f.referenceTime f.perspectiveTime

omit [LinearOrder T] in
@[simp] theorem isPresent_def (f : ReichenbachFrame T) :
    f.isPresent ↔ f.referenceTime = f.perspectiveTime := Iff.rfl

@[simp] theorem isFuture_def (f : ReichenbachFrame T) :
    f.isFuture ↔ f.perspectiveTime < f.referenceTime :=
  Core.Order.holds_after f.referenceTime f.perspectiveTime

@[simp] theorem isNonpast_def (f : ReichenbachFrame T) :
    f.isNonpast ↔ f.perspectiveTime ≤ f.referenceTime :=
  Core.Order.holds_notBefore f.referenceTime f.perspectiveTime

omit [LinearOrder T] in
@[simp] theorem isSimpleCase_def (f : ReichenbachFrame T) :
    f.isSimpleCase ↔ f.perspectiveTime = f.speechTime := Iff.rfl

@[simp] theorem defaultPR_def (f : ReichenbachFrame T) :
    f.defaultPR ↔ f.perspectiveTime ≤ f.referenceTime := Iff.rfl

@[simp] theorem defaultER_def (f : ReichenbachFrame T) :
    f.defaultER ↔ f.eventTime ≤ f.referenceTime := Iff.rfl

omit [LinearOrder T] in
@[simp] theorem isPerfective_def (f : ReichenbachFrame T) :
    f.isPerfective ↔ f.eventTime = f.referenceTime := Iff.rfl

@[simp] theorem isPerfect_def (f : ReichenbachFrame T) :
    f.isPerfect ↔ f.eventTime < f.referenceTime := Iff.rfl

@[simp] theorem isProspective_def (f : ReichenbachFrame T) :
    f.isProspective ↔ f.referenceTime < f.eventTime := Iff.rfl

/-- In the simple case (P = S), `isPast` reduces to R < S. -/
theorem isPast_simpleCase (f : ReichenbachFrame T) (h : f.isSimpleCase) :
    f.isPast ↔ f.referenceTime < f.speechTime := by
  simp only [isPast_def, isSimpleCase_def] at h ⊢
  rw [h]

instance (f : ReichenbachFrame T) : Decidable f.isPast := by
  unfold isPast; infer_instance

instance (f : ReichenbachFrame T) : Decidable f.isPresent :=
  inferInstanceAs (Decidable (f.referenceTime = f.perspectiveTime))

instance (f : ReichenbachFrame T) : Decidable f.isFuture := by
  unfold isFuture; infer_instance

instance (f : ReichenbachFrame T) : Decidable f.isNonpast := by
  unfold isNonpast; infer_instance

instance (f : ReichenbachFrame T) : Decidable f.isSimpleCase :=
  inferInstanceAs (Decidable (f.perspectiveTime = f.speechTime))

instance (f : ReichenbachFrame T) : Decidable f.defaultPR :=
  inferInstanceAs (Decidable (f.perspectiveTime ≤ f.referenceTime))

instance (f : ReichenbachFrame T) : Decidable f.defaultER :=
  inferInstanceAs (Decidable (f.eventTime ≤ f.referenceTime))

instance (f : ReichenbachFrame T) : Decidable f.isPerfective :=
  inferInstanceAs (Decidable (f.eventTime = f.referenceTime))

instance (f : ReichenbachFrame T) : Decidable f.isPerfect :=
  inferInstanceAs (Decidable (f.eventTime < f.referenceTime))

instance (f : ReichenbachFrame T) : Decidable f.isProspective :=
  inferInstanceAs (Decidable (f.referenceTime < f.eventTime))

/-! ### Domain Bridge -/

/-- The Reichenbach frame as a generic temporal `Domain` over the
    universal `Orientation` role vocabulary: central = utterance
    (S), sub-TOs = [perspective (P), topic (R), situation (E)], every
    TO a point interval (degenerate via `TO.pure`). This is the
    canonical bridge from the four-field record to the
    framework-agnostic `Domain` substrate.

    Proved equal to `Domain.ofReichenbachPoints` (`toDomain_eq`); the
    four `find?` simp lemmas inherited from `Domain` then resolve all
    role lookups by `rfl`. -/
def toDomain (f : ReichenbachFrame T) : Domain T Orientation :=
  Domain.ofReichenbachPoints f.speechTime f.perspectiveTime
    f.referenceTime f.eventTime

@[simp] theorem toDomain_eq (f : ReichenbachFrame T) :
    f.toDomain = Domain.ofReichenbachPoints
      f.speechTime f.perspectiveTime f.referenceTime f.eventTime := rfl

@[simp] theorem toDomain_labels (f : ReichenbachFrame T) :
    f.toDomain.labels = Domain.reichenbachLabels := rfl

@[simp] theorem toDomain_findUtterance (f : ReichenbachFrame T) :
    f.toDomain.find? .utterance = some (TO.pure f.speechTime) := rfl

@[simp] theorem toDomain_findPerspective (f : ReichenbachFrame T) :
    f.toDomain.find? .perspective = some (TO.pure f.perspectiveTime) := rfl

@[simp] theorem toDomain_findTopic (f : ReichenbachFrame T) :
    f.toDomain.find? .topic = some (TO.pure f.referenceTime) := rfl

@[simp] theorem toDomain_findSituation (f : ReichenbachFrame T) :
    f.toDomain.find? .situation = some (TO.pure f.eventTime) := rfl

-- ──── Predicate bridges: each predicate as a `relatedByName` query ────

/-- `isPast` is exactly `topic precedes perspective` in the Allen
    algebra against the domain — the Reichenbach predicate grounded by
    construction in the Allen projection function on point intervals. -/
theorem isPast_iff_relatedByName (f : ReichenbachFrame T) :
    f.isPast ↔ f.toDomain.relatedByName precedesSet .topic .perspective := by
  rw [isPast_def,
    Domain.relatedByName_iff precedesSet (toDomain_findTopic f) (toDomain_findPerspective f)]
  exact (TO.pure_precedes_iff _ _).symm

/-- `isFuture` is exactly `perspective precedes topic` in the Allen
    algebra against the domain. -/
theorem isFuture_iff_relatedByName (f : ReichenbachFrame T) :
    f.isFuture ↔ f.toDomain.relatedByName precedesSet .perspective .topic := by
  rw [isFuture_def,
    Domain.relatedByName_iff precedesSet (toDomain_findPerspective f) (toDomain_findTopic f)]
  exact (TO.pure_precedes_iff _ _).symm

/-- `isPresent` is exactly `topic equal perspective` in the Allen
    algebra against the domain. -/
theorem isPresent_iff_relatedByName (f : ReichenbachFrame T) :
    f.isPresent ↔ f.toDomain.relatedByName equalSet .topic .perspective := by
  rw [Domain.relatedByName_iff equalSet (toDomain_findTopic f) (toDomain_findPerspective f)]
  exact (TO.pure_equal_iff _ _).symm

/-- `isPerfect` is exactly `situation precedes topic` in the Allen
    algebra against the domain. -/
theorem isPerfect_iff_relatedByName (f : ReichenbachFrame T) :
    f.isPerfect ↔ f.toDomain.relatedByName precedesSet .situation .topic := by
  rw [Domain.relatedByName_iff precedesSet (toDomain_findSituation f) (toDomain_findTopic f)]
  exact (TO.pure_precedes_iff _ _).symm

/-- `isProspective` is exactly `topic precedes situation` in the Allen
    algebra against the domain. -/
theorem isProspective_iff_relatedByName (f : ReichenbachFrame T) :
    f.isProspective ↔ f.toDomain.relatedByName precedesSet .topic .situation := by
  rw [Domain.relatedByName_iff precedesSet (toDomain_findTopic f) (toDomain_findSituation f)]
  exact (TO.pure_precedes_iff _ _).symm

/-- `isPerfective` is exactly `situation equal topic` in the Allen
    algebra against the domain. (For the point-time approximation; the
    proper interval-based perfective/imperfective distinction lives in
    `Semantics/Lexical/Verb/ViewpointAspect.lean`.) -/
theorem isPerfective_iff_relatedByName (f : ReichenbachFrame T) :
    f.isPerfective ↔ f.toDomain.relatedByName equalSet .situation .topic := by
  rw [Domain.relatedByName_iff equalSet (toDomain_findSituation f) (toDomain_findTopic f)]
  exact (TO.pure_equal_iff _ _).symm

end ReichenbachFrame

/-! ### TenseSystem and AspectSystem Instances -/

/-! Reichenbach as a `TenseSystem` (anchor = P, situation = R)
    and `AspectSystem` (event = E, reference = R) instance.
    The instances commit Reichenbach to the `Orientation` role
    vocabulary so generic Domain-level tooling (e.g.
    `relatedByName`-driven analyses) can dispatch over any tense or
    aspect framework. The concrete `isPast`/`isPerfect`/etc.
    predicates remain on `ReichenbachFrame`; the Allen bridges above
    (`*_iff_relatedByName`) show how they project into the algebra. -/

instance reichenbachFrame_tenseSystem {T : Type*} [LinearOrder T] :
    TenseSystem (ReichenbachFrame T) T Orientation where
  toDomain := ReichenbachFrame.toDomain
  anchor := .perspective
  located := .topic
  anchor_mem := fun f => by
    rw [ReichenbachFrame.toDomain_labels]
    decide

instance reichenbachFrame_aspectSystem {T : Type*} [LinearOrder T] :
    AspectSystem (ReichenbachFrame T) T Orientation where
  toDomain := ReichenbachFrame.toDomain
  event := .situation
  reference := .topic

/-! ### Generic-predicate specializations

The generic `TenseSystem`/`AspectSystem` predicates agree with the
concrete `ReichenbachFrame` predicates — the frame is the point-time
specialization of the interval-native generic layer. -/

section GenericSpecialization

variable {T : Type*} [LinearOrder T]

@[simp] theorem tenseSystem_isPast_iff (f : ReichenbachFrame T) :
    TenseSystem.isPast f ↔ f.isPast :=
  (ReichenbachFrame.isPast_iff_relatedByName f).symm

@[simp] theorem tenseSystem_isPresent_iff (f : ReichenbachFrame T) :
    TenseSystem.isPresent f ↔ f.isPresent :=
  (ReichenbachFrame.isPresent_iff_relatedByName f).symm

@[simp] theorem tenseSystem_isFuture_iff (f : ReichenbachFrame T) :
    TenseSystem.isFuture f ↔ f.isFuture :=
  (ReichenbachFrame.isFuture_iff_relatedByName f).symm

@[simp] theorem aspectSystem_isPerfect_iff (f : ReichenbachFrame T) :
    AspectSystem.isPerfect f ↔ f.isPerfect :=
  (ReichenbachFrame.isPerfect_iff_relatedByName f).symm

@[simp] theorem aspectSystem_isPerfective_iff (f : ReichenbachFrame T) :
    AspectSystem.isPerfective f ↔ f.isPerfective :=
  (ReichenbachFrame.isPerfective_iff_relatedByName f).symm

@[simp] theorem aspectSystem_isProspective_iff (f : ReichenbachFrame T) :
    AspectSystem.isProspective f ↔ f.isProspective :=
  (ReichenbachFrame.isProspective_iff_relatedByName f).symm

/-- **Point frames cannot be imperfective.** [klein-1994]'s imperfective
    (TT properly inside TSit) requires a non-degenerate interval, and
    every `ReichenbachFrame` TO is a point. The audit-level claim that
    "the imperfective is unrepresentable in the point-frame core" is
    here a theorem, not a docstring. -/
theorem ReichenbachFrame.not_aspectSystem_isImperfective
    (f : ReichenbachFrame T) : ¬ AspectSystem.isImperfective f := by
  rintro ⟨i, j, hi, hj, hrel⟩
  have hi' : f.toDomain.find? .topic = some i := hi
  have hj' : f.toDomain.find? .situation = some j := hj
  rw [ReichenbachFrame.toDomain_findTopic] at hi'
  rw [ReichenbachFrame.toDomain_findSituation] at hj'
  obtain rfl := Option.some.inj hi'
  obtain rfl := Option.some.inj hj'
  exact TO.not_pure_properContainment _ _ hrel

end GenericSpecialization

end Time
