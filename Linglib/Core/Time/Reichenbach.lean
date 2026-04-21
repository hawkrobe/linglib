import Linglib.Core.Time.Domain
import Linglib.Core.Time.System

/-!
# Reichenbach's Temporal Framework
@cite{kiparsky-2002} @cite{klein-1994} @cite{reichenbach-1947}

@cite{reichenbach-1947} / @cite{klein-1994} tense–aspect parameters, extended with
@cite{kiparsky-2002}'s perspective time P.

Three (four) distinguished times:
- **S** (Speech time): When the utterance occurs
- **P** (Perspective time): Origin of temporal deixis
- **R** (Reference/Topic time): The time being talked about
- **E** (Event time): When the event occurs

Tense relates R to P; Aspect relates E to R.

## Domain bridge

`ReichenbachFrame` is the four-slot point-time record used throughout
linglib's tense modules. The `toDomain` builder lifts it to a generic
`Core.Time.Domain` (central = S, sub-TOs = [P, R, E], all as point
intervals via `TO.point`). The `*_iff_relatedByName` bridge theorems
re-express each Boolean predicate (`isPast`, `isPerfect`, …) as a
`Domain.relatedByName` query against named atom-sets from the Allen
algebra. This grounds the Reichenbach predicates in the Allen
projection function (`Interval.allenRel`) without changing the
existing four-field record — downstream call sites continue to use
`f.referenceTime`, `f.isPast`, etc., while domain-level tooling can
work with `f.toDomain` and `relatedByName`.
-/

namespace Core.Time.Reichenbach

open Core.Time (Domain NamedTO TO Orientation)
open Core.Time.AllenRelation (precedesSet equalSet)

/--
Reichenbach's temporal parameters for tense/aspect analysis,
extended with @cite{kiparsky-2002}'s perspective time P.

- `speechTime`: When the utterance is made (S)
- `perspectiveTime`: Origin of temporal deixis (P, @cite{kiparsky-2002})
- `referenceTime`: The time being talked about (R, Klein's "topic time")
- `eventTime`: When the described event occurs (E)

P = S in root clauses but diverges for flashbacks, free indirect discourse,
and embedded tenses. Tense locates R relative to P (not S).
-/
structure ReichenbachFrame (Time : Type*) where
  /-- Speech time (S): when the utterance occurs -/
  speechTime : Time
  /-- Perspective time (P): origin of temporal deixis.
      Equals S in root clauses; shifts in flashback, FID, embedded tenses. -/
  perspectiveTime : Time
  /-- Reference time (R): the time under discussion -/
  referenceTime : Time
  /-- Event time (E): when the described event occurs (E) -/
  eventTime : Time

namespace ReichenbachFrame

variable {Time : Type*} [LinearOrder Time]

/-- PAST: R < P (reference time precedes perspective time).
    @cite{kiparsky-2002}: tense locates R relative to P, not S. -/
def isPast (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.perspectiveTime

/-- PRESENT: R = P (reference time equals perspective time). -/
def isPresent (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime = f.perspectiveTime

/-- FUTURE: P < R (perspective time precedes reference time). -/
def isFuture (f : ReichenbachFrame Time) : Prop :=
  f.perspectiveTime < f.referenceTime

/-- Simple case: P = S (root clause, no perspective shift). -/
def isSimpleCase (f : ReichenbachFrame Time) : Prop :=
  f.perspectiveTime = f.speechTime

/-- Kiparsky's unmarked P–R default: P ≤ R. -/
def defaultPR (f : ReichenbachFrame Time) : Prop :=
  f.perspectiveTime ≤ f.referenceTime

/-- Kiparsky's unmarked E–R default: E ≤ R. -/
def defaultER (f : ReichenbachFrame Time) : Prop :=
  f.eventTime ≤ f.referenceTime

/-- In the simple case (P = S), isPast reduces to R < S. -/
theorem isPast_simpleCase (f : ReichenbachFrame Time) (h : f.isSimpleCase) :
    f.isPast ↔ f.referenceTime < f.speechTime := by
  simp only [isPast, isSimpleCase] at *; rw [h]

/-- Perfective: E ⊆ R (event contained in reference).
    Simplified to E = R for point-based times.
    TODO: proper interval-based perfective/imperfective distinction
    lives in `Theories/Semantics/Lexical/Verb/ViewpointAspect.lean`. -/
def isPerfective (f : ReichenbachFrame Time) : Prop :=
  f.eventTime = f.referenceTime

/-- Perfect: E < R (event precedes reference) -/
def isPerfect (f : ReichenbachFrame Time) : Prop :=
  f.eventTime < f.referenceTime

/-- Prospective: R < E (reference precedes event) -/
def isProspective (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.eventTime

-- ════════════════════════════════════════════════════
-- § Domain Bridge
-- ════════════════════════════════════════════════════

/-- The Reichenbach frame as a generic temporal `Domain` over the
    universal `Orientation` role vocabulary: central = utterance
    (S), sub-TOs = [perspective (P), topic (R), situation (E)], every
    TO a point interval (degenerate via `TO.point`). This is the
    canonical bridge from the four-field record to the
    framework-agnostic `Domain` substrate.

    Proved equal to `Domain.ofReichenbachPoints` (`toDomain_eq`); the
    four `find?` simp lemmas inherited from `Domain` then resolve all
    role lookups by `rfl`. -/
def toDomain (f : ReichenbachFrame Time) : Domain Time Orientation :=
  Domain.ofReichenbachPoints f.speechTime f.perspectiveTime
    f.referenceTime f.eventTime

@[simp] theorem toDomain_eq (f : ReichenbachFrame Time) :
    f.toDomain = Domain.ofReichenbachPoints
      f.speechTime f.perspectiveTime f.referenceTime f.eventTime := rfl

@[simp] theorem toDomain_labels (f : ReichenbachFrame Time) :
    f.toDomain.labels = Domain.reichenbachLabels := rfl

@[simp] theorem toDomain_findUtterance (f : ReichenbachFrame Time) :
    f.toDomain.find? .utterance = some (TO.point f.speechTime) := rfl

@[simp] theorem toDomain_findPerspective (f : ReichenbachFrame Time) :
    f.toDomain.find? .perspective = some (TO.point f.perspectiveTime) := rfl

@[simp] theorem toDomain_findTopic (f : ReichenbachFrame Time) :
    f.toDomain.find? .topic = some (TO.point f.referenceTime) := rfl

@[simp] theorem toDomain_findSituation (f : ReichenbachFrame Time) :
    f.toDomain.find? .situation = some (TO.point f.eventTime) := rfl

-- ──── Predicate bridges: each Boolean predicate as a `relatedByName` query ────

/-- Helper: for point intervals at times `s` and `t`, `precedesSet`
    holds iff `s < t`. -/
private theorem point_precedes_iff (s t : Time) :
    Core.Time.AllenRelation.holdsIn precedesSet (TO.point s) (TO.point t) ↔ s < t := by
  unfold precedesSet
  rw [Core.Time.AllenRelation.holdsIn_singleton]
  rfl

/-- Helper: for point intervals at times `s` and `t`, `equalSet`
    holds iff `s = t`. -/
private theorem point_equal_iff (s t : Time) :
    Core.Time.AllenRelation.holdsIn equalSet (TO.point s) (TO.point t) ↔ s = t := by
  unfold equalSet
  rw [Core.Time.AllenRelation.holdsIn_singleton]
  refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩

/-- `isPast` is exactly `topic precedes perspective` in the Allen
    algebra against the domain — the Reichenbach predicate grounded by
    construction in the Allen projection function on point intervals. -/
theorem isPast_iff_relatedByName (f : ReichenbachFrame Time) :
    f.isPast ↔ f.toDomain.relatedByName precedesSet .topic .perspective := by
  unfold isPast Domain.relatedByName Domain.relatedBy
  refine ⟨fun h => ?_, fun ⟨i, j, hi, hj, hrel⟩ => ?_⟩
  · refine ⟨TO.point f.referenceTime, TO.point f.perspectiveTime,
            toDomain_findTopic f, toDomain_findPerspective f, ?_⟩
    exact (point_precedes_iff _ _).mpr h
  · rw [toDomain_findTopic] at hi; rw [toDomain_findPerspective] at hj
    obtain ⟨rfl⟩ := Option.some.inj hi
    obtain ⟨rfl⟩ := Option.some.inj hj
    exact (point_precedes_iff _ _).mp hrel

/-- `isFuture` is exactly `perspective precedes topic` in the Allen
    algebra against the domain. -/
theorem isFuture_iff_relatedByName (f : ReichenbachFrame Time) :
    f.isFuture ↔ f.toDomain.relatedByName precedesSet .perspective .topic := by
  unfold isFuture Domain.relatedByName Domain.relatedBy
  refine ⟨fun h => ?_, fun ⟨i, j, hi, hj, hrel⟩ => ?_⟩
  · refine ⟨TO.point f.perspectiveTime, TO.point f.referenceTime,
            toDomain_findPerspective f, toDomain_findTopic f, ?_⟩
    exact (point_precedes_iff _ _).mpr h
  · rw [toDomain_findPerspective] at hi; rw [toDomain_findTopic] at hj
    obtain ⟨rfl⟩ := Option.some.inj hi
    obtain ⟨rfl⟩ := Option.some.inj hj
    exact (point_precedes_iff _ _).mp hrel

/-- `isPresent` is exactly `topic equal perspective` in the Allen
    algebra against the domain. -/
theorem isPresent_iff_relatedByName (f : ReichenbachFrame Time) :
    f.isPresent ↔ f.toDomain.relatedByName equalSet .topic .perspective := by
  unfold isPresent Domain.relatedByName Domain.relatedBy
  refine ⟨fun h => ?_, fun ⟨i, j, hi, hj, hrel⟩ => ?_⟩
  · refine ⟨TO.point f.referenceTime, TO.point f.perspectiveTime,
            toDomain_findTopic f, toDomain_findPerspective f, ?_⟩
    exact (point_equal_iff _ _).mpr h
  · rw [toDomain_findTopic] at hi; rw [toDomain_findPerspective] at hj
    obtain ⟨rfl⟩ := Option.some.inj hi
    obtain ⟨rfl⟩ := Option.some.inj hj
    exact (point_equal_iff _ _).mp hrel

/-- `isPerfect` is exactly `situation precedes topic` in the Allen
    algebra against the domain. -/
theorem isPerfect_iff_relatedByName (f : ReichenbachFrame Time) :
    f.isPerfect ↔ f.toDomain.relatedByName precedesSet .situation .topic := by
  unfold isPerfect Domain.relatedByName Domain.relatedBy
  refine ⟨fun h => ?_, fun ⟨i, j, hi, hj, hrel⟩ => ?_⟩
  · refine ⟨TO.point f.eventTime, TO.point f.referenceTime,
            toDomain_findSituation f, toDomain_findTopic f, ?_⟩
    exact (point_precedes_iff _ _).mpr h
  · rw [toDomain_findSituation] at hi; rw [toDomain_findTopic] at hj
    obtain ⟨rfl⟩ := Option.some.inj hi
    obtain ⟨rfl⟩ := Option.some.inj hj
    exact (point_precedes_iff _ _).mp hrel

/-- `isProspective` is exactly `topic precedes situation` in the Allen
    algebra against the domain. -/
theorem isProspective_iff_relatedByName (f : ReichenbachFrame Time) :
    f.isProspective ↔ f.toDomain.relatedByName precedesSet .topic .situation := by
  unfold isProspective Domain.relatedByName Domain.relatedBy
  refine ⟨fun h => ?_, fun ⟨i, j, hi, hj, hrel⟩ => ?_⟩
  · refine ⟨TO.point f.referenceTime, TO.point f.eventTime,
            toDomain_findTopic f, toDomain_findSituation f, ?_⟩
    exact (point_precedes_iff _ _).mpr h
  · rw [toDomain_findTopic] at hi; rw [toDomain_findSituation] at hj
    obtain ⟨rfl⟩ := Option.some.inj hi
    obtain ⟨rfl⟩ := Option.some.inj hj
    exact (point_precedes_iff _ _).mp hrel

/-- `isPerfective` is exactly `situation equal topic` in the Allen
    algebra against the domain. (For the point-time approximation; the
    proper interval-based perfective/imperfective distinction lives in
    `Theories/Semantics/Lexical/Verb/ViewpointAspect.lean`.) -/
theorem isPerfective_iff_relatedByName (f : ReichenbachFrame Time) :
    f.isPerfective ↔ f.toDomain.relatedByName equalSet .situation .topic := by
  unfold isPerfective Domain.relatedByName Domain.relatedBy
  refine ⟨fun h => ?_, fun ⟨i, j, hi, hj, hrel⟩ => ?_⟩
  · refine ⟨TO.point f.eventTime, TO.point f.referenceTime,
            toDomain_findSituation f, toDomain_findTopic f, ?_⟩
    exact (point_equal_iff _ _).mpr h
  · rw [toDomain_findSituation] at hi; rw [toDomain_findTopic] at hj
    obtain ⟨rfl⟩ := Option.some.inj hi
    obtain ⟨rfl⟩ := Option.some.inj hj
    exact (point_equal_iff _ _).mp hrel

end ReichenbachFrame

-- ════════════════════════════════════════════════════
-- § TenseSystem and AspectSystem Instances
-- ════════════════════════════════════════════════════

/-! Reichenbach as a `Core.Time.TenseSystem` (anchor = P, situation = R)
    and `Core.Time.AspectSystem` (event = E, reference = R) instance.
    The instances commit Reichenbach to the `Orientation` role
    vocabulary so generic Domain-level tooling (e.g.
    `relatedByName`-driven analyses) can dispatch over any tense or
    aspect framework. The concrete `isPast`/`isPerfect`/etc.
    predicates remain on `ReichenbachFrame`; the Allen bridges above
    (`*_iff_relatedByName`) show how they project into the algebra. -/

instance reichenbachFrame_tenseSystem {Time : Type*} [LinearOrder Time] :
    Core.Time.TenseSystem (ReichenbachFrame Time) Time Orientation where
  toDomain := ReichenbachFrame.toDomain
  anchor := .perspective
  situation := .topic

instance reichenbachFrame_aspectSystem {Time : Type*} [LinearOrder Time] :
    Core.Time.AspectSystem (ReichenbachFrame Time) Time Orientation where
  toDomain := ReichenbachFrame.toDomain
  event := .situation
  reference := .topic

end Core.Time.Reichenbach
