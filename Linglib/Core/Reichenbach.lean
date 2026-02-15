import Mathlib.Order.Basic

/-!
# Reichenbach's Temporal Framework

Reichenbach (1947) / Klein (1994) tense–aspect parameters, extended with
Kiparsky's (2002) perspective time P.

Three (four) distinguished times:
- **S** (Speech time): When the utterance occurs
- **P** (Perspective time): Origin of temporal deixis (Kiparsky 2002)
- **R** (Reference/Topic time): The time being talked about
- **E** (Event time): When the event occurs

Tense relates R to P; Aspect relates E to R.

## References

- Reichenbach, H. (1947). Elements of Symbolic Logic.
- Klein, W. (1994). Time in Language.
- Kiparsky, P. (2002). Event structure and the perfect.
-/

namespace Core.Reichenbach

/--
Reichenbach's temporal parameters for tense/aspect analysis,
extended with Kiparsky's (2002) perspective time P.

- `speechTime`: When the utterance is made (S)
- `perspectiveTime`: Origin of temporal deixis (P, Kiparsky 2002)
- `referenceTime`: The time being talked about (R, Klein's "topic time")
- `eventTime`: When the described event occurs (E)

P = S in root clauses but diverges for flashbacks, free indirect discourse,
and embedded tenses. Tense locates R relative to P (not S).
-/
structure ReichenbachFrame (Time : Type*) where
  /-- Speech time (S): when the utterance occurs -/
  speechTime : Time
  /-- Perspective time (P): origin of temporal deixis (Kiparsky 2002).
      Equals S in root clauses; shifts in flashback, FID, embedded tenses. -/
  perspectiveTime : Time
  /-- Reference time (R): the time under discussion -/
  referenceTime : Time
  /-- Event time (E): when the event takes place -/
  eventTime : Time

namespace ReichenbachFrame

variable {Time : Type*} [LinearOrder Time]

/-- PAST: R < P (reference time precedes perspective time).
    Kiparsky (2002): tense locates R relative to P, not S. -/
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

/-- Perfective: E ⊆ R (event contained in reference) -/
def isPerfective (f : ReichenbachFrame Time) : Prop :=
  f.eventTime = f.referenceTime  -- Simplified: E = R

/-- Imperfective: R ⊆ E (reference contained in event) -/
def isImperfective (f : ReichenbachFrame Time) : Prop :=
  f.eventTime = f.referenceTime  -- Simplified: needs intervals for proper treatment

/-- Perfect: E < R (event precedes reference) -/
def isPerfect (f : ReichenbachFrame Time) : Prop :=
  f.eventTime < f.referenceTime

/-- Prospective: R < E (reference precedes event) -/
def isProspective (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.eventTime

end ReichenbachFrame

end Core.Reichenbach
