import Linglib.Semantics.Tense.Defs

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

-/

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
    lives in `Semantics/Aspect/Basic.lean` (`Perfectivity`). -/
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

end ReichenbachFrame

end Time
