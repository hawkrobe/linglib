module

public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Aspect.Viewpoint
public import Mathlib.Data.Finset.Image

/-!
# Iatridou et al. (2001): Observations about the form and meaning of the perfect

Iatridou, Anagnostopoulou and Izvorski account for the perfect with a perfect time span, whose
left boundary the argument of a perfect-level adverbial sets and whose right boundary tense
sets. The universal perfect asserts the underlying eventuality at every point of the span and
the existential perfect at some point. The universal perfect therefore holds at the right
boundary, the utterance time in the present perfect, and anteriority is not part of the perfect
but the position of a bounded eventuality inside a span ending at the time of tense.
Perfect-level adverbials differ in the quantification over the span they permit, and the
covert adverbial of an unmodified perfect is inclusive. Only an unbounded participle can fill
the span, so Greek, whose participle is perfective, has no universal perfect.

## Main statements

* `universal_at_rb`: the universal perfect holds at the right boundary.
* `bounded_before_rb`: a bounded eventuality ends by the right boundary.
* `unmodified_never_universal`: unmodified perfects are never universal.
* `forQuantifications_initial`: sentence-initial *for* yields only the universal reading.
* `greek_no_universal`: Greek has no universal perfect.

## Implementation notes

* A point-level eventuality predicate is read off an event's runtime, `t ∈ τ e`, so that the
  universal reading is inclusion of the span in the runtime and the bounded existential
  reading inclusion of the runtime in the span; the paper's *properly included* is weakened
  to inclusion, as in the library's `Aspect.PRFV`.

## References

* [iatridou-anagnostopoulou-izvorski-2001]
-/

@[expose] public section

namespace IatridouEtAl2001

open Event (τ)

open Aspect

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### The perfect time span and its two readings -/

/-- The universal reading, (18c), asserts the eventuality at every point of the span, its
endpoints included. -/
def universal (P : W → E → Prop) : IntervalPred W T :=
  fun w pts ↦ ∃ e, P w e ∧ ∀ t ∈ pts, t ∈ (τ e)

/-- The existential reading, (18e), asserts the eventuality at some point of the span. -/
def existential (P : W → E → Prop) : IntervalPred W T :=
  fun w pts ↦ ∃ e, P w e ∧ ∃ t ∈ pts, t ∈ (τ e)

/-- A bounded eventuality, (44c), is asserted complete and lies inside the span. -/
def bounded (P : W → E → Prop) : IntervalPred W T :=
  fun w pts ↦ ∃ e, P w e ∧ τ e ≤ pts

variable (P : W → E → Prop)

theorem existential_of_universal {w : W} {pts : NonemptyInterval T} (h : universal P w pts) :
    existential P w pts :=
  let ⟨e, he, hall⟩ := h
  ⟨e, he, pts.fst, NonemptyInterval.mem_def.2 ⟨le_rfl, pts.fst_le_snd⟩, hall _
    (NonemptyInterval.mem_def.2 ⟨le_rfl, pts.fst_le_snd⟩)⟩

theorem existential_of_bounded {w : W} {pts : NonemptyInterval T} (h : bounded P w pts) :
    existential P w pts := by
  obtain ⟨e, he, hle⟩ := h
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hle
  exact ⟨e, he, (τ e).fst, NonemptyInterval.mem_def.2 ⟨h₁, (τ e).fst_le_snd.trans h₂⟩,
    NonemptyInterval.mem_def.2 ⟨le_rfl, (τ e).fst_le_snd⟩⟩

/-- The existential reading is monotone in the span, Point 3, so nothing ties the left
boundary to the eventuality; the span is not the E–R interval, and (28) has a span from 1991
around a visit in the fall of 1993. -/
theorem existential_mono {w : W} {pts pts' : NonemptyInterval T} (hle : pts ≤ pts')
    (h : existential P w pts) : existential P w pts' :=
  let ⟨e, he, t, ht, hte⟩ := h
  ⟨e, he, t, NonemptyInterval.coe_subset_coe.2 hle ht, hte⟩

/-- On the universal reading the eventuality holds at the right boundary, the time
tense supplies, by assertion, Point 1; in the present perfect that is the utterance time. -/
theorem universal_at_rb {adv : NonemptyInterval T → Prop} {w : W} {t : T}
    (h : PERF_ADV (universal P) adv ⟨w, t⟩) : ∃ e, P w e ∧ t ∈ (τ e) := by
  obtain ⟨pts, _, hrb, e, he, hall⟩ := h
  have hrb' : pts.snd = t := hrb
  exact ⟨e, he, hall t (NonemptyInterval.mem_def.2 ⟨hrb' ▸ pts.fst_le_snd, hrb'.ge⟩)⟩

/-- On the left boundary, as Mittwoch observes, with *since 1990* the eventuality holds in
1990 by assertion. -/
theorem universal_at_lb {t₀ : T} {w : W} {t : T}
    (h : PERF_ADV (universal P) (LB t₀) ⟨w, t⟩) : ∃ e, P w e ∧ t₀ ∈ (τ e) := by
  obtain ⟨pts, hlb, _, e, he, hall⟩ := h
  have hlb' : pts.fst = t₀ := hlb
  exact ⟨e, he, hall t₀ (NonemptyInterval.mem_def.2 ⟨hlb'.le, hlb' ▸ pts.fst_le_snd⟩)⟩

/-- Anteriority is not a component of the perfect, Point 5. A bounded eventuality inside a
span that ends at the tense's time ends by that time, which in the present perfect is
pastness; the universal perfect, holding at that time, is not anterior. -/
theorem bounded_before_rb {adv : NonemptyInterval T → Prop} {w : W} {t : T}
    (h : PERF_ADV (bounded P) adv ⟨w, t⟩) : ∃ e, P w e ∧ (τ e).snd ≤ t := by
  obtain ⟨pts, _, hrb, e, he, hle⟩ := h
  have hrb' : pts.snd = t := hrb
  exact ⟨e, he, hrb' ▸ (NonemptyInterval.le_def.1 hle).2⟩

/-- A bounded eventuality fills the span only by terminating exactly at its right boundary, (44d)
and (45). -/
theorem bounded_fills_iff (e : E) (pts : NonemptyInterval T) :
    τ e ≤ pts ∧ pts ≤ τ e ↔ τ e = pts :=
  ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩

/-! ### Perfect-level adverbials -/

/-- A `Quantification` is what a perfect-level adverbial imposes over the points of the span,
durative and universal or inclusive and existential. -/
inductive Quantification where
  | durative
  | inclusive
  deriving DecidableEq, Repr

/-- `q.reading` is the reading that the quantification `q` yields. -/
def Quantification.reading : Quantification → IntervalPred W T
  | .durative => universal P
  | .inclusive => existential P

/-- A `PerfectAdverbial` is one of the perfect-level adverbials of (16), *lately*, or the covert
adverbial of an unmodified perfect. -/
inductive PerfectAdverbial where
  | since
  | forDuration
  | atLeastSince
  | everSince
  | always
  | forDurationNow
  | lately
  | covert
  deriving DecidableEq, Repr

/-- By (16), *since* and perfect-level *for* permit the universal reading, *at least since*,
*ever since*, *always* and *for … now* require it; *lately* and the covert adverbial are
inclusive, existential closure being the default. -/
def PerfectAdverbial.quantifications : PerfectAdverbial → Finset Quantification
  | .since => {.durative, .inclusive}
  | .forDuration | .atLeastSince | .everSince | .always | .forDurationNow => {.durative}
  | .lately | .covert => {.inclusive}

/-- Unmodified perfects are never universal, since the covert perfect-level adverbial is
inclusive. -/
theorem unmodified_never_universal :
    Quantification.durative ∉ PerfectAdverbial.covert.quantifications := by decide

/-- *Since* permits both readings whatever its position, being always perfect-level, (24). -/
theorem since_quantifications :
    PerfectAdverbial.since.quantifications = {.durative, .inclusive} := rfl

/-- A `Level` is the level at which an adverbial attaches, which corresponds to scope. -/
inductive Level where
  | perfectLevel
  | eventualityLevel
  deriving DecidableEq, Repr

/-- A `Position` is the surface position of a *for*-adverbial. -/
inductive Position where
  | initial
  | final
  deriving DecidableEq, Repr

/-- A sentence-initial *for*-adverbial has merged above the eventuality and is perfect-level;
a sentence-final one may be either. -/
def forLevels : Position → Finset Level
  | .initial => {.perfectLevel}
  | .final => {.perfectLevel, .eventualityLevel}

/-- A perfect-level *for* is durative; an eventuality-level *for* leaves the covert inclusive
perfect-level adverbial in charge of the span. -/
def Level.spanQuantification : Level → Quantification
  | .perfectLevel => .durative
  | .eventualityLevel => .inclusive

/-- `forQuantifications p` are the readings a *for*-adverbial permits in the position `p`. -/
def forQuantifications (pos : Position) : Finset Quantification :=
  (forLevels pos).image Level.spanQuantification

/-- Sentence-initial *for* yields the universal reading only, (23b). -/
theorem forQuantifications_initial : forQuantifications .initial = {.durative} := by decide

/-- Sentence-final *for* is ambiguous, (23a). -/
theorem forQuantifications_final : forQuantifications .final = {.durative, .inclusive} := by
  decide

/-! ### The aspect of the participle -/

/-- A `Participle` is an aspect that a perfect participle can be based on; the perfective
asserts completion, and the imperfective and Smith's neutral do not. -/
inductive Participle where
  | perfective
  | imperfective
  | neutral
  deriving DecidableEq, Repr

/-- An unbounded participle does not assert an endpoint, so its eventuality can fill a span. -/
def Participle.Unbounded : Participle → Prop
  | .perfective => False
  | .imperfective | .neutral => True

/-- A `PerfectLanguage` is one of the languages of Section 3.4, with the participles on which its
perfect is based. -/
inductive PerfectLanguage where
  | greek
  | bulgarian
  deriving DecidableEq, Repr

def PerfectLanguage.participles : PerfectLanguage → Finset Participle
  | .greek => {.perfective}
  | .bulgarian => {.perfective, .imperfective, .neutral}

/-- The universal perfect is available when some participle is unbounded, Point 4. -/
def UniversalAvailable (l : PerfectLanguage) : Prop := ∃ p ∈ l.participles, p.Unbounded

/-- Greek's perfect participle is perfective, so there is no universal perfect, (30) and (34). -/
theorem greek_no_universal : ¬ UniversalAvailable .greek := by
  rintro ⟨p, hp, hu⟩
  simp only [PerfectLanguage.participles, Finset.mem_singleton] at hp
  subst hp
  exact hu

/-- Bulgarian's imperfective and neutral participles yield the universal perfect, (36) and
(39). -/
theorem bulgarian_universal : UniversalAvailable .bulgarian := ⟨.imperfective, by decide, trivial⟩

/-- In the English forms of (42) a nonstative is progressive exactly when unbounded, while a
stative is nonprogressive either way. -/
inductive Morphology where
  | progressive
  | nonprogressive
  deriving DecidableEq, Repr

def englishForm (stative unbounded : Bool) : Morphology :=
  if !stative && unbounded then .progressive else .nonprogressive

/-- A nonstative can fill the span only in the progressive, (41). -/
theorem nonstative_unbounded_iff (unbounded : Bool) :
    englishForm false unbounded = .progressive ↔ unbounded = true := by
  cases unbounded <;> decide

end IatridouEtAl2001
