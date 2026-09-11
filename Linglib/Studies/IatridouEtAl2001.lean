import Linglib.Semantics.Tense.TemporalAdverbials
import Mathlib.Data.Finset.Image

/-!
# Iatridou et al. (2001): Observations about the form and meaning of the perfect

This file formalizes the perfect time span account of
[iatridou-anagnostopoulou-izvorski-2001]. A perfect introduces a time span whose left
boundary is set by the argument of a perfect-level adverbial and whose right boundary is set
by tense, the library's `Aspect.PERF_ADV`; the universal perfect asserts the underlying
eventuality at every point of the span, the existential perfect at some point (`universal`,
`existential`, the logical forms (18c) and (18e)). Point 1 follows: the universal perfect
holds at the right boundary by assertion, the utterance time in the present perfect
(`universal_at_rb`), and so *she has been sick ever since 1990 but she is fine now* is a
contradiction. Point 5 follows too: anteriority is not a component of the perfect but the
position of a bounded eventuality inside a span that ends at the tense's time
(`bounded_before_rb`), which is why the universal perfect is not anterior.

Point 2 is the classification of perfect-level adverbials by the quantification they permit
over the span (`PerfectAdverbial.quantifications`, (16)): the covert perfect-level adverbial
of an unmodified perfect is inclusive, so unmodified perfects are never universal
(`unmodified_never_universal`); *for*-adverbials are perfect-level or eventuality-level and
only perfect-level when sentence-initial, so a sentence-initial *for* yields the universal
reading alone (`forQuantifications_initial`). Point 3 is that the span is not the
Reichenbachian E–R interval: the existential reading is monotone in the span
(`existential_mono`). Point 4 predicts the universal perfect from the aspect of the participle:
only an unbounded participle can fill the span, so Greek, whose participle is perfective,
has no universal perfect while Bulgarian's imperfective and neutral participles do
(`greek_no_universal`, `bulgarian_universal`), and English nonstatives need the progressive.

## Implementation notes

* A point-level eventuality predicate is read off an event's runtime, `t ∈ e.τ`, so that the
  universal reading is inclusion of the span in the runtime and the bounded existential
  reading inclusion of the runtime in the span; the paper's *properly included* is weakened
  to inclusion, as in the library's `Aspect.PRFV`.
* `BoundaryKind` is consumed by `IatridouZeijlstra2021`.

## References

* [iatridou-anagnostopoulou-izvorski-2001]
-/

namespace IatridouEtAl2001

open Aspect Tense.TemporalAdverbials

variable {W T : Type*} [LinearOrder T]

/-! ### The perfect time span and its two readings -/

/-- Which boundary of a time span is set: the left boundary by the argument of the
perfect-level adverbial, the right boundary by tense (Section 3.1). -/
inductive BoundaryKind where
  | left
  | right
  deriving DecidableEq, Repr

/-- (18c): the universal reading, the eventuality at every point of the span, its endpoints
included. -/
def universal (P : W → Event T → Prop) : IntervalPred W T :=
  λ w pts => ∃ e, P w e ∧ ∀ t ∈ pts, t ∈ e.τ

/-- (18e): the existential reading, the eventuality at some point of the span. -/
def existential (P : W → Event T → Prop) : IntervalPred W T :=
  λ w pts => ∃ e, P w e ∧ ∃ t ∈ pts, t ∈ e.τ

/-- (44c): a bounded eventuality, asserted complete, lying inside the span. -/
def bounded (P : W → Event T → Prop) : IntervalPred W T :=
  λ w pts => ∃ e, P w e ∧ e.τ ≤ pts

variable (P : W → Event T → Prop)

theorem existential_of_universal {w : W} {pts : NonemptyInterval T} (h : universal P w pts) :
    existential P w pts :=
  let ⟨e, he, hall⟩ := h
  ⟨e, he, pts.fst, NonemptyInterval.mem_def.2 ⟨le_rfl, pts.fst_le_snd⟩, hall _
    (NonemptyInterval.mem_def.2 ⟨le_rfl, pts.fst_le_snd⟩)⟩

theorem existential_of_bounded {w : W} {pts : NonemptyInterval T} (h : bounded P w pts) :
    existential P w pts := by
  obtain ⟨e, he, hle⟩ := h
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hle
  exact ⟨e, he, e.τ.fst, NonemptyInterval.mem_def.2 ⟨h₁, e.τ.fst_le_snd.trans h₂⟩,
    NonemptyInterval.mem_def.2 ⟨le_rfl, e.τ.fst_le_snd⟩⟩

/-- Point 3: the existential reading is monotone in the span, so nothing ties the left
boundary to the eventuality; the span is not the E–R interval, and (28) has a span from 1991
around a visit in the fall of 1993. -/
theorem existential_mono {w : W} {pts pts' : NonemptyInterval T} (hle : pts ≤ pts')
    (h : existential P w pts) : existential P w pts' :=
  let ⟨e, he, t, ht, hte⟩ := h
  ⟨e, he, t, NonemptyInterval.coe_subset_coe.2 hle ht, hte⟩

/-- Point 1: on the universal reading the eventuality holds at the right boundary, the time
tense supplies, by assertion; in the present perfect that is the utterance time. -/
theorem universal_at_rb {adv : PTSConstraint T} {w : W} {t : T}
    (h : PERF_ADV (universal P) adv ⟨w, t⟩) : ∃ e, P w e ∧ t ∈ e.τ := by
  obtain ⟨pts, hrb, _, e, he, hall⟩ := h
  have hrb' : pts.snd = t := hrb
  exact ⟨e, he, hall t (NonemptyInterval.mem_def.2 ⟨hrb' ▸ pts.fst_le_snd, hrb'.ge⟩)⟩

/-- Mittwoch's observation, on the left boundary: with *since 1990* the eventuality holds in
1990 by assertion. -/
theorem universal_at_lb {t₀ : T} {w : W} {t : T}
    (h : PERF_ADV (universal P) (everSince t₀) ⟨w, t⟩) : ∃ e, P w e ∧ t₀ ∈ e.τ := by
  obtain ⟨pts, _, hlb, e, he, hall⟩ := h
  have hlb' : pts.fst = t₀ := hlb
  exact ⟨e, he, hall t₀ (NonemptyInterval.mem_def.2 ⟨hlb'.le, hlb' ▸ pts.fst_le_snd⟩)⟩

/-- Point 5: anteriority is not a component of the perfect. A bounded eventuality inside a
span that ends at the tense's time ends by that time, which in the present perfect is
pastness; the universal perfect, holding at that time, is not anterior. -/
theorem bounded_before_rb {adv : PTSConstraint T} {w : W} {t : T}
    (h : PERF_ADV (bounded P) adv ⟨w, t⟩) : ∃ e, P w e ∧ e.τ.snd ≤ t := by
  obtain ⟨pts, hrb, _, e, he, hle⟩ := h
  have hrb' : pts.snd = t := hrb
  exact ⟨e, he, hrb' ▸ (NonemptyInterval.le_def.1 hle).2⟩

/-- (44d) and (45): a bounded eventuality fills the span only by terminating exactly at its
right boundary. -/
theorem bounded_fills_iff (e : Event T) (pts : NonemptyInterval T) :
    e.τ ≤ pts ∧ pts ≤ e.τ ↔ e.τ = pts :=
  ⟨λ h => le_antisymm h.1 h.2, λ h => ⟨h.le, h.ge⟩⟩

/-! ### Perfect-level adverbials -/

/-- The quantification a perfect-level adverbial imposes over the points of the span:
durative, universal quantification, or inclusive, existential. -/
inductive Quantification where
  | durative
  | inclusive
  deriving DecidableEq, Repr

/-- The reading each quantification yields. -/
def Quantification.reading : Quantification → IntervalPred W T
  | .durative => universal P
  | .inclusive => existential P

/-- The perfect-level adverbials of (16), *lately*, and the covert adverbial of an
unmodified perfect. -/
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

/-- (16): *since* and perfect-level *for* permit the universal reading, *at least since*,
*ever since*, *always* and *for … now* require it; *lately* and the covert adverbial are
inclusive, existential closure being the default. -/
def PerfectAdverbial.quantifications : PerfectAdverbial → Finset Quantification
  | .since => {.durative, .inclusive}
  | .forDuration | .atLeastSince | .everSince | .always | .forDurationNow => {.durative}
  | .lately | .covert => {.inclusive}

/-- Section 3.2.1: unmodified perfects are never universal, the covert perfect-level
adverbial being inclusive. -/
theorem unmodified_never_universal :
    Quantification.durative ∉ PerfectAdverbial.covert.quantifications := by decide

/-- (24): *since* permits both readings whatever its position, being always perfect-level. -/
theorem since_quantifications :
    PerfectAdverbial.since.quantifications = {.durative, .inclusive} := rfl

/-- The level at which an adverbial attaches, corresponding to scope. -/
inductive Level where
  | perfectLevel
  | eventualityLevel
  deriving DecidableEq, Repr

/-- The surface position of a *for*-adverbial. -/
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

/-- The readings a *for*-adverbial permits by position. -/
def forQuantifications (pos : Position) : Finset Quantification :=
  (forLevels pos).image Level.spanQuantification

/-- (23b): sentence-initial *for* yields the universal reading only. -/
theorem forQuantifications_initial : forQuantifications .initial = {.durative} := by decide

/-- (23a): sentence-final *for* is ambiguous. -/
theorem forQuantifications_final : forQuantifications .final = {.durative, .inclusive} := by
  decide

/-! ### The aspect of the participle -/

/-- The aspects a perfect participle can be based on: the perfective asserts completion, the
imperfective and Smith's neutral do not. -/
inductive Participle where
  | perfective
  | imperfective
  | neutral
  deriving DecidableEq, Repr

/-- An unbounded participle does not assert an endpoint, so its eventuality can fill a span. -/
def Participle.Unbounded : Participle → Prop
  | .perfective => False
  | .imperfective | .neutral => True

/-- The languages of Section 3.4 with the participles on which the perfect is based. -/
inductive PerfectLanguage where
  | greek
  | bulgarian
  deriving DecidableEq, Repr

def PerfectLanguage.participles : PerfectLanguage → Finset Participle
  | .greek => {.perfective}
  | .bulgarian => {.perfective, .imperfective, .neutral}

/-- Point 4: the universal perfect is available when some participle is unbounded. -/
def UniversalAvailable (l : PerfectLanguage) : Prop := ∃ p ∈ l.participles, p.Unbounded

/-- (30) and (34): Greek's perfect participle is perfective, so there is no universal
perfect. -/
theorem greek_no_universal : ¬ UniversalAvailable .greek := by
  rintro ⟨p, hp, hu⟩
  simp only [PerfectLanguage.participles, Finset.mem_singleton] at hp
  subst hp
  exact hu

/-- (36) and (39): Bulgarian's imperfective and neutral participles yield it. -/
theorem bulgarian_universal : UniversalAvailable .bulgarian := ⟨.imperfective, by decide, trivial⟩

/-- The English forms of (42): a nonstative is progressive exactly when unbounded, while a
stative is nonprogressive either way. -/
inductive Morphology where
  | progressive
  | nonprogressive
  deriving DecidableEq, Repr

def englishForm (stative unbounded : Bool) : Morphology :=
  if !stative && unbounded then .progressive else .nonprogressive

/-- (41): a nonstative can fill the span only in the progressive. -/
theorem nonstative_unbounded_iff (unbounded : Bool) :
    englishForm false unbounded = .progressive ↔ unbounded = true := by
  cases unbounded <;> decide

end IatridouEtAl2001
