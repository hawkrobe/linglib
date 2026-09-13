import Linglib.Studies.Anscombe1964
import Linglib.Semantics.Degree.Basic

/-!
# Rett (2020): Eliminating EARLIEST: a general semantics for before and after

This file formalizes the paper's semantics for *before* and *after* as antonyms over converse
scales. Each relates some time of its main clause to the most informative time of its embedded
clause, the least on the *before* scale and the greatest on the *after* scale, `before` and
`after`, with maximality relativized to the scale as in the degree domain,
`Degree.maxOnScale`. Two aspectual coercions supply the remaining readings: a process may
denote the onset of its duration, `inchoative`, and a culmination its telos, `completive`, so
that against a process an *after* clause is ambiguous between the end and the onset while a
*before* clause is not, and against a culmination a *before* clause is ambiguous between the
start and the telos while an *after* clause is not: the six readings of the paper's Table 1
and no seventh, `before_process`, `before_culmination_telos`, `after_process_onset`,
`after_culmination`, instantiated by the paper's (23) and (24). The default readings are
downward entailing in the embedded clause, `before_antitone` and `after_antitone`, the
account's route to NPI licensing, and the coerced readings are not,
`not_before_completive_antitone`. Anscombe's *before*, a time of the main clause before every
time of the embedded clause, is the default reading whenever the embedded clause has a first
time, `before_iff_beforeEver`.

## Implementation notes

Run times are the substrate's `RunTimes`, sets of intervals, and an eventuality's duration is
its `timeTrace`; the coercions act on the trace, so an eventuality's class enters only through
which coercion `readings` makes available, as in the paper's (19) and (21). The typological
survey of section 2.4 lives in the temporal-connective fragments, and the veridicality
asymmetry and the NPI facts of (25) and (26) receive no proposal in the paper beyond
monotonicity.

## References

* [J. Rett, *Eliminating EARLIEST: a general semantics for before and after*
  (2020)][rett-2020]
* [G. E. M. Anscombe, *Before and after* (1964)][anscombe-1964]
* [O. Heinämäki, *Semantics of English temporal connectives* (1974)][heinamaki-1974]
* [D. Beaver, C. Condoravdi, *A uniform analysis of before and after*
  (2003)][beaver-condoravdi-2003]
* [C. Condoravdi, *NPI licensing in temporal clauses* (2010)][condoravdi-2010]
* [M. Krifka, *Before and after without coercion: comment on the paper by Cleo Condoravdi*
  (2010)][krifka-2010b]
* [H. de Swart, *Aspect shift and coercion* (1998)][de-swart-1998]
* [J. Dölling, *Aspectual coercion and eventuality structure* (2014)][dolling-2014]
* [H. Rullmann, *Maximality in the semantics of wh-constructions* (1995)][rullmann-1995]
* [C. Kennedy, *Projecting the adjective* (1997)][kennedy-1997]
-/

namespace Rett2020a

open Tense Degree Anscombe1964

variable {T : Type*} [LinearOrder T]

/-! ### The relations and the coercions -/

/-- *A before B* (22a): some time of `A` precedes the most informative time of `B` on the
*before* scale, its least. -/
def before (A B : RunTimes T) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale .lt (timeTrace B), t < m

/-- *A after B* (22b): some time of `A` follows the most informative time of `B` on the
*after* scale, its greatest. -/
def after (A B : RunTimes T) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale .gt (timeTrace B), m < t

/-- Inchoative coercion (19): a process may denote the onset of its duration, the greatest
lower bound of its times. -/
def inchoative (p : RunTimes T) : RunTimes T :=
  {i | ∃ g, IsLeast (timeTrace p) g ∧ i = NonemptyInterval.pure g}

/-- Completive coercion (21): a culmination may denote its telos, the least upper bound of
its times. -/
def completive (p : RunTimes T) : RunTimes T :=
  {i | ∃ l, IsGreatest (timeTrace p) l ∧ i = NonemptyInterval.pure l}

/-- The aspectual classes of Moens and Steedman as the paper groups them: processes, states
and activities, and culminations, accomplishments and achievements. -/
inductive Class where
  | process
  | culmination

/-- The denotations available to an embedded eventuality of a class with run times `p`: the
run times themselves, and the coercion its class allows. -/
def readings : Class → RunTimes T → Set (RunTimes T)
  | .process, p => {p, inchoative p}
  | .culmination, p => {p, completive p}

theorem timeTrace_inchoative (p : RunTimes T) :
    timeTrace (inchoative p) = {g | IsLeast (timeTrace p) g} := by
  ext t
  simp only [mem_timeTrace, inchoative, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, ht⟩
    exact (NonemptyInterval.mem_pure.mp ht) ▸ hg
  · exact λ h => ⟨_, ⟨t, h, rfl⟩, NonemptyInterval.mem_pure.mpr rfl⟩

theorem timeTrace_completive (p : RunTimes T) :
    timeTrace (completive p) = {l | IsGreatest (timeTrace p) l} := by
  ext t
  simp only [mem_timeTrace, completive, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, ht⟩
    exact (NonemptyInterval.mem_pure.mp ht) ▸ hl
  · exact λ h => ⟨_, ⟨t, h, rfl⟩, NonemptyInterval.mem_pure.mpr rfl⟩

variable {A B : RunTimes T} {m : T}

/-- Against an embedded clause with a first time, *before* is precedence of that time. -/
theorem before_iff_of_isLeast (h : IsLeast (timeTrace B) m) :
    before A B ↔ ∃ t ∈ timeTrace A, t < m := by
  simp only [before, maxOnScale_lt_eq, Set.mem_ofPred_eq]
  exact ⟨λ ⟨t, ht, _, hm, htm⟩ => ⟨t, ht, hm.unique h ▸ htm⟩, λ ⟨t, ht, htm⟩ => ⟨t, ht, m, h, htm⟩⟩

/-- Against an embedded clause with a last time, *after* is succession of that time. -/
theorem after_iff_of_isGreatest (h : IsGreatest (timeTrace B) m) :
    after A B ↔ ∃ t ∈ timeTrace A, m < t := by
  simp only [after, maxOnScale_gt_eq, Set.mem_ofPred_eq]
  exact ⟨λ ⟨t, ht, _, hm, htm⟩ => ⟨t, ht, hm.unique h ▸ htm⟩, λ ⟨t, ht, htm⟩ => ⟨t, ht, m, h, htm⟩⟩

theorem timeTrace_completive_of_isGreatest (h : IsGreatest (timeTrace B) m) :
    timeTrace (completive B) = {m} := by
  rw [timeTrace_completive]
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨h, λ _ hx => hx.unique h⟩

theorem timeTrace_inchoative_of_isLeast (h : IsLeast (timeTrace B) m) :
    timeTrace (inchoative B) = {m} := by
  rw [timeTrace_inchoative]
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨h, λ _ hx => hx.unique h⟩

/-- Completive coercion turns *before* into precedence of the telos. -/
theorem before_completive_iff (h : IsGreatest (timeTrace B) m) :
    before A (completive B) ↔ ∃ t ∈ timeTrace A, t < m :=
  before_iff_of_isLeast (by rw [timeTrace_completive_of_isGreatest h]; exact isLeast_singleton)

/-- Inchoative coercion turns *after* into succession of the onset. -/
theorem after_inchoative_iff (h : IsLeast (timeTrace B) m) :
    after A (inchoative B) ↔ ∃ t ∈ timeTrace A, m < t :=
  after_iff_of_isGreatest (by rw [timeTrace_inchoative_of_isLeast h]; exact isGreatest_singleton)

/-- Inchoative coercion leaves *before* as it is: the onset is already its point. -/
theorem before_inchoative_iff (h : IsLeast (timeTrace B) m) :
    before A (inchoative B) ↔ before A B := by
  rw [before_iff_of_isLeast h, before_iff_of_isLeast (B := inchoative B)]
  rw [timeTrace_inchoative_of_isLeast h]; exact isLeast_singleton

/-- Completive coercion leaves *after* as it is: the telos is already its point. -/
theorem after_completive_iff (h : IsGreatest (timeTrace B) m) :
    after A (completive B) ↔ after A B := by
  rw [after_iff_of_isGreatest h, after_iff_of_isGreatest (B := completive B)]
  rw [timeTrace_completive_of_isGreatest h]; exact isGreatest_singleton

/-! ### Table 1 -/

variable (A) (i : NonemptyInterval T)

theorem isLeast_timeTrace_stative : IsLeast (timeTrace (stativeDenotation i)) i.fst :=
  ⟨mem_timeTrace_stativeDenotation.mpr ⟨le_rfl, i.fst_le_snd⟩,
    λ _ ht => (mem_timeTrace_stativeDenotation.mp ht).1⟩

theorem isGreatest_timeTrace_stative : IsGreatest (timeTrace (stativeDenotation i)) i.snd :=
  ⟨mem_timeTrace_stativeDenotation.mpr ⟨i.fst_le_snd, le_rfl⟩,
    λ _ ht => (mem_timeTrace_stativeDenotation.mp ht).2⟩

theorem isLeast_timeTrace_accomplishment :
    IsLeast (timeTrace (accomplishmentDenotation i)) i.fst := by
  rw [timeTrace_accomplishmentDenotation, ← timeTrace_stativeDenotation]
  exact isLeast_timeTrace_stative i

theorem isGreatest_timeTrace_accomplishment :
    IsGreatest (timeTrace (accomplishmentDenotation i)) i.snd := by
  rw [timeTrace_accomplishmentDenotation, ← timeTrace_stativeDenotation]
  exact isGreatest_timeTrace_stative i

/-- Against a process, *before* has one reading, precedence of its onset ((4a)): inchoative
coercion changes nothing, and completive coercion is unavailable. -/
theorem before_process :
    ∀ B ∈ readings .process (stativeDenotation i), (before A B ↔ ∃ t ∈ timeTrace A, t < i.fst) := by
  simp only [readings, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨before_iff_of_isLeast (isLeast_timeTrace_stative i),
    (before_inchoative_iff (isLeast_timeTrace_stative i)).trans
      (before_iff_of_isLeast (isLeast_timeTrace_stative i))⟩

/-- Against a culmination, *before* reads as precedence of its start ((5a), the paper's
(23a)) ... -/
theorem before_culmination_start :
    before A (accomplishmentDenotation i) ↔ ∃ t ∈ timeTrace A, t < i.fst :=
  before_iff_of_isLeast (isLeast_timeTrace_accomplishment i)

/-- ... or, under completive coercion, of its telos ((23b)). -/
theorem before_culmination_telos :
    before A (completive (accomplishmentDenotation i)) ↔ ∃ t ∈ timeTrace A, t < i.snd :=
  before_completive_iff (isGreatest_timeTrace_accomplishment i)

/-- Against a process, *after* reads as succession of its end ((5b), the paper's (24a)) ... -/
theorem after_process_end :
    after A (stativeDenotation i) ↔ ∃ t ∈ timeTrace A, i.snd < t :=
  after_iff_of_isGreatest (isGreatest_timeTrace_stative i)

/-- ... or, under inchoative coercion, of its onset ((24b)). -/
theorem after_process_onset :
    after A (inchoative (stativeDenotation i)) ↔ ∃ t ∈ timeTrace A, i.fst < t :=
  after_inchoative_iff (isLeast_timeTrace_stative i)

/-- Against a culmination, *after* has one reading, succession of its telos ((4b)): completive
coercion changes nothing, and inchoative coercion is unavailable. -/
theorem after_culmination :
    ∀ B ∈ readings .culmination (accomplishmentDenotation i),
      (after A B ↔ ∃ t ∈ timeTrace A, i.snd < t) := by
  simp only [readings, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨after_iff_of_isGreatest (isGreatest_timeTrace_accomplishment i),
    (after_completive_iff (isGreatest_timeTrace_accomplishment i)).trans
      (after_iff_of_isGreatest (isGreatest_timeTrace_accomplishment i))⟩

/-- A stative main clause is *before* an embedded clause with a first time iff its onset
precedes that time. -/
theorem before_stative_iff (h : IsLeast (timeTrace B) m) :
    before (stativeDenotation i) B ↔ i.fst < m := by
  rw [before_iff_of_isLeast h]
  exact ⟨λ ⟨_, ht, htm⟩ => (mem_timeTrace_stativeDenotation.mp ht).1.trans_lt htm,
    λ h => ⟨i.fst, (isLeast_timeTrace_stative i).1, h⟩⟩

/-- A stative main clause is *after* an embedded clause with a last time iff its end follows
that time. -/
theorem after_stative_iff (h : IsGreatest (timeTrace B) m) :
    after (stativeDenotation i) B ↔ m < i.snd := by
  rw [after_iff_of_isGreatest h]
  exact ⟨λ ⟨_, ht, htm⟩ => htm.trans_le (mem_timeTrace_stativeDenotation.mp ht).2,
    λ h => ⟨i.snd, (isGreatest_timeTrace_stative i).1, h⟩⟩

variable (j : NonemptyInterval T)

theorem before_stative_accomplishment_iff :
    before (stativeDenotation i) (accomplishmentDenotation j) ↔ i.fst < j.fst :=
  before_stative_iff i (isLeast_timeTrace_accomplishment j)

theorem before_stative_completive_iff :
    before (stativeDenotation i) (completive (accomplishmentDenotation j)) ↔ i.fst < j.snd :=
  before_stative_iff i (by
    rw [timeTrace_completive_of_isGreatest (isGreatest_timeTrace_accomplishment j)]
    exact isLeast_singleton)

theorem after_stative_stative_iff :
    after (stativeDenotation i) (stativeDenotation j) ↔ j.snd < i.snd :=
  after_stative_iff i (isGreatest_timeTrace_stative j)

theorem after_stative_inchoative_iff :
    after (stativeDenotation i) (inchoative (stativeDenotation j)) ↔ j.fst < i.snd :=
  after_stative_iff i (by
    rw [timeTrace_inchoative_of_isLeast (isLeast_timeTrace_stative j)]
    exact isGreatest_singleton)

/-- (23): John met Mary at three, and Mary climbed the mountain from one to four. Before the
start of the climb is false, before its telos true. -/
theorem example23 :
    ¬ before {NonemptyInterval.pure 15} (accomplishmentDenotation ⟨⟨13, 16⟩, by omega⟩) ∧
      before {NonemptyInterval.pure 15}
        (completive (accomplishmentDenotation ⟨⟨13, 16⟩, by omega⟩)) := by
  simp [before_culmination_start, before_culmination_telos]

/-- (24): John met Mary in 2022, and Mary was president from 2021 to 2028. After the end of
her term is false, after its onset true. -/
theorem example24 :
    ¬ after {NonemptyInterval.pure 2022} (stativeDenotation ⟨⟨2021, 2028⟩, by omega⟩) ∧
      after {NonemptyInterval.pure 2022}
        (inchoative (stativeDenotation ⟨⟨2021, 2028⟩, by omega⟩)) := by
  simp [after_process_end, after_process_onset]

/-! ### Monotonicity -/

/-- *Before* on its default reading is downward entailing in the embedded clause: a
sub-eventuality with a first time starts no earlier. -/
theorem before_antitone {B' : RunTimes T} (h : timeTrace B' ⊆ timeTrace B)
    (hB' : ∃ m', IsLeast (timeTrace B') m') : before A B → before A B' := by
  rintro ⟨t, ht, m, hm, htm⟩
  obtain ⟨m', hm'⟩ := hB'
  rw [maxOnScale_lt_eq] at hm
  exact ⟨t, ht, m', by rw [maxOnScale_lt_eq]; exact hm', htm.trans_le (hm.2 (h hm'.1))⟩

/-- *After* on its default reading is downward entailing in the embedded clause: a
sub-eventuality with a last time ends no later. -/
theorem after_antitone {B' : RunTimes T} (h : timeTrace B' ⊆ timeTrace B)
    (hB' : ∃ m', IsGreatest (timeTrace B') m') : after A B → after A B' := by
  rintro ⟨t, ht, m, hm, htm⟩
  obtain ⟨m', hm'⟩ := hB'
  rw [maxOnScale_gt_eq] at hm
  exact ⟨t, ht, m', by rw [maxOnScale_gt_eq]; exact hm', (hm.2 (h hm'.1)).trans_lt htm⟩

/-- The coerced reading is not: precedence of a telos does not carry over to a
sub-eventuality with an earlier telos, so a *before* clause licenses NPIs only on its default
reading (25). -/
theorem not_before_completive_antitone (h₃ : ∃ a b c : T, a < b ∧ b < c) :
    ¬ ∀ A B B' : RunTimes T, timeTrace B' ⊆ timeTrace B → (∃ l', IsGreatest (timeTrace B') l') →
      before A (completive B) → before A (completive B') := by
  obtain ⟨a, b, c, hab, hbc⟩ := h₃
  intro h
  have := h {NonemptyInterval.pure b} (accomplishmentDenotation ⟨⟨a, c⟩, hab.le.trans hbc.le⟩)
    (accomplishmentDenotation (NonemptyInterval.pure a))
    (by
      rw [timeTrace_accomplishmentDenotation, timeTrace_accomplishmentDenotation]
      rintro t ht
      obtain rfl := NonemptyInterval.mem_pure.mp ht
      exact NonemptyInterval.mem_def.mpr ⟨le_rfl, hab.le.trans hbc.le⟩)
    ⟨a, isGreatest_timeTrace_accomplishment _⟩
    ((before_culmination_telos _ _).mpr ⟨b, mem_timeTrace_pure.mpr rfl, hbc⟩)
  obtain ⟨t, ht, htm⟩ := (before_culmination_telos _ _).mp this
  obtain rfl := mem_timeTrace_pure.mp ht
  exact absurd (htm.trans hab) (lt_irrefl _)

/-! ### Anscombe -/

/-- Anscombe's *before*, a time of the main clause before every time of the embedded clause,
is the default reading whenever the embedded clause has a first time. -/
theorem before_iff_beforeEver (h : IsLeast (timeTrace B) m) :
    before A B ↔ Anscombe.beforeEver A B :=
  (before_iff_of_isLeast h).trans (beforeEver_iff_lt_least h).symm

/-- *After* entails Anscombe's existential *after*, a time of the main clause after some time
of the embedded clause. -/
theorem after_imp_after : after A B → Anscombe.after A B := by
  rintro ⟨t, ht, m, hm, htm⟩
  exact ⟨t, ht, m, hm.1, htm⟩

end Rett2020a
