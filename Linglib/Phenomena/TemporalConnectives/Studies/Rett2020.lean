import Linglib.Phenomena.TemporalConnectives.Studies.Anscombe1964
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Phenomena.TemporalConnectives.Studies.Karttunen1974
import Linglib.Fragments.English.TemporalExpressions


/-!
# @cite{rett-2020}: Antonymy + Aspectual Coercion
@cite{rett-2020} @cite{rett-2026} @cite{jin-koenig-2021} @cite{krifka-2010b}*before* and *after* are antonyms on converse scales, with strong defaults @cite{de-swart-1998} @cite{dolling-2014}
(before-start, after-finish). Non-default readings require aspectual coercion:
**INCHOAT** (GLB, atelic → onset) or **COMPLET** (LUB, telic → telos), which
incur processing cost.

Rett's formal analysis (eqs. 22a-b):
- ⟦A before B⟧ = ∃t ∈ A [t ≺ MAX(B_≺)]
- ⟦A after B⟧ = ∃t ∈ A [t ≻ MAX(B_≻)]

Both theories use ∃ over the main clause A: "some time in A bears the
relation to (some characterization) B." They differ in how B's
reference point is selected (all of B vs MAX of B).

## Level

**Level 2 (interval sets)**: operates on `SentDenotation` directly, using
`maxOnScale` from `Core.Scale` to select the informative bound.

## Bridges

- `INCHOAT` extracts the same point as `CoSType.inception` (onset of a state)
- `COMPLET` extracts the dual: the finish point of a telic event
- `stativeDenotation` has the subinterval property (connects to Krifka CUM)
- Both theories agree on unambiguous cases (stative before, telic after)

## Ambidirectionality

*before* is truth-conditionally insensitive to negation of its argument
(ambidirectional), which is why it licenses expletive negation cross-
linguistically. *after* and *while* are not ambidirectional.

-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval
open Semantics.Tense.Aspect.LexicalAspect
open Semantics.Lexical.Verb.ChangeOfState
open Core.Scale (maxOnScale isAmbidirectional maxOnScale_singleton
  maxOnScale_lt_closedInterval maxOnScale_gt_closedInterval)

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: Rett's Truth Conditions
-- ============================================================================

/-- Rett's *before* (eq. 22a): ∃t ∈ times(A) [t ≺ MAX(times(B)_≺)].
    Some time in A precedes the maximal (on the ≺ scale) time of B. -/
def Rett.before (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· < ·) (timeTrace B), t < m

/-- Rett's *after* (eq. 22b): ∃t ∈ times(A) [t ≻ MAX(times(B)_≻)].
    Some time in A succeeds the maximal (on the ≻ scale) time of B. -/
def Rett.after (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· > ·) (timeTrace B), t > m

-- ============================================================================
-- § 2: Aspectual Coercion Operators
-- ============================================================================

/-- Inchoative coercion / GLB (@cite{rett-2020}, eq. 19; @cite{de-swart-1998}; @cite{dolling-2014}).
    Maps a process (atelic) denotation to a singleton containing its onset point.
    GLB(T) = ιt[t ∈ T ∧ ∀t' ∈ T, t ≤ t']

    Linguistically: "Amy was surprised" → "the start of Amy being surprised".
    Cross-linguistically realized as inchoative morphology (Russian *-sja*,
    Tagalog PFV.NEUT). -/
def INCHOAT (p : SentDenotation Time) : SentDenotation Time :=
  { i | ∃ onset : Time,
    (∀ j ∈ p, onset ≤ j.start) ∧
    (∀ t, (∀ j ∈ p, t ≤ j.start) → t ≤ onset) ∧
    i = Interval.point onset }

/-- Completive coercion / LUB (@cite{rett-2020}, eq. 21; @cite{dolling-2014}).
    Maps a culmination (telic) denotation to a singleton containing its telos.
    LUB(T) = ιt[t ∈ T ∧ ∀t' ∈ T, t ≥ t']

    Linguistically: "Jane climbed the mountain" → "the moment Jane reached
    the top". Cross-linguistically realized as completive morphology
    (Tagalog AIA). -/
def COMPLET (p : SentDenotation Time) : SentDenotation Time :=
  { i | ∃ telos : Time,
    (∀ j ∈ p, j.finish ≤ telos) ∧
    (∀ t, (∀ j ∈ p, j.finish ≤ t) → telos ≤ t) ∧
    i = Interval.point telos }

-- ============================================================================
-- § 3: INCHOAT / COMPLET Bridge Theorems
-- ============================================================================

/-- INCHOAT extracts the start point of a stative denotation. -/
theorem inchoat_bridges_inception (i : Interval Time) :
    INCHOAT (stativeDenotation i) = { j | j = Interval.point i.start } := by
  ext k
  simp only [INCHOAT, stativeDenotation, Set.mem_setOf_eq, subinterval]
  constructor
  · rintro ⟨onset, h_lb, h_glb, rfl⟩
    have h1 : onset ≤ i.start := h_lb i ⟨le_refl _, le_refl _⟩
    have h2 : i.start ≤ onset := h_glb i.start (λ j ⟨hjs, _⟩ => hjs)
    exact congrArg Interval.point (le_antisymm h1 h2)
  · rintro rfl
    exact ⟨i.start, λ j ⟨hjs, _⟩ => hjs, λ t ht => ht i ⟨le_refl _, le_refl _⟩, rfl⟩

/-- COMPLET extracts the finish point of an accomplishment denotation. -/
theorem complet_bridges_cessation (i : Interval Time) :
    COMPLET (accomplishmentDenotation i) = { j | j = Interval.point i.finish } := by
  ext k
  simp only [COMPLET, accomplishmentDenotation, Set.mem_setOf_eq]
  constructor
  · rintro ⟨telos, h_ub, h_lub, rfl⟩
    have h1 : i.finish ≤ telos := h_ub i rfl
    have h2 : telos ≤ i.finish := h_lub i.finish (λ j hj => hj ▸ le_refl _)
    exact congrArg Interval.point (le_antisymm h2 h1)
  · rintro rfl
    exact ⟨i.finish, λ j hj => hj ▸ le_refl _, λ t ht => ht i rfl, rfl⟩

-- ============================================================================
-- § 4: Theory Agreement (Anscombe ↔ Rett)
-- ============================================================================

/-- Both theories predict "before-start" for statives.

    When B is stative (subinterval-closed), both theories reduce to
    "some time in A precedes all times in B":
    - Anscombe directly: ∃ t ∈ A, ∀ t' ∈ B, t < t'
    - Rett: ∃ t ∈ A, t < MAX(B_≺). For statives, MAX on ≺ picks B.start
      (the GLB), and t < B.start ↔ t < all times in B. -/
theorem anscombe_rett_agree_stative_before_start
    (A : SentDenotation Time) (i_B : Interval Time) :
    (Anscombe.before A (stativeDenotation i_B) ↔
     Rett.before A (stativeDenotation i_B)) := by
  constructor
  · rintro ⟨t, ht_A, h_all⟩
    have h_start_mem : i_B.start ∈ timeTrace (stativeDenotation i_B) := by
      rw [timeTrace_stativeDenotation]; exact ⟨le_refl _, i_B.valid⟩
    exact ⟨t, ht_A, i_B.start,
      ⟨h_start_mem, fun t' ht' hne => by
        rw [timeTrace_stativeDenotation] at ht'
        exact lt_of_le_of_ne ht'.1 (Ne.symm hne)⟩,
      h_all _ h_start_mem⟩
  · rintro ⟨t, ht_A, m, ⟨_, hm_min⟩, htm⟩
    exact ⟨t, ht_A, fun t' ht' => by
      by_cases heq : t' = m
      · exact heq ▸ htm
      · exact lt_trans htm (hm_min t' ht' heq)⟩

/-- Rett's analysis implies Anscombe's for telic "after".

    The converse does NOT hold: Anscombe.after only requires *some* point
    of B to precede some point of A (∃ t' ∈ B, t' < t), while Rett requires
    A to follow B's *finish* (t > MAX₍>₎(B) = i_B.finish). These differ
    when A overlaps B without extending past B's endpoint. -/
theorem rett_implies_anscombe_telic_after_finish
    (A : SentDenotation Time) (i_B : Interval Time) :
    Rett.after A (accomplishmentDenotation i_B) →
    Anscombe.after A (accomplishmentDenotation i_B) := by
  rintro ⟨t, ht_A, m, ⟨hm_mem, _⟩, htm⟩
  rw [timeTrace_accomplishmentDenotation] at hm_mem
  exact ⟨t, ht_A, m, by rw [timeTrace_accomplishmentDenotation]; exact hm_mem, htm⟩

-- ============================================================================
-- § 5: Rett → Anscombe (General Projection)
-- ============================================================================

/-- Rett's *before* implies Anscombe's *before* in general.

    From Rett: t < m where m = min(timeTrace B). Since m < all other
    points in timeTrace B (by maxOnScale), t < every point in timeTrace B.
    This gives Anscombe's ∀-quantified conclusion. -/
theorem rett_before_implies_anscombe (A B : SentDenotation Time) :
    Rett.before A B → Anscombe.before A B := by
  rintro ⟨t, ht, m, ⟨hm_mem, hm_min⟩, htm⟩
  exact ⟨t, ht, fun t' ht' => by
    by_cases heq : t' = m
    · exact heq ▸ htm
    · exact lt_trans htm (hm_min t' ht' heq)⟩

/-- Rett's *after* implies Anscombe's *after* in general.

    Immediate: m ∈ maxOnScale(timeTrace B) implies m ∈ timeTrace B,
    and t > m gives the existential witness for Anscombe.after. -/
theorem rett_after_implies_anscombe (A B : SentDenotation Time) :
    Rett.after A B → Anscombe.after A B := by
  rintro ⟨t, ht, m, ⟨hm_mem, _⟩, htm⟩
  exact ⟨t, ht, m, hm_mem, htm⟩

-- ============================================================================
-- § 6: Ambidirectionality (@cite{rett-2026})
-- ============================================================================

/-! ### Expletive negation and ambidirectionality

@cite{rett-2026} shows that *before* is **ambidirectional**: negating B
in "A before B" doesn't change truth conditions. This is why
*before*-clauses license expletive negation cross-linguistically
(@cite{jin-koenig-2021}: 50 of 74 EN-attesting languages, from a 722-language survey).

The mechanism: for B = [s, f], both B and its
**pre-event complement** (−∞, s] share s as their "most informative
closed bound" on the < scale. The *before* construction relates A only
to this bound, so negating B is truth-conditionally vacuous.

*After* is NOT ambidirectional: negating B shifts the relevant bound.
*While* requires total temporal overlap; ¬B fails when A overlaps B. -/

/-- *Before* truth conditions depend only on MAX₍<₎ of B's time trace. -/
theorem before_determined_by_max (A B₁ B₂ : SentDenotation Time)
    (h : maxOnScale (· < ·) (timeTrace B₁) = maxOnScale (· < ·) (timeTrace B₂)) :
    Rett.before A B₁ ↔ Rett.before A B₂ := by
  constructor <;> rintro ⟨t, ht, m, hm, htm⟩ <;> exact ⟨t, ht, m, h ▸ hm, htm⟩

/-- When B's time trace is a closed interval [s, f], Rett.before reduces to
    "∃ t ∈ A, t < s". -/
theorem rett_before_closedTrace_eq (A B : SentDenotation Time) (s f : Time) (hsf : s ≤ f)
    (htrace : timeTrace B = { t | s ≤ t ∧ t ≤ f }) :
    Rett.before A B ↔ ∃ t ∈ timeTrace A, t < s := by
  unfold Rett.before
  rw [htrace, maxOnScale_lt_closedInterval s f hsf]
  constructor
  · rintro ⟨t, ht, m, rfl, htm⟩; exact ⟨t, ht, htm⟩
  · rintro ⟨t, ht, htm⟩; exact ⟨t, ht, s, rfl, htm⟩

/-- COMPLET on a stative denotation extracts the finish point. -/
theorem complet_stative (i : Interval Time) :
    COMPLET (stativeDenotation i) = { j | j = Interval.point i.finish } := by
  ext k
  simp only [COMPLET, stativeDenotation, Set.mem_setOf_eq, subinterval]
  constructor
  · rintro ⟨telos, h_ub, h_lub, rfl⟩
    have h1 : i.finish ≤ telos := h_ub i ⟨le_refl _, le_refl _⟩
    have h2 : telos ≤ i.finish := h_lub i.finish (fun j ⟨_, hjf⟩ => hjf)
    exact congrArg Interval.point (le_antisymm h2 h1)
  · rintro rfl
    exact ⟨i.finish, fun j ⟨_, hjf⟩ => hjf, fun t ht => ht i ⟨le_refl _, le_refl _⟩, rfl⟩

/-- The pre-event complement of an event interval [s, f]. -/
def preEventDenotation (bot : Time) (i : Interval Time) (hbot : bot ≤ i.start) :
    SentDenotation Time :=
  stativeDenotation ⟨bot, i.start, hbot⟩

/-- The time trace of a stative denotation is the closed interval [start, finish]. -/
theorem timeTrace_stative_closedInterval (i : Interval Time) :
    timeTrace (stativeDenotation i) = { t | i.start ≤ t ∧ t ≤ i.finish } := by
  rw [timeTrace_stativeDenotation]; ext; simp [contains]

/-- MAX₍<₎ of a stative denotation's time trace is {start}. -/
theorem maxOnScale_lt_stative (i : Interval Time) :
    maxOnScale (· < ·) (timeTrace (stativeDenotation i)) = {i.start} := by
  rw [timeTrace_stative_closedInterval, maxOnScale_lt_closedInterval _ _ i.valid]

/-- The time trace of `COMPLET(preEventDenotation bot i)` is the degenerate
    interval `{i.start}`. -/
theorem timeTrace_complet_preEvent (bot : Time) (i : Interval Time) (hbot : bot ≤ i.start) :
    timeTrace (COMPLET (preEventDenotation bot i hbot)) =
    { t | i.start ≤ t ∧ t ≤ i.start } := by
  unfold preEventDenotation
  rw [complet_stative]
  show timeTrace (accomplishmentDenotation (Interval.point i.start)) = _
  rw [timeTrace_accomplishmentDenotation]
  ext; simp [contains, point]

/-- MAX₍<₎ of the COMPLET of a pre-event denotation is {start}. -/
theorem maxOnScale_lt_complet_preEvent (bot : Time) (i : Interval Time) (hbot : bot ≤ i.start) :
    maxOnScale (· < ·) (timeTrace (COMPLET (preEventDenotation bot i hbot))) =
    {i.start} := by
  rw [timeTrace_complet_preEvent, maxOnScale_lt_closedInterval _ _ (le_refl _)]

/-- *Before* is truth-conditionally insensitive to event polarity.

    Both select the same boundary point s through different mechanisms:
    the original uses the default *before*-start reading (MAX₍<₎),
    while the negated version requires COMPLET coercion to extract the
    end of the pre-event interval. -/
theorem before_preEvent_ambidirectional (A : SentDenotation Time) (i_B : Interval Time)
    (bot : Time) (hbot : bot ≤ i_B.start) :
    Rett.before A (stativeDenotation i_B) ↔
    Rett.before A (COMPLET (preEventDenotation bot i_B hbot)) := by
  apply before_determined_by_max
  rw [maxOnScale_lt_stative, maxOnScale_lt_complet_preEvent]

/-- *After* is NOT ambidirectional: negating B changes
    truth conditions because MAX₍>₎(B) ≠ MAX₍>₎(¬B). -/
theorem after_not_ambidirectional (hab : ∃ (a b : Time), a < b) :
    ¬ ∀ (A : SentDenotation Time) (B : Set Time),
      isAmbidirectional (λ X => ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· > ·) X, t > m) B := by
  obtain ⟨a, b, hab⟩ := hab
  intro h
  have h_amb := h {Interval.point b} {a}
  have h_fB : ∃ t ∈ timeTrace ({Interval.point b} : SentDenotation Time),
      ∃ m ∈ maxOnScale (· > ·) ({a} : Set Time), t > m :=
    ⟨b, ⟨Interval.point b, rfl, le_refl _, le_refl _⟩,
     a, ⟨rfl, fun _ hx' hne => absurd hx' hne⟩, hab⟩
  obtain ⟨t, ht_A, m, ⟨hm_mem, hm_dom⟩, htm⟩ := h_amb.mp h_fB
  obtain ⟨j, hj_mem, hj_s, hj_f⟩ := ht_A
  simp only [Set.mem_singleton_iff] at hj_mem
  subst hj_mem
  simp only [Interval.point] at hj_s hj_f
  have ht_eq : t = b := le_antisymm hj_f hj_s
  have hb_compl : b ∈ ({a} : Set Time)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hab
  by_cases hmb : m = b
  · rw [ht_eq, hmb] at htm; exact absurd htm (lt_irrefl _)
  · rw [ht_eq] at htm; exact absurd htm (not_lt.mpr (le_of_lt (hm_dom b hb_compl (Ne.symm hmb))))

omit [LinearOrder Time] in
/-- *While* is not ambidirectional. -/
theorem while_not_ambidirectional [Inhabited Time] :
    ¬ ∀ (A B : Set Time),
      isAmbidirectional (λ X => ∀ t ∈ A, t ∈ X) B := by
  intro h
  have := h {default} {default}
  simp only [isAmbidirectional] at this
  have lhs : ∀ t ∈ ({default} : Set Time), t ∈ ({default} : Set Time) := fun _ h => h
  have rhs := this.mp lhs (default : Time) rfl
  exact absurd rfl rhs

end Semantics.Tense.TemporalConnectives

-- ============================================================================
-- Concrete Scenario Verification (from original study file)
-- ============================================================================


/-!
# Temporal Connective Truth-Condition Examples
@cite{heinamaki-1974} @cite{rett-2020} @cite{karttunen-1974}

Concrete scenarios verifying that the Anscombe, Rett, and Karttunen
formalizations produce correct truth-value judgments.

Scenarios 1–6 verify @cite{rett-2020} Table 1 for *before*/*after*.
Scenarios 7–10 verify @cite{heinamaki-1974} Chs. 6, 8, 9 for *since*, *by*, *till*.

## Scenarios (ℕ time points)

| # | ME           | EE                   | Connective | Result |
|---|--------------|----------------------|------------|--------|
| 1 | point(1)     | stative [5,10]       | before     | True   |
| 2 | point(12)    | stative [5,10]       | after      | True   |
| 3 | point(1)     | accomplishment [3,8] | before     | True   |
| 4 | point(12)    | accomplishment [3,8] | after      | True   |
| 5 | point(7)     | stative [5,10]       | before     | False  |
| 6 | point(7)     | stative [5,10]       | after      | False  |
| 7 | stative[5,10]| point(5)             | since      | True   |
| 8 | point(1)     | point(3)             | by         | True   |
| 9 | point(3)     | point(3)             | by         | True   |
| 9'| point(3)     | point(3)             | before     | False  |
|10 | stative[5,10]| point(5)             | till       | True   |

-/

namespace Phenomena.TemporalConnectives.Examples

open Core.Time
open Core.Time.Interval
open Semantics.Tense.TemporalConnectives

-- ============================================================================
-- § 1: Concrete Intervals
-- ============================================================================

/-- ME: "John left" — punctual event at time 1 (early). -/
def me_early : Interval ℕ := Interval.point 1

/-- ME: "John left" — punctual event at time 12 (late). -/
def me_late : Interval ℕ := Interval.point 12

/-- ME: punctual event at time 7 (inside the stative EE). -/
def me_inside : Interval ℕ := Interval.point 7

/-- EE: "she was president" — stative, running [5, 10]. -/
def ee_stative : Interval ℕ :=
  { start := 5, finish := 10, valid := by omega }

/-- EE: "she climbed the mountain" — accomplishment, [3, 8]. -/
def ee_accomplishment : Interval ℕ :=
  { start := 3, finish := 8, valid := by omega }

-- Sentence denotations
abbrev A_early := accomplishmentDenotation me_early
abbrev A_late := accomplishmentDenotation me_late
abbrev A_inside := accomplishmentDenotation me_inside
abbrev B_stative := stativeDenotation ee_stative
abbrev B_telic := accomplishmentDenotation ee_accomplishment

/-- Rewriting lemma: membership in timeTrace of our stative denotation. -/
private theorem mem_tt_stative {t : ℕ} :
    t ∈ timeTrace B_stative ↔ 5 ≤ t ∧ t ≤ 10 := by
  rw [timeTrace_stativeDenotation]
  simp [contains, ee_stative]

/-- Rewriting lemma: membership in timeTrace of our telic denotation. -/
private theorem mem_tt_telic {t : ℕ} :
    t ∈ timeTrace B_telic ↔ 3 ≤ t ∧ t ≤ 8 := by
  rw [timeTrace_accomplishmentDenotation]
  simp [contains, ee_accomplishment]

/-- Rewriting lemma: membership in timeTrace of early ME. -/
private theorem mem_tt_early {t : ℕ} :
    t ∈ timeTrace A_early ↔ t = 1 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_early, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of late ME. -/
private theorem mem_tt_late {t : ℕ} :
    t ∈ timeTrace A_late ↔ t = 12 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_late, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of inside ME. -/
private theorem mem_tt_inside {t : ℕ} :
    t ∈ timeTrace A_inside ↔ t = 7 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_inside, Interval.point, Set.mem_setOf_eq]
  omega

-- ============================================================================
-- § 2: Scenario 1 — ME(1) before stative EE[5,10]
-- ============================================================================

/-- "John left₁ before she was president₅₋₁₀" — True under Anscombe.
    Witness: t = 1 ∈ ME, and 1 < all t' ∈ [5, 10]. -/
theorem scenario1_anscombe : Anscombe.before A_early B_stative := by
  refine ⟨1, mem_tt_early.mpr rfl, ?_⟩
  intro t' ht'
  exact Nat.lt_of_lt_of_le (by omega) (mem_tt_stative.mp ht').1

/-- "John left₁ before she was president₅₋₁₀" — True under Rett.
    Witness: t = 1, m = 5 (the GLB of [5, 10] on the ≺ scale). -/
theorem scenario1_rett : Rett.before A_early B_stative := by
  refine ⟨1, mem_tt_early.mpr rfl, 5, ⟨mem_tt_stative.mpr ⟨le_refl _, by omega⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨h1, _⟩ := mem_tt_stative.mp hx'
  omega

-- ============================================================================
-- § 3: Scenario 2 — ME(12) after stative EE[5,10]
-- ============================================================================

/-- "John left₁₂ after she was president₅₋₁₀" — True under Anscombe.
    Witness: t = 12, t' = 5 (any point in EE suffices). -/
theorem scenario2_anscombe : Anscombe.after A_late B_stative := by
  exact ⟨12, mem_tt_late.mpr rfl, 5, mem_tt_stative.mpr ⟨le_refl _, by omega⟩, by omega⟩

/-- "John left₁₂ after she was president₅₋₁₀" — True under Rett.
    Witness: t = 12, m = 10 (the LUB of [5, 10] on the ≻ scale). -/
theorem scenario2_rett : Rett.after A_late B_stative := by
  refine ⟨12, mem_tt_late.mpr rfl, 10, ⟨mem_tt_stative.mpr ⟨by omega, le_refl _⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨_, h2⟩ := mem_tt_stative.mp hx'
  omega

-- ============================================================================
-- § 4: Scenario 3 — ME(1) before accomplishment EE[3,8]
-- ============================================================================

/-- "John met Mary₁ before she climbed the mountain₃₋₈" — True under Anscombe.
    Witness: t = 1, and 1 < all t' in [3, 8]. -/
theorem scenario3_anscombe : Anscombe.before A_early B_telic := by
  refine ⟨1, mem_tt_early.mpr rfl, ?_⟩
  intro t' ht'
  have ⟨h1, _⟩ := mem_tt_telic.mp ht'
  omega

/-- "John met Mary₁ before she climbed the mountain₃₋₈" — True under Rett.
    Witness: t = 1, m = 3 (the GLB of [3, 8] on the ≺ scale). -/
theorem scenario3_rett : Rett.before A_early B_telic := by
  refine ⟨1, mem_tt_early.mpr rfl, 3, ⟨mem_tt_telic.mpr ⟨le_refl _, by omega⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨h1, _⟩ := mem_tt_telic.mp hx'
  omega

-- ============================================================================
-- § 5: Scenario 4 — ME(12) after accomplishment EE[3,8]
-- ============================================================================

/-- "John met Mary₁₂ after she climbed the mountain₃₋₈" — True under Anscombe.
    Witness: t = 12, t' = 3. -/
theorem scenario4_anscombe : Anscombe.after A_late B_telic := by
  exact ⟨12, mem_tt_late.mpr rfl, 3, mem_tt_telic.mpr ⟨le_refl _, by omega⟩, by omega⟩

/-- "John met Mary₁₂ after she climbed the mountain₃₋₈" — True under Rett.
    Witness: t = 12, m = 8 (the LUB of [3, 8] on the ≻ scale). -/
theorem scenario4_rett : Rett.after A_late B_telic := by
  refine ⟨12, mem_tt_late.mpr rfl, 8, ⟨mem_tt_telic.mpr ⟨by omega, le_refl _⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨_, h2⟩ := mem_tt_telic.mp hx'
  omega

-- ============================================================================
-- § 6: Negative scenarios — ME inside EE
-- ============================================================================

/-- "John left₇ before she was president₅₋₁₀" — False under Anscombe.
    Any witness t from ME (t=7) fails: t'=7 ∈ EE and ¬(7 < 7). -/
theorem scenario5_anscombe_false : ¬ Anscombe.before A_inside B_stative := by
  intro ⟨t, ht, hall⟩
  have := mem_tt_inside.mp ht
  subst this
  have h7 := hall 7 (mem_tt_stative.mpr ⟨by omega, by omega⟩)
  omega

/-- "John left₇ after she was president₅₋₁₀" — False under Rett.
    The max on the ≻ scale is 10, and ¬(7 > 10). -/
theorem scenario6_rett_false : ¬ Rett.after A_inside B_stative := by
  intro ⟨t, ht, m, ⟨hm_mem, hm_max⟩, hgt⟩
  have := mem_tt_inside.mp ht
  subst this
  have ⟨hm_lo, hm_hi⟩ := mem_tt_stative.mp hm_mem
  -- 7 > m means m < 7. But m must be maximal on ≻: ∀ x' ≠ m, m > x'.
  -- If m < 10, then 10 ∈ [5,10] and 10 ≠ m, so m > 10 — contradiction.
  -- If m = 10, then 7 > 10 is false.
  by_cases hm10 : m = 10
  · omega
  · have h10 := hm_max 10 (mem_tt_stative.mpr ⟨by omega, le_refl _⟩) (Ne.symm hm10)
    omega

-- ============================================================================
-- § 7: Theory Agreement on Concrete Scenarios
-- ============================================================================

/-- Both theories agree on scenario 1 (ME before stative EE). -/
theorem scenario1_agree : Anscombe.before A_early B_stative ∧
    Rett.before A_early B_stative :=
  ⟨scenario1_anscombe, scenario1_rett⟩

/-- Both theories agree on scenario 2 (ME after stative EE). -/
theorem scenario2_agree : Anscombe.after A_late B_stative ∧
    Rett.after A_late B_stative :=
  ⟨scenario2_anscombe, scenario2_rett⟩

/-- Both theories agree on scenario 3 (ME before accomplishment EE). -/
theorem scenario3_agree : Anscombe.before A_early B_telic ∧
    Rett.before A_early B_telic :=
  ⟨scenario3_anscombe, scenario3_rett⟩

/-- Both theories agree on scenario 4 (ME after accomplishment EE). -/
theorem scenario4_agree : Anscombe.after A_late B_telic ∧
    Rett.after A_late B_telic :=
  ⟨scenario4_anscombe, scenario4_rett⟩

-- ============================================================================
-- § 8: INCHOAT / COMPLET on Concrete Data
-- ============================================================================

/-- INCHOAT of "she was president₅₋₁₀" = {point(5)}.
    Verifies that inchoative coercion extracts the onset. -/
theorem inchoat_stative_ee :
    INCHOAT B_stative = { j | j = Interval.point 5 } :=
  inchoat_bridges_inception ee_stative

/-- COMPLET of "she climbed the mountain₃₋₈" = {point(8)}.
    Verifies that completive coercion extracts the telos. -/
theorem complet_telic_ee :
    COMPLET B_telic = { j | j = Interval.point 8 } :=
  complet_bridges_cessation ee_accomplishment

-- ============================================================================
-- § 9: *Since*, *By*, *Till* on Concrete Data (@cite{heinamaki-1974})
-- ============================================================================

/-- ME: stative [5, 10] — "He has been happy." -/
abbrev A_stative := stativeDenotation ee_stative

/-- EE: punctual event at time 5 — "she arrived." -/
def ee_onset : Interval ℕ := Interval.point 5
abbrev B_onset := accomplishmentDenotation ee_onset

/-- Rewriting lemma: membership in timeTrace of onset EE. -/
private theorem mem_tt_onset {t : ℕ} :
    t ∈ timeTrace B_onset ↔ t = 5 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, ee_onset, Interval.point, Set.mem_setOf_eq]
  omega

/-- ME: punctual event at time 3 — "arrived at 3pm" (for *by* coincidence case). -/
def me_at_deadline : Interval ℕ := Interval.point 3
abbrev A_at_deadline := accomplishmentDenotation me_at_deadline

/-- EE: punctual event at time 3 — "3pm" (deadline). -/
def ee_deadline : Interval ℕ := Interval.point 3
abbrev B_deadline := accomplishmentDenotation ee_deadline

/-- Rewriting lemma: membership in timeTrace of the at-deadline ME. -/
private theorem mem_tt_at_deadline {t : ℕ} :
    t ∈ timeTrace A_at_deadline ↔ t = 3 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_at_deadline, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of the deadline EE. -/
private theorem mem_tt_deadline {t : ℕ} :
    t ∈ timeTrace B_deadline ↔ t = 3 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, ee_deadline, Interval.point, Set.mem_setOf_eq]
  omega

/-- "He has been happy₅₋₁₀ since she arrived₅" — True under `Karttunen.since`.
    Witness: t = 5 ∈ B, and ∀t' ∈ A (i.e., 5 ≤ t' ≤ 10), 5 ≤ t'. -/
theorem scenario_since : Karttunen.since A_stative B_onset := by
  refine ⟨5, mem_tt_onset.mpr rfl, ?_⟩
  intro t' ht'
  exact (mem_tt_stative.mp ht').1

/-- *Since* is veridical for its complement in scenario: she arrived. -/
theorem scenario_since_veridical :
    Karttunen.since A_stative B_onset → ∃ t, t ∈ timeTrace B_onset :=
  since_veridical_complement _ _

/-- "He arrived₁ by 3pm₃" — True under `Karttunen.by_`.
    Witness: t = 1 ∈ A, and ∀t' ∈ B (t' = 3), 1 ≤ 3. -/
theorem scenario_by_strict : Karttunen.by_ A_early B_deadline := by
  refine ⟨1, mem_tt_early.mpr rfl, ?_⟩
  intro t' ht'; have := mem_tt_deadline.mp ht'; omega

/-- "He arrived₃ by 3pm₃" — True under `Karttunen.by_`.
    Witness: t = 3 ∈ A, 3 ≤ 3 (coincidence allowed). -/
theorem scenario_by_coincidence : Karttunen.by_ A_at_deadline B_deadline := by
  refine ⟨3, mem_tt_at_deadline.mpr rfl, ?_⟩
  intro t' ht'; have := mem_tt_deadline.mp ht'; omega

/-- "He arrived₃ before 3pm₃" — FALSE under `Anscombe.before`.
    Need 3 < 3, which fails. Shows *by* ⊋ *before*. -/
theorem scenario_before_coincidence_false :
    ¬ Anscombe.before A_at_deadline B_deadline := by
  intro ⟨t, ht, hall⟩
  have ht3 := mem_tt_at_deadline.mp ht
  have hlt := hall 3 (mem_tt_deadline.mpr rfl)
  omega

/-- *By* but not *before* on the same scenario: demonstrates the strict
    weakening from `before_implies_by`. -/
theorem by_without_before :
    Karttunen.by_ A_at_deadline B_deadline ∧
    ¬ Anscombe.before A_at_deadline B_deadline :=
  ⟨scenario_by_coincidence, scenario_before_coincidence_false⟩

/-- "He slept₅₋₁₀ till she arrived₅" — True under `Karttunen.till`.
    Witness: t = 5 ∈ both time traces (overlap). -/
theorem scenario_till : Karttunen.till A_stative B_onset := by
  exact ⟨5, mem_tt_stative.mpr ⟨le_refl _, by omega⟩, mem_tt_onset.mpr rfl⟩

/-- *Till* agrees with *until* on the same scenario (definitional). -/
theorem till_matches_until_scenario :
    Karttunen.till A_stative B_onset ↔ Karttunen.until A_stative B_onset :=
  till_iff_until _ _

-- ============================================================================
-- § 10: Punctual *Until* + Negation (@cite{karttunen-1974})
-- ============================================================================

/-! ### Not...until scenarios

Karttunen's identity: punctual *until* = ¬*before* (eq. 33).
We verify this on concrete time points.

| # | ME           | EE          | Construction    | Result |
|---|--------------|-------------|-----------------|--------|
|11 | point(3)     | point(5)    | not...until     | True   |
|12 | point(3)     | point(5)    | presup + assert | when   |
|13 | point(7)     | point(5)    | not...until     | False  |
-/

/-- ME: "The princess woke up" — punctual event at time 3 (early). -/
def me_wake_early : Interval ℕ := Interval.point 3

/-- EE: "The prince kissed her" — punctual event at time 5. -/
def ee_kiss : Interval ℕ := Interval.point 5

abbrev A_wake_early := accomplishmentDenotation me_wake_early
abbrev B_kiss := accomplishmentDenotation ee_kiss

/-- Rewriting lemma: membership in timeTrace of wake event. -/
private theorem mem_tt_wake {t : ℕ} :
    t ∈ timeTrace A_wake_early ↔ t = 3 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_wake_early, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of kiss event. -/
private theorem mem_tt_kiss {t : ℕ} :
    t ∈ timeTrace B_kiss ↔ t = 5 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, ee_kiss, Interval.point, Set.mem_setOf_eq]
  omega

/-- Scenario 11: "The princess woke up₃ before the prince kissed her₅" — TRUE.
    3 < 5. This is the base *before* that gets negated in punctual *until*. -/
theorem scenario11_before_true : Anscombe.before A_wake_early B_kiss := by
  refine ⟨3, mem_tt_wake.mpr rfl, ?_⟩
  intro t' ht'; have := mem_tt_kiss.mp ht'; omega

/-- Scenario 11': "The princess didn't wake up₃ until the prince kissed her₅" — FALSE.
    NOT(BEFORE) = NOT(wake₃ before kiss₅) = ¬(3 < 5) = False.
    The princess DID wake up before the kiss, so "not until" is false. -/
theorem scenario11_notUntil_false : ¬ Karttunen.notUntil A_wake_early B_kiss := by
  intro h; exact h scenario11_before_true

/-- ME: "The princess woke up" — punctual event at time 5 (AT the kiss). -/
def me_wake_at_kiss : Interval ℕ := Interval.point 5
abbrev A_wake_at := accomplishmentDenotation me_wake_at_kiss

private theorem mem_tt_wake_at {t : ℕ} :
    t ∈ timeTrace A_wake_at ↔ t = 5 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_wake_at_kiss, Interval.point, Set.mem_setOf_eq]
  omega

/-- Scenario 12: "The princess didn't wake up₅ until the prince kissed her₅"
    — TRUE. NOT(BEFORE) = NOT(wake₅ before kiss₅) = ¬(5 < 5) = True.
    She woke up at exactly the time of the kiss. -/
theorem scenario12_notUntil_true : Karttunen.notUntil A_wake_at B_kiss := by
  intro ⟨t, ht, hall⟩
  have ht5 := mem_tt_wake_at.mp ht
  have hlt := hall 5 (mem_tt_kiss.mpr rfl)
  omega

/-- Scenario 12': Presupposition (wake₅ before kiss₅ ∨ wake₅ when kiss₅) is
    satisfied: the waking happens at the kiss time (when), so the left
    disjunct is false but the right is true. -/
theorem scenario12_presupposition :
    Anscombe.before A_wake_at B_kiss ∨ Karttunen.when_ A_wake_at B_kiss :=
  Or.inr ⟨5, mem_tt_wake_at.mpr rfl, mem_tt_kiss.mpr rfl⟩

/-- Scenario 12'': Presupposition + assertion → when (disjunctive syllogism).
    This is Karttunen's key result: "not until" + presupposition derives "when". -/
theorem scenario12_derives_when :
    Karttunen.when_ A_wake_at B_kiss :=
  notUntil_with_presupposition A_wake_at B_kiss
    scenario12_presupposition scenario12_notUntil_true

/-- ME: "The princess woke up" — punctual event at time 7 (AFTER the kiss). -/
def me_wake_late : Interval ℕ := Interval.point 7
abbrev A_wake_late := accomplishmentDenotation me_wake_late

private theorem mem_tt_wake_late {t : ℕ} :
    t ∈ timeTrace A_wake_late ↔ t = 7 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_wake_late, Interval.point, Set.mem_setOf_eq]
  omega

/-- Scenario 13: "The princess didn't wake up₇ until the prince kissed her₅"
    — TRUE. NOT(BEFORE) = NOT(wake₇ before kiss₅) = ¬(7 < 5) = True.
    She woke up after the kiss, so she didn't wake up before it. -/
theorem scenario13_notUntil_true : Karttunen.notUntil A_wake_late B_kiss := by
  intro ⟨t, ht, hall⟩
  have ht7 := mem_tt_wake_late.mp ht
  have hlt := hall 5 (mem_tt_kiss.mpr rfl)
  omega

/-- Scenario 13': wake₇ is NOT when kiss₅ (no overlap at any time point). -/
theorem scenario13_not_when : ¬ Karttunen.when_ A_wake_late B_kiss := by
  rintro ⟨t, ht_w, ht_k⟩
  have := mem_tt_wake_late.mp ht_w
  have := mem_tt_kiss.mp ht_k
  omega

/-- Scenario 13'': The presupposition (before ∨ when) is NOT satisfied,
    so *not...until* is vacuously true but pragmatically infelicitous.
    This models why "She didn't wake up until the prince kissed her" is
    odd when she woke up AFTER the kiss — the presupposition fails. -/
theorem scenario13_presup_fails :
    ¬ (Anscombe.before A_wake_late B_kiss ∨ Karttunen.when_ A_wake_late B_kiss) := by
  intro h
  cases h with
  | inl hbefore =>
    obtain ⟨t, ht, hall⟩ := hbefore
    have := mem_tt_wake_late.mp ht
    have := hall 5 (mem_tt_kiss.mpr rfl)
    omega
  | inr hwhen => exact scenario13_not_when hwhen

end Phenomena.TemporalConnectives.Examples
