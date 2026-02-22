import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Anscombe
import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Rett (2020): Antonymy + Aspectual Coercion
@cite{rett-2020} @cite{rett-2026}

*before* and *after* are antonyms on converse scales, with strong defaults
(before-start, after-finish). Non-default readings require aspectual coercion:
**INCHOAT** (GLB, atelic → onset) or **COMPLET** (LUB, telic → telos), which
incur processing cost.

Rett's formal analysis (eqs. 22a-b):
- ⟦A before B⟧ = ∃t ∈ A [t ≺ MAX(B_≺)]
- ⟦A after B⟧  = ∃t ∈ A [t ≻ MAX(B_≻)]

Both theories use ∃ over the main clause A: "some time in A bears the
relation to (some characterization of) B." They differ in how B's
reference point is selected (all of B vs MAX of B).

## Level

**Level 2 (interval sets)**: operates on `SentDenotation` directly, using
`maxOnScale` from `Core.Scale` to select the informative bound.

## Bridges

- `INCHOAT` extracts the same point as `CoSType.inception` (onset of a state)
- `COMPLET` extracts the dual: the finish point of a telic event
- `stativeDenotation` has the subinterval property (connects to Krifka CUM)
- Both theories agree on unambiguous cases (stative before, telic after)

## Ambidirectionality (Rett 2026)

*before* is truth-conditionally insensitive to negation of its argument
(ambidirectional), which is why it licenses expletive negation cross-
linguistically. *after* and *while* are not ambidirectional.

## References

- Rett, J. (2020). Eliminating EARLIEST: a general semantics for *before* and
  *after*. *Proceedings of Sinn und Bedeutung* 24, 201–218.
- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
- Krifka, M. (2010). *Before* and *after* without coercion. *NLLT* 28, 911–929.
- Jin, Y. & Koenig, J.-P. (2021). A cross-linguistic study of expletive
  negation. *Linguistic Typology* 25(1), 39–78.
-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval
open Semantics.Lexical.Verb.Aspect
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

/-- Inchoative coercion / GLB (Rett 2020, eq. 19; de Swart 1998; Dölling 2014).
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

/-- Completive coercion / LUB (Rett 2020, eq. 21; Dölling 2014).
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

/-- Both theories predict "before-start" for statives (Rett 2020, Table 1).

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

/-- Rett's analysis implies Anscombe's for telic "after" (Rett 2020, Table 1).

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
-- § 6: Ambidirectionality (Rett 2026)
-- ============================================================================

/-! ### Expletive negation and ambidirectionality

Rett (2026, §5) shows that *before* is **ambidirectional**: negating B
in "A before B" doesn't change truth conditions. This is why
*before*-clauses license expletive negation cross-linguistically
(Jin & Koenig 2021: 50 languages).

The mechanism (Rett 2026, §5.2): for B = [s, f], both B and its
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

/-- The pre-event complement of an event interval [s, f] (Rett 2026, §5.1). -/
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

/-- *Before* is truth-conditionally insensitive to event polarity (Rett 2026, §5.2).

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

/-- *After* is NOT ambidirectional (Rett 2026, §3.3): negating B changes
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
