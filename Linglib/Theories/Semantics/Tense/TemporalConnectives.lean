import Linglib.Core.MeasurementScale
import Linglib.Core.Time
import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Temporal Connective Semantics: *before* and *after*

Two competing semantic analyses of English *before*/*after*-clauses:

1. **Under-specification (Anscombe 1964; Krifka 2010b)**: Single lexical entry.
   *before B* = λt. ∀t' ∈ B, t < t'  (all of B follows the reference time)
   *after B*  = λt. ∃t' ∈ B, t' < t  (some of B precedes the reference time)
   Both are predicates on a time t; "A before B" holds when some time in A
   satisfies the predicate. Multiple readings arise from which point of B
   is relevant, determined by telicity.

2. **Ambiguity (Rett 2020)**: *before* and *after* are antonyms on converse
   scales, with strong defaults (before-start, after-finish). Non-default
   readings require aspectual coercion: **INCHOAT** (GLB, atelic → onset) or
   **COMPLET** (LUB, telic → telos), which incur processing cost.

   Rett's formal analysis (eqs. 22a-b):
   - ⟦A before B⟧ = ∃t ∈ A [t ≺ MAX(B_≺)]
   - ⟦A after B⟧  = ∃t ∈ A [t ≻ MAX(B_≻)]

Both theories use ∃ over the main clause A: "some time in A bears the
relation to (some characterization of) B." They differ in how B's
reference point is selected (all of B vs MAX of B).

## Bridges

- `INCHOAT` extracts the same point as `CoSType.inception` (onset of a state)
- `COMPLET` extracts the dual: the finish point of a telic event
- `stativeDenotation` has the subinterval property (connects to Krifka CUM)
- Both theories agree on unambiguous cases (stative before, telic after)

## References

- Anscombe, E. (1964). Before and after. *The Philosophical Review* 73, 3–24.
- Rett, J. (2020). Eliminating EARLIEST: a general semantics for *before* and
  *after*. *Proceedings of Sinn und Bedeutung* 24, 201–218.
- Krifka, M. (2010). *Before* and *after* without coercion. *NLLT* 28, 911–929.
- Alstott, A. & Aravind, A. (2026). Aspectual coercion in *before*/*after*-clauses.
- Beaver, D. & Condoravdi, C. (2003). A uniform analysis of *before* and *after*.
-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval
open Semantics.Lexical.Verb.Aspect
open Semantics.Lexical.Verb.ChangeOfState
open Core.Scale (maxOnScale isAmbidirectional maxOnScale_singleton
  maxOnScale_lt_closedInterval maxOnScale_gt_closedInterval)

-- ============================================================================
-- § 1: Sentence Denotations as Interval Sets
-- ============================================================================

variable {Time : Type*} [LinearOrder Time]

/-- A sentence denotes a set of temporal intervals (its "run-times").
    Statives denote homogeneous interval sets; accomplishments denote singletons. -/
abbrev SentDenotation (Time : Type*) [LE Time] := Set (Interval Time)

/-- The set of all time points contained in some interval of a denotation.
    This projects from interval-set representation to time-set representation,
    which is what Rett's (2020) formalization quantifies over. -/
def timeTrace (p : SentDenotation Time) : Set Time :=
  { t | ∃ i ∈ p, i.contains t }

/-- Stative denotation: the maximal interval `i` plus all its subintervals.
    Captures the subinterval (homogeneity) property of states/activities. -/
def stativeDenotation (i : Interval Time) : SentDenotation Time :=
  { j | subinterval j i }

/-- Accomplishment denotation: exactly the singleton interval `i`.
    Captures the quantized property of telic events. -/
def accomplishmentDenotation (i : Interval Time) : SentDenotation Time :=
  { j | j = i }

-- ============================================================================
-- § 2: Anscombe (1964) / Krifka (2010b) Under-specification
-- ============================================================================

/-- Anscombe's *before B* as a predicate on times (Krifka 2010b, eq. 13a):
    λt. ∀t' ∈ times(B), t < t'. All times at which B holds follow t.

    "A before B" then holds when some time in A satisfies this predicate. -/
def Anscombe.before (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

/-- Anscombe's *after B* as a predicate on times (Krifka 2010b, eq. 13b):
    λt. ∃t' ∈ times(B), t' < t. Some time at which B holds precedes t.

    "A after B" then holds when some time in A satisfies this predicate. -/
def Anscombe.after (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' < t

-- ============================================================================
-- § 3: Rett (2020) Antonymy + Aspectual Coercion
-- ============================================================================

/-- Rett's *before* (eq. 22a): ∃t ∈ times(A) [t ≺ MAX(times(B)_≺)].
    Some time in A precedes the maximal (on the ≺ scale) time of B. -/
def Rett.before (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· < ·) (timeTrace B), t < m

/-- Rett's *after* (eq. 22b): ∃t ∈ times(A) [t ≻ MAX(times(B)_≻)].
    Some time in A succeeds the maximal (on the ≻ scale) time of B. -/
def Rett.after (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· > ·) (timeTrace B), t > m

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
-- § 4: Proved Properties
-- ============================================================================

/-- Stative denotations are closed under subintervals (the subinterval property).
    This connects to Krifka's CUM (cumulative reference): if an interval is in
    the denotation, all its subintervals are too. -/
theorem stative_denotation_subinterval_closed (i : Interval Time) :
    ∀ j ∈ stativeDenotation i,
      ∀ k, subinterval k j → k ∈ stativeDenotation i := by
  intro j hj k hkj
  exact ⟨le_trans hj.1 hkj.1, le_trans hkj.2 hj.2⟩

/-- Every point subinterval of a stative denotation's maximal interval is in the set. -/
theorem stativeDenotation_contains_point (i : Interval Time) (t : Time)
    (ht : i.contains t) : Interval.point t ∈ stativeDenotation i :=
  ⟨ht.1, ht.2⟩

/-- An accomplishment denotation has exactly one member. -/
theorem accomplishmentDenotation_singleton (i : Interval Time) :
    ∀ j, j ∈ accomplishmentDenotation i ↔ j = i :=
  λ _ => Iff.rfl

/-- The maximal interval is in its own stative denotation (reflexivity). -/
theorem stativeDenotation_self (i : Interval Time) :
    i ∈ stativeDenotation i :=
  ⟨le_refl _, le_refl _⟩

/-- The time trace of a stative denotation is exactly the set of times
    contained in the maximal interval. -/
theorem timeTrace_stativeDenotation (i : Interval Time) :
    timeTrace (stativeDenotation i) = { t | i.contains t } := by
  ext t
  simp only [timeTrace, stativeDenotation, Set.mem_setOf_eq, contains, subinterval]
  constructor
  · rintro ⟨j, ⟨hjs, hjf⟩, hjt_s, hjt_f⟩
    exact ⟨le_trans hjs hjt_s, le_trans hjt_f hjf⟩
  · rintro ⟨hs, hf⟩
    exact ⟨Interval.point t, ⟨hs, hf⟩, le_refl _, le_refl _⟩

/-- The time trace of an accomplishment denotation is exactly the set of times
    contained in the unique interval. -/
theorem timeTrace_accomplishmentDenotation (i : Interval Time) :
    timeTrace (accomplishmentDenotation i) = { t | i.contains t } := by
  ext t
  simp only [timeTrace, accomplishmentDenotation, Set.mem_setOf_eq, contains]
  constructor
  · rintro ⟨j, rfl, hs, hf⟩
    exact ⟨hs, hf⟩
  · rintro ⟨hs, hf⟩
    exact ⟨i, rfl, hs, hf⟩

-- ============================================================================
-- § 5: INCHOAT / COMPLET Bridge Theorems
-- ============================================================================

/-- INCHOAT extracts the start point of a stative denotation.

    For `stativeDenotation i`, all members j satisfy `i.start ≤ j.start`
    (from subinterval), and i itself is a member with `j.start = i.start`.
    So the GLB of start times is exactly `i.start`. -/
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

/-- COMPLET extracts the finish point of an accomplishment denotation.

    For `accomplishmentDenotation i = {i}`, the unique member is i,
    so the LUB of finish times is `i.finish`. -/
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
-- § 6: Theory Agreement
-- ============================================================================

/-- Both theories predict "before-start" for statives (Rett 2020, Table 1).

    When B is stative (subinterval-closed), both theories reduce to
    "some time in A precedes all times in B":
    - Anscombe directly: ∃ t ∈ A, ∀ t' ∈ B, t < t'
    - Rett: ∃ t ∈ A, t < MAX(B_≺). For statives, MAX on ≺ picks B.start
      (the GLB), and t < B.start ↔ t < all times in B.

    (→) Anscombe → Rett: Take m = i_B.start, which is the minimum of
    timeTrace(stativeDenotation i_B), hence in maxOnScale (· < ·).
    The Anscombe ∀ gives t < i_B.start directly.

    (←) Rett → Anscombe: m ∈ maxOnScale (· < ·) means m is less than
    all other elements of the time trace. So for any t' in the trace,
    either t' = m (then t < m = t') or t' ≠ m (then m < t', so t < t'). -/
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
    when A overlaps B without extending past B's endpoint.

    Counterexample: B = [0, 10], A at time 5. Then 0 < 5 (Anscombe holds)
    but 5 < 10 (Rett fails). The ↔ formulation was incorrect; the theories
    genuinely diverge on the after-finish case when A overlaps B. -/
theorem rett_implies_anscombe_telic_after_finish
    (A : SentDenotation Time) (i_B : Interval Time) :
    Rett.after A (accomplishmentDenotation i_B) →
    Anscombe.after A (accomplishmentDenotation i_B) := by
  rintro ⟨t, ht_A, m, ⟨hm_mem, _⟩, htm⟩
  rw [timeTrace_accomplishmentDenotation] at hm_mem
  exact ⟨t, ht_A, m, by rw [timeTrace_accomplishmentDenotation]; exact hm_mem, htm⟩

-- ============================================================================
-- § 7: Ambidirectionality (Rett 2026)
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

Crucially, Rett's argument uses the **pre-event complement** (times
before B starts), not the full set-theoretic complement Bᶜ. She
explicitly stipulates (§5.1) that only pre-event runtimes of negative
events are relevant for temporal relations with embedded negation.
The full complement Bᶜ = (−∞, s) ∪ (f, +∞) has MAX₍<₎ = ∅ for dense
orders (no minimum in an open set), so `isAmbidirectional` with Bᶜ
is false in general.

*After* is NOT ambidirectional: negating B shifts the relevant bound,
so EN in *after*-clauses would be truth-conditionally distinct.

*While* requires total temporal overlap; ¬B fails when A overlaps B.

- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
- Jin, M. & Koenig, J.-P. (2021). A cross-linguistic survey of expletive
  negation. *Glossa* 6(1):25.
-/

/-- *Before* truth conditions depend only on MAX₍<₎ of B's time trace:
    if two denotations have the same `maxOnScale (· < ·)` on their time
    traces, then `Rett.before` gives the same truth conditions.

    This is the structural basis of Rett's (2026) ambidirectionality
    argument: *before* is insensitive to negation iff B and the
    pre-event complement of B share the same MAX₍<₎ on their time traces. -/
theorem before_determined_by_max (A B₁ B₂ : SentDenotation Time)
    (h : maxOnScale (· < ·) (timeTrace B₁) = maxOnScale (· < ·) (timeTrace B₂)) :
    Rett.before A B₁ ↔ Rett.before A B₂ := by
  constructor <;> rintro ⟨t, ht, m, hm, htm⟩ <;> exact ⟨t, ht, m, h ▸ hm, htm⟩

/-- When B's time trace is a closed interval [s, f], Rett.before reduces to
    "∃ t ∈ A, t < s". This is because MAX₍<₎([s,f]) = {s}
    (by `maxOnScale_lt_closedInterval`).

    Applied to stative/accomplishment denotations via `timeTrace_stativeDenotation`
    or `timeTrace_accomplishmentDenotation`. -/
theorem rett_before_closedTrace_eq (A B : SentDenotation Time) (s f : Time) (hsf : s ≤ f)
    (htrace : timeTrace B = { t | s ≤ t ∧ t ≤ f }) :
    Rett.before A B ↔ ∃ t ∈ timeTrace A, t < s := by
  unfold Rett.before
  rw [htrace, maxOnScale_lt_closedInterval s f hsf]
  constructor
  · rintro ⟨t, ht, m, rfl, htm⟩; exact ⟨t, ht, htm⟩
  · rintro ⟨t, ht, htm⟩; exact ⟨t, ht, s, rfl, htm⟩

/-- *Before* is ambidirectional w.r.t. the **pre-event complement** (Rett 2026, §5.2).

    Rett's argument: for B = [s, f], the pre-event complement is (−∞, s].
    Both B and the pre-event complement share s as their MAX₍<₎ element,
    so `Rett.before A B ↔ Rett.before A (preEvent B)`.

    **Status**: sorry. The formalization requires:
    1. A definition of `preEventComplement` capturing Rett's stipulation
       that only pre-event runtimes are relevant
    2. A proof that `maxOnScale (· < ·) (preEvent [s,f]) = {s}`, which
       requires the pre-event complement to be closed at s (i.e., (−∞, s]
       rather than the open (−∞, s))
    3. Temporal model constraints ensuring the pre-event complement is
       non-empty and closed at the boundary

    The original `isAmbidirectional` formulation (using full Bᶜ) is false:
    Bᶜ = (−∞, s) ∪ (f, +∞) has MAX₍<₎ = ∅ for dense Time (no minimum
    in an open set), and MAX₍<₎ = {min(Bᶜ)} ≠ {s} for discrete Time. -/
theorem before_ambidirectional (A : SentDenotation Time) (s f : Time) (hsf : s ≤ f) :
    isAmbidirectional
      (λ X => ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· < ·) X, t < m)
      { t | s ≤ t ∧ t ≤ f } := by
  sorry

/-- *After* is NOT ambidirectional (Rett 2026, §3.3): negating B in
    "A after B" changes truth conditions because MAX₍>₎(B) ≠ MAX₍>₎(¬B).

    Counterexample: B = {a} (singleton), A = {point b} with a < b.
    MAX₍>₎(B) = {a} (vacuously), so ∃ t ∈ A, t > a holds (b > a).
    For Bᶜ, any m ∈ maxOnScale (· > ·) Bᶜ satisfies m ≥ b (since b ∈ Bᶜ
    and m must dominate all others), so b > m fails. -/
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
/-- *While* is not ambidirectional: "∀ t ∈ A, t ∈ B" and "∀ t ∈ A, t ∈ Bᶜ"
    cannot both hold when A ∩ B is nonempty. So the construction is
    truth-conditionally sensitive to the polarity of its argument. -/
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
