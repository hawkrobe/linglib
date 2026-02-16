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
open Core.Scale (maxOnScale isAmbidirectional maxOnScale_singleton)

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
-- § 6: Theory Agreement (sorry'd — see notes)
-- ============================================================================

/-- Both theories predict "before-start" for statives (Rett 2020, Table 1).

    When B is stative (subinterval-closed), both theories reduce to
    "some time in A precedes all times in B":
    - Anscombe directly: ∃ t ∈ A, ∀ t' ∈ B, t < t'
    - Rett: ∃ t ∈ A, t < MAX(B_≺). For statives, MAX on ≺ picks B.start
      (the GLB), and t < B.start ↔ t < all times in B.

    The ← direction (Rett → Anscombe) requires showing that if
    t < MAX(B_≺) then t < all of B, which needs the stative's
    subinterval property to guarantee MAX(B_≺) = B.start.

    TODO: The proof requires showing maxOnScale (· < ·) (timeTrace (stativeDenotation i))
    = {i.start}, which follows from the same GLB argument as inchoat_bridges_inception
    but applied to timeTrace rather than interval starts. -/
theorem anscombe_rett_agree_stative_before_start
    (A : SentDenotation Time) (i_B : Interval Time) :
    (Anscombe.before A (stativeDenotation i_B) ↔
     Rett.before A (stativeDenotation i_B)) := by
  sorry

/-- Both theories predict "after-finish" for accomplishments (Rett 2020, Table 1).

    When B is an accomplishment (singleton {i}), both reduce to
    "some time in A follows the finish of i":
    - Anscombe: ∃ t ∈ A, ∃ t' ∈ {i}, t' < t — i.e., ∃ t ∈ A, some point in i < t
    - Rett: ∃ t ∈ A, t > MAX(B_≻). For singletons, MAX on ≻ picks i.finish
      (the LUB), so t > i.finish.

    The → direction (Anscombe → Rett) requires that the Anscombe witness t'
    can be promoted to i.finish (via MAX). This holds because the only interval
    in B is i, so times(B) = [i.start, i.finish] and MAX_≻ = i.finish.

    TODO: The proof requires showing maxOnScale (· > ·) (timeTrace (accomplishmentDenotation i))
    = {i.finish}, analogous to complet_bridges_cessation. -/
theorem anscombe_rett_agree_telic_after_finish
    (A : SentDenotation Time) (i_B : Interval Time) :
    (Anscombe.after A (accomplishmentDenotation i_B) ↔
     Rett.after A (accomplishmentDenotation i_B)) := by
  sorry

-- ============================================================================
-- § 7: Ambidirectionality (Rett 2026)
-- ============================================================================

/-! ### Expletive negation and ambidirectionality

Rett (2026, §3) shows that *before* is **ambidirectional**: negating B
in "A before B" doesn't change truth conditions, because MAX₍<₎ on B
and MAX₍<₎ on ¬B share the starting-point bound (for telic B on a
closed interval). This is why *before*-clauses license expletive
negation cross-linguistically (Jin & Koenig 2021: 50 languages).

*After* is NOT ambidirectional: negating B yields trivially-true truth
conditions (A > −∞), so EN in *after*-clauses would be truth-conditionally
distinct (uninformative).

*While* requires total temporal overlap; ¬B fails when A overlaps B.

- Rett, J. (2026). Semantic ambivalence and expletive negation. *Language*.
- Jin, M. & Koenig, J.-P. (2021). A cross-linguistic survey of expletive
  negation. *Glossa* 6(1):25.
-/

/-- *Before* is ambidirectional on closed intervals (Rett 2026, §3.2):
    when B is the time trace of a telic event — a closed interval [s, f] —
    MAX₍<₎(B) and MAX₍<₎(Bᶜ) share s as their informative bound.

    The critical hypothesis is that B is a **closed interval**: B = {t | s ≤ t ∧ t ≤ f}.
    Without this, the theorem is false (e.g., for open or unbounded B,
    MAX₍<₎(Bᶜ) may not share a bound with MAX₍<₎(B)).

    Proof sketch: MAX₍<₎({t | s ≤ t ∧ t ≤ f}) = {s} because s is in B
    and s < t' for all t' ∈ B with t' ≠ s. For Bᶜ = (−∞, s) ∪ (f, +∞),
    MAX₍<₎(Bᶜ) depends on whether (−∞, s) is nonempty, but the infimum
    of the right component f is > s, so "A before Bᶜ" ↔ "∃ t ∈ A, t < s"
    ↔ "A before B". -/
theorem before_ambidirectional (A : SentDenotation Time) (s f : Time) (hsf : s ≤ f) :
    isAmbidirectional
      (λ X => ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· < ·) X, t < m)
      { t | s ≤ t ∧ t ≤ f } := by
  sorry

/-- *After* is NOT ambidirectional (Rett 2026, §3.3): negating B in
    "A after B" changes truth conditions because MAX₍>₎(B) ≠ MAX₍>₎(¬B).
    For telic B = [s, f], MAX₍>₎(B) = {f}, but MAX₍>₎(¬B) on an
    unbounded complement may be empty (no element >-dominates all others),
    making "A after ¬B" trivially false, or — if it exists — yields a
    different bound. Either way, truth conditions change. -/
theorem after_not_ambidirectional :
    ¬ ∀ (A : SentDenotation Time) (B : Set Time),
      isAmbidirectional (λ X => ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale (· > ·) X, t > m) B := by
  sorry

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
