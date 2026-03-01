import Linglib.Core.Scales.Scale
import Linglib.Core.Temporal.Time

/-!
# Temporal Connective Infrastructure
@cite{allen-1983} @cite{krifka-1989}

Shared types and basic lemmas for temporal connective semantics.

**Sentence denotations** are sets of temporal intervals — the "run-times" of
a sentence's truth. Two canonical patterns:
- **Stative**: the maximal interval plus all its subintervals (homogeneity)
- **Accomplishment**: a singleton interval (quantized)

**Temporal trace** (`timeTrace`) projects from interval sets (Level 2) to point
sets (Level 1). This is the lower half of the three-level projection chain:

```
Level 3: EvPred Time              (event predicates)
    ↓ eventDenotation             (see EventBridge.lean)
Level 2: SentDenotation Time      (interval sets — this file)
    ↓ timeTrace
Level 1: Set Time                 (point sets)
```

-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: Sentence Denotations as Interval Sets
-- ============================================================================

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
-- § 2: Basic Properties
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

end Semantics.Tense.TemporalConnectives
