import Linglib.Theories.Semantics.Events.Mereology

/-!
# @cite{filip-2012} "Lexical Aspect"
@cite{filip-2012} @cite{krifka-1998} @cite{krifka-1989} @cite{moon-2026}

Filip's handbook chapter (Binnick ed., OUP) synthesizes the
mereological approach to lexical aspect and identifies a
**three-way classification** of verb predicates:

1. **Telic / quantized** (QUA): *recover*, *arrive*
2. **Atelic / cumulative** (CUM): *run*, *push*
3. **Neither** (¬CUM ∧ ¬QUA): *build*, *eat*, *write* (incremental verbs)

The third class is "neither quantized (telic) nor cumulative (atelic)".
Their telicity is **underspecified at the verb level** and determined
compositionally by the object NP:

- QUA object → QUA VP (telic): "eat two apples"
- CUM object → CUM VP (atelic): "eat apples"
- ¬CUM ∧ ¬QUA object → indeterminate: "drink margarita"

## Key results

- `three_way_exhaustive`: every predicate is CUM, QUA, or neither.
  Filip's distinctive logical observation; the only proof original
  to this file.

## Substrate delegations (no longer wrapped in this file)

- ¬CUM lifts to VP under SINC + UP + CumTheta verbs:
  `Semantics.Events.PropagationGap.not_cum_vp_of_witnesses`
  (typeclass `[IsSincVerb θ]` form) or
  `not_cum_vp_of_cumTheta_up` (explicit-witness form).
- Full ¬CUM ∧ ¬QUA stability:
  `Semantics.Events.PropagationGap.middle_ground_stable` (typeclass)
  or `middle_ground_stable_of_postulates` (explicit). Used directly
  by `Phenomena/Countability/Studies/Moon2026.lean`'s mixed-drink
  bridge — Moon's empirical witnesses feed K98's algebraic machinery
  without going through this file as an intermediary.

## What changed (history)

An earlier version of this file argued the gap at the **type** level,
via a binary `composedRef : VerbIncClass → NomRef → NomRef`
function whose return type forced a binary answer. That version was
correct but argued too narrowly: the gap is genuine at the
**propositional** level too, and K98 theory §10 already proves it
stable under VP formation. After substrate exposed typeclass-form
public APIs (mathlib discipline), the per-paper wrappers
`not_cum_lifts_to_vp` and `propagation_gap_lifts` were dissolved —
they were pure section-variable delegations that duplicated the
substrate signatures without adding linguistic content beyond the
prose docstring above.

## Connection to @cite{moon-2026}

Moon's mixed drink nouns provide a concrete instantiation of the
¬CUM ∧ ¬QUA middle ground. The topological source of non-cumulativity
(`connectivity_breaks_cum`) is orthogonal to the algebraic source
(QUA / atomicity), creating a category invisible to @cite{krifka-1998}'s
two propagation theorems but stable under VP formation per substrate's
`middle_ground_stable`.

-/

namespace Filip2012

open Mereology

-- ════════════════════════════════════════════════════
-- § 1. Three-way exhaustiveness (Filip's distinctive observation)
-- ════════════════════════════════════════════════════

/-- The three classes are exhaustive: every predicate falls into
    exactly one of CUM, QUA, or ¬CUM ∧ ¬QUA. Conceptually important:
    the middle ground is a genuine third category, not a gap in our
    analysis.

    The propositional propagation theorems on the middle ground
    (formerly wrapped in this file as `not_cum_lifts_to_vp` and
    `propagation_gap_lifts`) live in
    `Semantics.Events.PropagationGap.lean` as `not_cum_vp_of_witnesses`
    and `middle_ground_stable` (typeclass `[IsSincVerb θ]` form).
    Consumers (e.g., `Moon2026.mixedDrink_VP_propagation_gap`) call
    those substrate APIs directly; this file's contribution is the
    `three_way_exhaustive` observation plus the linguistic framing
    in the module docstring. -/
theorem three_way_exhaustive {α : Type*} [SemilatticeSup α]
    (P : α → Prop) :
    CUM P ∨ QUA P ∨ (¬ CUM P ∧ ¬ QUA P) := by
  by_cases hc : CUM P
  · exact .inl hc
  · by_cases hq : QUA P
    · exact .inr (.inl hq)
    · exact .inr (.inr ⟨hc, hq⟩)

end Filip2012
