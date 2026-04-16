import Linglib.Core.Constraint.Decoder
import Mathlib.Algebra.Tropical.BigOperators

/-!
# Semiring View of Deterministic Decoders

When the noise kernel is `dirac` (no noise), score aggregation in a
constraint system is itself an algebraic operation: the *additive*
operation in a tropical or max-plus semiring. This is the bridge from
the RUM/decoder picture to the parsing-theoretic semiring picture
(@cite{goodman-1999}; @cite{eisner-2002}; @cite{mohri-2002}).

| Decoder            | Underlying algebraic structure                    |
|--------------------|---------------------------------------------------|
| `argminDecoder`    | min-plus tropical semiring `Tropical R`           |
| `argmaxDecoder`    | max-plus semiring (= tropical over `OrderDual R`) |
| `softmaxDecoder α` | log-sum-exp ("warped") semiring on `ℝ`            |

In each row, the *additive* identity of the semiring is the "winner
takes all" choice operation across alternatives, and the *multiplicative*
identity is the per-candidate score-combination operation. The decoder's
job is then to identify which candidates realise the additive identity.

## What this file proves

The bridge to mathlib's `Tropical R` (a min-plus semiring): the tropical
sum of `trop`-tagged scores is `trop` of their `inf`. Specialised to a
Finset of candidates, this says that choosing the additive identity in
the tropical semiring picks out exactly the score that `argminDecoder`
distributes its mass over — making the algebraic and operational views
of OT coincide.

The max-plus dual follows by replacing `R` with `OrderDual R`: HG's
argmax is then the same algebraic operation in the dual semiring.

## What is deferred

The log-sum-exp ↔ max-plus correspondence in the `α → ∞` limit is
the semiring-homomorphism statement of `softmax_argmax_limit`
(`Core.Agent.RationalAction`). Its full categorical statement —
log-sum-exp as a one-parameter family of semirings deforming to
max-plus — requires limit-of-semiring infrastructure not yet built
out here.
-/

namespace Core.Constraint

open Tropical

-- ============================================================================
-- § 1: Tropical Sum = Inf (Min-Plus / OT)
-- ============================================================================

/-- The tropical sum of scores equals the `inf` of the underlying values.

    Aggregating "or" alternatives in `Tropical R` (where `+` is `min`)
    computes the minimum. This is the algebraic statement underlying
    `argminDecoder`: the OT winner is the candidate realising the
    tropical sum.

    Direct restatement of mathlib's `Finset.untrop_sum'` for clarity in
    the constraint-system context. -/
theorem trop_sum_eq_inf_score {Cand R : Type*} [LinearOrder R] [OrderTop R]
    (cands : Finset Cand) (score : Cand → R) :
    untrop (∑ c ∈ cands, trop (score c)) = cands.inf score := by
  rw [Finset.untrop_sum']
  rfl

-- ============================================================================
-- § 2: Argmin Picks the Tropical Sum's Value (OT)
-- ============================================================================

/-- A candidate `c ∈ cands` is an `argminDecoder` winner exactly when its
    score equals the tropical-semiring sum of all candidate scores.

    This is the operational ↔ algebraic bridge for OT: the decoder's
    notion of "winner" coincides with the candidate realising the
    additive identity of the tropical semiring. -/
theorem argmin_winner_iff_trop_sum {Cand R : Type*}
    [LinearOrder R] [OrderTop R]
    {cands : Finset Cand} {score : Cand → R} {c : Cand} (hc : c ∈ cands) :
    (∀ c' ∈ cands, score c ≤ score c') ↔
    score c = untrop (∑ c' ∈ cands, trop (score c')) := by
  rw [trop_sum_eq_inf_score]
  constructor
  · intro hmin
    apply le_antisymm
    · exact Finset.le_inf (fun c' hc' => hmin c' hc')
    · exact Finset.inf_le hc
  · intro heq c' hc'
    rw [heq]
    exact Finset.inf_le hc'

-- ============================================================================
-- § 3: Max-Plus Dual (HG)
-- ============================================================================

/-!
## Max-plus semiring for HG

The max-plus semiring on `R` is the tropical semiring on `OrderDual R`:
addition is `max` (= `min` in the dual order), multiplication is the
underlying `+`. For real-valued harmony scores in HG, the relevant
structure is max-plus on `WithBot ℝ` (with `-∞` as the additive identity).

The argmax decoder is the max-plus analogue of `argminDecoder`:
`argmaxDecoder` picks the candidate(s) realising the max-plus sum of
all candidate scores, i.e., the maximum harmony.

Stating this via the existing tropical machinery requires going through
`OrderDual` plus `WithTop` instances; for our purposes the concrete
`argminDecoder ↔ trop_sum` bridge above is the main statement, and the
HG case is its dual.
-/

end Core.Constraint
