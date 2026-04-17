import Linglib.Core.Constraint.Dequantization.LogSumExp.Basic
import Linglib.Core.Constraint.Dequantization.LogSumExp.Limit
import Linglib.Core.Constraint.Decoder

/-!
# Softmax as `lse`-Renormalised Exponential
@cite{litvinov-2005}

The bridge between the warped semiring (`lse α`) and the choice rule
(`softmaxDecoder α`). The softmax probability admits the clean
"partition-function" form

```
  softmaxDecoder α |>.decode cands score c
    = exp(α · (score c - lseFinset α cands score))
```

for `c ∈ cands` (the candidate set), since the partition function
`Z = Σ exp(α · score c')` is exactly `exp(α · lseFinset α cands score)`
by the cancellation identity `exp_alpha_lseFinset`.

This identity makes the softmax → argmax limit a direct corollary of
the lse → max limit (`lse_tendsto_max`):
- `lseFinset α cands score → max_c (score c)` as `α → ∞`,
- so the exponent `α · (score c - lseFinset α cands score)` tends to
  `0` for the unique maximizer (probability → 1) and to `−∞` for any
  loser (probability → 0).

That gives a uniform algebraic explanation for OT-as-MaxEnt-limit:
the softmax decoder is "exp of the gap between this candidate's score
and the lse-summary score," and the gap closes exactly on the winners
when the warped semiring is dequantized.
-/

namespace Core.Constraint

open Real Finset

-- ============================================================================
-- § 1: The Partition-Function Form of `softmaxDecoder`
-- ============================================================================

/-- **Partition-function form of the softmax decoder.** For `c ∈ cands`
    and `α ≠ 0`,

    ```
      softmaxDecoder α |>.decode cands score c
        = exp(α · (score c - lseFinset α cands score))
    ```

    Direct from the cancellation identity `exp_alpha_lseFinset`: the
    denominator `Σ exp(α · score c')` equals `exp(α · lseFinset α …)`,
    so the softmax ratio reduces to `exp(α · score c) / exp(α · lse)
    = exp(α · (score c − lse))`. -/
theorem softmaxDecoder_eq_exp_score_sub_lse {Cand : Type*} (α : ℝ) (hα : α ≠ 0)
    {cands : Finset Cand} (score : Cand → ℝ) {c : Cand} (hc : c ∈ cands) :
    (softmaxDecoder α).decode cands score c
      = exp (α * (score c - lseFinset α cands score)) := by
  classical
  have hne : cands.Nonempty := ⟨c, hc⟩
  show (if c ∈ cands then exp (α * score c) / ∑ c' ∈ cands, exp (α * score c')
        else 0) = _
  rw [if_pos hc, ← exp_alpha_lseFinset α hα hne score]
  rw [show α * (score c - lseFinset α cands score)
        = α * score c - α * lseFinset α cands score from by ring,
      Real.exp_sub]

-- ============================================================================
-- § 2: A Clean "lse-Centred" Form of the Softmax Probability
-- ============================================================================

/-- The softmax-decoder probability of a candidate, written as a single
    exponential of the *gap* between its score and the lse summary.

    Useful corollary: when `score c = max_c' score`, the gap closes in
    the `α → ∞` limit (since `lseFinset α cands score → max`), so the
    exponent → `0` and the probability → `1`. When `score c < max`, the
    exponent → `α · (score c - max) → −∞`, so the probability → `0`.
    See `Limit.lean` for the limit theorem and Phase 4 for the formal
    argmax-winner characterisation. -/
theorem softmaxDecoder_eq_exp_gap {Cand : Type*} (α : ℝ) (hα : α ≠ 0)
    {cands : Finset Cand} (score : Cand → ℝ) (c : Cand) (hc : c ∈ cands) :
    (softmaxDecoder α).decode cands score c
      = exp (α * (score c - lseFinset α cands score)) :=
  softmaxDecoder_eq_exp_score_sub_lse α hα score hc

-- ============================================================================
-- § 3: Dual statement — `softmaxDecoder = exp(α·s) / exp(α·lse)` (raw form)
-- ============================================================================

/-- The raw ratio form of the partition-function identity.

    Sometimes more convenient than `_eq_exp_gap` when chaining with
    inequalities on the partition function (e.g., comparing softmax
    probabilities of two different candidates: the `lse` term cancels). -/
theorem softmaxDecoder_eq_exp_div_exp_lse {Cand : Type*} (α : ℝ) (hα : α ≠ 0)
    {cands : Finset Cand} (score : Cand → ℝ) {c : Cand} (hc : c ∈ cands) :
    (softmaxDecoder α).decode cands score c
      = exp (α * score c) / exp (α * lseFinset α cands score) := by
  classical
  have hne : cands.Nonempty := ⟨c, hc⟩
  show (if c ∈ cands then exp (α * score c) / ∑ c' ∈ cands, exp (α * score c')
        else 0) = _
  rw [if_pos hc, ← exp_alpha_lseFinset α hα hne score]

end Core.Constraint
