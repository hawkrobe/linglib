import Linglib.Core.Constraint.Semiring
import Linglib.Core.Constraint.Dequantization.LogSumExp.Softmax
import Linglib.Core.Constraint.Dequantization.ViolationSemiring
import Linglib.Core.Constraint.Dequantization.OTLimit

/-!
# The Constraint-Framework Deformation Lattice
@cite{smolensky-legendre-2006} @cite{prince-smolensky-1993}
@cite{goldwater-johnson-2003} @cite{riggle-2009} @cite{litvinov-2005}

OT, HG, MaxEnt, and Stochastic OT are not four unrelated frameworks but
the four corners of a single **deformation lattice**, parameterised by
two independent dequantization axes:

```
                    weights = real-valued, exp-separated?
                  ───────────────────────────────────────►
                     no                       yes
              ┌─────────────────────┬──────────────────────┐
   soft   ⌃   │                     │                      │
   (α<∞)  │   │      MaxEnt         │   Stochastic OT      │
          │   │   (real-soft)       │  (categorical-soft)  │
          │   │                     │                      │
   ───────┼───┼─────────────────────┼──────────────────────┤
          │   │                     │                      │
   hard   │   │        HG           │        OT            │
   (α→∞)  │   │   (real-hard)       │  (categorical-hard)  │
          │   │                     │                      │
              └─────────────────────┴──────────────────────┘
```

- **Vertical axis** (temperature, `α → ∞`): Maslov dequantization of
  the warped semiring (`Constraint/LogSumExp/Limit.lean`).
  `lseFinset α cands score → cands.sup' hne score`. The soft
  aggregator (sum-of-exponentials) becomes the hard one (max).
- **Horizontal axis** (weight separation): exponential separation of
  HG weights (`Constraint/OTLimit.lean`, `ViolationSemiring.lean`).
  The weight map V → T preserves not just ⊗ but also ⊕, so the
  HG argmax coincides with the OT lex-min.

Going around the lattice diagonally — MaxEnt → OT — is then the
composition: dequantize the temperature *and* exponentially separate
the weights. The composite limit theorem is `maxent_ot_limit` in
`Constraint/OTLimit.lean`.

## What this file adds

`OTLimit.lean` already proves `maxent_ot_limit` via `softmax_argmax_limit`
(Banach-style concentration of softmax on argmax). This file provides
the **algebraic, semiring-level** restatement: the same composite limit
viewed through the lens of `lseFinset` (the warped semiring's additive
operator at finite temperature). The two viewpoints are equivalent —
softmax(α·H)(c) → 1 iff lseFinset α H → H(c) — but the lse picture makes
the two dequantization axes visible side-by-side.

Concretely:

1. `lse_aggregator_tendsto_winner_harmony` — the `lseFinset α` aggregator
   on harmony scores tends to the harmony of the OT winner as α → ∞.
   This is `argmax_winner_iff_lse_max_limit` composed with
   `ot_lex_imp_higher_harmony`.

2. `softmax_decoder_gap_form` — packaged restatement of the
   partition-function identity `softmax = exp(α · gap)`, where the gap
   is the difference between this candidate's harmony and the warped
   aggregate. The OT winner closes the gap to 0 in the limit; losers
   open it to −∞.

The two together say: the OT winner is exactly the candidate whose
harmony "tracks the soft aggregator all the way to the limit." Every
other candidate's softmax probability decays exponentially in the gap.
-/

namespace Core.Constraint

open Real Filter Topology Finset
open Core.Constraint.OT Core.Constraint.ViolationSemiring

-- ============================================================================
-- § 1: The Soft Aggregator on Harmony Scores
-- ============================================================================

/-- The `lseFinset α` aggregator applied to harmony scores converges to
    the OT winner's harmony as `α → ∞`.

    This is the lse-flavored restatement of `maxent_ot_limit`. Where
    `maxent_ot_limit` says the softmax probability concentrates on the
    OT winner, this says the warped aggregator's value converges to the
    OT winner's harmony — i.e., the OT winner is exactly the candidate
    whose harmony is realised in the dequantized limit of the warped
    semiring's additive operator.

    The proof composes:
    1. `ot_lex_imp_higher_harmony` (HG–OT agreement under exponentially
       separated weights)
    2. `argmax_winner_iff_lse_max_limit` (the dequantized argmax bridge,
       § 4 of `Constraint/Semiring.lean`) -/
theorem lse_aggregator_tendsto_winner_harmony {C : Type} [DecidableEq C]
    (ranking : List (NamedConstraint C)) (M : Nat) (hM : 0 < M)
    (cands : Finset C) (c_opt : C) (hc_opt : c_opt ∈ cands)
    (hbound : ∀ c ∈ cands, ∀ con ∈ ranking, con.eval c ≤ M)
    (hlex : ∀ c ∈ cands, c ≠ c_opt → LexStrictlyBetter
      (fun i : Fin ranking.length => (ranking.get i).eval c_opt)
      (fun i : Fin ranking.length => (ranking.get i).eval c)) :
    Tendsto (fun α : ℝ =>
        lseFinset α cands (harmonyScoreR (otToWeighted ranking M))) atTop
      (𝓝 (harmonyScoreR (otToWeighted ranking M) c_opt)) := by
  have hne : cands.Nonempty := ⟨c_opt, hc_opt⟩
  apply (argmax_winner_iff_lse_max_limit hne hc_opt).mp
  intro c' hc'
  by_cases h : c' = c_opt
  · subst h; exact le_refl _
  · exact le_of_lt (ot_lex_imp_higher_harmony ranking M hM c_opt c'
      (fun con hcon => ⟨hbound c_opt hc_opt con hcon, hbound c' hc' con hcon⟩)
      (hlex c' hc' h))

-- ============================================================================
-- § 2: The Softmax Gap Form
-- ============================================================================

/-- **Softmax-decoder gap form.** For `c ∈ cands` and `α ≠ 0`, the
    softmax probability is `exp(α · (score c − lseFinset))`. The
    lse-summary `lseFinset α cands score` lies in `[max_c' score c',
    max_c' score c' + log(card)/α]` (sandwich from `LogSumExp/Limit.lean`).

    Reading this off:
    - For the unique max-score candidate, the gap `score c − lseFinset`
      tends to `0` as `α → ∞`, so the probability tends to `1`.
    - For any sub-optimal candidate, the gap tends to `score c − max < 0`,
      so `α · gap → −∞`, so the probability tends to `0`.

    This is `softmaxDecoder_eq_exp_score_sub_lse` repackaged with a
    pointer to the dequantization story; the per-candidate limit
    behaviour is the algebraic content of `softmax_argmax_limit`. -/
theorem softmax_decoder_gap_form {Cand : Type*} (α : ℝ) (hα : α ≠ 0)
    {cands : Finset Cand} (score : Cand → ℝ) {c : Cand} (hc : c ∈ cands) :
    (softmaxDecoder α).decode cands score c
      = exp (α * (score c - lseFinset α cands score)) :=
  softmaxDecoder_eq_exp_score_sub_lse α hα score hc

end Core.Constraint
