import Linglib.Core.Optimization.Semiring
import Linglib.Core.Optimization.Dequantization.LogSumExp.Softmax
import Linglib.Phonology.HarmonicGrammar.OTLimit

/-!
# The Constraint-Framework Deformation Lattice
[smolensky-legendre-2006] [prince-smolensky-1993]
[goldwater-johnson-2003] [riggle-2009] [litvinov-2005]

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

This says: the OT winner is exactly the candidate whose harmony "tracks
the soft aggregator all the way to the limit."
-/

namespace HarmonicGrammar
open Constraints

open Core.Optimization


open Real Filter Topology Finset
open Constraints

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
theorem lse_aggregator_tendsto_winner_harmony {C : Type*} [DecidableEq C]
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M)
    (cands : Finset C) (c_opt : C) (hc_opt : c_opt ∈ cands)
    (hbound : ∀ c ∈ cands, ∀ con ∈ ranking, con c ≤ M)
    (hlex : ∀ c ∈ cands, c ≠ c_opt →
      toLex (fun i : Fin ranking.length => (ranking.get i) c_opt) <
      toLex (fun i : Fin ranking.length => (ranking.get i) c)) :
    Tendsto (fun α : ℝ =>
        lseFinset α cands (harmonyScore ranking.get (expWeights ranking.length M))) atTop
      (𝓝 (harmonyScore ranking.get (expWeights ranking.length M) c_opt)) := by
  have hne : cands.Nonempty := ⟨c_opt, hc_opt⟩
  apply (argmax_winner_iff_lse_max_limit hne hc_opt).mp
  intro c' hc'
  by_cases h : c' = c_opt
  · subst h; exact le_refl _
  · exact le_of_lt (ot_lex_imp_higher_harmony ranking M hM c_opt c'
      (fun con hcon => ⟨hbound c_opt hc_opt con hcon, hbound c' hc' con hcon⟩)
      (hlex c' hc' h))

end HarmonicGrammar
