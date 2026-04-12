import Linglib.Theories.Pragmatics.IBR.Core
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits

/-!
# RSA–IBR Bridge: Softmax → Argmax Limit

As the rationality parameter α → ∞, RSA S1 concentrates on the
IBR-optimal message. This is because RSA S1 is a softmax over
log-informativity scores, and softmax → argmax as α → ∞
(`Softmax.tendsto_softmax_infty_at_max`).

This bridges RSA's probabilistic speaker to IBR's categorical
best-response operator. Combined with `ibr_equals_exhMW`
(in `ScalarGames.lean`), the full limit chain is:

```
RSA S1 (softmax) ──α→∞──> IBR S1 (argmax) ────> exhMW ──closure──> exhIE
```

The practical consequence: any phenomenon that exhaustification-based
theories cannot distinguish (e.g., @cite{denic-2023}'s
domain-size-invariant inference puzzle), RSA also cannot distinguish
in the high-rationality limit. Probabilistic mechanisms (like
informativeness-based pruning) are the only way out.
-/

namespace RSA.IBR

open Core

/-- Floor score for false messages. Uses -log(|State|) - 1, which is always
    below the minimum possible log-informativity for any true message. -/
noncomputable def falseMessageScore (G : InterpGame) : ℝ :=
  - Real.log (Fintype.card G.State : ℝ) - 1

/-- RSA S1 probability (real version for limit theorems).

RSA S1 is exactly softmax over log-informativity scores:
  rsaS1(m | s) = exp(α · log(inf(m))) / Σ exp(α · log(inf(m')))
              = inf(m)^α / Σ inf(m')^α
              = softmax(log ∘ inf, α)(m)
-/
noncomputable def rsaS1Real (G : InterpGame) (α : ℝ) (s : G.State) : G.Message → ℝ :=
  let score := λ m =>
    if G.meaning m s then Real.log (G.informativity m : ℝ) else falseMessageScore G
  softmax score α

/-- **The Limit Theorem** (@cite{franke-2011}, formalized):

As α → ∞, RSA S1 probability concentrates on the uniquely most
informative true message — which is exactly the IBR-optimal message.

This follows from `Softmax.tendsto_softmax_infty_at_max`: softmax
converges to 1 at the unique maximum as α → ∞. -/
theorem rsa_speaker_to_ibr (G : InterpGame) [Nonempty G.Message] (s : G.State) (m : G.Message)
    (hTrue : G.meaning m s = true)
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    Filter.Tendsto (λ α => rsaS1Real G α s m) Filter.atTop (nhds 1) := by
  let score := λ m' => if G.meaning m' s then Real.log (G.informativity m' : ℝ) else falseMessageScore G
  have hmax : ∀ m', m' ≠ m → score m' < score m := by
    intro m' hne
    simp only [score, hTrue, ↓reduceIte]
    split_ifs with hm'
    · have hm'_pos : 0 < G.informativity m' := by
        simp only [InterpGame.informativity]
        split_ifs with hcard
        · exfalso
          have hempty : G.trueStates m' = ∅ := Finset.card_eq_zero.mp hcard
          have hs_mem : s ∈ G.trueStates m' := G.mem_trueStates.mpr hm'
          simp only [hempty, Finset.notMem_empty] at hs_mem
        · exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard))
      exact Real.log_lt_log (Rat.cast_pos.mpr hm'_pos) (Rat.cast_lt.mpr (hUnique m' hne hm'))
    · simp only [falseMessageScore]
      haveI : Nonempty G.State := ⟨s⟩
      have hcard_pos : 0 < Fintype.card G.State := Fintype.card_pos
      have hs_in_true : s ∈ G.trueStates m := G.mem_trueStates.mpr hTrue
      have htrue_card_pos : 0 < (G.trueStates m).card :=
        Finset.card_pos.mpr ⟨s, hs_in_true⟩
      have htrue_card_le : (G.trueStates m).card ≤ Fintype.card G.State :=
        Finset.card_le_card (Finset.subset_univ _)
      have hinf_eq : G.informativity m = 1 / (G.trueStates m).card := by
        simp only [InterpGame.informativity]
        split_ifs with hcard
        · exact absurd hcard (Nat.pos_iff_ne_zero.mp htrue_card_pos)
        · rfl
      have hlog_eq : Real.log (G.informativity m : ℝ) = -Real.log ((G.trueStates m).card : ℝ) := by
        rw [hinf_eq]
        simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
            (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp htrue_card_pos)),
            Real.log_one]
        ring
      rw [hlog_eq]
      have hlog_le : Real.log ((G.trueStates m).card : ℝ) ≤ Real.log (Fintype.card G.State : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr htrue_card_pos) (Nat.cast_le.mpr htrue_card_le)
      linarith
  exact Softmax.tendsto_softmax_infty_at_max score m hmax

end RSA.IBR
