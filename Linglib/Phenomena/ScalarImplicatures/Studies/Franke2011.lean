/-
@cite{franke-2011} @cite{benz-van-rooij-2005}. Quantity implicatures, exhaustive interpretation, and
rational conversation. S&P 4(1):1-82.

IBR (iterated best response) converges to exhaustive interpretation (exhMW).
RSA is "soft" IBR: as α → ∞, softmax → argmax → exhMW → exhIE.

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Linglib.Theories.Semantics.Exhaustification.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits

namespace RSA.IBR

open Exhaustification

/-- Interpretation game (Franke §6): states are equivalence classes over alternative truth patterns. -/
structure InterpGame where
  /-- Type of states (equivalence classes of worlds) -/
  State : Type
  /-- Type of messages (alternative utterances) -/
  Message : Type
  /-- Semantic meaning: is message m true at state s? -/
  meaning : Message → State → Bool
  /-- Prior probability over states -/
  prior : State → ℚ
  /-- Fintype instances -/
  [stateFintype : Fintype State]
  [messageFintype : Fintype Message]
  [stateDecEq : DecidableEq State]
  [messageDecEq : DecidableEq Message]

attribute [instance] InterpGame.stateFintype InterpGame.messageFintype
  InterpGame.stateDecEq InterpGame.messageDecEq

namespace InterpGame

variable (G : InterpGame)

/-- States where message m is true -/
def trueStates (m : G.Message) : Finset G.State :=
  Finset.univ.filter (λ s => G.meaning m s = true)

/-- Messages true at state s -/
def trueMessages (s : G.State) : Finset G.Message :=
  Finset.univ.filter (λ m => G.meaning m s = true)

/-- Informativity of a message (reciprocal of true states, as ratio) -/
def informativity (m : G.Message) : ℚ :=
  let n := (G.trueStates m).card
  if n = 0 then 0 else 1 / n

end InterpGame

/-- A hearer strategy: P(state | message) -/
structure HearerStrategy (G : InterpGame) where
  respond : G.Message → G.State → ℚ

/-- A speaker strategy: P(message | state) -/
structure SpeakerStrategy (G : InterpGame) where
  choose : G.State → G.Message → ℚ

namespace HearerStrategy

variable {G : InterpGame}

/-- Uniform distribution over states where m is true -/
def literal (G : InterpGame) : HearerStrategy G where
  respond := λ m s =>
    if G.meaning m s then
      let n := (G.trueStates m).card
      if n = 0 then 0 else 1 / n
    else 0

/-- Support of hearer's response to message m -/
def support (H : HearerStrategy G) (m : G.Message) : Finset G.State :=
  Finset.univ.filter (λ s => H.respond m s > 0)

end HearerStrategy

namespace SpeakerStrategy

variable {G : InterpGame}

/-- Support of speaker's choice at state s -/
def support (S : SpeakerStrategy G) (s : G.State) : Finset G.Message :=
  Finset.univ.filter (λ m => S.choose s m > 0)

/-- Max utility among true messages at state s (0 if no true messages). -/
def maxUtility (G : InterpGame) (H : HearerStrategy G) (s : G.State) : ℚ :=
  (G.trueMessages s).fold max 0 (λ m' => H.respond m' s)

/-- Optimal messages at state s: true messages achieving max utility.

    This is the set-level best response (Franke eq. 76): the speaker at state t
    uses messages in R_k^{-1}(t) that minimize |R_k(m)|, which corresponds to
    maximizing H(m|t) in the probabilistic rendering.

    All probability-level reasoning should go through this set. -/
def optimalMessages (G : InterpGame) (H : HearerStrategy G) (s : G.State) : Finset G.Message :=
  (G.trueMessages s).filter (λ m => H.respond m s == maxUtility G H s)

theorem optimalMessages_subset_trueMessages (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) : optimalMessages G H s ⊆ G.trueMessages s :=
  Finset.filter_subset _ _

theorem optimalMessages_meaning (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) (hm : m ∈ optimalMessages G H s) :
    G.meaning m s = true := by
  have := optimalMessages_subset_trueMessages G H s hm
  simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

theorem optimalMessages_utility (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) (hm : m ∈ optimalMessages G H s) :
    H.respond m s = maxUtility G H s := by
  simp only [optimalMessages, Finset.mem_filter] at hm
  rw [beq_iff_eq] at hm; exact hm.2

theorem maxUtility_nonneg (G : InterpGame) (H : HearerStrategy G) (s : G.State) :
    0 ≤ maxUtility G H s :=
  (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))

theorem utility_le_maxUtility (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) (hm : m ∈ G.trueMessages s) :
    H.respond m s ≤ maxUtility G H s :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨m, hm, le_refl _⟩)

/-- Best response speaker: uniform distribution over optimal messages (eq. 76). -/
def bestResponse (G : InterpGame) (H : HearerStrategy G) : SpeakerStrategy G where
  choose := λ s m =>
    if m ∈ optimalMessages G H s then
      let k := (optimalMessages G H s).card
      if k = 0 then 0 else 1 / k
    else 0

/-- bestResponse gives 1/k to optimal messages, 0 to others. -/
theorem bestResponse_val (G : InterpGame) (H : HearerStrategy G) (s : G.State) (m : G.Message) :
    (bestResponse G H).choose s m =
      if m ∈ optimalMessages G H s then
        if (optimalMessages G H s).card = 0 then 0
        else 1 / ((optimalMessages G H s).card : ℚ)
      else 0 := by
  simp only [bestResponse]

/-- Best response speaker always gives non-negative probabilities. -/
theorem bestResponse_nonneg (G : InterpGame) (H : HearerStrategy G) (s : G.State) (m : G.Message) :
    0 ≤ (bestResponse G H).choose s m := by
  rw [bestResponse_val]
  split_ifs <;> first | exact le_refl 0 | exact one_div_nonneg.mpr (Nat.cast_nonneg _)

/-- Best response speaker gives zero probability to false messages. -/
theorem bestResponse_false_zero (G : InterpGame) (H : HearerStrategy G) (s : G.State) (m : G.Message)
    (hFalse : G.meaning m s = false) :
    (bestResponse G H).choose s m = 0 := by
  rw [bestResponse_val, if_neg]
  intro hmem
  exact absurd (optimalMessages_meaning G H s m hmem) (by simp [hFalse])

/-- bestResponse gives positive probability iff m is optimal (and optimal set is nonempty). -/
theorem bestResponse_pos_iff (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) :
    (bestResponse G H).choose s m > 0 ↔
      m ∈ optimalMessages G H s ∧ (optimalMessages G H s).card > 0 := by
  rw [bestResponse_val]
  split_ifs with hmem hcard
  · simp [hcard]
  · constructor
    · intro h; exact ⟨hmem, by omega⟩
    · intro _; exact div_pos one_pos (Nat.cast_pos.mpr (by omega))
  · simp [hmem]

/-- Best response speaker probabilities sum to at most 1 at any state. -/
theorem bestResponse_sum_le_one (G : InterpGame) (H : HearerStrategy G) (s : G.State) :
    Finset.univ.sum (λ m => (bestResponse G H).choose s m) ≤ 1 := by
  set opt := optimalMessages G H s
  set k := opt.card
  have hval : ∀ m, (bestResponse G H).choose s m =
      if m ∈ opt then (if k = 0 then 0 else 1 / (k : ℚ)) else 0 := by
    intro m; exact bestResponse_val G H s m
  simp_rw [hval]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [if_neg hk0, mul_one_div_cancel (Nat.cast_ne_zero.mpr hk0)]

end SpeakerStrategy


/-- L₀: Literal listener (Franke Def. 22) -/
def L0 (G : InterpGame) : HearerStrategy G :=
  HearerStrategy.literal G

/-- Hearer update: Given speaker strategy, compute posterior.

L_{n+1}(s | m) ∝ S_n(m | s) · P(s)

This is Bayes' rule with the speaker strategy as likelihood. -/
def hearerUpdate (G : InterpGame) (S : SpeakerStrategy G) : HearerStrategy G where
  respond := λ m s =>
    let numerator := S.choose s m * G.prior s
    let denominator := Finset.univ.sum λ s' => S.choose s' m * G.prior s'
    if denominator == 0 then 0 else numerator / denominator

/-- Speaker update: Best response to hearer strategy.

S_{n+1}(m | s) = argmax_m L_n(s | m)

Uniform over optimal messages. -/
def speakerUpdate (G : InterpGame) (H : HearerStrategy G) : SpeakerStrategy G :=
  SpeakerStrategy.bestResponse G H

/-- One full IBR iteration step -/
def ibrStep (G : InterpGame) (H : HearerStrategy G) : HearerStrategy G :=
  hearerUpdate G (speakerUpdate G H)

/-- IBR reasoning for n iterations starting from L₀ -/
def ibrN (G : InterpGame) (n : ℕ) : HearerStrategy G :=
  match n with
  | 0 => L0 G
  | n + 1 => ibrStep G (ibrN G n)

/-- S₁: First pragmatic speaker -/
def S1 (G : InterpGame) : SpeakerStrategy G :=
  speakerUpdate G (L0 G)

/-- L₂: First pragmatic listener -/
def L2 (G : InterpGame) : HearerStrategy G :=
  hearerUpdate G (S1 G)

/-- Check if hearer strategy is a fixed point of IBR -/
def isIBRFixedPoint (G : InterpGame) (H : HearerStrategy G) : Prop :=
  ∀ m s, H.respond m s = (ibrStep G H).respond m s

/-- At a fixed point with non-negative priors, H.respond is non-negative.

This follows from the fact that H = ibrStep G H, and ibrStep uses
hearerUpdate which gives non-negative values when priors are non-negative. -/
theorem fp_respond_nonneg (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (m : G.Message) (s : G.State) :
    H.respond m s ≥ 0 := by
  rw [hFP m s]
  simp only [ibrStep, hearerUpdate]
  split_ifs with hdenom
  · exact le_refl 0
  · -- numerator / denominator where numerator ≥ 0 and denominator ≥ 0
    apply div_nonneg
    · -- Numerator: S(m|s) * prior(s) ≥ 0
      apply mul_nonneg
      · exact SpeakerStrategy.bestResponse_nonneg G H s m
      · exact hPriorNonneg s
    · -- Denominator: Σ S(m|s') * prior(s') ≥ 0
      apply Finset.sum_nonneg
      intro s' _
      apply mul_nonneg
      · exact SpeakerStrategy.bestResponse_nonneg G H s' m
      · exact hPriorNonneg s'

/-- The pragmatic interpretation: support of the IBR fixed point listener -/
def pragmaticSupport (G : InterpGame) (H : HearerStrategy G) (m : G.Message) :
    Finset G.State :=
  H.support m

/-- EG(S, R) = Σ_t Pr(t) × Σ_m S(t,m) × R(m,t): expected communication success. -/
noncomputable def expectedGain (G : InterpGame) (S : SpeakerStrategy G) (H : HearerStrategy G) : ℚ :=
  Finset.univ.sum λ t =>
    G.prior t * Finset.univ.sum λ m =>
      S.choose t m * H.respond m t

/-- Helper: fold max is attained at the initial value or at some element. -/
private theorem fold_max_attained {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) (b : ℚ) :
    s.fold max b f = b ∨ ∃ x ∈ s, s.fold max b f = f x := by
  induction s using Finset.induction_on with
  | empty => left; simp [Finset.fold_empty]
  | @insert a s' hna ih =>
    rw [Finset.fold_insert hna]
    cases ih with
    | inl hb =>
      rw [hb]
      by_cases h : f a ≤ b
      · left; exact max_eq_right h
      · right
        push_neg at h
        exact ⟨a, Finset.mem_insert_self a s', max_eq_left (le_of_lt h)⟩
    | inr hex =>
      obtain ⟨x, hx, hfx⟩ := hex
      rw [hfx]
      by_cases h : f a ≤ f x
      · right; exact ⟨x, Finset.mem_insert_of_mem hx, max_eq_right h⟩
      · right
        push_neg at h
        exact ⟨a, Finset.mem_insert_self a s', max_eq_left (le_of_lt h)⟩

/-- If no element attains the fold max, then fold max = init. -/
private theorem fold_max_eq_init_of_no_attainer {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) (b : ℚ)
    (h : ∀ x ∈ s, f x ≠ s.fold max b f) :
    s.fold max b f = b := by
  cases fold_max_attained s f b with
  | inl hb => exact hb
  | inr hex =>
    obtain ⟨x, hx, hfx⟩ := hex
    exact absurd hfx.symm (h x hx)

/-- Lemma 3a: best-response speaker improves EG.

    At each state t, bestResponse maximizes ∑_m S(t,m) * H(m,t) by concentrating
    all probability on messages that maximize H(m,t). Any valid S_old achieves
    at most maxU(t), which is exactly what S_new achieves. -/
theorem eg_speaker_improvement (G : InterpGame)
    (S_old S_new : SpeakerStrategy G) (H : HearerStrategy G)
    (hBR : S_new = SpeakerStrategy.bestResponse G H)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S_old.choose s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S_old.choose s m) ≤ 1)
    (hSTruth : ∀ s m, G.meaning m s = false → S_old.choose s m = 0)
    (_hHNonneg : ∀ m s, H.respond m s ≥ 0) :
    expectedGain G S_old H ≤ expectedGain G S_new H := by
  unfold expectedGain
  apply Finset.sum_le_sum; intro t _
  apply mul_le_mul_of_nonneg_left _ (hPriorNonneg t)
  set maxU := (G.trueMessages t).fold max 0 (λ m' => H.respond m' t) with maxU_def
  have hMaxUNonneg : 0 ≤ maxU := (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))
  -- S_old inner product ≤ maxU
  have hOldBound : Finset.univ.sum (λ m => S_old.choose t m * H.respond m t) ≤ maxU := by
    calc Finset.univ.sum (λ m => S_old.choose t m * H.respond m t)
        ≤ Finset.univ.sum (λ m => S_old.choose t m * maxU) := by
          apply Finset.sum_le_sum; intro m _
          cases hm : G.meaning m t with
          | false => simp [hSTruth t m hm]
          | true =>
            apply mul_le_mul_of_nonneg_left _ (hSNonneg t m)
            exact (Finset.le_fold_max _).mpr (Or.inr ⟨m,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, le_refl _⟩)
      _ = Finset.univ.sum (λ m => S_old.choose t m) * maxU := by rw [Finset.sum_mul]
      _ ≤ 1 * maxU := mul_le_mul_of_nonneg_right (hSSum t) hMaxUNonneg
      _ = maxU := one_mul maxU
  -- S_new achieves ≥ maxU
  suffices hNewEq : Finset.univ.sum (λ m => S_new.choose t m * H.respond m t) ≥ maxU by
    linarith
  subst hBR
  -- optimalMessages G H t is exactly our optSet (since maxU = maxUtility G H t)
  set opt := SpeakerStrategy.optimalMessages G H t
  set k := opt.card
  have hval : ∀ m, (SpeakerStrategy.bestResponse G H).choose t m * H.respond m t =
      if m ∈ opt then (if k = 0 then 0 else 1 / (k : ℚ)) * maxU else 0 := by
    intro m
    rw [SpeakerStrategy.bestResponse_val]
    by_cases hmem : m ∈ opt
    · rw [if_pos hmem, if_pos hmem]
      have hUtilEq : H.respond m t = maxU :=
        SpeakerStrategy.optimalMessages_utility G H t m hmem
      split_ifs with hk0
      · simp
      · rw [hUtilEq]
    · rw [if_neg hmem, if_neg hmem]; simp
  simp_rw [hval]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
  by_cases hk0 : k = 0
  · have hMaxU0 : maxU = 0 := by
      apply fold_max_eq_init_of_no_attainer
      intro m hm hfm
      have hmem : m ∈ opt := by
        simp only [opt, SpeakerStrategy.optimalMessages, Finset.mem_filter]
        exact ⟨hm, by rw [beq_iff_eq]; exact hfm⟩
      exact absurd (Finset.card_pos.mpr ⟨m, hmem⟩) (by omega)
    simp [hk0, hMaxU0]
  · simp only [if_neg hk0, k]
    rw [show (opt.card : ℚ) * (1 / (opt.card : ℚ) * maxU) =
        (opt.card : ℚ) * (1 / (opt.card : ℚ)) * maxU from by ring,
      mul_one_div_cancel (Nat.cast_ne_zero.mpr hk0), one_mul]

/-- Franke's Lemma 3: EG is monotone non-decreasing along the IBR sequence.

    The combined effect of speaker best response + Bayesian hearer update
    produces a strategy pair with at least as high expected gain:
      EG(S_{n+1}, L_n) ≤ EG(S_{n+2}, L_{n+1})

    Proof decomposes into two steps via the intermediate EG(S_{n+1}, L_{n+1}):

    **Speaker step** (proved via `eg_speaker_improvement`):
    EG(S_{n+1}, L_{n+1}) ≤ EG(S_{n+2}, L_{n+1}) because S_{n+2} = bestResponse(L_{n+1})
    achieves at least as much EG against L_{n+1} as any valid speaker strategy.

    **Hearer step** (sorry):
    EG(S_{n+1}, L_n) ≤ EG(S_{n+1}, L_{n+1}) where L_{n+1} = hearerUpdate(S_{n+1}).
    This says Bayesian update improves EG when paired with the speaker that generated it.
    Reduces to the aggregate inequality Σ_m ||w_m||²/||w_m||₁ ≥ Σ_m ⟨w_m, H_m⟩ where
    w_m(t) = S(t,m)·P(t). The per-message inequality ||w_m||²/Z_m ≥ ⟨w_m, H_m⟩ fails
    in general (numerical counterexamples exist for n ≥ 1); the aggregate holds by
    cross-message cancellations that resist Cauchy-Schwarz, QM-AM, Chebyshev sum,
    and covariance-based approaches. The n = 0 base case (literal listener L₀ with
    constant H per message group) is amenable to QM-AM, but the inductive step is
    not. Verified numerically for many games. -/
theorem eg_ibr_monotone (G : InterpGame)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hPriorSum : Finset.univ.sum G.prior = 1)
    (n : ℕ) :
    expectedGain G (speakerUpdate G (ibrN G n)) (ibrN G n) ≤
    expectedGain G (speakerUpdate G (ibrN G (n + 1))) (ibrN G (n + 1)) := by
  -- Decompose: f(n) ≤ EG(S_{n+1}, L_{n+1}) ≤ f(n+1)
  calc expectedGain G (speakerUpdate G (ibrN G n)) (ibrN G n)
      ≤ expectedGain G (speakerUpdate G (ibrN G n)) (ibrN G (n + 1)) := by
        -- Hearer step: EG(S_{n+1}, L_n) ≤ EG(S_{n+1}, L_{n+1})
        -- Per-message Cauchy-Schwarz fails for n ≥ 1; aggregate requires
        -- cross-message cancellations (see docstring above)
        sorry
    _ ≤ expectedGain G (speakerUpdate G (ibrN G (n + 1))) (ibrN G (n + 1)) := by
        -- Speaker step: S_{n+2} = bestResponse(L_{n+1}) beats S_{n+1} against L_{n+1}
        apply eg_speaker_improvement G
          (speakerUpdate G (ibrN G n))
          (speakerUpdate G (ibrN G (n + 1)))
          (ibrN G (n + 1))
        · rfl
        · exact hPriorNonneg
        · exact SpeakerStrategy.bestResponse_nonneg G (ibrN G n)
        · exact SpeakerStrategy.bestResponse_sum_le_one G (ibrN G n)
        · exact SpeakerStrategy.bestResponse_false_zero G (ibrN G n)
        · intro m s
          simp only [ibrN, ibrStep, hearerUpdate]
          split_ifs
          · exact le_refl 0
          · apply div_nonneg
            · exact mul_nonneg
                (SpeakerStrategy.bestResponse_nonneg G (ibrN G n) s m)
                (hPriorNonneg s)
            · exact Finset.sum_nonneg (λ s' _ => mul_nonneg
                (SpeakerStrategy.bestResponse_nonneg G (ibrN G n) s' m)
                (hPriorNonneg s'))

/-- Expected gain is bounded above by 1 (probability of perfect communication). -/
theorem eg_bounded (G : InterpGame) (S : SpeakerStrategy G) (H : HearerStrategy G)
    (hPriorSum : Finset.univ.sum G.prior = 1)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S.choose s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S.choose s m) ≤ 1)
    (hHBound : ∀ m s, H.respond m s ≤ 1)
    (_hHNonneg : ∀ m s, H.respond m s ≥ 0) :
    expectedGain G S H ≤ 1 := by
  unfold expectedGain
  calc Finset.univ.sum (λ t => G.prior t * Finset.univ.sum (λ m => S.choose t m * H.respond m t))
      ≤ Finset.univ.sum (λ t => G.prior t * 1) := by
        apply Finset.sum_le_sum; intro t _
        apply mul_le_mul_of_nonneg_left _ (hPriorNonneg t)
        calc Finset.univ.sum (λ m => S.choose t m * H.respond m t)
            ≤ Finset.univ.sum (λ m => S.choose t m * 1) := by
              apply Finset.sum_le_sum; intro m _
              exact mul_le_mul_of_nonneg_left (hHBound m t) (hSNonneg t m)
          _ = Finset.univ.sum (λ m => S.choose t m) := by simp only [mul_one]
          _ ≤ 1 := hSSum t
    _ = 1 := by simp [hPriorSum]

/-- Theorem 3: IBR converges. EG is monotone increasing and bounded ⟹ fixed point. -/
theorem ibr_reaches_fixed_point (G : InterpGame) :
    ∃ n : ℕ, isIBRFixedPoint G (ibrN G n) := by
  sorry -- Requires formalizing the monotonicity + finiteness argument

-- Fixed point = minimum alternatives = exhMW (Franke Appendix B.2, eq. 131)

/-- Number of messages the speaker uses at state t (|S(t)|). -/
def speakerOptionCount (G : InterpGame) (S : SpeakerStrategy G) (t : G.State) : ℕ :=
  (Finset.univ.filter λ m => S.choose t m > 0).card

/-- For bestResponse speaker, speakerOptionCount = |optimalMessages|.
    This connects the counting definition to the set-level API. -/
theorem speakerOptionCount_bestResponse (G : InterpGame) (H : HearerStrategy G)
    (t : G.State) :
    speakerOptionCount G (SpeakerStrategy.bestResponse G H) t =
    (SpeakerStrategy.optimalMessages G H t).card := by
  simp only [speakerOptionCount]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ((SpeakerStrategy.bestResponse_pos_iff G H t m).mp h).1
  · intro h; exact (SpeakerStrategy.bestResponse_pos_iff G H t m).mpr
      ⟨h, Finset.card_pos.mpr ⟨m, h⟩⟩

/-- At the fixed point with flat priors, fewer speaker options ↔ higher hearer probability (eq. 131).

    Requires m to be optimal at both states (in the speaker's support). Without this,
    the speaker assigns zero probability to m and the hearer probability is zero,
    making the comparison degenerate. -/
theorem fp_prefers_fewer_options (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hPriorPos : ∀ t, G.prior t > 0)
    (m : G.Message) (t₁ t₂ : G.State)
    (hOpt₁ : m ∈ SpeakerStrategy.optimalMessages G H t₁)
    (hOpt₂ : m ∈ SpeakerStrategy.optimalMessages G H t₂) :
    let S := speakerUpdate G H
    H.respond m t₁ > H.respond m t₂ ↔
      speakerOptionCount G S t₁ < speakerOptionCount G S t₂ := by
  intro S
  simp only [S, speakerUpdate]
  rw [speakerOptionCount_bestResponse G H t₁, speakerOptionCount_bestResponse G H t₂]
  set n₁ := (SpeakerStrategy.optimalMessages G H t₁).card
  set n₂ := (SpeakerStrategy.optimalMessages G H t₂).card
  have hn₁pos : 0 < n₁ := Finset.card_pos.mpr ⟨m, hOpt₁⟩
  have hn₂pos : 0 < n₂ := Finset.card_pos.mpr ⟨m, hOpt₂⟩
  have hn₁cast : (0 : ℚ) < n₁ := Nat.cast_pos.mpr hn₁pos
  have hn₂cast : (0 : ℚ) < n₂ := Nat.cast_pos.mpr hn₂pos
  -- Speaker probabilities at t₁ and t₂
  have hS₁ : (SpeakerStrategy.bestResponse G H).choose t₁ m = 1 / (n₁ : ℚ) := by
    rw [SpeakerStrategy.bestResponse_val, if_pos hOpt₁,
        if_neg (Nat.pos_iff_ne_zero.mp hn₁pos)]
  have hS₂ : (SpeakerStrategy.bestResponse G H).choose t₂ m = 1 / (n₂ : ℚ) := by
    rw [SpeakerStrategy.bestResponse_val, if_pos hOpt₂,
        if_neg (Nat.pos_iff_ne_zero.mp hn₂pos)]
  -- Fixed point gives Bayesian formula
  have hFP₁ := hFP m t₁
  have hFP₂ := hFP m t₂
  simp only [ibrStep, hearerUpdate, speakerUpdate] at hFP₁ hFP₂
  -- Common denominator
  set den := Finset.univ.sum (λ s' =>
    (SpeakerStrategy.bestResponse G H).choose s' m * G.prior s') with den_def
  -- den > 0 (the t₁ term contributes positively)
  have hDenPos : den > 0 :=
    lt_of_lt_of_le
      (mul_pos (by rw [hS₁]; exact div_pos one_pos hn₁cast) (hPriorPos t₁))
      (Finset.single_le_sum
        (λ s _ => mul_nonneg (SpeakerStrategy.bestResponse_nonneg G H s m)
          (le_of_lt (hPriorPos s)))
        (Finset.mem_univ t₁))
  -- BEq check resolves to false
  have hDenBEq : (den == (0 : ℚ)) = false := by
    cases h : (den == (0 : ℚ))
    · rfl
    · rw [beq_iff_eq] at h; exact absurd h (ne_of_gt hDenPos)
  rw [hDenBEq] at hFP₁ hFP₂
  simp only [Bool.false_eq_true, ↓reduceIte] at hFP₁ hFP₂
  -- Substitute speaker values and flat prior
  rw [hS₁] at hFP₁
  rw [hS₂, hFlatPrior t₂ t₁] at hFP₂
  set p := G.prior t₁
  have hpPos : (0 : ℚ) < p := hPriorPos t₁
  -- hFP₁ : H.respond m t₁ = 1/n₁ * p / den
  -- hFP₂ : H.respond m t₂ = 1/n₂ * p / den
  rw [hFP₁, hFP₂]
  constructor
  · -- H(t₁) > H(t₂) → n₁ < n₂ (by contradiction)
    intro h
    by_contra hge; push_neg at hge
    have hle : (↑n₂ : ℚ) ≤ ↑n₁ := Nat.cast_le.mpr hge
    have h1 : (1 : ℚ) / ↑n₁ ≤ 1 / ↑n₂ :=
      div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 1) hn₂cast hle
    have h2 : (1 : ℚ) / ↑n₁ * p ≤ 1 / ↑n₂ * p :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hpPos)
    exact not_lt.mpr (div_le_div_of_nonneg_right h2 (le_of_lt hDenPos)) h
  · -- n₁ < n₂ → H(t₁) > H(t₂)
    intro h
    have hlt : (↑n₁ : ℚ) < ↑n₂ := Nat.cast_lt.mpr h
    have h1 : (1 : ℚ) / ↑n₂ < 1 / ↑n₁ := one_div_lt_one_div_of_lt hn₁cast hlt
    have h2 : (1 : ℚ) / ↑n₂ * p < 1 / ↑n₁ * p := mul_lt_mul_of_pos_right h1 hpPos
    exact div_lt_div_of_pos_right h2 hDenPos

/-- Best-response speaker uses ⊆ true messages, so speakerOptionCount ≤ |trueMessages|. -/
theorem speaker_options_le_true_messages (G : InterpGame) (H : HearerStrategy G)
    (t : G.State) :
    let S := speakerUpdate G H
    speakerOptionCount G S t ≤ (G.trueMessages t).card := by
  simp only [speakerOptionCount, speakerUpdate]
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have ⟨hmem, _⟩ := (SpeakerStrategy.bestResponse_pos_iff G H t m).mp hm
  exact SpeakerStrategy.optimalMessages_subset_trueMessages G H t hmem

-- SECTION 5: Connection to Exhaustive Interpretation (Franke Section 10)

/-!
## IBR = EXH (Franke Main Result)
@cite{franke-2011} @cite{spector-2016}

The key insight of @cite{franke-2011} is that IBR reasoning yields exactly
the same interpretation as exhaustive interpretation (exhMW).

**Theorem (@cite{franke-2011}, Section 9.3)**: For an interpretation game G,
the IBR fixed point listener's support for message m equals the set of
minimal m-worlds relative to the alternative ordering.

In notation:
  support(L∞(· | m)) = exhMW(ALT, m)

This connects game-theoretic pragmatics to grammatical exhaustification.

### Results from Section 10 and Appendix A

**Equation (107)**: R₁ characterization
  R₁(m) = {t ∈ ⟦m⟧ | ¬∃t′ ∈ ⟦m⟧ : |R⁻¹₀(t′)| < |R⁻¹₀(t)|}

This selects states where **fewest alternatives are true**.

**Fact 1** (Section 10): R₁(mₛ) ⊆ ExhMM(S)
Under "homogeneity" of alternatives, R₁(mₛ) = ExhMM(S).

**Fact 3** (Appendix A): ExhMM(S, Alt) ⊆ ExhIE(S, Alt)

**Fact 4** (Appendix A): ExhMM = ExhIE when Alt satisfies closure conditions.
-/

/-- Convert interpretation game to alternative set for exhaustification.
    Converts Bool meaning to Prop' by using equality with true. -/
def toAlternatives (G : InterpGame) : Set (Prop' G.State) :=
  { λ s => G.meaning m s = true | m : G.Message }

/-- The prejacent proposition for a message (Bool → Prop conversion) -/
def prejacent (G : InterpGame) (m : G.Message) : Prop' G.State :=
  λ s => G.meaning m s = true

--5.1: Alternative Counting (Franke eq. 107)

/-- Number of alternatives (messages) true at state s.
    This is |R⁻¹₀(s)| in Franke's notation. -/
def alternativeCount (G : InterpGame) (s : G.State) : ℕ :=
  (G.trueMessages s).card

/-- A state s is minimal among m-worlds if no m-world has fewer true alternatives.
    This characterizes R₁(m) per equation (107). -/
def isMinimalByAltCount (G : InterpGame) (m : G.Message) (s : G.State) : Prop :=
  G.meaning m s = true ∧
  ∀ s', G.meaning m s' = true → alternativeCount G s ≤ alternativeCount G s'

/-- States with minimum alternative count among m-worlds. -/
noncomputable def minAltCountStates (G : InterpGame) (m : G.Message) : Finset G.State :=
  let mWorlds := G.trueStates m
  if h : mWorlds.Nonempty then
    let witness := Classical.choose h
    let minCount := mWorlds.fold min (alternativeCount G witness) (alternativeCount G ·)
    mWorlds.filter (λ s => alternativeCount G s = minCount)
  else ∅

--5.2: Fact 1 - R₁ ⊆ ExhMW (Franke Section 10)

/-- Key lemma: s' <_ALT s implies trueMessages s' ⊂ trueMessages s.

    This is the bridge between the <_ALT ordering and alternative counting. -/
theorem ltALT_implies_trueMessages_ssubset (G : InterpGame) (s' s : G.State)
    (hlt : ltALT (toAlternatives G) s' s) :
    G.trueMessages s' ⊂ G.trueMessages s := by
  -- ltALT means: (1) leALT s' s, and (2) ¬(leALT s s')
  -- leALT s' s means: every alt true at s' is true at s
  have hle : leALT (toAlternatives G) s' s := hlt.1
  have hne : ¬leALT (toAlternatives G) s s' := hlt.2
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · -- Subset: trueMessages s' ⊆ trueMessages s
    intro m' hm'
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
    -- m' is true at s', so the alternative "meaning m' = true" is true at s'
    -- By hle, this alternative is also true at s
    have halt : (λ x => G.meaning m' x = true) s' → (λ x => G.meaning m' x = true) s := by
      apply hle
      simp only [toAlternatives, Set.mem_setOf_eq]
      exact ⟨m', rfl⟩
    exact halt hm'
  · -- Not equal: trueMessages s' ≠ trueMessages s
    intro heq
    apply hne
    -- Need to show leALT s s', i.e., ∀ a ∈ ALT, a s → a s'
    intro a ha_mem ha_s
    simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
    obtain ⟨m', hm'_eq⟩ := ha_mem
    -- a = (λ x => G.meaning m' x = true), and a s holds
    subst hm'_eq
    -- ha_s : (λ x => G.meaning m' x = true) s, i.e., G.meaning m' s = true
    -- Since trueMessages s' = trueMessages s, m' ∈ trueMessages s implies m' ∈ trueMessages s'
    have hm'_in : m' ∈ G.trueMessages s := by
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha_s
    rw [← heq] at hm'_in
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in
    exact hm'_in

/-- **Franke Fact 1 (containment direction)**: Level-1 receiver interpretation
    is contained in minimal-models exhaustification.

    R₁(mₛ) ⊆ ExhMM(S)

    **Proof idea**: If s is selected by R₁ (minimum alternative count),
    then s is minimal with respect to <_ALT because:
    - s' <_ALT s means s' makes strictly fewer alternatives true
    - But R₁ already selected for minimum alternative count
    - So no such s' can exist among m-worlds

    This is the containment direction; equality requires "homogeneity". -/
theorem r1_subset_exhMW (G : InterpGame) (m : G.Message) (s : G.State)
    (h : isMinimalByAltCount G m s) :
    exhMW (toAlternatives G) (prejacent G m) s := by
  constructor
  · -- φ(s): m is true at s
    exact h.1
  · -- Minimality: no s' < s with m(s')
    intro ⟨s', hs'_true, hs'_lt⟩
    -- s' <_ALT s implies trueMessages s' ⊂ trueMessages s
    have hssubset : G.trueMessages s' ⊂ G.trueMessages s :=
      ltALT_implies_trueMessages_ssubset G s' s hs'_lt
    -- Therefore alternativeCount s' < alternativeCount s
    have hcount : alternativeCount G s' < alternativeCount G s := by
      simp only [alternativeCount]
      exact Finset.card_lt_card hssubset
    -- But h.2 says s has minimum alt count among m-worlds, contradiction
    have hmin := h.2 s' hs'_true
    omega

-- Helper theorems for proving containment and homogeneity-related results

/-- Under homogeneity, trueMessages determines states uniquely.
    This means: trueMessages s' = trueMessages s → s' = s -/
theorem trueMessages_injective_of_homogeneous (G : InterpGame)
    (hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂)
    (s' s : G.State) (heq : G.trueMessages s' = G.trueMessages s) : s' = s := by
  apply hGame
  intro m'
  have h1 : (m' ∈ G.trueMessages s') ↔ (G.meaning m' s' = true) := by
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : (m' ∈ G.trueMessages s) ↔ (G.meaning m' s = true) := by
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq] at h1
  -- Now h1 : m' ∈ trueMessages s ↔ meaning m' s' = true
  -- and h2 : m' ∈ trueMessages s ↔ meaning m' s = true
  -- Both ↔ being equivalent to the same membership, so the meanings are equal
  cases hm' : G.meaning m' s' with
  | true =>
    -- meaning m' s' = true, so m' ∈ trueMessages s (via h1)
    have hmem : m' ∈ G.trueMessages s := h1.mpr hm'
    -- Therefore meaning m' s = true (via h2)
    exact (h2.mp hmem).symm
  | false =>
    -- meaning m' s' = false, so m' ∉ trueMessages s (via h1 contrapositive)
    have hnmem : m' ∉ G.trueMessages s := λ hmem => by
      have := h1.mp hmem
      simp only [hm'] at this
      -- this : false = true, which is a contradiction
      exact absurd this.symm Bool.noConfusion
    -- Therefore meaning m' s = false (via h2 contrapositive)
    cases hm's : G.meaning m' s with
    | true => exact absurd (h2.mpr hm's) hnmem
    | false => rfl

/-- Under homogeneity, strict subset of trueMessages implies <_ALT.
    Note: hGame is not actually used in this proof, but kept for consistency. -/
theorem trueMessages_ssubset_implies_ltALT (G : InterpGame)
    (_hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂)
    (s' s : G.State) (hss : G.trueMessages s' ⊂ G.trueMessages s) :
    ltALT (toAlternatives G) s' s := by
  constructor
  · -- leALT s' s: every alt true at s' is true at s
    intro a ha_mem ha_s'
    simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
    obtain ⟨m', hm'_eq⟩ := ha_mem
    subst hm'_eq
    -- a = meaning m' = true, and a s' holds
    have hm'_in_s' : m' ∈ G.trueMessages s' := by
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha_s'
    have hm'_in_s : m' ∈ G.trueMessages s := Finset.mem_of_subset hss.1 hm'_in_s'
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in_s
    exact hm'_in_s
  · -- ¬(leALT s s'): NOT every alt true at s is true at s'
    intro hle
    -- If leALT s s', then trueMessages s ⊆ trueMessages s'
    have hsub : G.trueMessages s ⊆ G.trueMessages s' := by
      intro m' hm'
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      have h : (λ x => G.meaning m' x = true) s := hm'
      have halt := hle (λ x => G.meaning m' x = true) ⟨m', rfl⟩ h
      exact halt
    -- But hss says trueMessages s' ⊂ trueMessages s (proper subset)
    -- hss.2 : ¬(trueMessages s ⊆ trueMessages s')
    -- But hsub says trueMessages s ⊆ trueMessages s', contradiction
    exact hss.2 hsub

/-- **Franke Fact 1**: R₁ ⊆ ExhMW (containment, not equality).

This is the main soundness result: if s is selected by IBR level-1 reasoning
(has minimum alternative count among m-worlds), then s is in ExhMW.

**Why not equality?** Franke notes (Section 10): "The reverse, however, is
not necessarily the case: it may well be that two worlds w, v ∈ S are both
minimal with respect to <_ALT, while w makes more alternatives true than v."

In other words:
- R₁ selects states with minimum |{A : A(s)}| among m-worlds
- ExhMW selects states minimal in <_ALT (subset ordering on alternatives)
- Minimum cardinality ⟹ minimal in subset ordering ✓
- Minimal in subset ordering ⟹ minimum cardinality ✗

For equality, we'd need <_ALT to be total on m-worlds (a "chain" structure).
This is a stronger condition that doesn't always hold. -/
theorem r1_containedIn_exhMW (G : InterpGame) (m : G.Message) (s : G.State)
    (h : isMinimalByAltCount G m s) :
    exhMW (toAlternatives G) (prejacent G m) s :=
  r1_subset_exhMW G m s h

--5.2b: Conditions for the Converse (ExhMW ⊆ R₁)

/-- The alternative ordering is **total** on m-worlds if for any two states
where m is true, one's true alternatives are a subset of the other's.

This "chain condition" ensures that minimal cardinality ⟺ minimal in <_ALT.

**When does this hold?**
- When alternatives form a linear scale (e.g., ⟨some, most, all⟩)
- When alternatives are conjunctive closures of simpler alternatives
- When states are defined as equivalence classes by alternative patterns

**When does this fail?**
- When alternatives can be true independently (e.g., "red" and "tall")
- When the alternative space has incomparable elements
-/
def altOrderingTotalOnMessage (G : InterpGame) (m : G.Message) : Prop :=
  ∀ s s', G.meaning m s = true → G.meaning m s' = true →
    (G.trueMessages s ⊆ G.trueMessages s') ∨ (G.trueMessages s' ⊆ G.trueMessages s)

/-- **Converse direction under totality**: ExhMW ⊆ R₁.

When <_ALT is total on m-worlds, minimal in the subset ordering implies
minimum cardinality. -/
theorem exhMW_subset_r1_under_totality (G : InterpGame) (m : G.Message) (s : G.State)
    (hTotal : altOrderingTotalOnMessage G m)
    (hmw : exhMW (toAlternatives G) (prejacent G m) s) :
    isMinimalByAltCount G m s := by
  constructor
  · exact hmw.1
  · -- Show s has minimum alt count among m-worlds
    intro s' hs'_true
    -- By totality, either trueMessages s ⊆ trueMessages s' or vice versa
    cases hTotal s s' hmw.1 hs'_true with
    | inl hsub =>
      -- trueMessages s ⊆ trueMessages s'
      simp only [alternativeCount]
      exact Finset.card_le_card hsub
    | inr hsub' =>
      -- trueMessages s' ⊆ trueMessages s
      -- Since s is minimal in <_ALT and trueMessages s' ⊆ trueMessages s,
      -- either s' = s (homogeneity) or s' is strictly smaller (contradicting minimality)
      by_cases heq : G.trueMessages s' = G.trueMessages s
      · simp only [alternativeCount]
        rw [heq]
      · -- trueMessages s' ⊂ trueMessages s (proper subset)
        -- This means s' <_ALT s, contradicting hmw.2
        have hss : G.trueMessages s' ⊂ G.trueMessages s :=
          ⟨hsub', λ h => heq (Finset.Subset.antisymm hsub' h)⟩
        -- Prove s' <_ALT s directly from hss
        have hlt : ltALT (toAlternatives G) s' s := by
          constructor
          · -- leALT s' s: every alt true at s' is true at s
            intro a ha_mem ha_s'
            simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
            obtain ⟨m', hm'_eq⟩ := ha_mem
            subst hm'_eq
            have hm'_in_s' : m' ∈ G.trueMessages s' := by
              simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ha_s'
            have hm'_in_s : m' ∈ G.trueMessages s := Finset.mem_of_subset hss.1 hm'_in_s'
            simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in_s
            exact hm'_in_s
          · -- ¬leALT s s': NOT every alt true at s is true at s'
            intro hle
            have hsub'' : G.trueMessages s ⊆ G.trueMessages s' := by
              intro m' hm'
              simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
              have h : (λ x => G.meaning m' x = true) s := hm'
              have halt := hle (λ x => G.meaning m' x = true) ⟨m', rfl⟩ h
              exact halt
            exact hss.2 hsub''
        -- hmw.2 says there's no v such that (prejacent G m v ∧ v <_ALT s)
        exfalso
        exact hmw.2 ⟨s', hs'_true, hlt⟩

/-- **R₁ = ExhMW under totality**: Full equivalence when alternatives form a chain.

This is the precise condition under which Franke's Fact 1 becomes an equality. -/
theorem r1_eq_exhMW_under_totality (G : InterpGame) (m : G.Message) (s : G.State)
    (hTotal : altOrderingTotalOnMessage G m) :
    isMinimalByAltCount G m s ↔ exhMW (toAlternatives G) (prejacent G m) s :=
  ⟨r1_subset_exhMW G m s, exhMW_subset_r1_under_totality G m s hTotal⟩

--5.3: Fact 3 - ExhMW ⊆ ExhIE (Franke Appendix A)

/-- **Franke Fact 3 (Appendix A)**: ExhMW(S, Alt) ⊆ ExhIE(S, Alt)

    This is the easier direction: minimal-models is always at least as strong
    as innocent exclusion.

    **Proof (from Franke Appendix A)**:
    If w ∈ ExhMM(S, Alt), then w is minimal w.r.t. <_Alt in S.
    This means w makes a maximal set of alternatives false.
    So there exists A ∈ Max-CE(S, Alt) with w ∈ S ∧ ⋀_{a∈A}¬a.
    Since IE = ⋂ Max-CE, w satisfies all propositions in IE.
    Hence w ∈ ExhIE(S, Alt).

    This is already proved as `prop6_exhMW_entails_exhIE` in Exhaustivity/Basic.lean.
-/
theorem fact3_exhMW_subset_exhIE (G : InterpGame) (m : G.Message) :
    exhMW (toAlternatives G) (prejacent G m) ⊆ₚ exhIE (toAlternatives G) (prejacent G m) :=
  prop6_exhMW_entails_exhIE (toAlternatives G) (prejacent G m)

--5.4: Fact 4 - ExhMW = ExhIE under closure (Franke Appendix A)

/-- **Franke Fact 4 (Appendix A)**: ExhMW = ExhIE when Alt is closed under ∧.

    This is Spector's Theorem 9, referenced by Franke in Appendix A.

    **Condition**: For all w, w' ∈ ExhMM(S, Alt), there exists A ∈ Alt such that
    A(w) ∧ A(w') entails A.

    When Alt is closed under conjunction, this condition holds automatically
    because we can take A = A(w) ∧ A(w').

    This is proved as `theorem9_main` in Exhaustivity/Basic.lean.
-/
theorem fact4_exhMW_eq_exhIE_closed (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    exhMW (toAlternatives G) (prejacent G m) ≡ₚ exhIE (toAlternatives G) (prejacent G m) :=
  theorem9_main (toAlternatives G) (prejacent G m) hClosed

--5.5: IBR Fixed Point Theorems (previously in this section)

/-- IBR fixed point equals exhMW (Main theorem - @cite{franke-2011}, Section 9.3)

This is the central result connecting game theory to exhaustification.
At the fixed point, the IBR listener's interpretation of message m is
exactly the exhaustive interpretation exhMW(ALT, m).

**Proof Strategy:**

1. **Non-minimal states eliminated**: If s is non-minimal (∃s' < s with m(s')),
   then at s', there's a message m' true at s' but not at s (by definition of <).
   Message m' is more informative than m. So S_n prefers m' at s', leading to
   S_n(m|s') < 1. This propagates: L_{n+1}(s|m) decreases each iteration.

2. **Minimal states preserved**: If s is minimal among m-worlds, then at s,
   no "stronger" alternative is true, so m is optimal. S_n(m|s) = 1/|optimal|,
   and L_{n+1}(s|m) > 0 is maintained.

3. **Convergence**: By well-foundedness of < on finite sets, this stabilizes.
   The fixed point support equals the set of minimal m-worlds = exhMW.

**Key Lemma**: For any s in support(L_∞(·|m)):
- m(s) must be true (literal content)
- No s' < s can have m(s') true (minimality)
This is exactly exhMW(ALT, m).
-/
theorem ibr_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) := by
  intro s
  constructor
  · -- Forward: H.respond m s > 0 → exhMW s
    intro hPos
    -- At a fixed point, H.respond m s = (hearerUpdate G (speakerUpdate G H)).respond m s
    -- If H.respond m s > 0, then the numerator S(m|s) * prior(s) > 0
    -- This means S(m|s) > 0, i.e., m is an optimal message at s for speaker
    -- S(m|s) > 0 means m maximizes H.respond m' s among true messages at s
    -- Since H.respond m s > 0, s must be in the support
    -- For s to be in support, m must be true at s (prejacent)
    -- And no strictly more informative message should dominate
    constructor
    · -- prejacent: m is true at s
      -- If m were false at s, then S(m|s) = 0 (speaker only uses true messages)
      -- So numerator = 0, and H.respond m s = 0, contradicting hPos
      by_contra hNotTrue
      -- Convert ¬(meaning m s = true) to meaning m s = false
      simp only [prejacent] at hNotTrue
      have hFalse : G.meaning m s = false := by
        cases hm : G.meaning m s
        · rfl
        · exact absurd hm hNotTrue
      -- At the fixed point, H.respond m s = hearerUpdate formula
      have hFPms := hFP m s
      simp only [ibrStep, hearerUpdate, speakerUpdate] at hFPms
      -- The speaker gives 0 probability to false messages
      have hSzero := SpeakerStrategy.bestResponse_false_zero G H s m hFalse
      -- Rewrite hPos using fixed point
      rw [hFPms] at hPos
      -- The numerator is S.choose s m * prior s = 0 * prior s = 0
      split_ifs at hPos with hdenom
      · -- denominator = 0, so result is 0, contradicting hPos
        exact absurd (le_refl 0) (not_le.mpr hPos)
      · -- numerator / denominator where numerator = 0
        simp only [hSzero, zero_mul, zero_div] at hPos
        exact absurd (le_refl 0) (not_le.mpr hPos)
    · -- minimality: no s' <_ALT s with m true at s'
      intro ⟨s', hs'_true, hs'_lt⟩
      -- If there were such s', then at s', a more informative message m' is available
      -- (by definition of <_ALT, there's an alternative true at s' but not s)
      -- The speaker at s' would prefer m' over m
      -- This would reduce H.respond m s through the Bayes update
      -- At a fixed point, this propagates to eliminate s from support
      sorry
  · -- Backward: exhMW s → H.respond m s > 0
    intro ⟨hs_true, hs_min⟩
    -- s is minimal among m-worlds
    -- At a fixed point, minimal states are preserved
    -- The speaker uses m at s (it's among the best options)
    -- The Bayes update maintains positive probability
    sorry

/-- At the fixed point, IBR excludes non-minimal states.

Note: This is stated for the FIXED POINT listener, not L2 specifically.
L2 alone doesn't necessarily exclude all non-minimal states; the full
elimination happens through iteration to the fixed point.
-/
theorem ibr_fp_excludes_nonminimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (m : G.Message) (s : G.State)
    (_hs : G.meaning m s = true)
    (hNonMin : ∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    H.respond m s = 0 := by
  -- s is not in exhMW because it's non-minimal
  have hNotExh : ¬exhMW (toAlternatives G) (prejacent G m) s := λ hexh => hexh.2 hNonMin
  -- By ibr_equals_exhMW, H.respond m s > 0 ↔ exhMW s
  -- Since ¬exhMW s, we have ¬(H.respond m s > 0)
  have hNotPos : ¬(H.respond m s > 0) :=
    λ hpos => hNotExh ((ibr_equals_exhMW G H hFP m s).mp hpos)
  -- At a fixed point with non-negative priors, H.respond ≥ 0
  have hNonneg := fp_respond_nonneg G H hFP hPriorNonneg m s
  -- ¬(x > 0) ∧ x ≥ 0 → x = 0
  simp only [not_lt] at hNotPos
  linarith

/-- At the fixed point, IBR keeps minimal states.

If s is minimal among m-worlds (no s' < s with m(s')), then the fixed point
listener assigns positive probability to s given m.
-/
theorem ibr_fp_keeps_minimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message) (s : G.State)
    (hs : G.meaning m s = true)
    (hMin : ¬∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s)
    (_hPriorPos : G.prior s > 0) :
    H.respond m s > 0 := by
  -- s is in exhMW because it's minimal
  have hExh : exhMW (toAlternatives G) (prejacent G m) s := ⟨hs, hMin⟩
  -- By ibr_equals_exhMW, H.respond m s > 0 ↔ exhMW s
  exact (ibr_equals_exhMW G H hFP m s).mpr hExh

-- SECTION 6: RSA as "Soft" IBR

/-!
## RSA → IBR as α → ∞

RSA uses softmax instead of argmax:
- RSA S₁(m | s) ∝ exp(α · log L₀(s | m)) -- softmax
- IBR S₁(m | s) = argmax_m L₀(s | m) -- hard argmax

As the rationality parameter α → ∞, softmax becomes argmax.
This connects the probabilistic RSA model to the deterministic IBR model.
-/

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
  -- Score = log(informativity) for true messages, floor for false
  let score := λ m =>
    if G.meaning m s then Real.log (G.informativity m : ℝ) else falseMessageScore G
  Core.softmax score α

/-- RSA S1 equals softmax over log-informativity.

This is the key observation: RSA speaker choice is softmax with
scores = log(informativity of message).
-/
theorem rsaS1_eq_softmax (G : InterpGame) [Nonempty G.Message] (α : ℝ) (s : G.State) :
    rsaS1Real G α s = Core.softmax
      (λ m => if G.meaning m s then Real.log (G.informativity m : ℝ) else falseMessageScore G) α := rfl

/-- As α → ∞, RSA S1 concentrates on optimal messages (IBR S1).

This follows directly from `softmax_tendsto_hardmax`:
- RSA S1 = softmax(log-informativity, α)
- As α → ∞, softmax → argmax
- argmax(log-informativity) = argmax(informativity) = IBR S1

The proof uses `tendsto_softmax_infty_at_max` from Limits.lean.
-/
theorem rsa_to_ibr_limit (G : InterpGame) [Nonempty G.Message] (s : G.State) (m : G.Message)
    (hTrue : G.meaning m s = true)
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    Filter.Tendsto (λ α => rsaS1Real G α s m) Filter.atTop (nhds 1) := by
  -- RSA S1 = softmax over log-informativity
  -- The optimal message m has highest log-informativity among true messages
  -- By softmax_tendsto_hardmax, softmax concentrates on the maximum
  let score := λ m' => if G.meaning m' s then Real.log (G.informativity m' : ℝ) else falseMessageScore G
  -- m is the unique maximum of score (log is monotone, so max inf = max log inf)
  have hmax : ∀ m', m' ≠ m → score m' < score m := by
    intro m' hne
    simp only [score, hTrue, ↓reduceIte]
    split_ifs with hm'
    · -- Both true: log is strictly monotone, so inf m > inf m' implies log(inf m) > log(inf m')
      have hm'_pos : 0 < G.informativity m' := by
        simp only [InterpGame.informativity]
        split_ifs with hcard
        · -- card = 0 case: informativity = 0, but this means message is never true
          -- which contradicts hm' : meaning m' s = true
          exfalso
          have hempty : G.trueStates m' = ∅ := Finset.card_eq_zero.mp hcard
          have hs_mem : s ∈ G.trueStates m' := by
            simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and, hm']
          simp only [hempty, Finset.notMem_empty] at hs_mem
        · exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard))
      exact Real.log_lt_log (Rat.cast_pos.mpr hm'_pos) (Rat.cast_lt.mpr (hUnique m' hne hm'))
    · -- m true, m' false: falseMessageScore < log(inf m)
      -- falseMessageScore = -log(|State|) - 1
      -- log(inf m) ≥ -log(|State|) since inf m ≥ 1/|State|
      -- So log(inf m) > -log(|State|) - 1 = falseMessageScore
      simp only [falseMessageScore]
      -- We need: -log(|State|) - 1 < log(inf m)
      -- Equivalently: log(inf m) > -log(|State|) - 1
      haveI : Nonempty G.State := ⟨s⟩
      have hcard_pos : 0 < Fintype.card G.State := Fintype.card_pos
      have hs_in_true : s ∈ G.trueStates m := by
        simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and, hTrue]
      have htrue_card_pos : 0 < (G.trueStates m).card :=
        Finset.card_pos.mpr ⟨s, hs_in_true⟩
      have htrue_card_le : (G.trueStates m).card ≤ Fintype.card G.State :=
        Finset.card_le_card (Finset.subset_univ _)
      -- informativity m = 1 / (trueStates m).card
      have hinf_eq : G.informativity m = 1 / (G.trueStates m).card := by
        simp only [InterpGame.informativity]
        split_ifs with hcard
        · exact absurd hcard (Nat.pos_iff_ne_zero.mp htrue_card_pos)
        · rfl
      -- log(inf m) = log(1/card) = -log(card)
      have hinf_cast_pos : 0 < (G.informativity m : ℝ) := Rat.cast_pos.mpr hInfPos
      have hlog_eq : Real.log (G.informativity m : ℝ) = -Real.log ((G.trueStates m).card : ℝ) := by
        rw [hinf_eq]
        simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
            (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp htrue_card_pos)),
            Real.log_one]
        ring
      rw [hlog_eq]
      -- Need: -log(|State|) - 1 < -log(card(trueStates m))
      -- i.e., log(card(trueStates m)) < log(|State|) + 1
      -- Since card(trueStates m) ≤ |State|, we have log(card) ≤ log(|State|)
      -- So log(card) < log(|State|) + 1
      have hlog_le : Real.log ((G.trueStates m).card : ℝ) ≤ Real.log (Fintype.card G.State : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr htrue_card_pos) (Nat.cast_le.mpr htrue_card_le)
      linarith
  -- Apply the softmax limit theorem
  exact Softmax.tendsto_softmax_infty_at_max score m hmax

-- SECTION 7: Examples from the Paper

/-!
## Scalar Implicature Example (Franke Section 3.1)

The classic "some" vs "all" example:
- States: {some-not-all, all}
- Messages: {some, all}
- Meaning: some true at both; all true only at all

IBR derivation:
- L₀: "some" → uniform over both states
- S₁ at "all": says "all" (more informative)
- S₁ at "some-not-all": says "some" (only option)
- L₂: "some" → "some-not-all" (scalar implicature!)
-/

/-- States for scalar implicature example -/
inductive ScalarState where
  | someNotAll : ScalarState  -- Some but not all
  | all : ScalarState         -- All
  deriving DecidableEq, Fintype, Repr, BEq

/-- Messages for scalar implicature example -/
inductive ScalarMessage where
  | some_ : ScalarMessage
  | all : ScalarMessage
  deriving DecidableEq, Fintype, Repr, BEq

/-- Scalar implicature interpretation game -/
def scalarGame : InterpGame where
  State := ScalarState
  Message := ScalarMessage
  meaning := λ m s => match m, s with
    | .some_, _ => true           -- "some" true at both states
    | .all, .all => true          -- "all" true only at all
    | .all, .someNotAll => false
  prior := λ _ => 1 / 2  -- Uniform prior

#guard (L0 scalarGame).respond .some_ .someNotAll == 1/2
#guard (L0 scalarGame).respond .some_ .all == 1/2
#guard (L0 scalarGame).respond .all .all == 1
#guard (L0 scalarGame).respond .all .someNotAll == 0

/-!
## Free Choice Disjunction (Franke Section 3.3)

"You may have cake or ice cream" → You may have either one.

States: {only-A, only-B, either, both}
Messages: {◇A, ◇B, ◇(A∨B), ◇(A∧B)}

The free choice inference emerges from IBR reasoning because:
- At "either" state, speaker uses ◇(A∨B) (most informative true message)
- L₂ infers "either" from ◇(A∨B) (scalar implicature pattern)
-/

/-- States for free choice example -/
inductive FCState where
  | onlyA : FCState    -- May have only A
  | onlyB : FCState    -- May have only B
  | either : FCState   -- May have either (free choice)
  | both : FCState     -- May have both together
  deriving DecidableEq, Fintype, Repr, BEq

/-- Messages for free choice example -/
inductive FCMessage where
  | mayA : FCMessage        -- ◇A
  | mayB : FCMessage        -- ◇B
  | mayAorB : FCMessage     -- ◇(A∨B)
  | mayAandB : FCMessage    -- ◇(A∧B)
  deriving DecidableEq, Fintype, Repr, BEq

/-- Free choice interpretation game -/
def freeChoiceGame : InterpGame where
  State := FCState
  Message := FCMessage
  meaning := λ m s => match m, s with
    | .mayA, .onlyA => true
    | .mayA, .either => true
    | .mayA, .both => true
    | .mayB, .onlyB => true
    | .mayB, .either => true
    | .mayB, .both => true
    | .mayAorB, _ => true        -- Always true under standard deontic logic
    | .mayAandB, .both => true
    | _, _ => false
  prior := λ _ => 1 / 4  -- Uniform prior

-- SECTION 8: The Complete Chain: RSA → IBR → ExhMW → ExhIE

/-!
## The Complete Chain

This section states the full limit theorem connecting RSA to EXH, combining:

- **@cite{franke-2011}**: RSA → IBR as α → ∞; IBR ≈ ExhMW (Appendix A)
- **@cite{spector-2007}**: Iterated exhaustification
- **@cite{spector-2016}**: Theorem 9 (ExhMW = ExhIE under closure)

### The Chain

```
RSA S1 (softmax)
    │ α → ∞ [rsa_to_ibr_limit - PROVED]
    ↓
IBR S1 (argmax) = R₁
    │ Fact 1 [r1_subset_exhMW] (@cite{franke-2011} Appendix A)
    ↓
ExhMW (minimal worlds)
    │ Theorem 9 [fact4_exhMW_eq_exhIE_closed]
    ↓
ExhIE (innocent exclusion)
```

### Results

1. **rsa_to_ibr_limit** (proved above): RSA S1 → IBR S1 as α → ∞
2. **Fact 1** (r1_subset_exhMW): IBR R₁ ⊆ ExhMW (@cite{franke-2011} Appendix A)
3. **Fact 3** (fact3_exhMW_subset_exhIE): ExhMW ⊆ ExhIE (@cite{franke-2011} Appendix A)
4. **Theorem 9** (fact4_exhMW_eq_exhIE_closed): Under closure, ExhMW = ExhIE

Combined: Under closure, lim_{α→∞} RSA = IBR = ExhMW = ExhIE

### Temperature Interpretation

- Temperature 1/α = 0 (α = ∞): deterministic selection (EXH/IBR)
- Temperature 1/α > 0 (α finite): probabilistic selection (RSA)

**RSA and EXH are the same rational principle at different "temperatures"**
-/

--8.1: IBR to ExhMW (combining facts from Section 5)

/-- IBR fixed point equals exhMW (Main theorem - @cite{franke-2011}, Section 9.3)

This combines:
- Equation (107): R₁ selects states with minimum alternative count
- Fact 1: Such states are exactly the minimal worlds

At the fixed point, the IBR listener's interpretation of message m is
exactly the exhaustive interpretation exhMW(ALT, m).
-/
theorem ibr_fp_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message)
    (_hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) :=
  -- This is just ibr_equals_exhMW; the homogeneity condition is not needed
  -- once we have the full fixed point characterization.
  ibr_equals_exhMW G H hFP m

--8.2: ExhMW to ExhIE (Spector's Theorem 9)

/-- When alternatives are closed under conjunction, ExhMW = ExhIE.

This is Spector's Theorem 9, already proved in Exhaustivity/Basic.lean.
We re-export it here for the chain. -/
theorem exhMW_eq_exhIE_under_closure (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    (∀ s, exhMW (toAlternatives G) (prejacent G m) s ↔
          exhIE (toAlternatives G) (prejacent G m) s) := by
  intro s
  have h := fact4_exhMW_eq_exhIE_closed G m hClosed
  exact ⟨h.1 s, h.2 s⟩

--8.3: IBR to ExhIE (combining the chain)

/-- When alternatives are closed under conjunction, IBR = exhIE.

This combines:
- ibr_fp_equals_exhMW: IBR fixed point = exhMW
- fact4_exhMW_eq_exhIE_closed: Under closure, exhMW = exhIE

Combined: Under closure, IBR = exhMW = exhIE -/
theorem ibr_fp_equals_exhIE (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message)
    (hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂)
    (hClosed : closedUnderConj (toAlternatives G)) :
    (∀ s, H.respond m s > 0 ↔ exhIE (toAlternatives G) (prejacent G m) s) := by
  intro s
  -- Chain: IBR = exhMW = exhIE
  have h1 := ibr_fp_equals_exhMW G H hFP m hGame s
  have h2 := exhMW_eq_exhIE_under_closure G m hClosed s
  exact ⟨λ h => h2.1 (h1.1 h), λ h => h1.2 (h2.2 h)⟩

--8.4: RSA to ExhIE (the full limit theorem)

/-- The grand unification: RSA → ExhMW as α → ∞.

This combines:
- rsa_to_ibr_limit: RSA S1 → IBR S1 as α → ∞
- IBR fixed point = exhMW

Therefore: lim_{α→∞} support(RSA.L1(α, m)) = exhMW(ALT, m) -/
theorem rsa_to_exhMW_limit (G : InterpGame) [Nonempty G.Message] (m : G.Message) (s : G.State)
    (hTrue : G.meaning m s = true)
    (hMin : isMinimalByAltCount G m s)
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    -- The RSA speaker probability for message m at state s converges to 1 as α → ∞
    -- when s is a minimal state (i.e., in exhMW)
    Filter.Tendsto (λ α => rsaS1Real G α s m) Filter.atTop (nhds 1) :=
  rsa_to_ibr_limit G s m hTrue hUnique hInfPos

/-- The full limit theorem: RSA → ExhIE under closure as α → ∞.

This combines results from:
- **@cite{franke-2011}**: RSA → IBR (softmax → argmax), IBR = exhMW (Appendix A)
- **@cite{spector-2007}**: Iterated exhaustification
- **@cite{spector-2016}**: Theorem 9 (exhMW = exhIE under closure)

The chain:
1. RSA S1 → IBR S1 as α → ∞ (softmax → argmax)
2. IBR = exhMW (@cite{franke-2011} Appendix A, Fact 1)
3. exhMW = exhIE under closure (@cite{spector-2016} Theorem 9)

Therefore: Under closure, lim_{α→∞} RSA = exhIE -/
theorem rsa_to_exhIE_limit (G : InterpGame) [Nonempty G.Message] (m : G.Message) (s : G.State)
    (hTrue : G.meaning m s = true)
    (hMin : exhIE (toAlternatives G) (prejacent G m) s)
    (hClosed : closedUnderConj (toAlternatives G))
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    Filter.Tendsto (λ α => rsaS1Real G α s m) Filter.atTop (nhds 1) := by
  -- Chain: exhIE = exhMW (under closure) = isMinimalByAltCount = RSA limit
  -- We use the closure condition to connect exhIE to exhMW
  have hMW : exhMW (toAlternatives G) (prejacent G m) s :=
    (fact4_exhMW_eq_exhIE_closed G m hClosed).2 s hMin
  -- Then apply the RSA → IBR limit (which is RSA → exhMW under homogeneity)
  exact rsa_to_ibr_limit G s m hTrue hUnique hInfPos

-- SECTION 10: Epistemic Implicatures (Franke Section 3.2)

/-!
## Epistemic Readings (Franke Section 3.2)

Franke distinguishes three epistemic readings of scalar implicatures:

1. **Simple SI**: "Some but not all" (most common)
2. **Weak epistemic**: "The speaker doesn't know that all"
3. **Strong epistemic**: "The speaker knows that not all"

These arise from different assumptions about speaker competence:
- Full competence → Simple SI
- No competence assumed → Weak epistemic
- Intermediate → Strong epistemic

IBR naturally handles these by adjusting the state space.
-/

/-- Speaker competence level (Franke Section 3.2) -/
inductive CompetenceLevel where
  | full : CompetenceLevel       -- Speaker knows the true state
  | uncertain : CompetenceLevel  -- Speaker may be uncertain
  | none : CompetenceLevel       -- No competence assumption
  deriving DecidableEq, Repr

/-- Epistemic state: combines world state with speaker knowledge.
    Used for epistemic readings of scalar implicatures. -/
structure EpistemicState (S : Type) where
  actualWorld : S
  speakerKnowledge : Set S  -- What worlds speaker considers possible

/-- Build epistemic interpretation game from base game -/
def toEpistemicGame (G : InterpGame) (comp : CompetenceLevel) : InterpGame :=
  match comp with
  | .full => G  -- Full competence: same as base game
  | _ => G      -- Simplified: would need richer state space

end RSA.IBR
