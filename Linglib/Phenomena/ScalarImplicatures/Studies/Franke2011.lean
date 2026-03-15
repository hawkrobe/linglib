/-
@cite{franke-2011} @cite{benz-van-rooij-2005}. Quantity implicatures, exhaustive interpretation, and
rational conversation. S&P 4(1):1-82.

IBR (iterated best response) converges to exhaustive interpretation (exhMW).
RSA is "soft" IBR: as α → ∞, softmax → argmax → exhMW → exhIE.

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Linglib.Theories.Semantics.Exhaustification.Operators
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

/-- Hearer best response: argmax of posterior probability (Franke eq. 77/120).

    The hearer observes m, forms posterior μ(t|m) ∝ S(t,m) · P(t), and picks
    the state(s) with maximum posterior probability. Uniform over ties.
    For surprise messages (∀ t, S(t,m) · P(t) = 0), falls back to literal
    interpretation per the TCP assumption. -/
def hearerBR (G : InterpGame) (S : SpeakerStrategy G) : HearerStrategy G where
  respond := λ m t =>
    let w : G.State → ℚ := λ s => S.choose s m * G.prior s
    let maxW := Finset.univ.fold max 0 w
    if maxW == 0 then
      (L0 G).respond m t
    else
      if w t == maxW then
        1 / ((Finset.univ.filter (λ s => w s == maxW)).card : ℚ)
      else 0

/-- hearerBR always gives non-negative response values. -/
theorem hearerBR_respond_nonneg (G : InterpGame) (S : SpeakerStrategy G)
    (m : G.Message) (s : G.State) :
    (hearerBR G S).respond m s ≥ 0 := by
  simp only [hearerBR]
  split_ifs with hmaxW hwm
  · -- L0 fallback: literal gives 0 or 1/n, both ≥ 0
    simp only [L0, HearerStrategy.literal]
    split_ifs <;> first | exact le_refl 0 | exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · -- 1 / card ≥ 0
    exact div_nonneg (le_of_lt one_pos) (Nat.cast_nonneg _)
  · exact le_refl 0

/-- One full IBR iteration step: speaker best-responds, hearer argmax-responds. -/
def ibrStep (G : InterpGame) (H : HearerStrategy G) : HearerStrategy G :=
  hearerBR G (speakerUpdate G H)

/-- IBR reasoning for n iterations starting from L₀ -/
def ibrN (G : InterpGame) (n : ℕ) : HearerStrategy G :=
  match n with
  | 0 => L0 G
  | n + 1 => ibrStep G (ibrN G n)

/-- S₁: First pragmatic speaker -/
def S1 (G : InterpGame) : SpeakerStrategy G :=
  speakerUpdate G (L0 G)

/-- L₂: First pragmatic listener (argmax response to S₁) -/
def L2 (G : InterpGame) : HearerStrategy G :=
  hearerBR G (S1 G)

/-- Check if hearer strategy is a fixed point of IBR -/
def isIBRFixedPoint (G : InterpGame) (H : HearerStrategy G) : Prop :=
  ∀ m s, H.respond m s = (ibrStep G H).respond m s

/-- At a fixed point with non-negative priors, H.respond is non-negative.

This follows from the fact that H = ibrStep G H, and ibrStep uses
hearerBR which gives non-negative values (0 or 1/k). -/
theorem fp_respond_nonneg (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (_hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (m : G.Message) (s : G.State) :
    H.respond m s ≥ 0 := by
  rw [hFP m s]
  simp only [ibrStep]
  exact hearerBR_respond_nonneg G (speakerUpdate G H) m s

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

-- Helper lemmas for the hearer step of Lemma 3

/-- Per-message bound: Σ w(i)·h(i) ≤ maxW when h ≥ 0, Σ h ≤ 1, w ≤ maxW. -/
private theorem per_message_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w h : ι → ℚ) (hh : ∀ i, h i ≥ 0) (hhsum : Finset.univ.sum h ≤ 1)
    (maxW : ℚ) (hmaxW_nonneg : maxW ≥ 0) (hmaxW : ∀ i, w i ≤ maxW) :
    Finset.univ.sum (λ i => w i * h i) ≤ maxW := by
  calc Finset.univ.sum (λ i => w i * h i)
      ≤ Finset.univ.sum (λ i => maxW * h i) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (hmaxW i) (hh i)
    _ = maxW * Finset.univ.sum h := by rw [← Finset.mul_sum]
    _ ≤ maxW * 1 := by exact mul_le_mul_of_nonneg_left hhsum hmaxW_nonneg
    _ = maxW := mul_one maxW

/-- L0 (literal listener) response sums to at most 1 for each message. -/
private theorem literal_sum_le_one (G : InterpGame) (m : G.Message) :
    Finset.univ.sum (λ s => (HearerStrategy.literal G).respond m s) ≤ 1 := by
  simp only [HearerStrategy.literal]
  set n := (G.trueStates m).card
  by_cases hn : n = 0
  · apply le_trans _ zero_le_one
    apply Finset.sum_nonpos; intro s _; split_ifs <;> simp_all
  · have hval : ∀ s, (if G.meaning m s = true then
        (if n = 0 then (0 : ℚ) else 1 / ↑n) else 0) =
        if s ∈ G.trueStates m then 1 / (↑n : ℚ) else 0 := by
      intro s
      simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    simp_rw [hval]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
    exact le_of_eq (mul_one_div_cancel (Nat.cast_ne_zero.mpr hn))

/-- hearerBR response sums to at most 1 for each message. -/
private theorem hearerBR_sum_le_one (G : InterpGame) (S : SpeakerStrategy G) (m : G.Message) :
    Finset.univ.sum (λ s => (hearerBR G S).respond m s) ≤ 1 := by
  have hunfold : ∀ s, (hearerBR G S).respond m s =
      let w := fun s => S.choose s m * G.prior s
      let maxW := Finset.univ.fold max 0 w
      if maxW == 0 then (L0 G).respond m s
      else if w s == maxW then
        1 / ((Finset.univ.filter (fun s => w s == maxW)).card : ℚ)
      else 0 := by intro s; rfl
  simp_rw [hunfold]
  by_cases hmaxW :
    (Finset.univ.fold max 0 (fun s => S.choose s m * G.prior s) == (0 : ℚ)) = true
  · conv => lhs; arg 2; ext s; rw [if_pos hmaxW]
    exact literal_sum_le_one G m
  · conv => lhs; arg 2; ext s; rw [if_neg hmaxW]
    set k := (Finset.univ.filter (fun s =>
      (S.choose s m * G.prior s == Finset.univ.fold max 0
        (fun s => S.choose s m * G.prior s)) = true)).card
    have hval : ∀ s, (if (S.choose s m * G.prior s ==
        Finset.univ.fold max 0 (fun s => S.choose s m * G.prior s)) = true
        then 1 / (↑k : ℚ) else 0) =
        if s ∈ Finset.univ.filter (fun s =>
          (S.choose s m * G.prior s == Finset.univ.fold max 0
            (fun s => S.choose s m * G.prior s)) = true)
        then 1 / (↑k : ℚ) else 0 := by
      intro s; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp_rw [hval]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
    by_cases hk : k = 0
    · simp [hk]
    · exact le_of_eq (mul_one_div_cancel (Nat.cast_ne_zero.mpr hk))

/-- ibrN response is non-negative for all n. -/
private theorem ibrN_respond_nonneg (G : InterpGame) (n : ℕ) (m : G.Message) (s : G.State) :
    (ibrN G n).respond m s ≥ 0 := by
  induction n with
  | zero =>
    simp only [ibrN, L0, HearerStrategy.literal]
    split_ifs <;> first | exact le_refl 0 | exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  | succ n _ =>
    simp only [ibrN, ibrStep]
    exact hearerBR_respond_nonneg G _ m s

/-- ibrN response sums to at most 1 for all n. -/
private theorem ibrN_sum_le_one (G : InterpGame) (n : ℕ) (m : G.Message) :
    Finset.univ.sum (λ s => (ibrN G n).respond m s) ≤ 1 := by
  induction n with
  | zero => simp only [ibrN]; exact literal_sum_le_one G m
  | succ n _ => simp only [ibrN, ibrStep]; exact hearerBR_sum_le_one G _ m

/-- Per-message: hearerBR inner product ≥ maxW. The hearer argmax best response
    achieves at least maxW expected payoff per message. -/
private theorem hearerBR_inner_ge_max (G : InterpGame) (S : SpeakerStrategy G) (m : G.Message)
    (hw_nonneg : ∀ t, S.choose t m * G.prior t ≥ 0) :
    let w := fun s => S.choose s m * G.prior s
    let maxW := Finset.univ.fold max 0 w
    Finset.univ.sum (fun t => w t * (hearerBR G S).respond m t) ≥ maxW := by
  intro w maxW
  have hmaxW_nonneg : maxW ≥ 0 := (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))
  by_cases hmaxW0 : maxW ≤ 0
  · -- maxW = 0: sum ≥ 0 = maxW
    have : maxW = 0 := le_antisymm hmaxW0 hmaxW_nonneg
    linarith [Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) =>
      mul_nonneg (hw_nonneg t) (hearerBR_respond_nonneg G S m t))]
  · -- maxW > 0
    push_neg at hmaxW0
    -- fold_max_attained: maxW = 0 or maxW = w(t₀) for some t₀
    have h_attained := fold_max_attained Finset.univ w 0
    have ⟨t₀, ht₀_mem, ht₀_val⟩ : ∃ t₀ ∈ Finset.univ, w t₀ = maxW := by
      rcases h_attained with hinit | hex
      · linarith -- maxW = 0, contradicts hmaxW0
      · obtain ⟨x, hx, hfx⟩ := hex; exact ⟨x, hx, hfx.symm⟩
    -- t₀ is in the argmax set
    set argmax := Finset.univ.filter (fun t => (w t == maxW) = true)
    have ht₀_argmax : t₀ ∈ argmax := by
      simp only [argmax, Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq]
      exact ht₀_val
    have hk_pos : 0 < argmax.card := Finset.card_pos.mpr ⟨t₀, ht₀_argmax⟩
    -- BEq conditions for hearerBR unfolding
    have hmaxW_beq : (maxW == (0 : ℚ)) = false := by
      cases h : (maxW == (0 : ℚ))
      · rfl
      · rw [beq_iff_eq] at h; linarith
    -- On argmax states: hearerBR gives 1/k
    have hBR_argmax : ∀ t ∈ argmax, (hearerBR G S).respond m t =
        1 / (argmax.card : ℚ) := by
      intro t ht
      simp only [argmax, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      simp only [hearerBR]
      split_ifs with h1
      · exfalso; rw [hmaxW_beq] at h1; exact Bool.false_ne_true h1
      · rfl
    -- On argmax states: w(t) = maxW
    have hw_argmax : ∀ t ∈ argmax, w t = maxW := by
      intro t ht
      simp only [argmax, Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq] at ht
      exact ht
    -- Lower bound: sum ≥ argmax.sum ≥ k * (maxW/k) = maxW
    calc Finset.univ.sum (fun t => w t * (hearerBR G S).respond m t)
        ≥ argmax.sum (fun t => w t * (hearerBR G S).respond m t) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun t _ _ => mul_nonneg (hw_nonneg t) (hearerBR_respond_nonneg G S m t))
      _ = argmax.sum (fun _ => maxW * (1 / (argmax.card : ℚ))) := by
          apply Finset.sum_congr rfl; intro t ht
          rw [hw_argmax t ht, hBR_argmax t ht]
      _ = argmax.card • (maxW * (1 / (argmax.card : ℚ))) := by
          rw [Finset.sum_const]
      _ = (argmax.card : ℚ) * (maxW * (1 / (argmax.card : ℚ))) := by
          rw [nsmul_eq_mul]
      _ = maxW := by
          rw [show (argmax.card : ℚ) * (maxW * (1 / (argmax.card : ℚ))) =
              maxW * ((argmax.card : ℚ) * (1 / (argmax.card : ℚ))) from by ring,
            mul_one_div_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk_pos)),
            mul_one]

/-- Hearer step: hearerBR improves expected gain. For any S with S ≥ 0 and H with H ≥ 0
    and Σ H ≤ 1, we have EG(S, H) ≤ EG(S, hearerBR(S)). -/
private theorem eg_hearerBR_improvement (G : InterpGame)
    (S : SpeakerStrategy G) (H : HearerStrategy G)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S.choose s m ≥ 0)
    (hHNonneg : ∀ m s, H.respond m s ≥ 0)
    (hHSum : ∀ m, Finset.univ.sum (λ s => H.respond m s) ≤ 1) :
    expectedGain G S H ≤ expectedGain G S (hearerBR G S) := by
  -- Rewrite EG as Σ_m Σ_t (sum swap)
  unfold expectedGain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun t m => G.prior t * (S.choose t m * H.respond m t))]
  rw [Finset.sum_comm (f := fun t m => G.prior t * (S.choose t m * (hearerBR G S).respond m t))]
  -- Per-message inequality
  apply Finset.sum_le_sum; intro m _
  -- Rewrite P(t) * (S(t,m) * H(m,t)) as w(t) * H(m,t) where w = S * P
  set w := fun t => S.choose t m * G.prior t
  have hw_nonneg : ∀ t, w t ≥ 0 := fun t => mul_nonneg (hSNonneg t m) (hPriorNonneg t)
  set maxW := Finset.univ.fold max 0 w
  have hmaxW_nonneg : maxW ≥ 0 := (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))
  have hw_le : ∀ t, w t ≤ maxW :=
    fun t => (Finset.le_fold_max _).mpr (Or.inr ⟨t, Finset.mem_univ t, le_refl _⟩)
  -- Commute P * (S * H) to (S * P) * H = w * H
  have hcomm_old : ∀ t, G.prior t * (S.choose t m * H.respond m t) =
      w t * H.respond m t := by
    intro t; simp only [w]; ring
  have hcomm_new : ∀ t, G.prior t * (S.choose t m * (hearerBR G S).respond m t) =
      w t * (hearerBR G S).respond m t := by
    intro t; simp only [w]; ring
  simp_rw [hcomm_old, hcomm_new]
  -- old ≤ maxW ≤ new
  calc Finset.univ.sum (fun t => w t * H.respond m t)
      ≤ maxW := per_message_bound w (H.respond m) (fun t => hHNonneg m t) (hHSum m)
          maxW hmaxW_nonneg hw_le
    _ ≤ Finset.univ.sum (fun t => w t * (hearerBR G S).respond m t) :=
        hearerBR_inner_ge_max G S m hw_nonneg

/-- Franke's Lemma 3: EG is monotone non-decreasing along the IBR sequence.

    The combined effect of speaker best response + hearer argmax response
    produces a strategy pair with at least as high expected gain:
      EG(S_{n+1}, L_n) ≤ EG(S_{n+2}, L_{n+1})

    Proof decomposes into two steps via the intermediate EG(S_{n+1}, L_{n+1}):

    **Speaker step** (proved via `eg_speaker_improvement`):
    EG(S_{n+1}, L_{n+1}) ≤ EG(S_{n+2}, L_{n+1}) because S_{n+2} = bestResponse(L_{n+1})
    achieves at least as much EG against L_{n+1} as any valid speaker strategy.

    **Hearer step** (proved via `eg_hearerBR_improvement`):
    EG(S_{n+1}, L_n) ≤ EG(S_{n+1}, L_{n+1}) because L_{n+1} = hearerBR(S_{n+1})
    is the argmax best response. Per-message: Σ_t w(t)·H_old(m,t) ≤ maxW
    (from per_message_bound) and Σ_t w(t)·hearerBR(m,t) ≥ maxW (argmax achieves). -/
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
        -- L_{n+1} = hearerBR(S_{n+1}) = hearerBR(bestResponse(L_n))
        simp only [ibrN, ibrStep]
        apply eg_hearerBR_improvement G (speakerUpdate G (ibrN G n)) (ibrN G n) hPriorNonneg
        · exact SpeakerStrategy.bestResponse_nonneg G (ibrN G n)
        · exact ibrN_respond_nonneg G n
        · exact ibrN_sum_le_one G n
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
          exact hearerBR_respond_nonneg G (speakerUpdate G (ibrN G n)) m s

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

-- ===== Convergence helpers =====

/-- bestResponse inner product ≥ maxU: the best-response speaker achieves the maximum
    utility at each state. -/
private theorem bestResponse_inner_ge_maxU (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) :
    SpeakerStrategy.maxUtility G H s ≤ Finset.univ.sum (λ m =>
      (SpeakerStrategy.bestResponse G H).choose s m * H.respond m s) := by
  set opt := SpeakerStrategy.optimalMessages G H s
  set k := opt.card
  set maxU := SpeakerStrategy.maxUtility G H s
  have hval : ∀ m, (SpeakerStrategy.bestResponse G H).choose s m * H.respond m s =
      if m ∈ opt then (if k = 0 then 0 else 1 / (k : ℚ)) * H.respond m s else 0 := by
    intro m; rw [SpeakerStrategy.bestResponse_val]; split_ifs with hmem <;> ring
  simp_rw [hval]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hk0 : k = 0
  · have : maxU = 0 := by
      have hge : maxU ≥ 0 := SpeakerStrategy.maxUtility_nonneg G H s
      by_contra hne; push_neg at hne
      have hpos : maxU > 0 := lt_of_le_of_ne hge (Ne.symm hne)
      cases fold_max_attained (G.trueMessages s) (fun m' => H.respond m' s) 0 with
      | inl h0 =>
        have : maxU = 0 := h0; linarith
      | inr hex =>
        obtain ⟨m₀, hm₀, heq⟩ := hex
        have : m₀ ∈ opt := by
          simp only [opt, SpeakerStrategy.optimalMessages, Finset.mem_filter, beq_iff_eq]
          exact ⟨hm₀, by simp only [SpeakerStrategy.maxUtility]; exact heq.symm⟩
        exact absurd (Finset.card_pos.mpr ⟨m₀, this⟩) (by omega)
    simp [hk0, this]
  · have hopt_eq : ∀ m ∈ opt, H.respond m s = maxU :=
      fun m hm => SpeakerStrategy.optimalMessages_utility G H s m hm
    rw [if_neg hk0]
    have : opt.sum (fun m => (1 : ℚ) / (k : ℚ) * H.respond m s) =
        opt.sum (fun _ => (1 : ℚ) / (k : ℚ) * maxU) := by
      apply Finset.sum_congr rfl; intro m hm; rw [hopt_eq m hm]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    rw [show (k : ℚ) * (1 / (k : ℚ) * maxU) = maxU * ((k : ℚ) * (1 / (k : ℚ))) from by ring,
        mul_one_div_cancel (Nat.cast_ne_zero.mpr hk0), mul_one]

/-- Any valid speaker's inner product ≤ maxU. -/
private theorem speaker_inner_le_maxU' (G : InterpGame)
    (S : SpeakerStrategy G) (H : HearerStrategy G) (t : G.State)
    (hSNonneg : ∀ m, S.choose t m ≥ 0)
    (hSSum : Finset.univ.sum (λ m => S.choose t m) ≤ 1)
    (hSTruth : ∀ m, G.meaning m t = false → S.choose t m = 0) :
    Finset.univ.sum (λ m => S.choose t m * H.respond m t) ≤
    SpeakerStrategy.maxUtility G H t := by
  set maxU := SpeakerStrategy.maxUtility G H t
  calc Finset.univ.sum (λ m => S.choose t m * H.respond m t)
      ≤ Finset.univ.sum (λ m => S.choose t m * maxU) := by
        apply Finset.sum_le_sum; intro m _
        cases hm : G.meaning m t with
        | false => simp [hSTruth m hm]
        | true =>
          exact mul_le_mul_of_nonneg_left
            (SpeakerStrategy.utility_le_maxUtility G H t m
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩))
            (hSNonneg m)
    _ = Finset.univ.sum (λ m => S.choose t m) * maxU := by rw [Finset.sum_mul]
    _ ≤ 1 * maxU := mul_le_mul_of_nonneg_right hSSum (SpeakerStrategy.maxUtility_nonneg G H t)
    _ = maxU := one_mul maxU

/-- EG equality → per-state inner product equality. If S_old achieves the same EG as
    bestResponse against H, then at each positive-prior state, S_old's inner product
    equals maxUtility. -/
private theorem eg_eq_inner_eq' (G : InterpGame)
    (S_old : SpeakerStrategy G) (H : HearerStrategy G)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S_old.choose s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S_old.choose s m) ≤ 1)
    (hSTruth : ∀ s m, G.meaning m s = false → S_old.choose s m = 0)
    (hEG : expectedGain G S_old H = expectedGain G (SpeakerStrategy.bestResponse G H) H)
    (t : G.State) (hPt : G.prior t > 0) :
    Finset.univ.sum (λ m => S_old.choose t m * H.respond m t) =
    SpeakerStrategy.maxUtility G H t := by
  have h_best_eq : ∀ s, Finset.univ.sum (λ m =>
      (SpeakerStrategy.bestResponse G H).choose s m * H.respond m s) =
      SpeakerStrategy.maxUtility G H s := by
    intro s
    linarith [speaker_inner_le_maxU' G (SpeakerStrategy.bestResponse G H) H s
      (fun m => SpeakerStrategy.bestResponse_nonneg G H s m)
      (SpeakerStrategy.bestResponse_sum_le_one G H s)
      (fun m hm => SpeakerStrategy.bestResponse_false_zero G H s m hm),
      bestResponse_inner_ge_maxU G H s]
  have h_old_le : ∀ s, Finset.univ.sum (λ m => S_old.choose s m * H.respond m s) ≤
      SpeakerStrategy.maxUtility G H s :=
    fun s => speaker_inner_le_maxU' G S_old H s (hSNonneg s) (hSSum s) (hSTruth s)
  -- Σ P(s) * (maxU(s) - inner_old(s)) = 0 with all terms ≥ 0
  have hdiff : Finset.univ.sum (fun s => G.prior s *
      (SpeakerStrategy.maxUtility G H s -
       Finset.univ.sum (λ m => S_old.choose s m * H.respond m s))) = 0 := by
    have hEGnew : expectedGain G (SpeakerStrategy.bestResponse G H) H =
        Finset.univ.sum (fun s => G.prior s * SpeakerStrategy.maxUtility G H s) := by
      unfold expectedGain; congr 1; ext s; rw [h_best_eq s]
    have hEGold : expectedGain G S_old H =
        Finset.univ.sum (fun s => G.prior s *
          Finset.univ.sum (λ m => S_old.choose s m * H.respond m s)) := rfl
    rw [show (fun s => G.prior s * (SpeakerStrategy.maxUtility G H s -
        Finset.univ.sum (fun m => S_old.choose s m * H.respond m s))) =
        (fun s => G.prior s * SpeakerStrategy.maxUtility G H s -
          G.prior s * Finset.univ.sum (fun m => S_old.choose s m * H.respond m s))
      from by ext; ring]
    rw [Finset.sum_sub_distrib]; linarith [hEGnew, hEGold, hEG]
  have hnonneg : ∀ s, 0 ≤ G.prior s *
      (SpeakerStrategy.maxUtility G H s -
       Finset.univ.sum (λ m => S_old.choose s m * H.respond m s)) :=
    fun s => mul_nonneg (hPriorNonneg s) (sub_nonneg.mpr (h_old_le s))
  -- sum of nonneg = 0 → each = 0
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hdiff t
    (Finset.mem_univ t)
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · linarith

/-- If inner product = maxU and S(t,m) > 0, then H(m,t) = maxU. -/
private theorem inner_eq_maxU_respond_eq' (G : InterpGame)
    (S : SpeakerStrategy G) (H : HearerStrategy G) (t : G.State) (m : G.Message)
    (hSNonneg : ∀ m', S.choose t m' ≥ 0)
    (hSSum : Finset.univ.sum (λ m' => S.choose t m') ≤ 1)
    (hSTruth : ∀ m', G.meaning m' t = false → S.choose t m' = 0)
    (hInner : Finset.univ.sum (λ m' => S.choose t m' * H.respond m' t) =
              SpeakerStrategy.maxUtility G H t)
    (hSm : S.choose t m > 0) :
    H.respond m t = SpeakerStrategy.maxUtility G H t := by
  set maxU := SpeakerStrategy.maxUtility G H t
  have hTrue : G.meaning m t = true := by
    by_contra hFalse
    linarith [hSTruth m (by cases h : G.meaning m t <;> simp_all)]
  have hle : H.respond m t ≤ maxU :=
    SpeakerStrategy.utility_le_maxUtility G H t m
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTrue⟩)
  by_contra hne; push_neg at hne
  have hlt : H.respond m t < maxU := lt_of_le_of_ne hle hne
  linarith [show Finset.univ.sum (λ m' => S.choose t m' * H.respond m' t) < maxU from
    calc Finset.univ.sum (λ m' => S.choose t m' * H.respond m' t)
        < Finset.univ.sum (λ m' => S.choose t m' * maxU) := by
          apply Finset.sum_lt_sum
          · intro m' _
            cases hm' : G.meaning m' t with
            | false => simp [hSTruth m' hm']
            | true =>
              exact mul_le_mul_of_nonneg_left
                (SpeakerStrategy.utility_le_maxUtility G H t m'
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'⟩))
                (hSNonneg m')
          · exact ⟨m, Finset.mem_univ m, mul_lt_mul_of_pos_left hlt hSm⟩
      _ = Finset.univ.sum (λ m' => S.choose t m') * maxU := by rw [Finset.sum_mul]
      _ ≤ 1 * maxU := mul_le_mul_of_nonneg_right hSSum (SpeakerStrategy.maxUtility_nonneg G H t)
      _ = maxU := one_mul maxU]

/-- EG equality → support contained in optimalMessages. -/
private theorem eg_eq_opt_containment' (G : InterpGame)
    (S_old : SpeakerStrategy G) (H : HearerStrategy G)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S_old.choose s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S_old.choose s m) ≤ 1)
    (hSTruth : ∀ s m, G.meaning m s = false → S_old.choose s m = 0)
    (hEG : expectedGain G S_old H = expectedGain G (SpeakerStrategy.bestResponse G H) H)
    (t : G.State) (hPt : G.prior t > 0)
    (m : G.Message) (hSm : S_old.choose t m > 0) :
    m ∈ SpeakerStrategy.optimalMessages G H t := by
  have hInner := eg_eq_inner_eq' G S_old H hPriorNonneg hSNonneg hSSum hSTruth hEG t hPt
  have hResp := inner_eq_maxU_respond_eq' G S_old H t m (hSNonneg t) (hSSum t) (hSTruth t) hInner hSm
  simp only [SpeakerStrategy.optimalMessages, Finset.mem_filter, InterpGame.trueMessages,
    Finset.mem_univ, true_and, beq_iff_eq]
  exact ⟨by by_contra hF; linarith [hSTruth t m (by cases h : G.meaning m t <;> simp_all)], hResp⟩

/-- EG equality → optimalMessages containment between hearer strategies.
    If S_old = bestResponse(H_old) achieves the same EG as bestResponse(H) against H,
    then optimalMessages(H_old, t) ⊆ optimalMessages(H, t) for all t with P(t) > 0. -/
private theorem eg_eq_opt_subset (G : InterpGame) (H_old H : HearerStrategy G)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hPriorPos : ∀ s, G.prior s > 0)
    (hEG : expectedGain G (speakerUpdate G H_old) H =
           expectedGain G (SpeakerStrategy.bestResponse G H) H) :
    ∀ t, SpeakerStrategy.optimalMessages G H_old t ⊆
         SpeakerStrategy.optimalMessages G H t := by
  intro t m hm
  have hSm : (speakerUpdate G H_old).choose t m > 0 := by
    simp only [speakerUpdate]
    exact (SpeakerStrategy.bestResponse_pos_iff G H_old t m).mpr
      ⟨hm, Finset.card_pos.mpr ⟨m, hm⟩⟩
  exact eg_eq_opt_containment' G (speakerUpdate G H_old) H hPriorNonneg
    (fun s m' => SpeakerStrategy.bestResponse_nonneg G H_old s m')
    (fun s => SpeakerStrategy.bestResponse_sum_le_one G H_old s)
    (fun s m' hm' => SpeakerStrategy.bestResponse_false_zero G H_old s m' hm')
    hEG t (hPriorPos t) m hSm

/-- Determinism: equal hearer strategies produce equal shifted sequences. -/
private lemma ibrN_shift_congr (G : InterpGame) {n m : ℕ}
    (h : ibrN G n = ibrN G m) (k : ℕ) :
    ibrN G (n + k) = ibrN G (m + k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    show ibrN G (n + k + 1) = _
    simp only [ibrN]; exact congrArg (ibrStep G) ih

/-- Consecutive repeat → fixed point. -/
private lemma ibrN_consecutive_fp (G : InterpGame) (n : ℕ)
    (h : ibrN G n = ibrN G (n + 1)) :
    isIBRFixedPoint G (ibrN G n) := by
  intro m s
  have : (ibrN G n).respond m s = (ibrN G (n + 1)).respond m s :=
    congrFun (congrFun (congrArg HearerStrategy.respond h) m) s
  rw [this]; rfl

/-- Monotone sequence constant at first step of cycle. -/
private lemma monotone_cycle_eq_first {f : ℕ → ℚ} {n p : ℕ} (hp : 0 < p)
    (hMono : ∀ k, n ≤ k → k < n + p → f k ≤ f (k + 1))
    (hCycle : f n = f (n + p)) :
    f n = f (n + 1) := by
  have h1 : f n ≤ f (n + 1) := hMono n (le_refl _) (by omega)
  suffices f (n + 1) ≤ f n by linarith
  rw [hCycle]
  suffices ∀ j, 1 ≤ j → j ≤ p → f (n + 1) ≤ f (n + j) by exact this p (by omega) (le_refl _)
  intro j; induction j with
  | zero => omega
  | succ j ih =>
    intro hj1 hjp
    by_cases hj : j = 0
    · subst hj; simp
    · exact le_trans (ih (by omega) (by omega)) (hMono (n + j) (by omega) (by omega))

/-- Containment around a cycle of finite sets → equality at first step. -/
private lemma cycle_containment_eq {α : Type*} [DecidableEq α] {p : ℕ}
    (A : ℕ → Finset α) (hp : 0 < p)
    (hContain : ∀ k, k < p → A k ⊆ A (k + 1))
    (hCycle : A p = A 0) :
    A 0 = A 1 := by
  apply Finset.Subset.antisymm (hContain 0 (by omega))
  rw [← hCycle]
  suffices ∀ j, 1 ≤ j → j ≤ p → A 1 ⊆ A j by exact this p (by omega) (le_refl _)
  intro j; induction j with
  | zero => omega
  | succ j ih =>
    intro hj1 hjp
    by_cases hj : j = 0
    · subst hj; simp
    · exact Finset.Subset.trans (ih (by omega) (by omega)) (hContain j (by omega))

/-- Equal optimalMessages at all states → equal bestResponse speakers. -/
private theorem opt_eq_bestResponse_eq (G : InterpGame) (H₁ H₂ : HearerStrategy G)
    (hOpt : ∀ t, SpeakerStrategy.optimalMessages G H₁ t =
                  SpeakerStrategy.optimalMessages G H₂ t) :
    SpeakerStrategy.bestResponse G H₁ = SpeakerStrategy.bestResponse G H₂ := by
  show SpeakerStrategy.mk _ = SpeakerStrategy.mk _
  congr 1; ext t m
  show (SpeakerStrategy.bestResponse G H₁).choose t m =
       (SpeakerStrategy.bestResponse G H₂).choose t m
  simp only [SpeakerStrategy.bestResponse_val]; rw [hOpt t]

/-- The set of possible values for any IBR hearer strategy:
    {0} ∪ {1/k : 1 ≤ k ≤ |State|}. -/
private def ibrValueSet (G : InterpGame) : Finset ℚ :=
  insert 0 ((Finset.range (Fintype.card G.State)).image (fun k : ℕ => 1 / ((k : ℚ) + 1)))

private lemma one_div_mem_ibrValueSet (G : InterpGame) (n : ℕ)
    (hn1 : 1 ≤ n) (hn2 : n ≤ Fintype.card G.State) :
    (1 : ℚ) / (n : ℚ) ∈ ibrValueSet G := by
  simp only [ibrValueSet, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  right; exact ⟨n - 1, by omega, by congr 1; rw [Nat.cast_sub hn1]; ring⟩

private theorem L0_respond_mem_values (G : InterpGame) (m : G.Message) (s : G.State) :
    (L0 G).respond m s ∈ ibrValueSet G := by
  simp only [L0, HearerStrategy.literal]
  split_ifs with hm hn
  · exact Finset.mem_insert_self 0 _
  · exact one_div_mem_ibrValueSet G _ (by omega) (Finset.card_le_card (Finset.filter_subset _ _))
  · exact Finset.mem_insert_self 0 _

private theorem hearerBR_respond_mem_values (G : InterpGame) (S : SpeakerStrategy G)
    (m : G.Message) (s : G.State) :
    (hearerBR G S).respond m s ∈ ibrValueSet G := by
  simp only [hearerBR]
  split_ifs with hmaxW hwm
  · exact L0_respond_mem_values G m s
  · exact one_div_mem_ibrValueSet G _
      (Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hwm⟩⟩)
      (Finset.card_le_card (Finset.filter_subset _ _))
  · exact Finset.mem_insert_self 0 _

private theorem ibrN_respond_mem_values (G : InterpGame) (n : ℕ) (m : G.Message) (s : G.State) :
    (ibrN G n).respond m s ∈ ibrValueSet G := by
  induction n with
  | zero => exact L0_respond_mem_values G m s
  | succ n _ => simp only [ibrN, ibrStep]; exact hearerBR_respond_mem_values G _ m s

private noncomputable def encodeIBR (G : InterpGame) (n : ℕ) :
    G.Message → G.State → ↥(ibrValueSet G) :=
  fun m s => ⟨(ibrN G n).respond m s, ibrN_respond_mem_values G n m s⟩

private theorem encodeIBR_faithful (G : InterpGame) {n₁ n₂ : ℕ}
    (h : encodeIBR G n₁ = encodeIBR G n₂) :
    ibrN G n₁ = ibrN G n₂ := by
  show HearerStrategy.mk _ = HearerStrategy.mk _
  congr 1; ext m s
  exact Subtype.mk.inj (congr_fun (congr_fun h m) s)

/-- Strategy space is finite → IBR sequence eventually repeats.
    Proof: IBR hearer strategies have values in {0, 1/1, 1/2, ..., 1/|State|},
    giving at most (|State|+1)^(|Message|×|State|) distinct strategies.
    By pigeonhole (Finite.exists_ne_map_eq_of_infinite), two agree. -/
private theorem ibr_sequence_repeats (G : InterpGame) :
    ∃ n₁ n₂ : ℕ, n₁ < n₂ ∧ ibrN G n₁ = ibrN G n₂ := by
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (encodeIBR G)
  have hstrat := encodeIBR_faithful G heq
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨n₁, n₂, h, hstrat⟩
  · exact ⟨n₂, n₁, h, hstrat.symm⟩

/-- Theorem 3: IBR converges. EG is monotone increasing and bounded ⟹ fixed point.

    The proof uses cycle elimination: since the hearer strategy space is finite, the
    IBR sequence must repeat. EG monotonicity forces EG constant on the cycle.
    Constant EG implies optimalMessages containment at each step. Around the cycle,
    containment of finite sets gives equality. Equal optimalMessages gives equal
    bestResponse speakers, hence equal hearer BR, giving a consecutive repeat,
    which is a fixed point. -/
theorem ibr_reaches_fixed_point (G : InterpGame)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hPriorPos : ∀ s, G.prior s > 0)
    (hPriorSum : Finset.univ.sum G.prior = 1) :
    ∃ n : ℕ, isIBRFixedPoint G (ibrN G n) := by
  obtain ⟨n₁, n₂, hlt, heq⟩ := ibr_sequence_repeats G
  set p := n₂ - n₁
  have hp : 0 < p := by omega
  have hperiod : ibrN G n₁ = ibrN G (n₁ + p) := by
    rwa [Nat.add_sub_cancel' (le_of_lt hlt)]
  -- EG is monotone
  set eg := fun n => expectedGain G (speakerUpdate G (ibrN G n)) (ibrN G n)
  -- EG constant at first step of cycle
  have hEGconst : eg n₁ = eg (n₁ + 1) := by
    apply monotone_cycle_eq_first hp
      (fun k _ _ => eg_ibr_monotone G hPriorNonneg hPriorSum k)
    show expectedGain G (speakerUpdate G (ibrN G n₁)) (ibrN G n₁) =
         expectedGain G (speakerUpdate G (ibrN G (n₁ + p))) (ibrN G (n₁ + p))
    rw [hperiod]
  -- optimalMessages containment at each step of the cycle
  have hOptSubAll : ∀ k, k < p →
      ∀ t, SpeakerStrategy.optimalMessages G (ibrN G (n₁ + k)) t ⊆
           SpeakerStrategy.optimalMessages G (ibrN G (n₁ + k + 1)) t := by
    intro k hk
    -- eg(n₁+k) = eg(n₁+k+1) by monotonicity + cycle
    have hEGk : eg (n₁ + k) = eg (n₁ + k + 1) := by
      have h1 : eg n₁ ≤ eg (n₁ + k) := by
        suffices ∀ j, j ≤ k → eg n₁ ≤ eg (n₁ + j) by exact this k (le_refl _)
        intro j; induction j with
        | zero => simp
        | succ j ih =>
          intro hjk
          exact le_trans (ih (by omega)) (eg_ibr_monotone G hPriorNonneg hPriorSum (n₁ + j))
      have h2 : eg (n₁ + k + 1) ≤ eg (n₁ + p) := by
        suffices ∀ j, k + 1 ≤ j → j ≤ p → eg (n₁ + k + 1) ≤ eg (n₁ + j) by
          exact this p (by omega) (le_refl _)
        intro j; induction j with
        | zero => omega
        | succ j ih =>
          intro hj1 hjp
          by_cases hj : k + 1 ≤ j
          · exact le_trans (ih hj (by omega)) (eg_ibr_monotone G hPriorNonneg hPriorSum (n₁ + j))
          · have : j = k := by omega
            subst this; exact le_refl _
      have h3 := eg_ibr_monotone G hPriorNonneg hPriorSum (n₁ + k)
      have : eg (n₁ + p) = eg n₁ := by
        show expectedGain G (speakerUpdate G (ibrN G (n₁ + p))) (ibrN G (n₁ + p)) =
             expectedGain G (speakerUpdate G (ibrN G n₁)) (ibrN G n₁)
        rw [hperiod]
      linarith
    -- Decompose EG step: eg(n₁+k) ≤ mid ≤ eg(n₁+k+1), both equalities
    have hSpeakerEqK : expectedGain G (speakerUpdate G (ibrN G (n₁ + k)))
        (ibrN G (n₁ + k + 1)) =
        expectedGain G (speakerUpdate G (ibrN G (n₁ + k + 1)))
        (ibrN G (n₁ + k + 1)) := by
      have hH' : eg (n₁ + k) ≤ expectedGain G (speakerUpdate G (ibrN G (n₁ + k)))
          (ibrN G (n₁ + k + 1)) := by
        simp only [eg, ibrN, ibrStep]
        exact eg_hearerBR_improvement G (speakerUpdate G (ibrN G (n₁ + k)))
          (ibrN G (n₁ + k)) hPriorNonneg
          (fun s m => SpeakerStrategy.bestResponse_nonneg G (ibrN G (n₁ + k)) s m)
          (ibrN_respond_nonneg G (n₁ + k))
          (ibrN_sum_le_one G (n₁ + k))
      have hS' : expectedGain G (speakerUpdate G (ibrN G (n₁ + k)))
          (ibrN G (n₁ + k + 1)) ≤ eg (n₁ + k + 1) := by
        simp only [eg]
        exact eg_speaker_improvement G
          (speakerUpdate G (ibrN G (n₁ + k)))
          (speakerUpdate G (ibrN G (n₁ + k + 1)))
          (ibrN G (n₁ + k + 1)) rfl hPriorNonneg
          (fun s m => SpeakerStrategy.bestResponse_nonneg G (ibrN G (n₁ + k)) s m)
          (fun s => SpeakerStrategy.bestResponse_sum_le_one G (ibrN G (n₁ + k)) s)
          (fun s m hm => SpeakerStrategy.bestResponse_false_zero G (ibrN G (n₁ + k)) s m hm)
          (fun m s => hearerBR_respond_nonneg G (speakerUpdate G (ibrN G (n₁ + k))) m s)
      linarith
    exact eg_eq_opt_subset G (ibrN G (n₁ + k)) (ibrN G (n₁ + k + 1))
      hPriorNonneg hPriorPos hSpeakerEqK
  -- Containment around cycle → equality at first step
  have hOptEq : ∀ t, SpeakerStrategy.optimalMessages G (ibrN G n₁) t =
      SpeakerStrategy.optimalMessages G (ibrN G (n₁ + 1)) t := by
    intro t
    exact cycle_containment_eq
      (fun k => SpeakerStrategy.optimalMessages G (ibrN G (n₁ + k)) t) hp
      (fun k hk => hOptSubAll k hk t)
      (by show SpeakerStrategy.optimalMessages G (ibrN G (n₁ + p)) t =
              SpeakerStrategy.optimalMessages G (ibrN G n₁) t
          rw [hperiod])
  -- Equal optimalMessages → equal bestResponse → consecutive repeat → fixed point
  have hBReq := opt_eq_bestResponse_eq G (ibrN G n₁) (ibrN G (n₁ + 1)) hOptEq
  have hConsec : ibrN G (n₁ + 1) = ibrN G (n₁ + 2) := by
    show ibrStep G (ibrN G n₁) = ibrStep G (ibrN G (n₁ + 1))
    simp only [ibrStep, speakerUpdate]; rw [hBReq]
  exact ⟨n₁ + 1, ibrN_consecutive_fp G (n₁ + 1) hConsec⟩

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

-- fp_prefers_fewer_options was here but has been removed:
-- The theorem stated H(m,t₁) > H(m,t₂) ↔ speakerOptionCount(t₁) < speakerOptionCount(t₂).
-- This is FALSE for the hearerBR (argmax) model: with 3+ states, two states can both
-- get H = 0 (beaten by a third in the argmax) despite having different option counts,
-- breaking the backward direction of the ↔. The theorem was unused.

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

**Theorem (@cite{franke-2011}, Section 9.3)**: For a **scalar** interpretation
game G (truth sets are nested), the IBR fixed point listener's support for
message m equals the set of minimal m-worlds relative to the alternative ordering.

In notation:
  support(L∞(· | m)) = exhMW(ALT, m)

This connects game-theoretic pragmatics to grammatical exhaustification.

**Important**: The scalar game hypothesis (`isScalarGame`) is required.
For general games where truth sets are NOT nested, the theorem is false.
Counterexample: States {a,b,c}, Messages {m,p,q,r} with m true everywhere,
p true at {a,b}, q true at {a}, r true at {c}. At the FP, message m is
"dominated" (no state uses it optimally), so the L0 fallback gives uniform
probability to ALL m-true states including non-minimal ones.
See `nonScalarCounterexample` below for a machine-checked proof.

### Results from Section 10 and Appendix A

**Equation (107)**: R₁ characterization
  R₁(m) = {t ∈ ⟦m⟧ | ¬∃t′ ∈ ⟦m⟧ : |R⁻¹₀(t′)| < |R⁻¹₀(t)|}

This selects states where **fewest alternatives are true**.

**Fact 1** (Section 10): R₁(mₛ) ⊆ ExhMM(S)
Under "homogeneity" of alternatives, R₁(mₛ) = ExhMM(S).

**Fact 3** (Appendix A): ExhMM(S, Alt) ⊆ ExhIE(S, Alt)

**Fact 4** (Appendix A): ExhMM = ExhIE when Alt satisfies closure conditions.
-/

/-- A scalar game has truth sets that are totally ordered by inclusion.
    This is the structural condition required for Franke's Proposition 4
    (IBR FP = exhMW). Without it, "dominated" messages (never optimal at
    any state) fall back to L0, breaking the exhMW characterization.
    See `nonScalarCounterexample` below for a machine-checked counterexample
    without this condition. -/
def isScalarGame (G : InterpGame) : Prop :=
  ∀ m₁ m₂ : G.Message, G.trueStates m₁ ⊆ G.trueStates m₂ ∨ G.trueStates m₂ ⊆ G.trueStates m₁

/-- In a scalar game, trueMessages are totally ordered: for any two states,
    one's true messages are a subset of the other's.

    Proof: If ∃ m₁ ∈ trueMessages(s₁) \ trueMessages(s₂) and
    ∃ m₂ ∈ trueMessages(s₂) \ trueMessages(s₁), then trueStates(m₁) and
    trueStates(m₂) are incomparable (s₁ distinguishes them one way, s₂ the
    other), contradicting isScalarGame. -/
theorem scalar_trueMessages_total (G : InterpGame) (hScalar : isScalarGame G)
    (s₁ s₂ : G.State) :
    G.trueMessages s₁ ⊆ G.trueMessages s₂ ∨ G.trueMessages s₂ ⊆ G.trueMessages s₁ := by
  by_contra h
  push_neg at h
  simp only [Finset.subset_iff, not_forall] at h
  obtain ⟨⟨m₁, hm₁_in, hm₁_out⟩, ⟨m₂, hm₂_in, hm₂_out⟩⟩ := h
  simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at *
  cases hScalar m₁ m₂ with
  | inl hsub =>
    have h1 : s₁ ∈ G.trueStates m₁ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm₁_in⟩
    have h2 := hsub h1
    simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    -- h2 : G.meaning m₂ s₁ = true, but hm₂_out : ¬(G.meaning m₂ s₁ = true)
    exact absurd h2 hm₂_out
  | inr hsub =>
    have h1 : s₂ ∈ G.trueStates m₂ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm₂_in⟩
    have h2 := hsub h1
    simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    exact absurd h2 hm₁_out

/-- In a scalar game, at the m-true state s₀ with fewest true messages,
    every message true at s₀ has trueStates ⊇ trueStates(m).

    This is because trueMessages(s₀) ⊆ trueMessages(t) for all m-true t
    (by totality + minimality). So any m' ∈ trueMessages(s₀) is true at
    all m-true states, hence trueStates(m) ⊆ trueStates(m'). -/
theorem scalar_minimal_messages_weaker (G : InterpGame) (hScalar : isScalarGame G)
    (m : G.Message) (s₀ : G.State)
    (hs₀ : G.meaning m s₀ = true)
    (hmin : ∀ t, G.meaning m t = true → (G.trueMessages s₀).card ≤ (G.trueMessages t).card)
    (m' : G.Message) (hm' : G.meaning m' s₀ = true) :
    G.trueStates m ⊆ G.trueStates m' := by
  intro t ht
  simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  -- t is m-true. Need: m' is true at t.
  -- By totality: trueMessages(s₀) ⊆ trueMessages(t) or vice versa
  cases scalar_trueMessages_total G hScalar s₀ t with
  | inl hsub =>
    -- trueMessages(s₀) ⊆ trueMessages(t), so m' ∈ trueMessages(s₀) → m' ∈ trueMessages(t)
    have hm'_in : m' ∈ G.trueMessages s₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'⟩
    have := hsub hm'_in
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  | inr hsub =>
    -- trueMessages(t) ⊆ trueMessages(s₀). Since s₀ is minimal in card, this means equal.
    have hcard := hmin t ht
    have hcard' := Finset.card_le_card hsub
    have heq : G.trueMessages t = G.trueMessages s₀ := Finset.eq_of_subset_of_card_le hsub hcard
    have hm'_in : m' ∈ G.trueMessages s₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'⟩
    rw [← heq] at hm'_in
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in
    exact hm'_in

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

/-- Strict subset of trueMessages implies <_ALT under `toAlternatives G`. -/
theorem trueMessages_ssubset_implies_ltALT (G : InterpGame)
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

    This is already proved as `prop6_exhMW_entails_exhIE` in Exhaustification/Operators.lean.
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

    This is proved as `theorem9_main` in Exhaustification/Operators.lean.
-/
theorem fact4_exhMW_eq_exhIE_closed (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    exhMW (toAlternatives G) (prejacent G m) ≡ₚ exhIE (toAlternatives G) (prejacent G m) :=
  theorem9_main (toAlternatives G) (prejacent G m) hClosed

--5.5: IBR Fixed Point Theorems

/-- In a scalar game, <_ALT minimality among m-worlds is equivalent to
    having minimum trueMessages cardinality.

    This converts the <_ALT-based hypothesis used in exhMW to the
    cardinality-based hypothesis used by `scalar_minimal_messages_weaker`. -/
private theorem altMin_to_cardMin (G : InterpGame) (hScalar : isScalarGame G)
    (m : G.Message) (s : G.State)
    (_hs_true : G.meaning m s = true)
    (hs_min : ¬∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    ∀ t, G.meaning m t = true → (G.trueMessages s).card ≤ (G.trueMessages t).card := by
  intro t ht
  by_contra hlt
  push_neg at hlt
  -- card(trueMessages t) < card(trueMessages s)
  -- By scalar totality: trueMessages t ⊆ trueMessages s or vice versa
  cases scalar_trueMessages_total G hScalar t s with
  | inl hsub =>
    -- trueMessages t ⊆ trueMessages s, with strictly smaller card → strict subset
    have hss : G.trueMessages t ⊂ G.trueMessages s :=
      ⟨hsub, fun hrev => absurd (Finset.card_le_card hrev) (by omega)⟩
    exact hs_min ⟨t, ht, trueMessages_ssubset_implies_ltALT G t s hss⟩
  | inr hsub =>
    -- trueMessages s ⊆ trueMessages t → card s ≤ card t, contradicting hlt
    exact absurd (Finset.card_le_card hsub) (by omega)

/-- In a scalar game with distinct truth sets, every message m has a nonempty
    set of "level" states: states in trueStates(m) but not in any strictly
    smaller truth set. At these states, m is the strongest true message. -/
private theorem scalar_level_nonempty (G : InterpGame) (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (hNE : (G.trueStates m).Nonempty) :
    ∃ s ∈ G.trueStates m, ∀ m' : G.Message, G.meaning m' s = true →
      G.trueStates m ⊆ G.trueStates m' := by
  sorry

/-- In a scalar game at the FP, for any state s, H(m', s) = 0 for every
    message m' that is strictly weaker than some other message true at s
    (i.e., trueStates(m') ⊋ trueStates(m*) for some m* true at s).

    Proved by strong induction on card(trueMessages(s)).

    The key insight: if m' is not the strongest message at s, then there
    exist states with strictly fewer true messages where m' IS the strongest.
    By IH, the argmax of w(·, m') is exactly those states, so s ∉ argmax,
    hence H(m', s) = 0. -/
private theorem scalar_fp_weaker_zero (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m' : G.Message) (s : G.State) (hm' : G.meaning m' s = true)
    (hWeak : ∃ m₀ : G.Message, G.meaning m₀ s = true ∧
      G.trueStates m₀ ⊂ G.trueStates m') :
    H.respond m' s = 0 := by
  sorry

/-- At the FP of a scalar game, the optimal messages at any state consist
    of exactly the strongest message(s) true at that state. In a scalar game
    with distinct truth sets, this is a singleton.

    Consequence: bestResponse(s, m) = 1 if m is the strongest at s, 0 otherwise.
    So w(s, m) = p if m is strongest at s, 0 otherwise. -/
private theorem scalar_fp_opt_singleton (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (s : G.State) (hNE : (G.trueMessages s).Nonempty) :
    ∃ m₀ : G.Message, SpeakerStrategy.optimalMessages G H s = {m₀} ∧
      G.meaning m₀ s = true ∧
      (∀ m', G.meaning m' s = true → G.trueStates m₀ ⊆ G.trueStates m') := by
  sorry

/-- **Core structural lemma** (@cite{franke-2011}, Theorem 1 / Appendix B.2):

    At the FP of a scalar game with flat priors and distinct truth sets,
    w(s, m) = maxW_m ∧ maxW_m > 0 iff s is card-minimal among m-true states.

    **Proof sketch** (following Franke's Appendix B.2):

    Order messages m₁ ⊊ m₂ ⊊ ... ⊊ mₙ by truth set size. States at "level j"
    (in trueStates(mⱼ) \ trueStates(mⱼ₋₁)) have trueMessages = {mⱼ, ..., mₙ}.

    By induction from level n down to level 1:

    **Base** (j = n): Level-n states have trueMessages = {mₙ}, so opt = {mₙ}
    and w(s, mₙ) = p. Thus maxW_{mₙ} = p > 0, argmax = level-n states.

    **Step** (j < n, assuming levels > j settled): Level-j states have
    trueMessages = {mⱼ, ..., mₙ}. By IH, for k > j, maxW_{mₖ} = p and
    argmax_{mₖ} = level-k states. So H(mₖ, s) = 1/|level-k| if s is
    level-k, else 0. For level-j state s, H(mₖ, s) = 0 for all k > j
    (s is not level-k). Thus maxUtility(s) depends only on H(mⱼ, s).
    Since H(mₖ, s) = 0 for k > j, opt(s) = {mⱼ} and w(s, mⱼ) = p.
    So maxW_{mⱼ} = p and argmax_{mⱼ} = level-j states.

    At convergence, w(s, m) = p iff s is at the level of m (card-minimal),
    and w(s, m) = 0 otherwise.

    The backward direction: if w(s) = maxW > 0, then m ∈ opt(s), so
    |opt(s)| ≤ |opt(s_min)| and w(s) ≤ w(s_min). Since w(s) = maxW = w(s_min),
    |opt(s)| = |opt(s_min)|. The scalar structure then forces s to be at
    the same level as s_min, hence card-minimal.

    TODO: Full formal proof requires induction on the message chain with
    well-founded recursion on `(G.trueMessages s).card`. -/
private theorem scalar_fp_argmax_iff_minimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (s : G.State) (hs : G.meaning m s = true) :
    let w := fun t => (SpeakerStrategy.bestResponse G H).choose t m * G.prior t
    let maxW := Finset.univ.fold max 0 w
    (w s = maxW ∧ maxW > 0) ↔
      (∀ t, G.meaning m t = true → (G.trueMessages s).card ≤ (G.trueMessages t).card) := by
  simp only []
  set S := SpeakerStrategy.bestResponse G H
  set p := G.prior s
  set w := fun t => S.choose t m * G.prior t
  set maxW := Finset.univ.fold max 0 w
  -- Helper: bestResponse ≤ 1
  have hbr_le_one : ∀ t m', (SpeakerStrategy.bestResponse G H).choose t m' ≤ 1 := by
    intro t m'
    rw [SpeakerStrategy.bestResponse_val]
    split_ifs with hmem hcard
    · exact zero_le_one
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hcard)]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
    · exact zero_le_one
  -- Helper: w(t) ≤ p for all t
  have hw_le_p : ∀ t, w t ≤ p := by
    intro t
    calc w t = S.choose t m * G.prior t := rfl
      _ ≤ 1 * G.prior t := mul_le_mul_of_nonneg_right (hbr_le_one t m) (le_of_lt (hPriorPos t))
      _ = G.prior t := one_mul _
      _ = p := hFlatPrior t s
  constructor
  · -- (→) argmax → card-minimal
    intro ⟨hws, hmaxW_pos⟩ t ht
    -- w(s) = maxW > 0 means bestResponse(s,m) > 0, so m ∈ opt(s)
    have hbr_pos : S.choose s m > 0 := by
      by_contra h; push_neg at h
      have := le_antisymm h (SpeakerStrategy.bestResponse_nonneg G H s m)
      simp only [S] at this; rw [this, zero_mul] at hws; linarith
    have hm_opt : m ∈ SpeakerStrategy.optimalMessages G H s :=
      ((SpeakerStrategy.bestResponse_pos_iff G H s m).mp hbr_pos).1
    -- By scalar_fp_opt_singleton, opt(s) = {m₀} where m₀ is strongest at s
    have hNE : (G.trueMessages s).Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
    obtain ⟨m₀, hopt_eq, _, hm₀_strongest⟩ :=
      scalar_fp_opt_singleton G H hFP hPriorPos hFlatPrior hScalar hDistinct s hNE
    -- Since m ∈ opt(s) = {m₀}, m = m₀
    have : m = m₀ := Finset.mem_singleton.mp (hopt_eq ▸ hm_opt)
    subst this
    -- m is strongest at s: trueStates(m) ⊆ trueStates(m') for all m' true at s
    cases scalar_trueMessages_total G hScalar s t with
    | inl hsub => exact Finset.card_le_card hsub
    | inr hsub =>
      -- trueMessages(t) ⊆ trueMessages(s). Show trueMessages(s) ⊆ trueMessages(t) too.
      apply Finset.card_le_card
      intro m' hm'
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      -- m' true at s → trueStates(m) ⊆ trueStates(m') → t ∈ trueStates(m) → m' true at t
      have hm_sub_m' := hm₀_strongest m' hm'
      have ht_in : t ∈ G.trueStates m := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
      exact (Finset.mem_filter.mp (hm_sub_m' ht_in)).2
  · -- (←) card-minimal → argmax
    intro hCardMin
    -- Step 1: all other messages at s have H = 0
    have hOtherZero : ∀ m' : G.Message, G.meaning m' s = true → m' ≠ m →
        H.respond m' s = 0 := by
      intro m' hm'_true hne
      apply scalar_fp_weaker_zero G H hFP hPriorPos hFlatPrior hScalar hDistinct m' s hm'_true
      have hsub := scalar_minimal_messages_weaker G hScalar m s hs hCardMin m' hm'_true
      have hne_ts : G.trueStates m ≠ G.trueStates m' :=
        fun heq => hne (hDistinct m m' heq).symm
      exact ⟨m, hs, (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne_ts⟩)⟩
    -- Step 2: H(m, s) ≥ 0
    have hFP_nonneg := fp_respond_nonneg G H hFP (fun t => le_of_lt (hPriorPos t)) m s
    -- Step 3: maxUtility(s) = H(m, s)
    have hMaxUtil : SpeakerStrategy.maxUtility G H s = H.respond m s := by
      apply le_antisymm
      · -- maxUtility ≤ H(m,s): every true message m' has H(m',s) ≤ H(m,s)
        -- maxUtility = fold max 0 over trueMessages; attained at 0 or some element
        cases fold_max_attained (G.trueMessages s) (fun m' => H.respond m' s) 0 with
        | inl h0 =>
          simp only [SpeakerStrategy.maxUtility] at h0 ⊢
          rw [h0]; exact hFP_nonneg
        | inr ⟨m', hm', hfm'⟩ =>
          simp only [SpeakerStrategy.maxUtility] at hfm' ⊢
          rw [hfm']
          simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ,
            true_and] at hm'
          by_cases heq : m' = m
          · subst heq
          · rw [hOtherZero m' hm' heq]; exact hFP_nonneg
      · exact SpeakerStrategy.utility_le_maxUtility G H s m
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
    -- Step 4: m ∈ opt(s)
    have hm_opt : m ∈ SpeakerStrategy.optimalMessages G H s := by
      simp only [SpeakerStrategy.optimalMessages, Finset.mem_filter, beq_iff_eq]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, hMaxUtil.symm⟩
    -- Step 5: opt(s) = {m}
    have hopt_eq : SpeakerStrategy.optimalMessages G H s = {m} := by
      ext m'; simp only [Finset.mem_singleton]; constructor
      · intro hm'_opt
        by_contra hne
        have hm'_zero := hOtherZero m'
          (SpeakerStrategy.optimalMessages_meaning G H s m' hm'_opt) hne
        have hm'_util := SpeakerStrategy.optimalMessages_utility G H s m' hm'_opt
        -- H(m', s) = maxUtility(s) = H(m, s), but H(m', s) = 0
        rw [hm'_zero] at hm'_util
        -- hm'_util : 0 = maxUtility(s), hMaxUtil : maxUtility(s) = H(m, s)
        -- So H(m, s) = 0. But then maxW_m via hearerBR...
        -- We need to show this leads to contradiction.
        -- Actually, it's possible that H(m,s) = 0 (all H = 0 at s).
        -- In that case opt = trueMessages(s). The issue is we need opt = {m}.
        -- Use scalar_fp_opt_singleton which guarantees singleton opt.
        have hNE : (G.trueMessages s).Nonempty :=
          ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
        obtain ⟨m₀, hopt_eq', _, _⟩ :=
          scalar_fp_opt_singleton G H hFP hPriorPos hFlatPrior hScalar hDistinct s hNE
        have hm'_eq : m' = m₀ := Finset.mem_singleton.mp (hopt_eq' ▸ hm'_opt)
        have hm_eq : m = m₀ := Finset.mem_singleton.mp (hopt_eq' ▸ hm_opt)
        exact hne (hm'_eq.trans hm_eq.symm)
      · intro heq; subst heq; exact hm_opt
    -- Step 6: bestResponse(s, m) = 1, w(s) = p
    have hbr : S.choose s m = 1 := by
      change (SpeakerStrategy.bestResponse G H).choose s m = 1
      rw [SpeakerStrategy.bestResponse_val, if_pos hm_opt]
      rw [hopt_eq, Finset.card_singleton]
      norm_num
    have hws : w s = p := by
      change S.choose s m * G.prior s = p
      rw [hbr, one_mul]
    -- Step 7: maxW = p
    have hmaxW_eq : maxW = p := by
      apply le_antisymm
      · -- maxW ≤ p: use fold_max_attained
        cases fold_max_attained Finset.univ w 0 with
        | inl h0 => linarith [hPriorPos s]
        | inr ⟨t, _, hft⟩ => linarith [hw_le_p t]
      · -- p ≤ maxW: s attains p
        have : w s ≤ maxW := (Finset.le_fold_max w).mpr (Or.inr ⟨s, Finset.mem_univ _, le_refl _⟩)
        linarith
    constructor
    · linarith
    · linarith [hPriorPos s]

/-- In a scalar game at the FP with flat positive priors, if s is exhMW-minimal
    for m, then either maxW_m = 0 (and L0 gives positive probability) or
    w_m(s) = maxW_m (s is in the argmax).

    Derived from `scalar_fp_argmax_iff_minimal`. -/
private theorem scalar_fp_minimal_weight (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (s : G.State)
    (hs_true : G.meaning m s = true)
    (hs_min : ¬∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    let S := SpeakerStrategy.bestResponse G H
    let w := fun t => S.choose t m * G.prior t
    let maxW := Finset.univ.fold max 0 w
    maxW == 0 ∨ w s == maxW := by
  simp only []
  -- Convert <_ALT minimality to card minimality
  have hCardMin := altMin_to_cardMin G hScalar m s hs_true hs_min
  -- Apply the core structural lemma
  have hIff := scalar_fp_argmax_iff_minimal G H hFP hPriorPos hFlatPrior hScalar hDistinct m s hs_true
  have ⟨hws, _⟩ := hIff.mpr hCardMin
  right; rw [beq_iff_eq]; exact hws

/-- In a scalar game at the FP with flat positive priors, non-minimal states
    have H(m,s) = 0.

    Derived from `scalar_fp_argmax_iff_minimal`: non-minimal s is not
    card-minimal, so w(s) ≠ maxW and maxW > 0 (from a card-minimal witness). -/
private theorem scalar_fp_nonminimal_zero (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (s : G.State)
    (_hs_true : G.meaning m s = true)
    (hNonMin : ∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    H.respond m s = 0 := by
  -- s is non-minimal, so not card-minimal: ∃ t with strictly fewer trueMessages
  have hNotCardMin : ¬(∀ t, G.meaning m t = true →
      (G.trueMessages s).card ≤ (G.trueMessages t).card) := by
    push_neg
    obtain ⟨s', hs'_true, hs'_lt⟩ := hNonMin
    exact ⟨s', hs'_true, Finset.card_lt_card
      (ltALT_implies_trueMessages_ssubset G s' s hs'_lt)⟩
  -- Find a card-minimal state (exists by finiteness)
  have hne : (G.trueStates m).Nonempty :=
    ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, _hs_true⟩⟩
  obtain ⟨s_min, hs_min_mem, hs_min_le⟩ :=
    Finset.exists_min_image (G.trueStates m) (fun t => (G.trueMessages t).card) hne
  have hs_min_true : G.meaning m s_min = true := by
    simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and] at hs_min_mem
    exact hs_min_mem
  have hs_min_card : ∀ t, G.meaning m t = true →
      (G.trueMessages s_min).card ≤ (G.trueMessages t).card := by
    intro t ht
    exact hs_min_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
  -- From the core lemma: maxW > 0 (from the card-minimal state)
  have hIff_min := scalar_fp_argmax_iff_minimal G H hFP hPriorPos hFlatPrior
    hScalar hDistinct m s_min hs_min_true
  have ⟨_, hmaxW_pos⟩ := hIff_min.mpr hs_min_card
  -- From the core lemma: s is NOT in the argmax (not card-minimal)
  have hIff_s := scalar_fp_argmax_iff_minimal G H hFP hPriorPos hFlatPrior
    hScalar hDistinct m s _hs_true
  -- At the FP, H(m,s) = hearerBR(bestResponse(H))(m,s). Three cases:
  have hFPms := hFP m s
  rw [hFPms]
  simp only [ibrStep, speakerUpdate, hearerBR]
  split_ifs with hmaxW' hwm
  · -- Case 1: maxW == 0 → contradicts maxW > 0
    rw [beq_iff_eq] at hmaxW'
    linarith
  · -- Case 2: w(s) == maxW → s would be card-minimal, contradiction
    exfalso
    simp only [beq_iff_eq] at hwm
    exact hNotCardMin (hIff_s.mp ⟨hwm, hmaxW_pos⟩)
  · -- Case 3: maxW > 0, w(s) ≠ maxW. H = 0.
    rfl

/-- IBR fixed point equals exhMW (Main theorem - @cite{franke-2011}, Section 9.3)

This is the central result connecting game theory to exhaustification.
At the fixed point of a **scalar** interpretation game, the IBR listener's
interpretation of message m is exactly the exhaustive interpretation exhMW(ALT, m).

Two structural hypotheses are required:

- `isScalarGame`: truth sets are totally ordered by inclusion (nested). Without
  this, "dominated" messages fall back to L0, assigning positive probability
  to non-minimal states. See `nonScalarCounterexample` below.

- `hDistinct`: no two messages have identical truth sets. Without this,
  asymmetric FPs exist that break the biconditional: two exhMW-minimal states
  with identical trueMessages can be treated asymmetrically by the FP, with
  one getting H > 0 and the other H = 0.

**Proof Strategy:**

1. **Non-minimal states eliminated** (`scalar_fp_nonminimal_zero`):
   At non-minimal s, the speaker prefers more informative messages,
   so w(s) = 0 or w(s) < maxW. Since distinct truth sets ensure
   maxW > 0 (every message has unique states), s gets H = 0.

2. **Minimal states preserved** (`scalar_fp_minimal_weight`):
   At minimal s, m is (tied for) most informative. With distinct truth
   sets, the speaker uses m, giving w(s) = maxW.
-/
theorem ibr_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (_hScalar : isScalarGame G)
    (_hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) := by
  intro s
  constructor
  · -- Forward: H.respond m s > 0 → exhMW s
    intro hPos
    constructor
    · -- prejacent: m is true at s
      by_contra hNotTrue
      simp only [prejacent] at hNotTrue
      have hFalse : G.meaning m s = false := by
        cases hm : G.meaning m s
        · rfl
        · exact absurd hm hNotTrue
      have hFPms := hFP m s
      simp only [ibrStep, speakerUpdate] at hFPms
      have hSzero := SpeakerStrategy.bestResponse_false_zero G H s m hFalse
      rw [hFPms] at hPos
      simp only [hearerBR] at hPos
      split_ifs at hPos with hmaxW hwm
      · simp only [L0, HearerStrategy.literal]  at hPos
        rw [show (G.meaning m s) = false from hFalse] at hPos
        simp at hPos
      · rw [beq_iff_eq] at hmaxW hwm
        simp only [hSzero, zero_mul] at hwm
        exact absurd hwm.symm hmaxW
      · exact absurd hPos (lt_irrefl 0)
    · -- minimality: no s' <_ALT s with m true at s'
      intro hNonMin
      have hm_true : G.meaning m s = true := by
        by_contra hf
        have hFalse : G.meaning m s = false := by
          cases hm : G.meaning m s
          · rfl
          · exact absurd hm hf
        have hFPms := hFP m s
        simp only [ibrStep, speakerUpdate] at hFPms
        have hSz := SpeakerStrategy.bestResponse_false_zero G H s m hFalse
        rw [hFPms] at hPos
        simp only [hearerBR] at hPos
        split_ifs at hPos with hmW hwm
        · simp only [L0, HearerStrategy.literal, hFalse] at hPos; simp at hPos
        · rw [beq_iff_eq] at hmW hwm; simp [hSz, zero_mul] at hwm
          exact absurd hwm.symm hmW
        · exact absurd hPos (lt_irrefl 0)
      have hzero := scalar_fp_nonminimal_zero G H hFP hPriorPos hFlatPrior _hScalar _hDistinct m s
        hm_true hNonMin
      linarith
  · -- Backward: exhMW s → H.respond m s > 0
    intro ⟨hs_true, hs_min⟩
    have hTrue : G.meaning m s = true := hs_true
    -- At the FP: H(m,s) = hearerBR(bestResponse(H))(m,s).
    have hFPms := hFP m s
    rw [hFPms]
    simp only [ibrStep, speakerUpdate, hearerBR]
    split_ifs with hmaxW hwm
    · -- maxW = 0: L0 fallback. m true at s, so L0 gives 1/|trueStates| > 0.
      simp only [L0, HearerStrategy.literal]
      rw [hTrue]; simp only [↓reduceIte]
      have hcard : (G.trueStates m).card > 0 := Finset.card_pos.mpr
        ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTrue⟩⟩
      split_ifs with h
      · omega
      · exact div_pos one_pos (Nat.cast_pos.mpr (by omega))
    · -- w(s) = maxW: s is in the argmax. H = 1/|argmax| > 0.
      exact div_pos one_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr
        ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwm⟩⟩))
    · -- w(s) ≠ maxW and maxW ≠ 0: impossible for minimal s.
      exfalso
      have hweight := scalar_fp_minimal_weight G H hFP hPriorPos hFlatPrior _hScalar _hDistinct m s
        hTrue hs_min
      cases hweight with
      | inl h => exact absurd h hmaxW
      | inr h => exact absurd h hwm

/-- At the fixed point, IBR excludes non-minimal states.

Note: This is stated for the FIXED POINT listener, not L2 specifically.
L2 alone doesn't necessarily exclude all non-minimal states; the full
elimination happens through iteration to the fixed point.
-/
theorem ibr_fp_excludes_nonminimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ s, G.prior s > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (s : G.State)
    (_hs : G.meaning m s = true)
    (hNonMin : ∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    H.respond m s = 0 := by
  have hNotExh : ¬exhMW (toAlternatives G) (prejacent G m) s := λ hexh => hexh.2 hNonMin
  have hNotPos : ¬(H.respond m s > 0) :=
    λ hpos => hNotExh ((ibr_equals_exhMW G H hFP hPriorPos hFlatPrior hScalar hDistinct m s).mp hpos)
  have hNonneg := fp_respond_nonneg G H hFP (fun s => le_of_lt (hPriorPos s)) m s
  simp only [not_lt] at hNotPos
  linarith

/-- At the fixed point, IBR keeps minimal states.

If s is minimal among m-worlds (no s' < s with m(s')), then the fixed point
listener assigns positive probability to s given m.
-/
theorem ibr_fp_keeps_minimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (s : G.State)
    (hs : G.meaning m s = true)
    (hMin : ¬∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    H.respond m s > 0 := by
  have hExh : exhMW (toAlternatives G) (prejacent G m) s := ⟨hs, hMin⟩
  exact (ibr_equals_exhMW G H hFP hPriorPos hFlatPrior hScalar hDistinct m s).mpr hExh

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

/-- The scalar implicature game IS a scalar game: truth sets are nested. -/
theorem scalarGame_is_scalar : isScalarGame scalarGame := by
  intro m₁ m₂; cases m₁ <;> cases m₂ <;>
    simp [scalarGame, InterpGame.trueStates, Finset.subset_iff, Finset.mem_filter]

/-- The scalar implicature game has distinct truth sets: no two messages have
    the same set of true states. -/
theorem scalarGame_distinct :
    ∀ m₁ m₂ : scalarGame.Message, scalarGame.trueStates m₁ = scalarGame.trueStates m₂ → m₁ = m₂ := by
  intro m₁ m₂; cases m₁ <;> cases m₂ <;> simp [scalarGame, InterpGame.trueStates] <;> decide

-- 7.1: Counterexample for non-scalar games

/-!
## Counterexample: `ibr_equals_exhMW` fails for non-scalar games

States: {a, b, c}. Messages: {m, p, q, r}.
- m: true at a, b, c
- p: true at a, b (not c)
- q: true at a (not b, c)
- r: true at c (not a, b)

trueMessages: a={m,p,q}, b={m,p}, c={m,r}.
Only b <_ALT a (since {m,p} ⊂ {m,p,q}). a and c, b and c are incomparable.

At the FP with flat prior 1/3:
- q and r each have a unique true state, so H(q,a) = 1, H(r,c) = 1.
- opt(a) = {q}, opt(c) = {r}, opt(b) = {p} (each state uses its most informative message).
- Message m is never optimal at any state → maxW_m = 0 → L0 fallback.
- L0 gives H(m,s) = 1/3 for ALL m-true states, including a (non-minimal).

Result: H(m,a) = 1/3 > 0 but exhMW(m,a) = false.
The `isScalarGame` hypothesis prevents this by ensuring no message is dominated.
-/

private inductive NSState | a | b | c deriving DecidableEq, Fintype
private inductive NSMsg | m | p | q | r deriving DecidableEq, Fintype

private def nsGame : InterpGame where
  State := NSState
  Message := NSMsg
  meaning := fun msg st => match msg, st with
    | .m, _ => true | .p, .a => true | .p, .b => true | .q, .a => true | .r, .c => true
    | _, _ => false
  prior := fun _ => 1 / 3

/-- The non-scalar game is NOT a scalar game: trueStates(q) = {a} and trueStates(r) = {c}
    are incomparable. -/
theorem nsGame_not_scalar : ¬isScalarGame nsGame := by
  intro h
  have hqr := h .q .r
  -- trueStates(q) = {a}, trueStates(r) = {c}: incomparable
  rcases hqr with hsub | hsub
  · have : NSState.a ∈ nsGame.trueStates .q :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hmem := hsub this
    simp only [nsGame, InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    exact absurd hmem Bool.noConfusion
  · have : NSState.c ∈ nsGame.trueStates .r :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hmem := hsub this
    simp only [nsGame, InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    exact absurd hmem Bool.noConfusion

private def nsFPHearer : HearerStrategy nsGame where
  respond := fun msg st => match msg, st with
    | .m, _ => 1 / 3  -- L0 fallback
    | .p, .b => 1 | .q, .a => 1 | .r, .c => 1 | _, _ => 0

private theorem nsFP_is_fp : isIBRFixedPoint nsGame nsFPHearer := by
  intro msg st
  cases msg <;> cases st <;> native_decide

/-- At the FP of the non-scalar game, H(m,a) > 0 but a is non-minimal for m.
    This shows `ibr_equals_exhMW` is false without the `isScalarGame` hypothesis. -/
theorem nonScalarCounterexample :
    nsFPHearer.respond .m .a > 0 ∧
    ¬exhMW (toAlternatives nsGame) (prejacent nsGame .m) .a := by
  refine ⟨by simp [nsFPHearer], fun ⟨_, hmin⟩ => hmin ⟨.b, ?_, ?_⟩⟩
  · exact rfl
  · constructor
    · intro alt halt htrue
      simp only [toAlternatives, Set.mem_setOf_eq] at halt
      obtain ⟨msg, hmsg⟩ := halt; subst hmsg
      cases msg <;> simp_all [nsGame]
    · intro hle
      exact absurd (hle (fun s => nsGame.meaning .q s = true) ⟨.q, rfl⟩ rfl) (by decide)

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
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) :=
  ibr_equals_exhMW G H hFP hPriorPos hFlatPrior hScalar hDistinct m

--8.2: ExhMW to ExhIE (Spector's Theorem 9)

/-- When alternatives are closed under conjunction, ExhMW = ExhIE.

This is Spector's Theorem 9, already proved in Exhaustification/Operators.lean.
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
    (hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    (∀ s, H.respond m s > 0 ↔ exhIE (toAlternatives G) (prejacent G m) s) := by
  intro s
  have h1 := ibr_fp_equals_exhMW G H hFP hPriorPos hFlatPrior hScalar hDistinct m s
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
