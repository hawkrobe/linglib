/-
@cite{franke-2011} @cite{benz-van-rooij-2005}. Quantity implicatures, exhaustive interpretation, and
rational conversation. S&P 4(1):1-82.

IBR (iterated best response) converges to exhaustive interpretation (exhMW).
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Linglib.Core.Agent.RationalAction
import Linglib.Theories.Semantics.Exhaustification.Operators

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

@[simp] theorem mem_trueStates {m : G.Message} {s : G.State} :
    s ∈ G.trueStates m ↔ G.meaning m s = true := by
  simp [trueStates]

/-- Messages true at state s -/
def trueMessages (s : G.State) : Finset G.Message :=
  Finset.univ.filter (λ m => G.meaning m s = true)

@[simp] theorem mem_trueMessages {s : G.State} {m : G.Message} :
    m ∈ G.trueMessages s ↔ G.meaning m s = true := by
  simp [trueMessages]

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
  (G.trueMessages s).filter (λ m => H.respond m s = maxUtility G H s)

theorem optimalMessages_subset_trueMessages (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) : optimalMessages G H s ⊆ G.trueMessages s :=
  Finset.filter_subset _ _

theorem optimalMessages_meaning (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) (hm : m ∈ optimalMessages G H s) :
    G.meaning m s = true :=
  G.mem_trueMessages.mp (optimalMessages_subset_trueMessages G H s hm)

theorem optimalMessages_utility (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) (hm : m ∈ optimalMessages G H s) :
    H.respond m s = maxUtility G H s :=
  (Finset.mem_filter.mp hm).2

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

/-- Best response speaker gives at most probability 1 to any message. -/
theorem bestResponse_le_one (G : InterpGame) (H : HearerStrategy G)
    (s : G.State) (m : G.Message) :
    (bestResponse G H).choose s m ≤ 1 := by
  rw [bestResponse_val]
  split_ifs with _ hcard
  · exact zero_le_one
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hcard)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
  · exact zero_le_one

end SpeakerStrategy


/-- L₀: Literal listener (Franke Def. 22) -/
def L0 (G : InterpGame) : HearerStrategy G :=
  HearerStrategy.literal G

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
    if maxW = 0 then
      (L0 G).respond m t
    else
      if w t = maxW then
        1 / ((Finset.univ.filter (λ s => w s = maxW)).card : ℚ)
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

/-- Any valid speaker's inner product ≤ maxU at each state. -/
private theorem speaker_inner_le_maxU (G : InterpGame)
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
            (SpeakerStrategy.utility_le_maxUtility G H t m (G.mem_trueMessages.mpr hm))
            (hSNonneg m)
    _ = Finset.univ.sum (λ m => S.choose t m) * maxU := by rw [Finset.sum_mul]
    _ ≤ 1 * maxU := mul_le_mul_of_nonneg_right hSSum (SpeakerStrategy.maxUtility_nonneg G H t)
    _ = maxU := one_mul maxU

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
          simp only [opt, SpeakerStrategy.optimalMessages, Finset.mem_filter]
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
  subst hBR
  linarith [speaker_inner_le_maxU G S_old H t (hSNonneg t) (hSSum t) (hSTruth t),
            bestResponse_inner_ge_maxU G H t]

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
      simp only [InterpGame.mem_trueStates]
      split_ifs <;> simp_all
    simp_rw [hval]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
    exact le_of_eq (mul_one_div_cancel (Nat.cast_ne_zero.mpr hn))

/-- hearerBR response sums to at most 1 for each message. -/
private theorem hearerBR_sum_le_one (G : InterpGame) (S : SpeakerStrategy G) (m : G.Message) :
    Finset.univ.sum (λ s => (hearerBR G S).respond m s) ≤ 1 := by
  set w : G.State → ℚ := fun s => S.choose s m * G.prior s
  set maxW := Finset.univ.fold max 0 w
  by_cases hmaxW : maxW = 0
  · have hL0 : ∀ s, (hearerBR G S).respond m s = (L0 G).respond m s :=
      fun s => show (hearerBR G S).respond m s = _ by simp only [hearerBR]; rw [if_pos hmaxW]
    simp_rw [hL0]; exact literal_sum_le_one G m
  · set argmax := Finset.univ.filter (fun s => w s = maxW)
    set k := argmax.card
    have hval : ∀ s, (hearerBR G S).respond m s =
        if s ∈ argmax then 1 / (↑k : ℚ) else 0 := by
      intro s
      show (hearerBR G S).respond m s = _
      simp only [hearerBR]; rw [if_neg hmaxW]
      change (if w s = maxW then 1 / (↑k : ℚ) else 0) = _
      simp only [argmax, Finset.mem_filter, Finset.mem_univ, true_and]
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
    set argmax := Finset.univ.filter (fun t => w t = maxW)
    have ht₀_argmax : t₀ ∈ argmax :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀_val⟩
    have hk_pos : 0 < argmax.card := Finset.card_pos.mpr ⟨t₀, ht₀_argmax⟩
    -- On argmax states: hearerBR gives 1/k
    have hBR_argmax : ∀ t ∈ argmax, (hearerBR G S).respond m t =
        1 / (argmax.card : ℚ) := by
      intro t ht
      simp only [argmax, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      simp only [hearerBR]
      rw [if_neg (by linarith), if_pos ht]
    -- On argmax states: w(t) = maxW
    have hw_argmax : ∀ t ∈ argmax, w t = maxW := by
      intro t ht
      exact (Finset.mem_filter.mp ht).2
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
    linarith [speaker_inner_le_maxU G (SpeakerStrategy.bestResponse G H) H s
      (fun m => SpeakerStrategy.bestResponse_nonneg G H s m)
      (SpeakerStrategy.bestResponse_sum_le_one G H s)
      (fun m hm => SpeakerStrategy.bestResponse_false_zero G H s m hm),
      bestResponse_inner_ge_maxU G H s]
  have h_old_le : ∀ s, Finset.univ.sum (λ m => S_old.choose s m * H.respond m s) ≤
      SpeakerStrategy.maxUtility G H s :=
    fun s => speaker_inner_le_maxU G S_old H s (hSNonneg s) (hSSum s) (hSTruth s)
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
    SpeakerStrategy.utility_le_maxUtility G H t m (G.mem_trueMessages.mpr hTrue)
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
                (SpeakerStrategy.utility_le_maxUtility G H t m' (G.mem_trueMessages.mpr hm'))
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
    Finset.mem_univ, true_and]
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

/-- Monotone sequence constant at every step of a cycle.
    If f is monotone and f(n) = f(n + p), then f(n + k) = f(n + k + 1) for all k < p.
    Proof: f(n) ≤ f(n+k) ≤ f(n+k+1) ≤ f(n+p) = f(n), so all are equal. -/
private lemma monotone_cycle_all_eq {f : ℕ → ℚ} {n p : ℕ}
    (hMono : ∀ k, f k ≤ f (k + 1))
    (hCycle : f n = f (n + p))
    (k : ℕ) (hk : k < p) :
    f (n + k) = f (n + k + 1) := by
  have mono_shift : ∀ (a : ℕ) (j : ℕ), f a ≤ f (a + j) := by
    intro a j; induction j with
    | zero => simp
    | succ j ih => exact le_trans ih (hMono (a + j))
  have h1 := mono_shift n k
  have h2 := hMono (n + k)
  have h3 := mono_shift (n + k + 1) (p - k - 1)
  have h4 : n + k + 1 + (p - k - 1) = n + p := by omega
  rw [h4] at h3; linarith

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
  -- EG is monotone along the IBR sequence
  set eg := fun n => expectedGain G (speakerUpdate G (ibrN G n)) (ibrN G n)
  have hEGmono : ∀ k, eg k ≤ eg (k + 1) := eg_ibr_monotone G hPriorNonneg hPriorSum
  have hEGcycle : eg n₁ = eg (n₁ + p) := by
    simp only [eg]; rw [hperiod]
  -- optimalMessages containment at each step of the cycle
  have hOptSubAll : ∀ k, k < p →
      ∀ t, SpeakerStrategy.optimalMessages G (ibrN G (n₁ + k)) t ⊆
           SpeakerStrategy.optimalMessages G (ibrN G (n₁ + k + 1)) t := by
    intro k hk
    -- EG is constant on the entire cycle (monotone + cycle → all steps equal)
    have hEGk : eg (n₁ + k) = eg (n₁ + k + 1) :=
      monotone_cycle_all_eq hEGmono hEGcycle k hk
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
Without it, "dominated" messages (never optimal at any state) fall back to
L0, assigning uniform probability to ALL m-true states including non-minimal ones.

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
    any state) fall back to L0, breaking the exhMW characterization. -/
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
  simp only [InterpGame.mem_trueMessages] at *
  cases hScalar m₁ m₂ with
  | inl hsub =>
    have h1 : s₁ ∈ G.trueStates m₁ := G.mem_trueStates.mpr hm₁_in
    have h2 := hsub h1
    simp only [InterpGame.mem_trueStates] at h2
    -- h2 : G.meaning m₂ s₁ = true, but hm₂_out : ¬(G.meaning m₂ s₁ = true)
    exact absurd h2 hm₂_out
  | inr hsub =>
    have h1 : s₂ ∈ G.trueStates m₂ := G.mem_trueStates.mpr hm₂_in
    have h2 := hsub h1
    simp only [InterpGame.mem_trueStates] at h2
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
  simp only [InterpGame.mem_trueStates] at ht ⊢
  -- t is m-true. Need: m' is true at t.
  -- By totality: trueMessages(s₀) ⊆ trueMessages(t) or vice versa
  cases scalar_trueMessages_total G hScalar s₀ t with
  | inl hsub =>
    -- trueMessages(s₀) ⊆ trueMessages(t), so m' ∈ trueMessages(s₀) → m' ∈ trueMessages(t)
    exact G.mem_trueMessages.mp (hsub (G.mem_trueMessages.mpr hm'))
  | inr hsub =>
    -- trueMessages(t) ⊆ trueMessages(s₀). Since s₀ is minimal in card, this means equal.
    have hcard := hmin t ht
    have hcard' := Finset.card_le_card hsub
    have heq : G.trueMessages t = G.trueMessages s₀ := Finset.eq_of_subset_of_card_le hsub hcard
    exact G.mem_trueMessages.mp (heq ▸ G.mem_trueMessages.mpr hm')

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
    simp only [InterpGame.mem_trueMessages] at hm' ⊢
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
    have hm'_in : m' ∈ G.trueMessages s := G.mem_trueMessages.mpr ha_s
    exact G.mem_trueMessages.mp (heq ▸ hm'_in)

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
    have hm'_in_s' : m' ∈ G.trueMessages s' := G.mem_trueMessages.mpr ha_s'
    exact G.mem_trueMessages.mp (Finset.mem_of_subset hss.1 hm'_in_s')
  · -- ¬(leALT s s'): NOT every alt true at s is true at s'
    intro hle
    -- If leALT s s', then trueMessages s ⊆ trueMessages s'
    have hsub : G.trueMessages s ⊆ G.trueMessages s' := by
      intro m' hm'
      simp only [InterpGame.mem_trueMessages] at hm' ⊢
      have h : (λ x => G.meaning m' x = true) s := hm'
      have halt := hle (λ x => G.meaning m' x = true) ⟨m', rfl⟩ h
      exact halt
    -- But hss says trueMessages s' ⊂ trueMessages s (proper subset)
    -- hss.2 : ¬(trueMessages s ⊆ trueMessages s')
    -- But hsub says trueMessages s ⊆ trueMessages s', contradiction
    exact hss.2 hsub

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
      · -- trueMessages s' ⊂ trueMessages s, contradicting exhMW minimality
        have hss : G.trueMessages s' ⊂ G.trueMessages s :=
          ⟨hsub', λ h => heq (Finset.Subset.antisymm hsub' h)⟩
        exact absurd ⟨s', hs'_true, trueMessages_ssubset_implies_ltALT G s' s hss⟩ hmw.2

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
  -- Pick a state s in trueStates(m) with minimum card(trueMessages(s))
  have ⟨s, hs_in, hs_min⟩ := Finset.exists_min_image (G.trueStates m)
    (fun s => (G.trueMessages s).card) hNE
  refine ⟨s, hs_in, fun m' hm' => ?_⟩
  -- Need: trueStates(m) ⊆ trueStates(m')
  -- Equivalently: every m-true state is m'-true
  intro t ht
  simp only [InterpGame.mem_trueStates] at hs_in ht ⊢
  -- By scalar: trueStates(m) ⊆ trueStates(m') or trueStates(m') ⊆ trueStates(m)
  cases hScalar m m' with
  | inl hsub =>
    -- trueStates(m) ⊆ trueStates(m'), so m true at t → m' true at t
    exact (G.mem_trueStates.mp (hsub (G.mem_trueStates.mpr ht)))
  | inr hsub =>
    -- trueStates(m') ⊆ trueStates(m)
    -- m' true at s, so s ∈ trueStates(m'). Since trueStates(m') ⊆ trueStates(m),
    -- every m'-true state is m-true. So trueMessages of any m'-true state includes m.
    -- At s: m and m' are both true, so both in trueMessages(s).
    -- At t: m is true. Is m' true at t?
    -- We know trueMessages(s) is minimal among m-true states.
    -- By scalar totality: trueMessages(t) ⊆ trueMessages(s) or vice versa.
    cases scalar_trueMessages_total G hScalar t s with
    | inl hsub_tm =>
      -- trueMessages(t) ⊆ trueMessages(s). card(t) ≤ card(s).
      -- But s has min card among m-true states, so card(s) ≤ card(t). Equal.
      have heq := Finset.eq_of_subset_of_card_le hsub_tm
        (hs_min t (G.mem_trueStates.mpr ht))
      -- trueMessages(t) = trueMessages(s), so m' ∈ trueMessages(s) → m' ∈ trueMessages(t)
      have hm'_in_s : m' ∈ G.trueMessages s := G.mem_trueMessages.mpr hm'
      rw [← heq] at hm'_in_s
      exact G.mem_trueMessages.mp hm'_in_s
    | inr hsub_st =>
      -- trueMessages(s) ⊆ trueMessages(t), so m' ∈ trueMessages(s) → m' ∈ trueMessages(t)
      have hm'_in_s : m' ∈ G.trueMessages s := G.mem_trueMessages.mpr hm'
      exact G.mem_trueMessages.mp (hsub_st hm'_in_s)

/-- L0 response value for a true message. -/
private theorem L0_respond_true (G : InterpGame) (m : G.Message) (s : G.State)
    (hm : G.meaning m s = true) :
    (L0 G).respond m s = 1 / ((G.trueStates m).card : ℚ) := by
  simp only [L0, HearerStrategy.literal]
  split_ifs with h
  · exact absurd h (Finset.card_ne_zero.mpr ⟨s, G.mem_trueStates.mpr hm⟩)
  · rfl

/-- In a scalar game with distinct truth sets, for all n ≥ 0, the speaker's
    optimal messages at `ibrN G n` are the unique strongest message at each
    state. By induction on n (base = L0, step = hearerBR preserves). -/
private theorem ibrN_opt_singleton (G : InterpGame)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (n : ℕ) :
    ∀ (s : G.State), (G.trueMessages s).Nonempty →
    ∃ m₀ : G.Message, SpeakerStrategy.optimalMessages G (ibrN G n) s = {m₀} ∧
      G.meaning m₀ s = true ∧
      (∀ m', G.meaning m' s = true → G.trueStates m₀ ⊆ G.trueStates m') := by
  -- Helper: find the strongest message at any state
  have find_strongest : ∀ (s : G.State), (G.trueMessages s).Nonempty →
      ∃ m₀ ∈ G.trueMessages s, G.meaning m₀ s = true ∧
        (∀ m', G.meaning m' s = true → G.trueStates m₀ ⊆ G.trueStates m') ∧
        (∀ m', G.meaning m' s = true → m' ≠ m₀ →
          G.trueStates m₀ ⊂ G.trueStates m') := by
    intro s hNE
    obtain ⟨m₀, hm₀_in, hm₀_min⟩ := Finset.exists_min_image (G.trueMessages s)
      (fun m => (G.trueStates m).card) hNE
    have hm₀_in := G.mem_trueMessages.mp hm₀_in
    have hm₀_str : ∀ m', G.meaning m' s = true → G.trueStates m₀ ⊆ G.trueStates m' := by
      intro m' hm'
      cases hScalar m₀ m' with
      | inl h => exact h
      | inr h =>
        exact Finset.eq_of_subset_of_card_le h
          (hm₀_min m' (G.mem_trueMessages.mpr hm')) ▸ Finset.Subset.refl _
    refine ⟨m₀, G.mem_trueMessages.mpr hm₀_in, hm₀_in, hm₀_str, ?_⟩
    intro m' hm' hne
    exact lt_of_le_of_ne (hm₀_str m' hm')
      (fun heq => hne (hDistinct m₀ m' heq).symm)
  induction n with
  | zero =>
    intro s hNE
    obtain ⟨m₀, hm₀_mem, hm₀_in, hm₀_str, hm₀_sstr⟩ := find_strongest s hNE
    -- L0(m) ≤ L0(m₀) for all m; strict for m ≠ m₀
    have hL0_le : ∀ m ∈ G.trueMessages s, (L0 G).respond m s ≤ (L0 G).respond m₀ s := by
      intro m hm_mem
      have hm_mem := G.mem_trueMessages.mp hm_mem
      rw [L0_respond_true G m s hm_mem, L0_respond_true G m₀ s hm₀_in]
      exact div_le_div_of_nonneg_left zero_le_one
        (by exact_mod_cast Finset.card_pos.mpr ⟨s, G.mem_trueStates.mpr hm₀_in⟩)
        (by exact_mod_cast Finset.card_le_card (hm₀_str m hm_mem))
    have hL0_strict : ∀ m ∈ G.trueMessages s, m ≠ m₀ →
        (L0 G).respond m s < (L0 G).respond m₀ s := by
      intro m hm_mem hne
      have hm_mem := G.mem_trueMessages.mp hm_mem
      rw [L0_respond_true G m s hm_mem, L0_respond_true G m₀ s hm₀_in]
      exact div_lt_div_of_pos_left one_pos
        (by exact_mod_cast Finset.card_pos.mpr ⟨s, G.mem_trueStates.mpr hm₀_in⟩)
        (by exact_mod_cast Finset.card_lt_card (hm₀_sstr m hm_mem hne))
    -- maxUtility = L0(m₀, s)
    have hMaxUtil : SpeakerStrategy.maxUtility G (ibrN G 0) s = (L0 G).respond m₀ s := by
      simp only [ibrN]; apply le_antisymm
      · rcases fold_max_attained (G.trueMessages s) (fun m => (L0 G).respond m s) 0
            with h0 | ⟨m', hm', hfm'⟩
        · simp only [SpeakerStrategy.maxUtility, h0]
          rw [L0_respond_true G m₀ s hm₀_in]
          exact div_nonneg zero_le_one (Nat.cast_nonneg _)
        · simp only [SpeakerStrategy.maxUtility, hfm']; exact hL0_le m' hm'
      · exact SpeakerStrategy.utility_le_maxUtility G (ibrN G 0) s m₀ hm₀_mem
    have hopt : SpeakerStrategy.optimalMessages G (ibrN G 0) s = {m₀} := by
      ext m'; simp only [Finset.mem_singleton]; constructor
      · intro hm'_opt; by_contra hne
        have hm'_mem := SpeakerStrategy.optimalMessages_subset_trueMessages G (ibrN G 0) s hm'_opt
        have hL0_eq : (ibrN G 0).respond m' s = (L0 G).respond m' s := rfl
        linarith [hL0_strict m' hm'_mem hne,
          SpeakerStrategy.optimalMessages_utility G (ibrN G 0) s m' hm'_opt]
      · intro heq; subst heq
        exact Finset.mem_filter.mpr ⟨hm₀_mem, hMaxUtil.symm⟩
    exact ⟨m₀, hopt, hm₀_in, hm₀_str⟩
  | succ n ih =>
    intro s hNE
    obtain ⟨m₀, hm₀_mem, hm₀_in, hm₀_str, hm₀_sstr⟩ := find_strongest s hNE
    -- By IH: at any state t, opt = {strongest at t}
    -- So bestResponse(t, m) = 1 if m strongest at t, 0 otherwise
    set S := SpeakerStrategy.bestResponse G (ibrN G n) with hS_def
    set p := G.prior s with hp_def
    have hbr_eq : ∀ (t : G.State) (m : G.Message),
        (G.trueMessages t).Nonempty →
        G.meaning m t = true →
        (∀ m', G.meaning m' t = true → G.trueStates m ⊆ G.trueStates m') →
        S.choose t m = 1 := by
      intro t m htNE hmt hmstr
      obtain ⟨m₁, hopt₁, _, hstr₁⟩ := ih t htNE
      have hm_eq : m = m₁ := hDistinct m m₁
        (Finset.Subset.antisymm (hmstr m₁ (SpeakerStrategy.optimalMessages_meaning G
          (ibrN G n) t m₁ (hopt₁ ▸ Finset.mem_singleton_self m₁))) (hstr₁ m hmt))
      subst hm_eq
      rw [hS_def, SpeakerStrategy.bestResponse_val, if_pos (hopt₁ ▸ Finset.mem_singleton_self m),
        hopt₁, Finset.card_singleton]; norm_num
    have hbr_zero : ∀ (t : G.State) (m : G.Message),
        (G.trueMessages t).Nonempty →
        G.meaning m t = true →
        (∃ m₁, G.meaning m₁ t = true ∧ G.trueStates m₁ ⊂ G.trueStates m) →
        S.choose t m = 0 := by
      intro t m htNE hmt ⟨m₁, hm₁t, hss⟩
      obtain ⟨m_s, hopt_s, _, hstr_s⟩ := ih t htNE
      have : m ≠ m_s := by
        intro heq; subst heq
        exact absurd (hstr_s m₁ hm₁t) hss.2
      rw [hS_def, SpeakerStrategy.bestResponse_val, if_neg]
      rw [hopt_s]; exact mt Finset.mem_singleton.mp this
    -- H(m', s) = 0 for non-strongest m' at s
    have hH_zero : ∀ m', G.meaning m' s = true → m' ≠ m₀ →
        (ibrN G (n + 1)).respond m' s = 0 := by
      intro m' hm's hne
      -- w(s, m') = 0 (m' not strongest at s)
      have hws : S.choose s m' * G.prior s = 0 := by
        rw [hbr_zero s m' hNE hm's ⟨m₀, hm₀_in, hm₀_sstr m' hm's hne⟩, zero_mul]
      -- level states for m' exist, giving maxW > 0
      obtain ⟨t₀, ht₀_in, ht₀_str⟩ := scalar_level_nonempty G hScalar hDistinct m'
        ⟨s, G.mem_trueStates.mpr hm's⟩
      simp only [InterpGame.mem_trueStates] at ht₀_in
      have ht₀_NE : (G.trueMessages t₀).Nonempty :=
        ⟨m', G.mem_trueMessages.mpr ht₀_in⟩
      have hwt₀ : S.choose t₀ m' * G.prior t₀ = p := by
        rw [hbr_eq t₀ m' ht₀_NE ht₀_in ht₀_str, one_mul, hFlatPrior t₀ s]
      -- Use FP equation: ibrN(n+1) = hearerBR(S)
      have hFPms := show (ibrN G (n + 1)).respond m' s =
          (hearerBR G S).respond m' s from rfl
      rw [hFPms]; simp only [hearerBR]
      -- maxW > 0
      have hmaxW_pos : Finset.univ.fold max 0 (fun t => S.choose t m' * G.prior t) > 0 := by
        calc 0 < p := hPriorPos s
          _ = S.choose t₀ m' * G.prior t₀ := hwt₀.symm
          _ ≤ Finset.univ.fold max 0 _ :=
            (Finset.le_fold_max _).mpr (Or.inr ⟨t₀, Finset.mem_univ _, le_refl _⟩)
      rw [if_neg (by linarith), if_neg (by rw [hws]; linarith)]
    -- H(m₀, s) > 0
    have hH_pos : (ibrN G (n + 1)).respond m₀ s > 0 := by
      -- w(s, m₀) = p (m₀ strongest at s)
      have hws : S.choose s m₀ * G.prior s = p := by
        rw [hbr_eq s m₀ hNE hm₀_in hm₀_str, one_mul]
      -- maxW = p
      have hmaxW_le : Finset.univ.fold max 0 (fun t => S.choose t m₀ * G.prior t) ≤ p := by
        rcases fold_max_attained Finset.univ (fun t => S.choose t m₀ * G.prior t) 0
            with h0 | ⟨t, _, hft⟩
        · linarith [hPriorPos s]
        · calc Finset.univ.fold max 0 _ = S.choose t m₀ * G.prior t := hft
            _ ≤ 1 * G.prior t := mul_le_mul_of_nonneg_right
                (SpeakerStrategy.bestResponse_le_one G _ t m₀) (le_of_lt (hPriorPos t))
            _ = G.prior t := one_mul _
            _ = p := hFlatPrior t s
      have hmaxW_ge : Finset.univ.fold max 0 (fun t => S.choose t m₀ * G.prior t) ≥ p := by
        calc p = S.choose s m₀ * G.prior s := hws.symm
          _ ≤ _ := (Finset.le_fold_max _).mpr (Or.inr ⟨s, Finset.mem_univ _, le_refl _⟩)
      have hmaxW_eq : Finset.univ.fold max 0 (fun t => S.choose t m₀ * G.prior t) = p :=
        le_antisymm hmaxW_le hmaxW_ge
      -- ibrN(n+1)(m₀, s) via hearerBR: maxW > 0, w(s) = maxW
      have hFPms := show (ibrN G (n + 1)).respond m₀ s =
          (hearerBR G S).respond m₀ s from rfl
      rw [hFPms]; simp only [hearerBR]
      rw [if_neg (by linarith [hPriorPos s]), if_pos (show S.choose s m₀ * G.prior s =
          Finset.univ.fold max 0 fun s_1 => S.choose s_1 m₀ * G.prior s_1 by linarith)]
      exact div_pos one_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr
        ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩⟩))
    -- maxUtility = H(m₀, s) > 0
    have hMaxUtil : SpeakerStrategy.maxUtility G (ibrN G (n + 1)) s =
        (ibrN G (n + 1)).respond m₀ s := by
      apply le_antisymm
      · rcases fold_max_attained (G.trueMessages s)
            (fun m => (ibrN G (n + 1)).respond m s) 0 with h0 | ⟨m', hm', hfm'⟩
        · simp only [SpeakerStrategy.maxUtility, h0]; exact le_of_lt hH_pos
        · simp only [SpeakerStrategy.maxUtility, hfm']
          have hm' := G.mem_trueMessages.mp hm'
          by_cases heq : m' = m₀
          · subst heq; exact le_refl _
          · rw [hH_zero m' hm' heq]; exact le_of_lt hH_pos
      · exact SpeakerStrategy.utility_le_maxUtility G (ibrN G (n + 1)) s m₀ hm₀_mem
    have hopt : SpeakerStrategy.optimalMessages G (ibrN G (n + 1)) s = {m₀} := by
      ext m'; simp only [Finset.mem_singleton]; constructor
      · intro hm'_opt; by_contra hne
        have hm'_true := SpeakerStrategy.optimalMessages_meaning G (ibrN G (n + 1)) s m' hm'_opt
        linarith [hH_zero m' hm'_true hne,
          SpeakerStrategy.optimalMessages_utility G (ibrN G (n + 1)) s m' hm'_opt]
      · intro heq; subst heq
        exact Finset.mem_filter.mpr ⟨hm₀_mem, hMaxUtil.symm⟩
    exact ⟨m₀, hopt, hm₀_in, hm₀_str⟩

/-- At `ibrN G (k+1)` for a scalar game with flat positive priors and distinct
    truth sets, `H(m, s) > 0` iff `m` is the strongest message at `s`
    (smallest truth set among messages true at `s`).

    This replaces five intermediate lemmas (`scalar_fp_weaker_zero`,
    `scalar_fp_opt_singleton`, `scalar_fp_argmax_iff_minimal`,
    `scalar_fp_minimal_weight`, `scalar_fp_nonminimal_zero`) with a single
    characterization, following the direct structure of @cite{franke-2011}'s
    Appendix B.2 proof more closely.

    **Proof**: By `ibrN_opt_singleton`, the speaker at IBR level `k` uses only
    the strongest message at each state. So `bestResponse(s, m) = 1{m strongest}`
    and `w(s, m) = p · 1{m strongest at s}`. Level states from
    `scalar_level_nonempty` ensure `maxW_m = p > 0` for every message, ruling
    out the L0 fallback. Then hearerBR gives `H > 0` exactly at the argmax
    states, i.e., where `m` is strongest. -/
private theorem ibrN_respond_pos_iff_strongest (G : InterpGame)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (k : ℕ) (m : G.Message) (s : G.State) (hs : G.meaning m s = true) :
    (ibrN G (k + 1)).respond m s > 0 ↔
      (∀ m', G.meaning m' s = true → G.trueStates m ⊆ G.trueStates m') := by
  set S := SpeakerStrategy.bestResponse G (ibrN G k)
  set p := G.prior s
  set w := fun t => S.choose t m * G.prior t
  have hNE : (G.trueMessages s).Nonempty :=
    ⟨m, G.mem_trueMessages.mpr hs⟩
  -- From ibrN_opt_singleton: opt(s) = {m₀} where m₀ is the strongest at s
  obtain ⟨m₀, hopt₀, hm₀_true, hm₀_str⟩ :=
    ibrN_opt_singleton G hPriorPos hFlatPrior hScalar hDistinct k s hNE
  -- bestResponse values at s
  have hbr_m₀ : S.choose s m₀ = 1 := by
    rw [SpeakerStrategy.bestResponse_val, if_pos (hopt₀ ▸ Finset.mem_singleton_self m₀),
      hopt₀, Finset.card_singleton]; norm_num
  have hbr_ne : ∀ m', m' ≠ m₀ → S.choose s m' = 0 := fun m' hne => by
    rw [SpeakerStrategy.bestResponse_val, if_neg (hopt₀ ▸ mt Finset.mem_singleton.mp hne)]
  -- Level state t₀ for m: m is strongest there, giving w(t₀) = p
  obtain ⟨t₀, ht₀_in, ht₀_str⟩ := scalar_level_nonempty G hScalar hDistinct m
    ⟨s, G.mem_trueStates.mpr hs⟩
  have ht₀_in := G.mem_trueStates.mp ht₀_in
  have ht₀_NE : (G.trueMessages t₀).Nonempty :=
    ⟨m, G.mem_trueMessages.mpr ht₀_in⟩
  obtain ⟨m_t₀, hopt_t₀, _, hstr_t₀⟩ :=
    ibrN_opt_singleton G hPriorPos hFlatPrior hScalar hDistinct k t₀ ht₀_NE
  -- m = strongest at t₀ (by distinctness of truth sets)
  have hm_eq_mt₀ : m = m_t₀ := hDistinct m m_t₀
    (Finset.Subset.antisymm (ht₀_str m_t₀ (SpeakerStrategy.optimalMessages_meaning G
      (ibrN G k) t₀ m_t₀ (hopt_t₀ ▸ Finset.mem_singleton_self m_t₀))) (hstr_t₀ m ht₀_in))
  subst hm_eq_mt₀
  have hbr_t₀ : S.choose t₀ m = 1 := by
    rw [SpeakerStrategy.bestResponse_val, if_pos (hopt_t₀ ▸ Finset.mem_singleton_self m),
      hopt_t₀, Finset.card_singleton]; norm_num
  have hwt₀ : w t₀ = p := by
    show S.choose t₀ m * G.prior t₀ = p
    rw [hbr_t₀, one_mul, hFlatPrior t₀ s]
  -- maxW = p: every w(t) ≤ p (flat prior, bestResponse ≤ 1) and w(t₀) = p
  have hmaxW : Finset.univ.fold max 0 w = p := le_antisymm
    (by rcases fold_max_attained Finset.univ w 0 with h0 | ⟨t, _, hft⟩
        · linarith [hPriorPos s]
        · calc _ = w t := hft
            _ ≤ 1 * G.prior t := mul_le_mul_of_nonneg_right
                (SpeakerStrategy.bestResponse_le_one G _ t m) (le_of_lt (hPriorPos t))
            _ = p := by rw [one_mul, hFlatPrior t s])
    (hwt₀ ▸ (Finset.le_fold_max _).mpr (Or.inr ⟨t₀, Finset.mem_univ _, le_refl _⟩))
  -- Unfold ibrN(k+1) = hearerBR(S). Since maxW = p > 0, L0 fallback is ruled out.
  show (hearerBR G S).respond m s > 0 ↔ _
  simp only [hearerBR]
  rw [if_neg (by linarith [hPriorPos s] : Finset.univ.fold max 0
      (fun s_1 => S.choose s_1 m * G.prior s_1) ≠ 0)]
  -- Goal: (if w(s) = maxW then 1/|argmax| else 0) > 0 ↔ strongest
  constructor
  · -- Forward: H > 0 → m strongest at s
    intro hPos
    -- w(s) must equal maxW (otherwise H = 0)
    split_ifs at hPos with hwm
    · -- w(s) = maxW, so bestResponse(s,m) > 0, so m ∈ opt(s) = {m₀}, so m = m₀
      have hbr_pos : S.choose s m > 0 := by
        by_contra h; push_neg at h
        have := le_antisymm h (SpeakerStrategy.bestResponse_nonneg G (ibrN G k) s m)
        rw [this, zero_mul] at hwm; linarith [hPriorPos s]
      have hm_opt := ((SpeakerStrategy.bestResponse_pos_iff G (ibrN G k) s m).mp hbr_pos).1
      exact (Finset.mem_singleton.mp (hopt₀ ▸ hm_opt)) ▸ hm₀_str
    · exact absurd hPos (lt_irrefl 0)
  · -- Backward: m strongest → H > 0
    intro hStr
    -- m = m₀ (both strongest at s, distinct truth sets)
    have hm_eq : m = m₀ := hDistinct m m₀
      (Finset.Subset.antisymm (hStr m₀ hm₀_true) (hm₀_str m hs))
    subst hm_eq
    have hws : S.choose s m * G.prior s = Finset.univ.fold max 0 w := by
      rw [hbr_m₀, one_mul, hmaxW]
    rw [if_pos hws]
    exact div_pos one_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr
      ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hws⟩⟩))
/-- IBR fixed point equals exhMW (Main theorem — @cite{franke-2011}, Section 9.3)

This is the central result connecting game theory to exhaustification.
At the fixed point of a **scalar** interpretation game, the IBR listener's
interpretation of message m is exactly the exhaustive interpretation exhMW(ALT, m).

**Restriction**: Requires `hIBR : ∃ k, H = ibrN G (k + 1)`, i.e., H is from
the IBR iteration sequence. The claim is false for arbitrary FPs of scalar
games. This matches @cite{franke-2011}'s proof (Appendix B.2), which works
by induction on the IBR iteration, not FP alone.

Two structural hypotheses are required:

- `isScalarGame`: truth sets are totally ordered by inclusion (nested). Without
  this, "dominated" messages fall back to L0, assigning positive probability
  to non-minimal states.

- `hDistinct`: no two messages have identical truth sets. Without this,
  asymmetric FPs exist that break the biconditional.

**Proof**: By `ibrN_respond_pos_iff_strongest`, `H(m, s) > 0` iff `m` is the
strongest message at `s`. The bridge to exhMW uses `altMin_to_cardMin` and
`scalar_minimal_messages_weaker`: exhMW-minimality ↔ card-minimality ↔
`m` strongest at `s`. -/
theorem ibr_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (_hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (_hScalar : isScalarGame G)
    (_hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (_hIBR : ∃ k, H = ibrN G (k + 1))
    (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) := by
  obtain ⟨k, hH⟩ := _hIBR; subst hH
  intro s; constructor
  · -- Forward: H(m,s) > 0 → exhMW(m, s)
    intro hPos
    -- Step 1: m must be true at s (false messages always get H = 0)
    have hTrue : G.meaning m s = true := by
      by_contra hf
      have hFalse : G.meaning m s = false := Bool.eq_false_iff.mpr hf
      simp only [ibrN, ibrStep, speakerUpdate, hearerBR] at hPos
      have hSz := SpeakerStrategy.bestResponse_false_zero G (ibrN G k) s m hFalse
      simp only [hSz, zero_mul] at hPos
      split_ifs at hPos with hmW hwm
      · simp only [L0, HearerStrategy.literal, hFalse] at hPos; simp at hPos
      · exact hmW hwm.symm
      · simp at hPos
    -- Step 2: m is the strongest message at s (from ibrN_respond_pos_iff_strongest)
    have hStr := (ibrN_respond_pos_iff_strongest G hPriorPos hFlatPrior _hScalar _hDistinct
      k m s hTrue).mp hPos
    constructor
    · exact hTrue  -- prejacent
    · -- ¬∃ s' <_ALT s: if s' <_ALT s then trueMessages(s') ⊊ trueMessages(s),
      -- but m strongest at s means trueMessages(s) ⊆ trueMessages(s'), contradiction
      intro ⟨s', hs'_true, hs'_lt⟩
      have hss := ltALT_implies_trueMessages_ssubset G s' s hs'_lt
      apply hss.2
      intro m' hm'
      simp only [InterpGame.mem_trueMessages] at hm' ⊢
      -- m' true at s → trueStates(m) ⊆ trueStates(m') → s' ∈ trueStates(m) → m' true at s'
      exact G.mem_trueStates.mp (hStr m' hm' (G.mem_trueStates.mpr hs'_true))
  · -- Backward: exhMW(m, s) → H(m,s) > 0
    intro ⟨hTrue, hMin⟩
    -- exhMW-minimal → card-minimal → m strongest at s → H > 0
    have hCardMin := altMin_to_cardMin G _hScalar m s hTrue hMin
    have hStr : ∀ m', G.meaning m' s = true → G.trueStates m ⊆ G.trueStates m' :=
      fun m' hm' => scalar_minimal_messages_weaker G _hScalar m s hTrue hCardMin m' hm'
    exact (ibrN_respond_pos_iff_strongest G hPriorPos hFlatPrior _hScalar _hDistinct
      k m s hTrue).mpr hStr

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

-- L0: ◇(A∨B) true everywhere → uniform over all 4 states
#guard (L0 freeChoiceGame).respond .mayAorB .either == 1/4
-- L2: ◇(A∨B) → "either" (free choice inference emerges from IBR)
#guard (ibrN freeChoiceGame 2).respond .mayAorB .either > 0
#guard (ibrN freeChoiceGame 2).respond .mayAorB .onlyA == 0

end RSA.IBR
