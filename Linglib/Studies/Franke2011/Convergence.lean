import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Linglib.Studies.Franke2011.IBR

/-!
# IBR Convergence

General convergence proof for Iterated Best Response ([franke-2011] Appendix B.4).

Expected gain (EG) is monotone non-decreasing along the IBR sequence (Lemma 3),
and the strategy space is finite (pigeonhole), so IBR must reach a fixed point
(Theorem 3).

This machinery is **not needed** for scalar games, where `ibr_converges_to_exhMW`
(in `ScalarGames.lean`) shows IBR stabilizes at level 1. It is needed for
general (non-scalar) interpretation games.
-/

namespace Franke2011

variable {T M : Type*} [Fintype T] [Fintype M] [DecidableEq T] [DecidableEq M]
  (G : InterpGame T M)

/-- If no element attains the fold max, then fold max = init. -/
private theorem fold_max_eq_init_of_no_attainer {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) (b : ℚ)
    (h : ∀ x ∈ s, f x ≠ s.fold max b f) :
    s.fold max b f = b := by
  cases Finset.fold_max_attained s f b with
  | inl hb => exact hb
  | inr hex =>
    obtain ⟨x, hx, hfx⟩ := hex
    exact absurd hfx.symm (h x hx)

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
/-- Any valid speaker's inner product ≤ maxU at each state. -/
private theorem speaker_inner_le_maxU
    (S : T → M → ℚ) (H : M → T → ℚ) (t : T)
    (hSNonneg : ∀ m, S t m ≥ 0)
    (hSSum : Finset.univ.sum (λ m => S t m) ≤ 1)
    (hSTruth : ∀ m, ¬ G.meaning m t → S t m = 0) :
    Finset.univ.sum (λ m => S t m * H m t) ≤
    maxUtility G H t := by
  set maxU := maxUtility G H t
  calc Finset.univ.sum (λ m => S t m * H m t)
      ≤ Finset.univ.sum (λ m => S t m * maxU) := by
        apply Finset.sum_le_sum; intro m _
        by_cases hm : G.meaning m t
        · exact mul_le_mul_of_nonneg_left
            (utility_le_maxUtility G H t m (G.mem_trueMessages.mpr hm))
            (hSNonneg m)
        · simp [hSTruth m hm]
    _ = Finset.univ.sum (λ m => S t m) * maxU := by rw [Finset.sum_mul]
    _ ≤ 1 * maxU := mul_le_mul_of_nonneg_right hSSum (maxUtility_nonneg G H t)
    _ = maxU := one_mul maxU

omit [Fintype T] [DecidableEq T] in
/-- bestResponse inner product ≥ maxU: the best-response speaker achieves the maximum
    utility at each state. -/
private theorem bestResponse_inner_ge_maxU (H : M → T → ℚ)
    (s : T) :
    maxUtility G H s ≤ Finset.univ.sum (λ m =>
      (bestResponse G H) s m * H m s) := by
  set opt := optimalMessages G H s
  set k := opt.card
  set maxU := maxUtility G H s
  have hval : ∀ m, (bestResponse G H) s m * H m s =
      if m ∈ opt then (if k = 0 then 0 else 1 / (k : ℚ)) * H m s else 0 := by
    intro m; rw [bestResponse_val]; split_ifs with hmem <;> ring
  simp_rw [hval]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hk0 : k = 0
  · have : maxU = 0 := by
      have hge : maxU ≥ 0 := maxUtility_nonneg G H s
      by_contra hne; push Not at hne
      have hpos : maxU > 0 := lt_of_le_of_ne hge (Ne.symm hne)
      cases Finset.fold_max_attained (G.trueMessages s) (fun m' => H m' s) 0 with
      | inl h0 =>
        have : maxU = 0 := h0; linarith
      | inr hex =>
        obtain ⟨m₀, hm₀, heq⟩ := hex
        have : m₀ ∈ opt := by
          simp only [opt, optimalMessages, Finset.mem_filter]
          exact ⟨hm₀, by simp only [maxUtility]; exact heq.symm⟩
        exact absurd (Finset.card_pos.mpr ⟨m₀, this⟩) (by omega)
    simp [hk0, this]
  · have hopt_eq : ∀ m ∈ opt, H m s = maxU :=
      fun m hm => optimalMessages_utility G H s m hm
    rw [if_neg hk0]
    have : opt.sum (fun m => (1 : ℚ) / (k : ℚ) * H m s) =
        opt.sum (fun _ => (1 : ℚ) / (k : ℚ) * maxU) := by
      apply Finset.sum_congr rfl; intro m hm; rw [hopt_eq m hm]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    rw [show (k : ℚ) * (1 / (k : ℚ) * maxU) = maxU * ((k : ℚ) * (1 / (k : ℚ))) from by ring,
        mul_one_div_cancel (Nat.cast_ne_zero.mpr hk0), mul_one]

omit [DecidableEq T] in
/-- Lemma 3a: best-response speaker improves EG.

    At each state t, bestResponse maximizes ∑_m S(t,m) * H(m,t) by concentrating
    all probability on messages that maximize H(m,t). Any valid S_old achieves
    at most maxU(t), which is exactly what S_new achieves. -/
theorem eg_speaker_improvement
    (S_old S_new : T → M → ℚ) (H : M → T → ℚ)
    (hBR : S_new = bestResponse G H)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S_old s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S_old s m) ≤ 1)
    (hSTruth : ∀ s m, ¬ G.meaning m s → S_old s m = 0)
    (_hHNonneg : ∀ m s, H m s ≥ 0) :
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

omit [Fintype M] [DecidableEq M] in
/-- The literal listener sums to at most 1 for each message. -/
private theorem literal_sum_le_one (m : M) :
    Finset.univ.sum (λ s => G.literal m s) ≤ 1 := by
  have hval : ∀ s, G.literal m s =
      if s ∈ G.trueStates m then ((G.trueStates m).card : ℚ)⁻¹ else 0 := by
    intro s
    simp only [InterpGame.literal, InterpGame.mem_trueStates]
  simp_rw [hval]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  by_cases hn : (G.trueStates m).card = 0
  · simp [hn]
  · exact le_of_eq (mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn))

omit [Fintype M] [DecidableEq M] in
/-- hearerBR response sums to at most 1 for each message. -/
private theorem hearerBR_sum_le_one (S : T → M → ℚ) (m : M) :
    Finset.univ.sum (λ s => (hearerBR G S) m s) ≤ 1 := by
  set w : T → ℚ := fun s => S s m * G.prior s
  set maxW := Finset.univ.fold max 0 w
  by_cases hmaxW : maxW = 0
  · have hL0 : ∀ s, (hearerBR G S) m s = G.literal m s :=
      fun s => show (hearerBR G S) m s = _ by simp only [hearerBR]; rw [if_pos hmaxW]
    simp_rw [hL0]; exact literal_sum_le_one G m
  · set argmax := Finset.univ.filter (fun s => w s = maxW)
    set k := argmax.card
    have hval : ∀ s, (hearerBR G S) m s =
        if s ∈ argmax then 1 / (↑k : ℚ) else 0 := by
      intro s
      show (hearerBR G S) m s = _
      simp only [hearerBR]; rw [if_neg hmaxW]
      change (if w s = maxW then 1 / (↑k : ℚ) else 0) = _
      simp only [argmax, Finset.mem_filter, Finset.mem_univ, true_and]
    simp_rw [hval]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
    by_cases hk : k = 0
    · simp [hk]
    · exact le_of_eq (mul_one_div_cancel (Nat.cast_ne_zero.mpr hk))

omit [DecidableEq T] in
/-- ibrN response is non-negative for all n. -/
private theorem ibrN_respond_nonneg (n : ℕ) (m : M) (s : T) :
    (ibrN G n) m s ≥ 0 := by
  induction n with
  | zero =>
    simp only [ibrN, InterpGame.literal]
    split_ifs <;> first | exact le_refl 0 | exact inv_nonneg.mpr (Nat.cast_nonneg _)
  | succ n _ =>
    simp only [ibrN, ibrStep]
    exact hearerBR_respond_nonneg G _ m s

/-- ibrN response sums to at most 1 for all n. -/
private theorem ibrN_sum_le_one (n : ℕ) (m : M) :
    Finset.univ.sum (λ s => (ibrN G n) m s) ≤ 1 := by
  induction n with
  | zero => simp only [ibrN]; exact literal_sum_le_one G m
  | succ n _ => simp only [ibrN, ibrStep]; exact hearerBR_sum_le_one G _ m

omit [Fintype M] [DecidableEq T] [DecidableEq M] in
/-- Per-message: hearerBR inner product ≥ maxW. The hearer argmax best response
    achieves at least maxW expected payoff per message. -/
private theorem hearerBR_inner_ge_max (S : T → M → ℚ) (m : M)
    (hw_nonneg : ∀ t, S t m * G.prior t ≥ 0) :
    let w := fun s => S s m * G.prior s
    let maxW := Finset.univ.fold max 0 w
    Finset.univ.sum (fun t => w t * (hearerBR G S) m t) ≥ maxW := by
  intro w maxW
  have hmaxW_nonneg : maxW ≥ 0 := (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))
  by_cases hmaxW0 : maxW ≤ 0
  · -- maxW = 0: sum ≥ 0 = maxW
    have : maxW = 0 := le_antisymm hmaxW0 hmaxW_nonneg
    linarith [Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) =>
      mul_nonneg (hw_nonneg t) (hearerBR_respond_nonneg G S m t))]
  · -- maxW > 0
    push Not at hmaxW0
    -- fold_max_attained: maxW = 0 or maxW = w(t₀) for some t₀
    have h_attained := Finset.fold_max_attained Finset.univ w 0
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
    have hBR_argmax : ∀ t ∈ argmax, (hearerBR G S) m t =
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
    calc Finset.univ.sum (fun t => w t * (hearerBR G S) m t)
        ≥ argmax.sum (fun t => w t * (hearerBR G S) m t) :=
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

omit [DecidableEq M] in
/-- Hearer step: hearerBR improves expected gain. For any S with S ≥ 0 and H with H ≥ 0
    and Σ H ≤ 1, we have EG(S, H) ≤ EG(S, hearerBR(S)). -/
private theorem eg_hearerBR_improvement
    (S : T → M → ℚ) (H : M → T → ℚ)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S s m ≥ 0)
    (hHNonneg : ∀ m s, H m s ≥ 0)
    (hHSum : ∀ m, Finset.univ.sum (λ s => H m s) ≤ 1) :
    expectedGain G S H ≤ expectedGain G S (hearerBR G S) := by
  -- Rewrite EG as Σ_m Σ_t (sum swap)
  unfold expectedGain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun t m => G.prior t * (S t m * H m t))]
  rw [Finset.sum_comm (f := fun t m => G.prior t * (S t m * (hearerBR G S) m t))]
  -- Per-message inequality
  apply Finset.sum_le_sum; intro m _
  -- Rewrite P(t) * (S(t,m) * H(m,t)) as w(t) * H(m,t) where w = S * P
  set w := fun t => S t m * G.prior t
  have hw_nonneg : ∀ t, w t ≥ 0 := fun t => mul_nonneg (hSNonneg t m) (hPriorNonneg t)
  set maxW := Finset.univ.fold max 0 w
  have hmaxW_nonneg : maxW ≥ 0 := (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))
  have hw_le : ∀ t, w t ≤ maxW :=
    fun t => (Finset.le_fold_max _).mpr (Or.inr ⟨t, Finset.mem_univ t, le_refl _⟩)
  -- Commute P * (S * H) to (S * P) * H = w * H
  have hcomm_old : ∀ t, G.prior t * (S t m * H m t) =
      w t * H m t := by
    intro t; simp only [w]; ring
  have hcomm_new : ∀ t, G.prior t * (S t m * (hearerBR G S) m t) =
      w t * (hearerBR G S) m t := by
    intro t; simp only [w]; ring
  simp_rw [hcomm_old, hcomm_new]
  -- old ≤ maxW ≤ new
  calc Finset.univ.sum (fun t => w t * H m t)
      ≤ maxW := per_message_bound w (H m) (fun t => hHNonneg m t) (hHSum m)
          maxW hmaxW_nonneg hw_le
    _ ≤ Finset.univ.sum (fun t => w t * (hearerBR G S) m t) :=
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
theorem eg_ibr_monotone
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (n : ℕ) :
    expectedGain G (bestResponse G (ibrN G n)) (ibrN G n) ≤
    expectedGain G (bestResponse G (ibrN G (n + 1))) (ibrN G (n + 1)) := by
  -- Decompose: f(n) ≤ EG(S_{n+1}, L_{n+1}) ≤ f(n+1)
  calc expectedGain G (bestResponse G (ibrN G n)) (ibrN G n)
      ≤ expectedGain G (bestResponse G (ibrN G n)) (ibrN G (n + 1)) := by
        -- Hearer step: EG(S_{n+1}, L_n) ≤ EG(S_{n+1}, L_{n+1})
        -- L_{n+1} = hearerBR(S_{n+1}) = hearerBR(bestResponse(L_n))
        simp only [ibrN, ibrStep]
        apply eg_hearerBR_improvement G (bestResponse G (ibrN G n)) (ibrN G n) hPriorNonneg
        · exact bestResponse_nonneg G (ibrN G n)
        · exact ibrN_respond_nonneg G n
        · exact ibrN_sum_le_one G n
    _ ≤ expectedGain G (bestResponse G (ibrN G (n + 1))) (ibrN G (n + 1)) := by
        -- Speaker step: S_{n+2} = bestResponse(L_{n+1}) beats S_{n+1} against L_{n+1}
        apply eg_speaker_improvement G
          (bestResponse G (ibrN G n))
          (bestResponse G (ibrN G (n + 1)))
          (ibrN G (n + 1))
        · rfl
        · exact hPriorNonneg
        · exact bestResponse_nonneg G (ibrN G n)
        · exact bestResponse_sum_le_one G (ibrN G n)
        · exact bestResponse_false_zero G (ibrN G n)
        · intro m s
          exact hearerBR_respond_nonneg G (bestResponse G (ibrN G n)) m s

omit [DecidableEq T] [DecidableEq M] in
/-- Expected gain is bounded above by 1 (probability of perfect communication). -/
theorem eg_bounded (S : T → M → ℚ) (H : M → T → ℚ)
    (hPriorSum : Finset.univ.sum G.prior = 1)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S s m) ≤ 1)
    (hHBound : ∀ m s, H m s ≤ 1)
    (_hHNonneg : ∀ m s, H m s ≥ 0) :
    expectedGain G S H ≤ 1 := by
  unfold expectedGain
  calc Finset.univ.sum (λ t => G.prior t * Finset.univ.sum (λ m => S t m * H m t))
      ≤ Finset.univ.sum (λ t => G.prior t * 1) := by
        apply Finset.sum_le_sum; intro t _
        apply mul_le_mul_of_nonneg_left _ (hPriorNonneg t)
        calc Finset.univ.sum (λ m => S t m * H m t)
            ≤ Finset.univ.sum (λ m => S t m * 1) := by
              apply Finset.sum_le_sum; intro m _
              exact mul_le_mul_of_nonneg_left (hHBound m t) (hSNonneg t m)
          _ = Finset.univ.sum (λ m => S t m) := by simp only [mul_one]
          _ ≤ 1 := hSSum t
    _ = 1 := by simp [hPriorSum]

omit [DecidableEq T] in
/-- EG equality → per-state inner product equality. If S_old achieves the same EG as
    bestResponse against H, then at each positive-prior state, S_old's inner product
    equals maxUtility. -/
private theorem eg_eq_inner_eq'
    (S_old : T → M → ℚ) (H : M → T → ℚ)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S_old s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S_old s m) ≤ 1)
    (hSTruth : ∀ s m, ¬ G.meaning m s → S_old s m = 0)
    (hEG : expectedGain G S_old H = expectedGain G (bestResponse G H) H)
    (t : T) (hPt : G.prior t > 0) :
    Finset.univ.sum (λ m => S_old t m * H m t) =
    maxUtility G H t := by
  have h_best_eq : ∀ s, Finset.univ.sum (λ m =>
      (bestResponse G H) s m * H m s) =
      maxUtility G H s := by
    intro s
    linarith [speaker_inner_le_maxU G (bestResponse G H) H s
      (fun m => bestResponse_nonneg G H s m)
      (bestResponse_sum_le_one G H s)
      (fun m hm => bestResponse_false_zero G H s m hm),
      bestResponse_inner_ge_maxU G H s]
  have h_old_le : ∀ s, Finset.univ.sum (λ m => S_old s m * H m s) ≤
      maxUtility G H s :=
    fun s => speaker_inner_le_maxU G S_old H s (hSNonneg s) (hSSum s) (hSTruth s)
  -- Σ P(s) * (maxU(s) - inner_old(s)) = 0 with all terms ≥ 0
  have hdiff : Finset.univ.sum (fun s => G.prior s *
      (maxUtility G H s -
       Finset.univ.sum (λ m => S_old s m * H m s))) = 0 := by
    have hEGnew : expectedGain G (bestResponse G H) H =
        Finset.univ.sum (fun s => G.prior s * maxUtility G H s) := by
      unfold expectedGain; congr 1; ext s; rw [h_best_eq s]
    have hEGold : expectedGain G S_old H =
        Finset.univ.sum (fun s => G.prior s *
          Finset.univ.sum (λ m => S_old s m * H m s)) := rfl
    rw [show (fun s => G.prior s * (maxUtility G H s -
        Finset.univ.sum (fun m => S_old s m * H m s))) =
        (fun s => G.prior s * maxUtility G H s -
          G.prior s * Finset.univ.sum (fun m => S_old s m * H m s))
      from by ext; ring]
    rw [Finset.sum_sub_distrib]; linarith [hEGnew, hEGold, hEG]
  have hnonneg : ∀ s, 0 ≤ G.prior s *
      (maxUtility G H s -
       Finset.univ.sum (λ m => S_old s m * H m s)) :=
    fun s => mul_nonneg (hPriorNonneg s) (sub_nonneg.mpr (h_old_le s))
  -- sum of nonneg = 0 → each = 0
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hdiff t
    (Finset.mem_univ t)
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · linarith

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
/-- If inner product = maxU and S(t,m) > 0, then H(m,t) = maxU. -/
private theorem inner_eq_maxU_respond_eq'
    (S : T → M → ℚ) (H : M → T → ℚ) (t : T) (m : M)
    (hSNonneg : ∀ m', S t m' ≥ 0)
    (hSSum : Finset.univ.sum (λ m' => S t m') ≤ 1)
    (hSTruth : ∀ m', ¬ G.meaning m' t → S t m' = 0)
    (hInner : Finset.univ.sum (λ m' => S t m' * H m' t) =
              maxUtility G H t)
    (hSm : S t m > 0) :
    H m t = maxUtility G H t := by
  set maxU := maxUtility G H t
  have hTrue : G.meaning m t := by
    by_contra hFalse
    linarith [hSTruth m hFalse]
  have hle : H m t ≤ maxU :=
    utility_le_maxUtility G H t m (G.mem_trueMessages.mpr hTrue)
  by_contra hne; push Not at hne
  have hlt : H m t < maxU := lt_of_le_of_ne hle hne
  linarith [show Finset.univ.sum (λ m' => S t m' * H m' t) < maxU from
    calc Finset.univ.sum (λ m' => S t m' * H m' t)
        < Finset.univ.sum (λ m' => S t m' * maxU) := by
          apply Finset.sum_lt_sum
          · intro m' _
            by_cases hm' : G.meaning m' t
            · exact mul_le_mul_of_nonneg_left
                (utility_le_maxUtility G H t m' (G.mem_trueMessages.mpr hm'))
                (hSNonneg m')
            · simp [hSTruth m' hm']
          · exact ⟨m, Finset.mem_univ m, mul_lt_mul_of_pos_left hlt hSm⟩
      _ = Finset.univ.sum (λ m' => S t m') * maxU := by rw [Finset.sum_mul]
      _ ≤ 1 * maxU := mul_le_mul_of_nonneg_right hSSum (maxUtility_nonneg G H t)
      _ = maxU := one_mul maxU]

omit [DecidableEq T] in
/-- EG equality → support contained in optimalMessages. -/
private theorem eg_eq_opt_containment'
    (S_old : T → M → ℚ) (H : M → T → ℚ)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hSNonneg : ∀ s m, S_old s m ≥ 0)
    (hSSum : ∀ s, Finset.univ.sum (λ m => S_old s m) ≤ 1)
    (hSTruth : ∀ s m, ¬ G.meaning m s → S_old s m = 0)
    (hEG : expectedGain G S_old H = expectedGain G (bestResponse G H) H)
    (t : T) (hPt : G.prior t > 0)
    (m : M) (hSm : S_old t m > 0) :
    m ∈ optimalMessages G H t := by
  have hInner := eg_eq_inner_eq' G S_old H hPriorNonneg hSNonneg hSSum hSTruth hEG t hPt
  have hResp := inner_eq_maxU_respond_eq' G S_old H t m (hSNonneg t) (hSSum t) (hSTruth t)
    hInner hSm
  simp only [optimalMessages, Finset.mem_filter, InterpGame.trueMessages,
    Finset.mem_univ, true_and]
  exact ⟨by by_contra hF; linarith [hSTruth t m hF], hResp⟩

omit [DecidableEq T] in
/-- EG equality → optimalMessages containment between hearer strategies.
    If S_old = bestResponse(H_old) achieves the same EG as bestResponse(H) against H,
    then optimalMessages(H_old, t) ⊆ optimalMessages(H, t) for all t with P(t) > 0. -/
private theorem eg_eq_opt_subset (H_old H : M → T → ℚ)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hPriorPos : ∀ s, G.prior s > 0)
    (hEG : expectedGain G (bestResponse G H_old) H =
           expectedGain G (bestResponse G H) H) :
    ∀ t, optimalMessages G H_old t ⊆
         optimalMessages G H t := by
  intro t m hm
  have hSm : (bestResponse G H_old) t m > 0 :=
    (bestResponse_pos_iff G H_old t m).mpr
      ⟨hm, Finset.card_pos.mpr ⟨m, hm⟩⟩
  exact eg_eq_opt_containment' G (bestResponse G H_old) H hPriorNonneg
    (fun s m' => bestResponse_nonneg G H_old s m')
    (fun s => bestResponse_sum_le_one G H_old s)
    (fun s m' hm' => bestResponse_false_zero G H_old s m' hm')
    hEG t (hPriorPos t) m hSm

omit [DecidableEq T] in
/-- Determinism: equal hearer strategies produce equal shifted sequences. -/
private lemma ibrN_shift_congr {n m : ℕ}
    (h : ibrN G n = ibrN G m) (k : ℕ) :
    ibrN G (n + k) = ibrN G (m + k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    show ibrN G (n + k + 1) = _
    simp only [ibrN]; exact congrArg (ibrStep G) ih

omit [DecidableEq T] in
/-- Consecutive repeat → fixed point. -/
private lemma ibrN_consecutive_fp (n : ℕ)
    (h : ibrN G n = ibrN G (n + 1)) :
    isIBRFixedPoint G (ibrN G n) := by
  intro m s
  have : ibrN G n m s = ibrN G (n + 1) m s :=
    congrFun (congrFun h m) s
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

omit [Fintype T] [DecidableEq T] in
/-- Equal optimalMessages at all states → equal bestResponse speakers. -/
private theorem opt_eq_bestResponse_eq (H₁ H₂ : M → T → ℚ)
    (hOpt : ∀ t, optimalMessages G H₁ t =
                  optimalMessages G H₂ t) :
    bestResponse G H₁ = bestResponse G H₂ := by
  funext t m
  rw [bestResponse_val, bestResponse_val, hOpt t]

/-- The set of possible values for any IBR hearer strategy:
    {0} ∪ {1/k : 1 ≤ k ≤ |State|}. -/
private def ibrValueSet (T : Type*) [Fintype T] : Finset ℚ :=
  insert 0 ((Finset.range (Fintype.card T)).image (fun k : ℕ => 1 / ((k : ℚ) + 1)))

omit [DecidableEq T] in
private lemma one_div_mem_ibrValueSet (n : ℕ)
    (hn1 : 1 ≤ n) (hn2 : n ≤ Fintype.card T) :
    (1 : ℚ) / (n : ℚ) ∈ ibrValueSet T := by
  simp only [ibrValueSet, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  right; exact ⟨n - 1, by omega, by congr 1; rw [Nat.cast_sub hn1]; ring⟩

omit [Fintype M] [DecidableEq M] [DecidableEq T] in
private theorem L0_respond_mem_values (m : M) (s : T) :
    G.literal m s ∈ ibrValueSet T := by
  simp only [InterpGame.literal]
  split_ifs with hm
  · rw [← one_div]
    exact one_div_mem_ibrValueSet _
      (Finset.card_pos.mpr ⟨s, G.mem_trueStates.mpr hm⟩)
      (Finset.card_le_card (Finset.filter_subset _ _))
  · exact Finset.mem_insert_self 0 _

omit [Fintype M] [DecidableEq M] [DecidableEq T] in
private theorem hearerBR_respond_mem_values (S : T → M → ℚ)
    (m : M) (s : T) :
    (hearerBR G S) m s ∈ ibrValueSet T := by
  simp only [hearerBR]
  split_ifs with hmaxW hwm
  · exact L0_respond_mem_values G m s
  · exact one_div_mem_ibrValueSet _
      (Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hwm⟩⟩)
      (Finset.card_le_card (Finset.filter_subset _ _))
  · exact Finset.mem_insert_self 0 _

omit [DecidableEq T] in
private theorem ibrN_respond_mem_values (n : ℕ) (m : M) (s : T) :
    (ibrN G n) m s ∈ ibrValueSet T := by
  induction n with
  | zero => exact L0_respond_mem_values G m s
  | succ n _ => simp only [ibrN, ibrStep]; exact hearerBR_respond_mem_values G _ m s

private noncomputable def encodeIBR (n : ℕ) :
    M → T → ↥(ibrValueSet T) :=
  fun m s => ⟨(ibrN G n) m s, ibrN_respond_mem_values G n m s⟩

omit [DecidableEq T] in
private theorem encodeIBR_faithful {n₁ n₂ : ℕ}
    (h : encodeIBR G n₁ = encodeIBR G n₂) :
    ibrN G n₁ = ibrN G n₂ := by
  funext m s
  exact Subtype.mk.inj (congr_fun (congr_fun h m) s)

omit [DecidableEq T] in
/-- Strategy space is finite → IBR sequence eventually repeats.
    Proof: IBR hearer strategies have values in {0, 1/1, 1/2, ..., 1/|State|},
    giving at most (|State|+1)^(|Message|×|State|) distinct strategies.
    By pigeonhole (Finite.exists_ne_map_eq_of_infinite), two agree. -/
private theorem ibr_sequence_repeats :
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
theorem ibr_reaches_fixed_point
    (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (hPriorPos : ∀ s, G.prior s > 0) :
    ∃ n : ℕ, isIBRFixedPoint G (ibrN G n) := by
  obtain ⟨n₁, n₂, hlt, heq⟩ := ibr_sequence_repeats G
  set p := n₂ - n₁
  have hp : 0 < p := by omega
  have hperiod : ibrN G n₁ = ibrN G (n₁ + p) := by
    rwa [Nat.add_sub_cancel' (le_of_lt hlt)]
  -- EG is monotone along the IBR sequence
  set eg := fun n => expectedGain G (bestResponse G (ibrN G n)) (ibrN G n)
  have hEGmono : ∀ k, eg k ≤ eg (k + 1) := eg_ibr_monotone G hPriorNonneg
  have hEGcycle : eg n₁ = eg (n₁ + p) := by
    simp only [eg]; rw [hperiod]
  -- optimalMessages containment at each step of the cycle
  have hOptSubAll : ∀ k, k < p →
      ∀ t, optimalMessages G (ibrN G (n₁ + k)) t ⊆
           optimalMessages G (ibrN G (n₁ + k + 1)) t := by
    intro k hk
    -- EG is constant on the entire cycle (monotone + cycle → all steps equal)
    have hEGk : eg (n₁ + k) = eg (n₁ + k + 1) :=
      monotone_cycle_all_eq hEGmono hEGcycle k hk
    -- Decompose EG step: eg(n₁+k) ≤ mid ≤ eg(n₁+k+1), both equalities
    have hSpeakerEqK : expectedGain G (bestResponse G (ibrN G (n₁ + k)))
        (ibrN G (n₁ + k + 1)) =
        expectedGain G (bestResponse G (ibrN G (n₁ + k + 1)))
        (ibrN G (n₁ + k + 1)) := by
      have hH' : eg (n₁ + k) ≤ expectedGain G (bestResponse G (ibrN G (n₁ + k)))
          (ibrN G (n₁ + k + 1)) := by
        simp only [eg, ibrN, ibrStep]
        exact eg_hearerBR_improvement G (bestResponse G (ibrN G (n₁ + k)))
          (ibrN G (n₁ + k)) hPriorNonneg
          (fun s m => bestResponse_nonneg G (ibrN G (n₁ + k)) s m)
          (ibrN_respond_nonneg G (n₁ + k))
          (ibrN_sum_le_one G (n₁ + k))
      have hS' : expectedGain G (bestResponse G (ibrN G (n₁ + k)))
          (ibrN G (n₁ + k + 1)) ≤ eg (n₁ + k + 1) := by
        simp only [eg]
        exact eg_speaker_improvement G
          (bestResponse G (ibrN G (n₁ + k)))
          (bestResponse G (ibrN G (n₁ + k + 1)))
          (ibrN G (n₁ + k + 1)) rfl hPriorNonneg
          (fun s m => bestResponse_nonneg G (ibrN G (n₁ + k)) s m)
          (fun s => bestResponse_sum_le_one G (ibrN G (n₁ + k)) s)
          (fun s m hm => bestResponse_false_zero G (ibrN G (n₁ + k)) s m hm)
          (fun m s => hearerBR_respond_nonneg G (bestResponse G (ibrN G (n₁ + k))) m s)
      linarith
    exact eg_eq_opt_subset G (ibrN G (n₁ + k)) (ibrN G (n₁ + k + 1))
      hPriorNonneg hPriorPos hSpeakerEqK
  -- Containment around cycle → equality at first step
  have hOptEq : ∀ t, optimalMessages G (ibrN G n₁) t =
      optimalMessages G (ibrN G (n₁ + 1)) t := by
    intro t
    exact cycle_containment_eq
      (fun k => optimalMessages G (ibrN G (n₁ + k)) t) hp
      (fun k hk => hOptSubAll k hk t)
      (by show optimalMessages G (ibrN G (n₁ + p)) t =
              optimalMessages G (ibrN G n₁) t
          rw [hperiod])
  -- Equal optimalMessages → equal bestResponse → consecutive repeat → fixed point
  have hBReq := opt_eq_bestResponse_eq G (ibrN G n₁) (ibrN G (n₁ + 1)) hOptEq
  have hConsec : ibrN G (n₁ + 1) = ibrN G (n₁ + 2) := by
    show ibrStep G (ibrN G n₁) = ibrStep G (ibrN G (n₁ + 1))
    simp only [ibrStep]; rw [hBReq]
  exact ⟨n₁ + 1, ibrN_consecutive_fp G (n₁ + 1) hConsec⟩

end Franke2011
