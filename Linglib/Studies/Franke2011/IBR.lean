import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Linglib.Core.Order.Argmax
import Linglib.Pragmatics.SignalingGame.Interpretation

/-!
# Franke 2011: iterated best response dynamics

The IBR machinery of [franke-2011] §6–8 over the shared interpretation-game
carrier (`InterpGame`): best-response speaker (eq. (76)), Bayesian argmax
hearer (eq. (120); the light-system argmin form eq. (77) under flat priors),
the iteration `ibrN`, fixed points, and expected gain.

Strategies are ℚ-valued kernels as plain functions — a hearer strategy is
`M → T → ℚ`, a speaker strategy `T → M → ℚ`.

Indexing note: `ibrStep` composes a speaker best response with a hearer best
response, so `ibrN` tracks the *even* receiver subsequence R₀, R₂, R₄, … of
[franke-2011] — `ibrN G 1` is the paper's R₂, not R₁. For the scalar games of
`ScalarGames.lean` all receiver levels ≥ 1 coincide, so the distinction is
immaterial there.
-/

namespace Franke2011

variable {T M : Type*} (G : InterpGame T M)

/-! ### Speaker best response -/

section Speaker

variable [Fintype M]

/-- Max utility among true messages at state `s` (0 if no true messages). -/
def maxUtility (H : M → T → ℚ) (s : T) : ℚ :=
  (G.trueMessages s).fold max 0 (λ m' => H m' s)

/-- Optimal messages at state `s`: true messages achieving max utility — the
    set-level best response ([franke-2011] eq. (76)). All probability-level
    reasoning should go through this set. -/
def optimalMessages (H : M → T → ℚ) (s : T) : Finset M :=
  (G.trueMessages s).filter (λ m => H m s = maxUtility G H s)

theorem optimalMessages_subset_trueMessages (H : M → T → ℚ) (s : T) :
    optimalMessages G H s ⊆ G.trueMessages s :=
  Finset.filter_subset _ _

theorem optimalMessages_meaning (H : M → T → ℚ) (s : T) (m : M)
    (hm : m ∈ optimalMessages G H s) : G.meaning m s :=
  G.mem_trueMessages.mp (optimalMessages_subset_trueMessages G H s hm)

theorem optimalMessages_utility (H : M → T → ℚ) (s : T) (m : M)
    (hm : m ∈ optimalMessages G H s) : H m s = maxUtility G H s :=
  (Finset.mem_filter.mp hm).2

theorem maxUtility_nonneg (H : M → T → ℚ) (s : T) : 0 ≤ maxUtility G H s :=
  (Finset.le_fold_max 0).mpr (Or.inl (le_refl _))

theorem utility_le_maxUtility (H : M → T → ℚ) (s : T) (m : M)
    (hm : m ∈ G.trueMessages s) : H m s ≤ maxUtility G H s :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨m, hm, le_refl _⟩)

/-- For nonnegative hearer utilities, the optimal-message set is the argmax
    of hearer utility over the true messages — the carrier's `Finset.argmax`
    vocabulary. (Nonnegativity matters: `maxUtility` floors at 0, so with
    all-negative utilities `optimalMessages` is empty while the argmax set is
    not.) -/
theorem optimalMessages_eq_argmax [DecidableEq M] (H : M → T → ℚ) (s : T)
    (hH : ∀ m', 0 ≤ H m' s) :
    optimalMessages G H s = (G.trueMessages s).argmax (H · s) := by
  ext m
  simp only [optimalMessages, Finset.mem_filter, Finset.mem_argmax]
  refine and_congr_right fun hm =>
    ⟨fun h m' hm' => (utility_le_maxUtility G H s m' hm').trans_eq h.symm,
     fun h => le_antisymm (utility_le_maxUtility G H s m hm) ?_⟩
  rcases Finset.fold_max_attained (G.trueMessages s) (fun m' => H m' s) 0 with
    h0 | ⟨x, hx, hfx⟩
  · exact (show maxUtility G H s = 0 from h0).trans_le (hH m)
  · exact (show maxUtility G H s = H x s from hfx).trans_le (h x hx)

variable [DecidableEq M]

/-- Best response speaker: uniform distribution over optimal messages
    ([franke-2011] eq. (76)). -/
def bestResponse (H : M → T → ℚ) : T → M → ℚ := λ s m =>
  if m ∈ optimalMessages G H s then
    let k := (optimalMessages G H s).card
    if k = 0 then 0 else 1 / k
  else 0

/-- bestResponse gives 1/k to optimal messages, 0 to others. -/
theorem bestResponse_val (H : M → T → ℚ) (s : T) (m : M) :
    bestResponse G H s m =
      if m ∈ optimalMessages G H s then
        if (optimalMessages G H s).card = 0 then 0
        else 1 / ((optimalMessages G H s).card : ℚ)
      else 0 := by
  simp only [bestResponse]

/-- Best response speaker always gives non-negative probabilities. -/
theorem bestResponse_nonneg (H : M → T → ℚ) (s : T) (m : M) :
    0 ≤ bestResponse G H s m := by
  rw [bestResponse_val]
  split_ifs <;> first | exact le_refl 0 | exact one_div_nonneg.mpr (Nat.cast_nonneg _)

/-- Best response speaker gives zero probability to false messages. -/
theorem bestResponse_false_zero (H : M → T → ℚ) (s : T) (m : M)
    (hFalse : ¬ G.meaning m s) : bestResponse G H s m = 0 := by
  rw [bestResponse_val, if_neg]
  exact fun hmem => absurd (optimalMessages_meaning G H s m hmem) hFalse

/-- bestResponse gives positive probability iff m is optimal (and optimal set
    is nonempty). -/
theorem bestResponse_pos_iff (H : M → T → ℚ) (s : T) (m : M) :
    bestResponse G H s m > 0 ↔
      m ∈ optimalMessages G H s ∧ (optimalMessages G H s).card > 0 := by
  rw [bestResponse_val]
  split_ifs with hmem hcard
  · simp [hcard]
  · constructor
    · intro h; exact ⟨hmem, by omega⟩
    · intro _; exact div_pos one_pos (Nat.cast_pos.mpr (by omega))
  · simp [hmem]

/-- Best response speaker probabilities sum to at most 1 at any state. -/
theorem bestResponse_sum_le_one (H : M → T → ℚ) (s : T) :
    Finset.univ.sum (λ m => bestResponse G H s m) ≤ 1 := by
  set opt := optimalMessages G H s
  set k := opt.card
  have hval : ∀ m, bestResponse G H s m =
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
theorem bestResponse_le_one (H : M → T → ℚ) (s : T) (m : M) :
    bestResponse G H s m ≤ 1 := by
  rw [bestResponse_val]
  split_ifs with _ hcard
  · exact zero_le_one
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hcard)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
  · exact zero_le_one

end Speaker

/-! ### Hearer best response and the IBR sequence -/

section Hearer

variable [Fintype T]

/-- Hearer best response: argmax of posterior probability ([franke-2011]
    eq. (120); under flat priors it reduces to the light-system argmin form,
    eq. (77)).

    The hearer observes m, forms posterior μ(t|m) ∝ S(t,m) · P(t), and picks
    the state(s) with maximum posterior probability. Uniform over ties.
    For surprise messages (∀ t, S(t,m) · P(t) = 0), falls back to literal
    interpretation per the tcp assumption. -/
def hearerBR (S : T → M → ℚ) : M → T → ℚ := λ m t =>
  let w : T → ℚ := λ s => S s m * G.prior s
  let maxW := Finset.univ.fold max 0 w
  if maxW = 0 then G.literal m t
  else if w t = maxW then
    1 / ((Finset.univ.filter (λ s => w s = maxW)).card : ℚ)
  else 0

/-- hearerBR always gives non-negative response values. -/
theorem hearerBR_respond_nonneg (S : T → M → ℚ) (m : M) (t : T) :
    hearerBR G S m t ≥ 0 := by
  simp only [hearerBR, InterpGame.literal]
  split_ifs
  all_goals first
    | exact le_refl 0
    | exact inv_nonneg.mpr (Nat.cast_nonneg _)
    | exact div_nonneg (le_of_lt one_pos) (Nat.cast_nonneg _)

variable [Fintype M] [DecidableEq M]

/-- One full IBR iteration step: speaker best-responds, hearer
    argmax-responds. -/
def ibrStep (H : M → T → ℚ) : M → T → ℚ :=
  hearerBR G (bestResponse G H)

/-- IBR reasoning for n iterations starting from the literal listener. -/
def ibrN : ℕ → M → T → ℚ
  | 0 => G.literal
  | n + 1 => ibrStep G (ibrN n)

/-- A hearer strategy is a fixed point of the IBR step. -/
def isIBRFixedPoint (H : M → T → ℚ) : Prop :=
  ∀ m t, H m t = ibrStep G H m t

/-- EG(S, R) = Σ_t Pr(t) × Σ_m S(t,m) × R(m,t): expected communication
    success. -/
def expectedGain (S : T → M → ℚ) (H : M → T → ℚ) : ℚ :=
  Finset.univ.sum λ t =>
    G.prior t * Finset.univ.sum λ m => S t m * H m t

end Hearer

end Franke2011
