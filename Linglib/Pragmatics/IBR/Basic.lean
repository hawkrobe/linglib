import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Linglib.Core.Agent.RationalAction

/-!
# Iterated Best Response: Core Definitions

Game-theoretic pragmatics following @cite{franke-2011} §6-8.

Defines interpretation games (`InterpGame`), speaker/hearer strategies,
literal listener (L₀), best response operators, IBR iteration (`ibrN`),
fixed points, and expected gain (`expectedGain`).
-/

namespace RSA.IBR

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

end RSA.IBR
