import Linglib.Theories.Pragmatics.IBR.Core
import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# IBR for Scalar Games

For **scalar** interpretation games (truth sets totally ordered by inclusion),
IBR converges to exhaustive interpretation (exhMW) at level 1.

The proof chains through `strongestAt` as a bridge predicate:

    ibrN > 0  ↔  strongestAt  ↔  exhMW
    (rational choice)        (order theory)

The left equivalence is proved by induction on the IBR sequence
(`ibrN_pos_iff_strongestAt`). The right equivalence is pure order theory
with no probabilities (`strongestAt_iff_exhMW`).

This bypasses the general convergence machinery in `Convergence.lean`
(~680 lines of EG monotonicity) entirely for scalar games.

Key results:
- `ibr_equals_exhMW`: IBR FP support = exhMW (@cite{franke-2011} Proposition 4)
- `ibr_converges_to_exhMW`: IBR stabilizes at level 1 for scalar games
-/

namespace RSA.IBR

open Exhaustification

-- SECTION 1: Scalar Game Definition

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
    exact absurd h2 hm₂_out
  | inr hsub =>
    have h1 : s₂ ∈ G.trueStates m₂ := G.mem_trueStates.mpr hm₂_in
    have h2 := hsub h1
    simp only [InterpGame.mem_trueStates] at h2
    exact absurd h2 hm₁_out

/-- In a scalar game, at the m-true state s₀ with fewest true messages,
    every message true at s₀ has trueStates ⊇ trueStates(m).

    Proof: If ∃ m₁ ∈ trueMessages(s₁) \ trueMessages(s₂) and
    ∃ m₂ ∈ trueMessages(s₂) \ trueMessages(s₁), then trueStates(m₁) and
    trueStates(m₂) are incomparable, contradicting isScalarGame. -/
theorem scalar_minimal_messages_weaker (G : InterpGame) (hScalar : isScalarGame G)
    (m : G.Message) (s₀ : G.State)
    (hs₀ : G.meaning m s₀ = true)
    (hmin : ∀ t, G.meaning m t = true → (G.trueMessages s₀).card ≤ (G.trueMessages t).card)
    (m' : G.Message) (hm' : G.meaning m' s₀ = true) :
    G.trueStates m ⊆ G.trueStates m' := by
  intro t ht
  simp only [InterpGame.mem_trueStates] at ht ⊢
  cases scalar_trueMessages_total G hScalar s₀ t with
  | inl hsub =>
    exact G.mem_trueMessages.mp (hsub (G.mem_trueMessages.mpr hm'))
  | inr hsub =>
    have hcard := hmin t ht
    have hcard' := Finset.card_le_card hsub
    have heq : G.trueMessages t = G.trueMessages s₀ := Finset.eq_of_subset_of_card_le hsub hcard
    exact G.mem_trueMessages.mp (heq ▸ G.mem_trueMessages.mpr hm')

-- SECTION 2: Alternative Set Bridge

/-- Convert interpretation game to alternative set for exhaustification.
    Converts Bool meaning to Set by using equality with true. -/
def toAlternatives (G : InterpGame) : Set (Set G.State) :=
  { λ s => G.meaning m s = true | m : G.Message }

/-- The prejacent proposition for a message (Bool → Prop conversion) -/
def prejacent (G : InterpGame) (m : G.Message) : Set G.State :=
  λ s => G.meaning m s = true

-- SECTION 3: ALT ordering bridges

/-- Strict subset of trueMessages implies <_ALT under `toAlternatives G`. -/
theorem trueMessages_ssubset_implies_ltALT (G : InterpGame)
    (s' s : G.State) (hss : G.trueMessages s' ⊂ G.trueMessages s) :
    ltALT (toAlternatives G) s' s := by
  constructor
  · intro a ha_mem ha_s'
    simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
    obtain ⟨m', hm'_eq⟩ := ha_mem
    subst hm'_eq
    have hm'_in_s' : m' ∈ G.trueMessages s' := G.mem_trueMessages.mpr ha_s'
    exact G.mem_trueMessages.mp (Finset.mem_of_subset hss.1 hm'_in_s')
  · intro hle
    have hsub : G.trueMessages s ⊆ G.trueMessages s' := by
      intro m' hm'
      simp only [InterpGame.mem_trueMessages] at hm' ⊢
      have h : (λ x => G.meaning m' x = true) s := hm'
      have halt := hle (λ x => G.meaning m' x = true) ⟨m', rfl⟩ h
      exact halt
    exact hss.2 hsub

/-- Key lemma: s' <_ALT s implies trueMessages s' ⊂ trueMessages s. -/
theorem ltALT_implies_trueMessages_ssubset (G : InterpGame) (s' s : G.State)
    (hlt : ltALT (toAlternatives G) s' s) :
    G.trueMessages s' ⊂ G.trueMessages s := by
  have hle : leALT (toAlternatives G) s' s := hlt.1
  have hne : ¬leALT (toAlternatives G) s s' := hlt.2
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro m' hm'
    simp only [InterpGame.mem_trueMessages] at hm' ⊢
    have halt : (λ x => G.meaning m' x = true) s' → (λ x => G.meaning m' x = true) s := by
      apply hle
      simp only [toAlternatives, Set.mem_setOf_eq]
      exact ⟨m', rfl⟩
    exact halt hm'
  · intro heq
    apply hne
    intro a ha_mem ha_s
    simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
    obtain ⟨m', hm'_eq⟩ := ha_mem
    subst hm'_eq
    have hm'_in : m' ∈ G.trueMessages s := G.mem_trueMessages.mpr ha_s
    exact G.mem_trueMessages.mp (heq ▸ hm'_in)

-- SECTION 4: The strongestAt Bridge

/-- `strongestAt G m s` — "m is the strongest true message at s":
    m is true at s, and trueStates(m) is contained in trueStates(m')
    for every other message m' true at s.

    In a scalar game, this picks out the unique most informative message.
    This predicate is the purely set-theoretic bridge between the
    probabilistic IBR sequence and the logical exhMW operator:

      ibrN > 0  ↔  strongestAt  ↔  exhMW

    The left equivalence is rational choice (proved via `ibrN_opt_singleton`).
    The right equivalence is pure order theory (no probabilities). -/
def strongestAt (G : InterpGame) (m : G.Message) (s : G.State) : Prop :=
  G.meaning m s = true ∧
  ∀ m', G.meaning m' s = true → G.trueStates m ⊆ G.trueStates m'

/-- Forward: strongestAt → exhMW. Pure order theory, no probabilities. -/
theorem strongestAt_implies_exhMW (G : InterpGame)
    (m : G.Message) (s : G.State)
    (h : strongestAt G m s) :
    exhMW (toAlternatives G) (prejacent G m) s := by
  constructor
  · exact h.1
  · intro ⟨s', hs'_true, hs'_lt⟩
    have hss := ltALT_implies_trueMessages_ssubset G s' s hs'_lt
    apply hss.2
    intro m' hm'
    simp only [InterpGame.mem_trueMessages] at hm' ⊢
    exact G.mem_trueStates.mp (h.2 m' hm' (G.mem_trueStates.mpr hs'_true))

/-- Backward: exhMW → strongestAt (requires scalar game).

    exhMW-minimality → card-minimality (via scalar totality) →
    strongest (via `scalar_minimal_messages_weaker`). -/
theorem exhMW_implies_strongestAt (G : InterpGame) (hScalar : isScalarGame G)
    (m : G.Message) (s : G.State)
    (h : exhMW (toAlternatives G) (prejacent G m) s) :
    strongestAt G m s := by
  have hTrue := h.1
  have hMin := h.2
  -- Step 1: exhMW-minimal → card-minimal
  have hCardMin : ∀ t, G.meaning m t = true →
      (G.trueMessages s).card ≤ (G.trueMessages t).card := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    cases scalar_trueMessages_total G hScalar t s with
    | inl hsub =>
      have hss : G.trueMessages t ⊂ G.trueMessages s :=
        ⟨hsub, fun hrev => absurd (Finset.card_le_card hrev) (by omega)⟩
      exact hMin ⟨t, ht, trueMessages_ssubset_implies_ltALT G t s hss⟩
    | inr hsub =>
      exact absurd (Finset.card_le_card hsub) (by omega)
  -- Step 2: card-minimal → strongest
  exact ⟨hTrue, fun m' hm' =>
    scalar_minimal_messages_weaker G hScalar m s hTrue hCardMin m' hm'⟩

/-- For scalar games, strongestAt ↔ exhMW. The purely set-theoretic core
    of the IBR = exhMW theorem. No probabilities, no EG monotonicity. -/
theorem strongestAt_iff_exhMW (G : InterpGame) (hScalar : isScalarGame G)
    (m : G.Message) (s : G.State) :
    strongestAt G m s ↔ exhMW (toAlternatives G) (prejacent G m) s :=
  ⟨strongestAt_implies_exhMW G m s, exhMW_implies_strongestAt G hScalar m s⟩

-- SECTION 5: IBR Fixed Point = Strongest Message (Scalar Games)

/-- In a scalar game with distinct truth sets, every message m has a nonempty
    set of "level" states: states in trueStates(m) but not in any strictly
    smaller truth set. At these states, m is the strongest true message. -/
private theorem scalar_level_nonempty (G : InterpGame) (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (m : G.Message) (hNE : (G.trueStates m).Nonempty) :
    ∃ s ∈ G.trueStates m, ∀ m' : G.Message, G.meaning m' s = true →
      G.trueStates m ⊆ G.trueStates m' := by
  have ⟨s, hs_in, hs_min⟩ := Finset.exists_min_image (G.trueStates m)
    (fun s => (G.trueMessages s).card) hNE
  refine ⟨s, hs_in, fun m' hm' => ?_⟩
  intro t ht
  simp only [InterpGame.mem_trueStates] at hs_in ht ⊢
  cases hScalar m m' with
  | inl hsub =>
    exact (G.mem_trueStates.mp (hsub (G.mem_trueStates.mpr ht)))
  | inr hsub =>
    cases scalar_trueMessages_total G hScalar t s with
    | inl hsub_tm =>
      have heq := Finset.eq_of_subset_of_card_le hsub_tm
        (hs_min t (G.mem_trueStates.mpr ht))
      have hm'_in_s : m' ∈ G.trueMessages s := G.mem_trueMessages.mpr hm'
      rw [← heq] at hm'_in_s
      exact G.mem_trueMessages.mp hm'_in_s
    | inr hsub_st =>
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

/-- Under flat priors, if the speaker is deterministic for message m
    (S(t,m) ∈ {0,1} with at least one S=1), hearerBR gives H(m,s) > 0
    iff S(s,m) = 1.

    This captures @cite{franke-2011}'s eq. (131): with flat priors the
    posterior comparison μ(t₁|m) > μ(t₂|m) reduces to S(t₁,m) > S(t₂,m)
    because the priors cancel. So the argmax hearer picks exactly the
    states where the speaker sends m. -/
private theorem hearerBR_deterministic_flat (G : InterpGame)
    (S : SpeakerStrategy G) (m : G.Message) (s : G.State)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (t₀ : G.State) (ht₀ : S.choose t₀ m = 1)
    (hS_le : ∀ t, S.choose t m ≤ 1) :
    (hearerBR G S).respond m s > 0 ↔ S.choose s m = 1 := by
  set p := G.prior s
  set w := fun t => S.choose t m * G.prior t
  -- maxW = p: since S ≤ 1 and flat priors, w(t) ≤ p for all t, with equality at t₀.
  have hmaxW : Finset.univ.fold max 0 w = p := le_antisymm
    (by rcases fold_max_attained Finset.univ w 0 with h0 | ⟨t, _, hft⟩
        · linarith [hPriorPos s]
        · calc _ = w t := hft
            _ = S.choose t m * G.prior t := rfl
            _ ≤ 1 * G.prior t :=
                mul_le_mul_of_nonneg_right (hS_le t) (le_of_lt (hPriorPos t))
            _ = p := by rw [one_mul, hFlatPrior t s])
    (by calc p = 1 * G.prior t₀ := by rw [one_mul, hFlatPrior t₀ s]
        _ = S.choose t₀ m * G.prior t₀ := by rw [ht₀]
        _ ≤ _ := (Finset.le_fold_max _).mpr (Or.inr ⟨t₀, Finset.mem_univ _, le_refl _⟩))
  simp only [hearerBR]
  rw [if_neg (by linarith [hPriorPos s] : Finset.univ.fold max 0 w ≠ 0)]
  constructor
  · -- Forward: H > 0 → S(s,m) = 1
    intro hPos
    split_ifs at hPos with hwm
    · -- w(s) = maxW = p, so S(s,m) * p = p
      have h1 : S.choose s m * G.prior s = G.prior s := by linarith
      have h2 : (S.choose s m - 1) * G.prior s = 0 := by linarith
      linarith [(mul_eq_zero.mp h2).resolve_right (ne_of_gt (hPriorPos s))]
    · exact absurd hPos (lt_irrefl 0)
  · -- Backward: S(s,m) = 1 → H > 0
    intro hS1
    have hws : S.choose s m * G.prior s = Finset.univ.fold max 0 w := by
      rw [hS1, one_mul, hmaxW]
    rw [if_pos hws]
    exact div_pos one_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr
      ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hws⟩⟩))

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
    -- Helper: hearerBR_deterministic_flat gives H(m',s) > 0 ↔ S(s,m') = 1
    -- for any m' with a level state (eq. 131)
    have hBR_iff : ∀ m', (G.trueMessages s).Nonempty →
        (∃ t₁, S.choose t₁ m' = 1) →
        ((ibrN G (n + 1)).respond m' s > 0 ↔ S.choose s m' = 1) := by
      intro m' _ ⟨t₁, ht₁⟩
      exact hearerBR_deterministic_flat G S m' s hPriorPos hFlatPrior t₁ ht₁
        (fun t => SpeakerStrategy.bestResponse_le_one G (ibrN G n) t m')
    -- H(m', s) = 0 for non-strongest m' at s
    have hH_zero : ∀ m', G.meaning m' s = true → m' ≠ m₀ →
        (ibrN G (n + 1)).respond m' s = 0 := by
      intro m' hm's hne
      obtain ⟨t₀, ht₀_in, ht₀_str⟩ := scalar_level_nonempty G hScalar hDistinct m'
        ⟨s, G.mem_trueStates.mpr hm's⟩
      have ht₀_in := G.mem_trueStates.mp ht₀_in
      have ht₀_br : S.choose t₀ m' = 1 :=
        hbr_eq t₀ m' ⟨m', G.mem_trueMessages.mpr ht₀_in⟩ ht₀_in ht₀_str
      have hs_br : S.choose s m' = 0 :=
        hbr_zero s m' hNE hm's ⟨m₀, hm₀_in, hm₀_sstr m' hm's hne⟩
      have hNotPos := mt (hBR_iff m' hNE ⟨t₀, ht₀_br⟩).mp (by linarith)
      have hnn : (ibrN G (n + 1)).respond m' s ≥ 0 := hearerBR_respond_nonneg G S m' s
      linarith
    -- H(m₀, s) > 0
    have hH_pos : (ibrN G (n + 1)).respond m₀ s > 0 :=
      (hBR_iff m₀ hNE ⟨s, hbr_eq s m₀ hNE hm₀_in hm₀_str⟩).mpr
        (hbr_eq s m₀ hNE hm₀_in hm₀_str)
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
    (smallest truth set among messages true at `s`). -/
private theorem ibrN_respond_pos_iff_strongest (G : InterpGame)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (k : ℕ) (m : G.Message) (s : G.State) (hs : G.meaning m s = true) :
    (ibrN G (k + 1)).respond m s > 0 ↔
      (∀ m', G.meaning m' s = true → G.trueStates m ⊆ G.trueStates m') := by
  set S := SpeakerStrategy.bestResponse G (ibrN G k)
  have hNE : (G.trueMessages s).Nonempty := ⟨m, G.mem_trueMessages.mpr hs⟩
  -- From ibrN_opt_singleton: opt(s) = {m₀} where m₀ is the strongest at s
  obtain ⟨m₀, hopt₀, hm₀_true, hm₀_str⟩ :=
    ibrN_opt_singleton G hPriorPos hFlatPrior hScalar hDistinct k s hNE
  -- S(s, m₀) = 1, S(s, m') = 0 for m' ≠ m₀
  have hbr_m₀ : S.choose s m₀ = 1 := by
    rw [SpeakerStrategy.bestResponse_val, if_pos (hopt₀ ▸ Finset.mem_singleton_self m₀),
      hopt₀, Finset.card_singleton]; norm_num
  have hbr_ne : ∀ m', m' ≠ m₀ → S.choose s m' = 0 := fun m' hne => by
    rw [SpeakerStrategy.bestResponse_val, if_neg (hopt₀ ▸ mt Finset.mem_singleton.mp hne)]
  -- Find level state t₀ where m is strongest → S(t₀, m) = 1
  obtain ⟨t₀, ht₀_in, ht₀_str⟩ := scalar_level_nonempty G hScalar hDistinct m
    ⟨s, G.mem_trueStates.mpr hs⟩
  have ht₀_in := G.mem_trueStates.mp ht₀_in
  obtain ⟨m_t₀, hopt_t₀, _, hstr_t₀⟩ := ibrN_opt_singleton G hPriorPos hFlatPrior
    hScalar hDistinct k t₀ ⟨m, G.mem_trueMessages.mpr ht₀_in⟩
  have hm_eq : m = m_t₀ := hDistinct m m_t₀
    (Finset.Subset.antisymm (ht₀_str m_t₀ (SpeakerStrategy.optimalMessages_meaning G
      (ibrN G k) t₀ m_t₀ (hopt_t₀ ▸ Finset.mem_singleton_self m_t₀))) (hstr_t₀ m ht₀_in))
  subst hm_eq
  have hbr_t₀ : S.choose t₀ m = 1 := by
    rw [SpeakerStrategy.bestResponse_val, if_pos (hopt_t₀ ▸ Finset.mem_singleton_self m),
      hopt_t₀, Finset.card_singleton]; norm_num
  -- Apply eq. 131: H > 0 ↔ S = 1 ↔ m = m₀ ↔ m strongest
  have hBR := hearerBR_deterministic_flat G S m s hPriorPos hFlatPrior t₀ hbr_t₀
    (fun t => SpeakerStrategy.bestResponse_le_one G (ibrN G k) t m)
  constructor
  · intro hPos
    have hS1 := hBR.mp hPos
    -- S(s,m) = 1 means m ∈ opt(s) = {m₀}, so m = m₀
    have : m = m₀ := by
      have hpos : S.choose s m > 0 := by linarith
      exact Finset.mem_singleton.mp
        (hopt₀ ▸ ((SpeakerStrategy.bestResponse_pos_iff G (ibrN G k) s m).mp hpos).1)
    exact this ▸ hm₀_str
  · intro hStr
    have hm_eq : m = m₀ := hDistinct m m₀
      (Finset.Subset.antisymm (hStr m₀ hm₀_true) (hm₀_str m hs))
    exact hBR.mpr (hm_eq ▸ hbr_m₀)

-- SECTION 5: Main Theorems

/-- At `ibrN G (k+1)`, `H(m, s) > 0` iff `strongestAt G m s`.

    Thin wrapper around `ibrN_respond_pos_iff_strongest` that handles the
    case where m is false at s (both sides are false) and packages the
    result as the `strongestAt` predicate. -/
private theorem ibrN_pos_iff_strongestAt (G : InterpGame)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (k : ℕ) (m : G.Message) (s : G.State) :
    (ibrN G (k + 1)).respond m s > 0 ↔ strongestAt G m s := by
  constructor
  · intro hPos
    -- m must be true at s (false messages get H = 0)
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
    exact ⟨hTrue, (ibrN_respond_pos_iff_strongest G hPriorPos hFlatPrior hScalar
      hDistinct k m s hTrue).mp hPos⟩
  · intro ⟨hTrue, hStr⟩
    exact (ibrN_respond_pos_iff_strongest G hPriorPos hFlatPrior hScalar
      hDistinct k m s hTrue).mpr hStr

/-- IBR = exhMW (Main theorem — @cite{franke-2011}, Section 9.3)

At any IBR level k+1 of a **scalar** interpretation game, the listener's
positive-probability states for message m are exactly the exhMW-minimal states.

The proof chains through `strongestAt` as a bridge:

    ibrN > 0  ↔  strongestAt  ↔  exhMW
    (rational choice)        (order theory)

The left equivalence (`ibrN_pos_iff_strongestAt`) is proved by induction on
the IBR sequence. The right equivalence (`strongestAt_iff_exhMW`) is pure
order theory with no probabilities.

**Restriction**: Requires `hIBR : ∃ k, H = ibrN G (k + 1)`, i.e., H is from
the IBR iteration. The claim is false for arbitrary FPs of scalar games.

Two structural hypotheses:
- `isScalarGame`: truth sets are totally ordered by inclusion (nested)
- `hDistinct`: no two messages have identical truth sets -/
theorem ibr_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (_hFP : isIBRFixedPoint G H)
    (hPriorPos : ∀ t, G.prior t > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂)
    (hIBR : ∃ k, H = ibrN G (k + 1))
    (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) := by
  obtain ⟨k, hH⟩ := hIBR; subst hH
  intro s
  exact (ibrN_pos_iff_strongestAt G hPriorPos hFlatPrior hScalar hDistinct k m s).trans
    (strongestAt_iff_exhMW G hScalar m s)

/-- For scalar games, IBR stabilizes at level 1. No EG monotonicity needed.

    The IBR sequence for scalar games reaches its correct behavior at level 1:
    `ibrN G 1` already assigns positive probability exactly to exhMW-minimal
    states. This bypasses the general convergence machinery
    (`ibr_reaches_fixed_point`, ~350 lines of EG arithmetic) entirely. -/
theorem ibr_converges_to_exhMW (G : InterpGame)
    (hPriorPos : ∀ s, G.prior s > 0)
    (hFlatPrior : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂)
    (hScalar : isScalarGame G)
    (hDistinct : ∀ m₁ m₂ : G.Message, G.trueStates m₁ = G.trueStates m₂ → m₁ = m₂) :
    ∀ (m : G.Message) (s : G.State),
      (ibrN G 1).respond m s > 0 ↔
        exhMW (toAlternatives G) (prejacent G m) s := by
  intro m s
  exact (ibrN_pos_iff_strongestAt G hPriorPos hFlatPrior hScalar hDistinct 0 m s).trans
    (strongestAt_iff_exhMW G hScalar m s)

-- SECTION 6: Level-Uniform Generalization

/-- Level of a message: the states where m is the strongest true message.

    In a scalar game, these form an equivalence class of the truth-pattern
    partition. IBR reasoning assigns positive probability to (m, s) iff
    s is in the level of m. -/
def messageLevel (G : InterpGame) (m : G.Message) : Finset G.State :=
  Finset.univ.filter (λ s => G.meaning m s = true ∧
    ∀ m', G.meaning m' s = true → G.trueStates m ⊆ G.trueStates m')

/-- The prior is **level-uniform** if it is constant within each message's level.

    This is the minimal condition for IBR = exhMW. Flat priors (∀ t₁ t₂, P(t₁) = P(t₂))
    trivially satisfy this, but level-uniformity is strictly weaker. -/
def levelUniformPrior (G : InterpGame) : Prop :=
  ∀ (m : G.Message) (s₁ s₂ : G.State),
    s₁ ∈ messageLevel G m → s₂ ∈ messageLevel G m →
    G.prior s₁ = G.prior s₂

/-- An **equivalence class game** has states that are truth-pattern equivalence
    classes: each message level is a singleton set. In such games,
    `levelUniformPrior` holds for ANY positive prior (there's only one state
    per level, so the uniformity condition is vacuous).

    @cite{franke-2011}'s Theorem 1 shows that for equivalence class games,
    heavy = light systems — the prior doesn't affect the interpretation. -/
def isEquivalenceClassGame (G : InterpGame) : Prop :=
  ∀ (m : G.Message), (messageLevel G m).Nonempty →
    (messageLevel G m).card = 1

/-- Flat priors are level-uniform. -/
theorem flat_prior_is_levelUniform (G : InterpGame)
    (hFlat : ∀ t₁ t₂ : G.State, G.prior t₁ = G.prior t₂) :
    levelUniformPrior G :=
  fun _ _ _ _ _ => hFlat _ _

/-- Equivalence class games have level-uniform priors for any prior. -/
theorem eqclass_levelUniform (G : InterpGame) (hEq : isEquivalenceClassGame G) :
    levelUniformPrior G := by
  intro m s₁ s₂ hs₁ hs₂
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hEq m ⟨s₁, hs₁⟩)
  have h₁ : s₁ = a := Finset.mem_singleton.mp (ha ▸ hs₁)
  have h₂ : s₂ = a := Finset.mem_singleton.mp (ha ▸ hs₂)
  rw [h₁, h₂]

end RSA.IBR
