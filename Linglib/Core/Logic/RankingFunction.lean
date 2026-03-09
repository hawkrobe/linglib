import Linglib.Core.Order.Plausibility
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ranking Functions and Iterated Belief Revision

@cite{halpern-2003} @cite{darwiche-pearl-1997} @cite{spohn-1988}

Ranking functions (ordinal conditional functions, OCFs) provide a
qualitative, ordinal approach to belief revision that serves as the
quantitative semantics for System P + Rational Monotonicity.

@cite{spohn-1988} introduced ranking functions as ordinal-valued measures
of disbelief. We restrict to ℕ-valued rankings, following the
simplification noted in Note 16 of the paper. κ(w) = 0 means w is
maximally plausible (believed possible), while higher ranks indicate
greater implausibility. The normalization condition — some world has
rank 0 — ensures the belief state is non-vacuous.

## Key Results

1. **Ranking → Plausibility**: Every ranking function induces a
   plausibility ordering (§1), which in turn yields a preferential
   consequence relation satisfying System P.

2. **Connectedness**: Because ℕ is totally ordered, the induced
   plausibility ordering is connected (any two worlds are comparable),
   so Rational Monotonicity holds.

3. **A-part** (Def. 5): κ(w|A) = κ(w) - κ(A) extracts the relative
   ranking within A-worlds, shifted so the best A-world has rank 0.

4. **A,α-conditionalization** (Def. 6): The revision operation
   parameterized by firmness α. Higher α = firmer belief in the
   evidence.

5. **Independence** (Def. 8): κ(B ∩ C) = κ(B) + κ(C) when B,C
   are independent — the ordinal analogue of probabilistic independence.

6. **Darwiche-Pearl Postulates**: Ranking conditioning satisfies
   the iterated revision postulates C1–C4 (§2), which AGM alone
   does not constrain.

See `Phenomena.DefaultReasoning.Studies.Spohn1988` for a verified
concrete instance demonstrating evidence strength, commutativity
(Theorem 4), and the connection to `NormalityOrder`.

## Bridge to Probability (@cite{spohn-1988} §7)

Ranking conditioning is the ordinal analogue of Bayesian conditioning.
The structural parallel (min/+ for ordinals mirrors product/sum for
probabilities):

| Probability (ℚ, ·, Σ)         | Ranking (ℕ, min, +)              |
|-------------------------------|----------------------------------|
| P(A) = Σ_{w∈A} P(w)          | κ(A) = min_{w∈A} κ(w)           |
| P(A|B) = P(A∩B)/P(B)         | κ(w|A) = κ(w) - κ(A)            |
| P(A∩B) = P(A)·P(B|A)         | κ(A∩B) = κ(A) + κ(B|A)          |
| P(A∩B) = P(A)·P(B) (indep.)  | κ(A∩B) = κ(A) + κ(B) (indep.)   |

See `ConditioningMode.ranking` in `Core/Scales/EpistemicScale/Conditional.lean`
for the conditioning-mode classification.
-/

namespace Core.Logic.Ranking

open Core.Order (PlausibilityOrder PreferentialConsequence rationalMonotonicity)

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Ranking Functions
-- ══════════════════════════════════════════════════════════════════════

/-- A ranking function (ordinal conditional function) on worlds.

    κ : W → ℕ assigns each world a degree of disbelief.
    Normalization: some world has rank 0 (the agent considers at least
    one world possible).

    @cite{spohn-1988}, Definition 4 uses ordinals in the general case;
    we restrict to ℕ following Note 16 of the paper. -/
structure RankingFunction (W : Type*) where
  /-- The rank (degree of disbelief) of each world -/
  rank : W → ℕ
  /-- At least one world has rank 0 -/
  normalized : ∃ w, rank w = 0

namespace RankingFunction

variable {W : Type*}

/-- The rank of a proposition: the minimum rank among worlds
    satisfying it. Requires the proposition to be satisfiable.

    κ(φ) = min { κ(w) | φ w } -/
noncomputable def rankProp [Fintype W] (κ : RankingFunction W) (φ : W → Prop)
    [DecidablePred φ] (hsat : ∃ w, φ w) : ℕ :=
  Finset.inf' (Finset.univ.filter (fun w => φ w))
    (by obtain ⟨w, hw⟩ := hsat
        exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩)
    κ.rank

/-- The A-part of κ: the ranking restricted to A-worlds, shifted so
    the most plausible A-world has rank 0.

    @cite{spohn-1988}, Definition 5: κ(w|A) = κ(w) - κ(A) for w ∈ A.
    This is the primitive from which conditioning derives. -/
noncomputable def aPart [Fintype W] (κ : RankingFunction W) (φ : W → Prop)
    [DecidablePred φ] (hφ : ∃ w, φ w) (w : W) : ℕ :=
  κ.rank w - κ.rankProp φ hφ

/-- @cite{spohn-1988}, Theorem 2(a): For any proposition, either it
    or its negation has rank 0 (or both).

    Normalization propagates from worlds to propositions: the rank-0
    world satisfies either φ or ¬φ, making that side's rankProp = 0.
    This is the ordinal analogue of P(A) + P(Ā) = 1. -/
theorem rankProp_dichotomy [Fintype W] (κ : RankingFunction W)
    (φ : W → Prop) [DecidablePred φ] [DecidablePred (fun w => ¬φ w)]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w) :
    κ.rankProp φ hφ = 0 ∨ κ.rankProp (fun w => ¬φ w) hNφ = 0 := by
  obtain ⟨w₀, hw₀⟩ := κ.normalized
  by_cases hφw₀ : φ w₀
  · left
    have : κ.rankProp φ hφ ≤ 0 := by
      unfold rankProp
      exact (Finset.inf'_le κ.rank
        (Finset.mem_filter.mpr ⟨Finset.mem_univ w₀, hφw₀⟩)).trans (le_of_eq hw₀)
    omega
  · right
    have : κ.rankProp (fun w => ¬φ w) hNφ ≤ 0 := by
      unfold rankProp
      have hmem : w₀ ∈ Finset.univ.filter (fun w => ¬φ w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ w₀, hφw₀⟩
      exact (Finset.inf'_le κ.rank hmem).trans (le_of_eq hw₀)
    omega

/-- @cite{spohn-1988}, Theorem 2(b): The rank of a disjunction is
    the minimum of the disjuncts' ranks.

    κ(A ∪ B) = min(κ(A), κ(B)) for any non-empty A, B. This is
    because κ takes the minimum over worlds, and the minimum over a
    union equals the min of the minima over each part.

    This is the ordinal analogue of P(A ∪ B) = P(A) + P(B) for
    disjoint events (and ≤ for overlapping ones). -/
theorem rankProp_union [Fintype W] [DecidableEq W] (κ : RankingFunction W)
    (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    [DecidablePred (fun w => φ w ∨ ψ w)]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w) :
    κ.rankProp (fun w => φ w ∨ ψ w)
      (by obtain ⟨w, hw⟩ := hφ; exact ⟨w, Or.inl hw⟩) =
    min (κ.rankProp φ hφ) (κ.rankProp ψ hψ) := by
  unfold rankProp
  set Sφψ := Finset.univ.filter (fun w => φ w ∨ ψ w)
  set Sφ := Finset.univ.filter (fun w => φ w)
  set Sψ := Finset.univ.filter (fun w => ψ w)
  -- Nonemptiness witnesses
  have hSφ : (Sφ).Nonempty := by
    obtain ⟨w, hw⟩ := hφ; exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
  have hSψ : (Sψ).Nonempty := by
    obtain ⟨w, hw⟩ := hψ; exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
  have hSφψ : (Sφψ).Nonempty := by
    obtain ⟨w, hw⟩ := hφ; exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inl hw⟩⟩
  apply Nat.le_antisymm
  · -- inf'(φ ∨ ψ) ≤ min(inf'(φ), inf'(ψ))
    -- The (φ ∨ ψ)-set is a superset of each part, so its inf' ≤ each part's inf'
    rw [Nat.le_min]
    constructor
    · apply Finset.le_inf'
      intro w hw
      exact Finset.inf'_le κ.rank (show w ∈ Sφψ by
        rw [Finset.mem_filter] at hw ⊢; exact ⟨hw.1, Or.inl hw.2⟩)
    · apply Finset.le_inf'
      intro w hw
      exact Finset.inf'_le κ.rank (show w ∈ Sφψ by
        rw [Finset.mem_filter] at hw ⊢; exact ⟨hw.1, Or.inr hw.2⟩)
  · -- min(inf'(φ), inf'(ψ)) ≤ inf'(φ ∨ ψ)
    apply Finset.le_inf'
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw.2 with hφw | hψw
    · exact (Nat.min_le_left _ _).trans
        (Finset.inf'_le κ.rank (show w ∈ Sφ by rw [Finset.mem_filter]; exact ⟨hw.1, hφw⟩))
    · exact (Nat.min_le_right _ _).trans
        (Finset.inf'_le κ.rank (show w ∈ Sψ by rw [Finset.mem_filter]; exact ⟨hw.1, hψw⟩))

/-- A ranking function induces a plausibility ordering:
    w is at least as plausible as v iff κ(w) ≤ κ(v).

    Smoothness follows from the well-orderedness of ℕ:
    every non-empty subset of ℕ has a minimum, so among the
    φ-worlds with rank ≤ κ(w), we can find a minimal one. -/
def toPlausibilityOrder (κ : RankingFunction W) : PlausibilityOrder W where
  le := fun w v => κ.rank w ≤ κ.rank v
  le_refl := fun _ => Nat.le_refl _
  le_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  smooth := fun φ w hφw => by
    classical
    -- Among φ-worlds with rank ≤ κ(w), find one with minimal rank.
    -- Such worlds exist (w itself qualifies).
    -- The ranks of candidates form a nonempty subset of ℕ.
    -- Use Nat.find to get the minimal rank value.
    let minRank := Nat.find (⟨κ.rank w, w, hφw, Nat.le_refl _, rfl⟩ :
      ∃ n, ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧ κ.rank v = n)
    obtain ⟨v, hφv, hvw, hvrank⟩ := Nat.find_spec (⟨κ.rank w, w, hφw, Nat.le_refl _, rfl⟩ :
      ∃ n, ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧ κ.rank v = n)
    refine ⟨v, hφv, hvw, ?_⟩
    intro u hφu huv
    -- huv : κ(u) ≤ κ(v), need: κ(v) ≤ κ(u)
    -- If κ(u) < κ(v) = minRank, that contradicts minimality of minRank
    by_contra h
    push_neg at h
    -- h : κ(v) > κ(u), i.e., κ(u) < κ(v)
    have hlt : κ.rank u < minRank := by omega
    have huw : κ.rank u ≤ κ.rank w := Nat.le_trans (Nat.le_of_lt_succ (by omega)) hvw
    exact Nat.find_min (⟨κ.rank w, w, hφw, Nat.le_refl _, rfl⟩ :
      ∃ n, ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧ κ.rank v = n) hlt ⟨u, hφu, huw, rfl⟩

/-- The preferential consequence relation induced by a ranking function.
    Composes `toPlausibilityOrder` with `PlausibilityOrder.toPreferential`. -/
def toPreferential (κ : RankingFunction W) : PreferentialConsequence W :=
  κ.toPlausibilityOrder.toPreferential

/-- Ranking functions induce **connected** (total) plausibility orderings:
    for any two worlds, one is at least as plausible as the other.

    This follows from ℕ being linearly ordered. Connectedness is what
    distinguishes ranked models from merely preferential models and
    is what makes Rational Monotonicity hold. -/
theorem ranking_connected (κ : RankingFunction W) :
    κ.toPlausibilityOrder.toNormalityOrder.connected := by
  intro w v
  show κ.rank w ≤ κ.rank v ∨ κ.rank v ≤ κ.rank w
  omega

-- ══════════════════════════════════════════════════════════════════════
-- § 1b. Conditioning Operations
-- ══════════════════════════════════════════════════════════════════════

/-- A,α-conditionalization: revise κ by evidence φ with firmness α.

    @cite{spohn-1988}, Definition 6: κ_{A,α}(w) = κ(w|A) for w ∈ A,
    and α + κ(w|Ā) for w ∈ Ā. The parameter α controls how firmly
    the evidence is believed:

    - α = 0: neutral update (evidence doesn't change relative
      plausibility of ¬φ-worlds vs φ-worlds)
    - α > 0: φ-worlds become more plausible than ¬φ-worlds by
      at least α ranks
    - Large α: very firm belief in the evidence

    Requires both φ and ¬φ to be satisfiable (matching Spohn's
    requirement that A ∉ {∅, W}). -/
noncomputable def conditionα [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w) (α : ℕ) : RankingFunction W :=
  let _instNeg : DecidablePred (fun w => ¬φ w) := fun w => instDecidableNot
  { rank := fun w =>
      if φ w then κ.rank w - κ.rankProp φ hφ
      else α + (κ.rank w - κ.rankProp (fun w => ¬φ w) hNφ)
    normalized := by
      classical
      have hne : (Finset.univ.filter (fun w => φ w)).Nonempty := by
        obtain ⟨w, hw⟩ := hφ
        exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
      obtain ⟨v, hv_mem, hv_min⟩ := Finset.exists_mem_eq_inf' hne κ.rank
      have hφv : φ v := (Finset.mem_filter.mp hv_mem).2
      refine ⟨v, ?_⟩
      simp only [if_pos hφv]
      show κ.rank v - κ.rankProp φ hφ = 0
      unfold rankProp
      rw [← hv_min]
      exact Nat.sub_self _ }

/-- Ranking functions satisfy Rational Monotonicity.

    Because ℕ is totally ordered, the induced plausibility ordering is
    **ranked** (any two worlds are comparable). For ranked models,
    Rational Monotonicity holds: if φ |~ χ and ¬(φ |~ ¬ψ), then
    (φ ∧ ψ) |~ χ.

    Proof sketch: From ¬(φ |~ ¬ψ), there exists a minimal φ-world v
    satisfying ψ. Since ℕ is total, every minimal (φ∧ψ)-world has
    rank ≤ rank of any φ-world. So minimal (φ∧ψ)-worlds are among
    the minimal φ-worlds, and since φ |~ χ, they satisfy χ. -/
theorem ranking_rationalMonotonicity (κ : RankingFunction W) :
    rationalMonotonicity κ.toPreferential := by
  intro φ ψ χ hφχ hnotφψ
  -- hφχ : all minimal-φ worlds satisfy χ
  -- hnotφψ : NOT all minimal-φ worlds satisfy ¬ψ
  -- Goal: all minimal-(φ∧ψ) worlds satisfy χ
  intro w ⟨⟨hφw, hψw⟩, hmin_φψ⟩
  -- w is a minimal (φ∧ψ)-world. Show w is also a minimal φ-world.
  apply hφχ
  constructor
  · exact hφw
  · -- w is minimal among φ-worlds: for any φ-world v with le v w, show le w v
    intro v hφv hvw
    -- hvw : κ.rank v ≤ κ.rank w. Need: κ.rank w ≤ κ.rank v.
    -- Since ¬(φ |~ ¬ψ), there exists a minimal φ-world u that satisfies ψ.
    obtain ⟨u, hu⟩ := Classical.not_forall.mp hnotφψ
    obtain ⟨hu_min, hψu⟩ := Classical.not_imp.mp hu
    have hψu : ψ u := Classical.not_not.mp hψu
    obtain ⟨hφu, hminu⟩ := hu_min
    -- u is φ-minimal; show rank u ≤ rank v using ℕ totality
    have huv : κ.rank u ≤ κ.rank v := by
      by_contra h
      push_neg at h
      -- h : κ.rank v < κ.rank u, so κ.rank v ≤ κ.rank u
      have hmv := hminu v hφv (show κ.rank v ≤ κ.rank u from Nat.le_of_lt h)
      change κ.rank u ≤ κ.rank v at hmv
      omega
    -- huv : κ.rank u ≤ κ.rank v, so κ.rank u ≤ κ.rank w
    have huw : κ.rank u ≤ κ.rank w := Nat.le_trans huv hvw
    -- u is a (φ∧ψ)-world, and w is (φ∧ψ)-minimal, so rank w ≤ rank u
    have hwu := hmin_φψ u ⟨hφu, hψu⟩ huw
    -- rank w ≤ rank u ≤ rank v, so rank w ≤ rank v
    show κ.rank w ≤ κ.rank v
    exact Nat.le_trans hwu huv

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Iterated Belief Revision (@cite{darwiche-pearl-1997})
-- ══════════════════════════════════════════════════════════════════════

/-- The belief set of a ranking function: propositions true at all
    rank-0 worlds. These are the agent's current beliefs. -/
def beliefSet (κ : RankingFunction W) : Set (W → Prop) :=
  { ψ | ∀ w, κ.rank w = 0 → ψ w }

/-- Darwiche-Pearl postulate C1: if φ → ψ then (κ *_{ψ,β} ) *_{φ,α} = κ *_{φ,α}.
    Revising first by a weaker ψ (with any firmness β), then by a
    stronger φ that entails it (with any firmness α), yields the same
    result as revising directly by φ with firmness α.

    For ranking conditioning: if every φ-world is a ψ-world, then
    conditioning on ψ first doesn't change the relative ranks among
    φ-worlds after subsequent φ-conditioning. -/
def satisfies_C1 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w)
    (hψ : ∃ w, ψ w) (hNψ : ∃ w, ¬ψ w)
    (himp : ∀ w, φ w → ψ w)
    (α β : ℕ),
    ∀ w, φ w →
      ((κ.conditionα ψ hψ hNψ β).conditionα φ hφ
        (by obtain ⟨w, hw⟩ := hNφ; exact ⟨w, hw⟩) α).rank w =
      (κ.conditionα φ hφ hNφ α).rank w

/-- Darwiche-Pearl postulate C2: if φ → ¬ψ then (κ *_{ψ,β} ) *_{φ,α} = κ *_{φ,α}.
    If φ and ψ are incompatible, revising by ψ first doesn't affect
    the outcome of subsequent revision by φ. -/
def satisfies_C2 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w)
    (hψ : ∃ w, ψ w) (hNψ : ∃ w, ¬ψ w)
    (hdisj : ∀ w, φ w → ¬ψ w)
    (α β : ℕ),
    ∀ w, φ w →
      ((κ.conditionα ψ hψ hNψ β).conditionα φ hφ
        (by obtain ⟨w, hw⟩ := hNφ; exact ⟨w, hw⟩) α).rank w =
      (κ.conditionα φ hφ hNφ α).rank w

/-- Darwiche-Pearl postulate C3: if ψ ∈ beliefSet(κ *_{φ,α}),
    then ψ ∈ beliefSet((κ *_{ψ,β}) *_{φ,α}).
    If ψ is believed after revising by φ, then revising first by ψ
    preserves this. -/
def satisfies_C3 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w)
    (hψ : ∃ w, ψ w) (hNψ : ∃ w, ¬ψ w)
    (α β : ℕ),
    (fun w => ψ w) ∈ (κ.conditionα φ hφ hNφ α).beliefSet →
    (fun w => ψ w) ∈ ((κ.conditionα ψ hψ hNψ β).conditionα φ hφ
      (by obtain ⟨w, hw⟩ := hNφ; exact ⟨w, hw⟩) α).beliefSet

/-- Darwiche-Pearl postulate C4: if ¬ψ ∉ beliefSet(κ *_{φ,α}),
    then ¬ψ ∉ beliefSet((κ *_{ψ,β}) *_{φ,α}).
    If ¬ψ is not believed after revising by φ, then revising first
    by ψ doesn't make ¬ψ believed either. -/
def satisfies_C4 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w)
    (hψ : ∃ w, ψ w) (hNψ : ∃ w, ¬ψ w)
    (α β : ℕ),
    (fun w => ¬ψ w) ∉ (κ.conditionα φ hφ hNφ α).beliefSet →
    (fun w => ¬ψ w) ∉ ((κ.conditionα ψ hψ hNψ β).conditionα φ hφ
      (by obtain ⟨w, hw⟩ := hNφ; exact ⟨w, hw⟩) α).beliefSet

/-- **Theorem**: Ranking conditioning satisfies C1.

    When φ → ψ, conditioning κ on ψ shifts all ψ-worlds (including
    all φ-worlds) down by κ(ψ). Then conditioning on φ shifts the
    φ-worlds down by the new κ_ψ(φ) = κ(φ) - κ(ψ). Net shift for
    φ-worlds: κ(w) - κ(ψ) - (κ(φ) - κ(ψ)) = κ(w) - κ(φ), which
    equals direct conditioning on φ.

    TODO: The arithmetic involves nested Finset.inf' and ℕ subtraction,
    requiring careful handling of the relationship between rankProp
    computations across nested conditionings. -/
theorem ranking_satisfies_C1 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C1 := by
  sorry

/-- **Theorem**: Ranking conditioning satisfies C2.

    When φ and ψ are disjoint, φ-worlds are ¬ψ-worlds. After
    conditioning on ψ with firmness β, φ-worlds are shifted up by
    β + (A-part relative to ¬ψ). Subsequent conditioning on φ
    normalizes away this shift: the relative ordering among
    φ-worlds depends only on their original ranks.

    TODO: Requires showing that the β-dependent shift cancels in the
    double-conditioning arithmetic. -/
theorem ranking_satisfies_C2 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C2 := by
  sorry

/-- **Theorem**: Ranking conditioning satisfies C3.

    TODO: Requires relating belief sets across conditioned rankings.
    The key insight is that if ψ holds at all rank-0 worlds of κ*φ,
    then after pre-conditioning on ψ (which makes ψ-worlds more
    plausible), the rank-0 worlds of (κ*ψ)*φ are a subset of the
    rank-0 worlds of κ*φ (or have the same ψ-status). -/
theorem ranking_satisfies_C3 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C3 := by
  sorry

/-- **Theorem**: Ranking conditioning satisfies C4.

    TODO: Dual of C3. If there exists a rank-0 world of κ*φ
    satisfying ψ (i.e., ¬ψ is not believed), then pre-conditioning
    on ψ preserves this witness. -/
theorem ranking_satisfies_C4 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C4 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Independence (@cite{spohn-1988}, Definition 8)
-- ══════════════════════════════════════════════════════════════════════

/-- Two propositions are **independent** with respect to κ iff
    κ(φ ∩ ψ) = κ(φ) + κ(ψ).

    @cite{spohn-1988}, Definition 8 (simplified from σ-fields to
    propositions). This is the ordinal analogue of probabilistic
    independence P(A ∩ B) = P(A) · P(B): where probability uses
    multiplication, ranking uses addition. -/
def independent [Fintype W] (κ : RankingFunction W)
    (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    [DecidablePred (fun w => φ w ∧ ψ w)]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w)
    (hφψ : ∃ w, φ w ∧ ψ w) : Prop :=
  κ.rankProp (fun w => φ w ∧ ψ w) hφψ = κ.rankProp φ hφ + κ.rankProp ψ hψ

end RankingFunction

end Core.Logic.Ranking
