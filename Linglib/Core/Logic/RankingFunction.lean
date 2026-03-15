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
theorem rankProp_union [Fintype W] (κ : RankingFunction W)
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

/-- Spohn revision: α-conditionalization with canonical firmness
    α = κ(¬φ) + 1.

    This is the standard belief-revision operator for ranking functions
    (@cite{spohn-1988}). The firmness is determined by the current
    ranking, not a free parameter: the agent revises just firmly enough
    to make φ believed (the success postulate).

    C1 and C2 hold for `conditionα` with arbitrary α, β. C3 and C4
    require the canonical firmness — a counterexample with α = β = 1
    on a 4-world ranking shows the universally-quantified version is
    false. -/
noncomputable def revise [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w) : RankingFunction W :=
  have : DecidablePred (fun w => ¬φ w) := fun w => instDecidableNot
  κ.conditionα φ hφ hNφ (κ.rankProp (fun w => ¬φ w) hNφ + 1)

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

/-- Darwiche-Pearl postulate C3: if ψ ∈ beliefSet(κ * φ),
    then ψ ∈ beliefSet((κ * ψ) * φ).
    If ψ is believed after revising by φ, then revising first by ψ
    preserves this.

    Uses the canonical `revise` operator (firmness = κ(¬φ) + 1).
    The version with arbitrary firmness parameters is false — see
    the `revise` docstring. -/
def satisfies_C3 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w)
    (hψ : ∃ w, ψ w) (hNψ : ∃ w, ¬ψ w),
    (fun w => ψ w) ∈ (κ.revise φ hφ hNφ).beliefSet →
    (fun w => ψ w) ∈ ((κ.revise ψ hψ hNψ).revise φ hφ hNφ).beliefSet

/-- Darwiche-Pearl postulate C4: if ¬ψ ∉ beliefSet(κ * φ),
    then ¬ψ ∉ beliefSet((κ * ψ) * φ).
    If ¬ψ is not believed after revising by φ, then revising first
    by ψ doesn't make ¬ψ believed either.

    Uses the canonical `revise` operator (firmness = κ(¬φ) + 1). -/
def satisfies_C4 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w)
    (hψ : ∃ w, ψ w) (hNψ : ∃ w, ¬ψ w),
    (fun w => ¬ψ w) ∉ (κ.revise φ hφ hNφ).beliefSet →
    (fun w => ¬ψ w) ∉ ((κ.revise ψ hψ hNψ).revise φ hφ hNφ).beliefSet

/-- `rankProp` is ≤ any satisfying world's rank. -/
private theorem rankProp_le_rank [Fintype W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hsat : ∃ w, φ w) (w : W) (hw : φ w) :
    κ.rankProp φ hsat ≤ κ.rank w := by
  unfold rankProp
  exact Finset.inf'_le κ.rank (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)

/-- If φ ⊆ ψ, then `rankProp ψ ≤ rankProp φ` (min over superset ≤ min over subset). -/
private theorem rankProp_anti [Fintype W]
    (κ : RankingFunction W) (φ ψ : W → Prop)
    [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w)
    (himp : ∀ w, φ w → ψ w) :
    κ.rankProp ψ hψ ≤ κ.rankProp φ hφ := by
  unfold rankProp
  apply Finset.le_inf'
  intro v hv
  have hφv := (Finset.mem_filter.mp hv).2
  exact Finset.inf'_le κ.rank (Finset.mem_filter.mpr ⟨Finset.mem_univ v, himp v hφv⟩)

set_option maxHeartbeats 800000 in
/-- **Theorem**: Ranking conditioning satisfies C1.

    When φ → ψ, conditioning κ on ψ shifts all ψ-worlds (including
    all φ-worlds) down by κ(ψ). Then conditioning on φ shifts the
    φ-worlds down by the new κ_ψ(φ) = κ(φ) - κ(ψ). Net shift for
    φ-worlds: κ(w) - κ(ψ) - (κ(φ) - κ(ψ)) = κ(w) - κ(φ), which
    equals direct conditioning on φ. -/
theorem ranking_satisfies_C1 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C1 := by
  intro φ ψ _ _ hφ hNφ hψ hNψ himp α β w hφw
  have hψw : ψ w := himp w hφw
  set κ' := κ.conditionα ψ hψ hNψ β
  have h_κ'_at_φ : ∀ v, φ v → κ'.rank v = κ.rank v - κ.rankProp ψ hψ := by
    intro v hφv; simp only [κ', conditionα, if_pos (himp v hφv)]
  have h_κ'_rankProp : κ'.rankProp φ hφ = κ.rankProp φ hφ - κ.rankProp ψ hψ := by
    apply Nat.le_antisymm
    · have hne : (Finset.univ.filter fun w => φ w).Nonempty := by
        obtain ⟨w, hw⟩ := hφ; exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
      obtain ⟨v₀, hv₀_mem, hv₀_eq⟩ := Finset.exists_mem_eq_inf' hne κ.rank
      have hφv₀ := (Finset.mem_filter.mp hv₀_mem).2
      calc κ'.rankProp φ hφ
          ≤ κ'.rank v₀ := rankProp_le_rank κ' φ hφ v₀ hφv₀
        _ = κ.rank v₀ - κ.rankProp ψ hψ := h_κ'_at_φ v₀ hφv₀
        _ = κ.rankProp φ hφ - κ.rankProp ψ hψ := by
            congr 1; unfold rankProp; exact hv₀_eq.symm
    · unfold rankProp
      apply Finset.le_inf'
      intro v hv
      rw [h_κ'_at_φ v (Finset.mem_filter.mp hv).2]
      exact Nat.sub_le_sub_right (rankProp_le_rank κ φ hφ v (Finset.mem_filter.mp hv).2) _
  have h_lhs : (κ'.conditionα φ hφ (by obtain ⟨w, hw⟩ := hNφ; exact ⟨w, hw⟩) α).rank w =
      κ'.rank w - κ'.rankProp φ hφ := by
    simp only [conditionα, if_pos hφw]
  have h_rhs : (κ.conditionα φ hφ hNφ α).rank w = κ.rank w - κ.rankProp φ hφ := by
    simp only [conditionα, if_pos hφw]
  rw [h_lhs, h_rhs, h_κ'_at_φ w hφw, h_κ'_rankProp]
  have h1 : κ.rankProp ψ hψ ≤ κ.rankProp φ hφ := rankProp_anti κ φ ψ hφ hψ himp
  have h2 : κ.rankProp φ hφ ≤ κ.rank w := rankProp_le_rank κ φ hφ w hφw
  omega

set_option maxHeartbeats 800000 in
/-- **Theorem**: Ranking conditioning satisfies C2.

    When φ and ψ are disjoint, φ-worlds are ¬ψ-worlds. After
    conditioning on ψ with firmness β, φ-worlds are shifted up by
    β + (A-part relative to ¬ψ). Subsequent conditioning on φ
    normalizes away this shift: the relative ordering among
    φ-worlds depends only on their original ranks. -/
theorem ranking_satisfies_C2 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C2 := by
  intro φ ψ _ _ hφ hNφ hψ hNψ hdisj α β w hφw
  set κ' := κ.conditionα ψ hψ hNψ β
  have h_κ'_at_φ : ∀ v, φ v →
      κ'.rank v = β + (κ.rank v - κ.rankProp (fun w => ¬ψ w) hNψ) := by
    intro v hφv; simp only [κ', conditionα, if_neg (hdisj v hφv)]
  have h_κ'_rankProp : κ'.rankProp φ hφ =
      β + (κ.rankProp φ hφ - κ.rankProp (fun w => ¬ψ w) hNψ) := by
    apply Nat.le_antisymm
    · have hne : (Finset.univ.filter fun w => φ w).Nonempty := by
        obtain ⟨w, hw⟩ := hφ; exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
      obtain ⟨v₀, hv₀_mem, hv₀_eq⟩ := Finset.exists_mem_eq_inf' hne κ.rank
      have hφv₀ := (Finset.mem_filter.mp hv₀_mem).2
      calc κ'.rankProp φ hφ
          ≤ κ'.rank v₀ := rankProp_le_rank κ' φ hφ v₀ hφv₀
        _ = β + (κ.rank v₀ - κ.rankProp (fun w => ¬ψ w) hNψ) := h_κ'_at_φ v₀ hφv₀
        _ = β + (κ.rankProp φ hφ - κ.rankProp (fun w => ¬ψ w) hNψ) := by
            congr 1; congr 1; unfold rankProp; exact hv₀_eq.symm
    · unfold rankProp
      apply Finset.le_inf'
      intro v hv
      rw [h_κ'_at_φ v (Finset.mem_filter.mp hv).2]
      exact Nat.add_le_add_left
        (Nat.sub_le_sub_right (rankProp_le_rank κ φ hφ v (Finset.mem_filter.mp hv).2) _) _
  -- Both conditionα pick if-true for φ w. Show the rank expressions are equal.
  suffices κ'.rank w - κ'.rankProp φ hφ = κ.rank w - κ.rankProp φ hφ by
    show (κ'.conditionα φ hφ _ α).rank w = (κ.conditionα φ hφ hNφ α).rank w
    simp only [conditionα, if_pos hφw]; exact this
  have h1 := h_κ'_at_φ w hφw
  have h2 := h_κ'_rankProp
  -- h1: κ'.rank w = β + (κ.rank w - rp(¬ψ))
  -- h2: κ'.rankProp φ = β + (rp(φ) - rp(¬ψ))
  rw [h1, h2]
  have h3 : κ.rankProp φ hφ ≤ κ.rank w := rankProp_le_rank κ φ hφ w hφw
  have h4 : κ.rankProp (fun w => ¬ψ w) hNψ ≤ κ.rankProp φ hφ :=
    rankProp_anti κ φ (fun w => ¬ψ w) hφ hNψ hdisj
  omega

set_option maxHeartbeats 800000 in
/-- **Theorem**: Ranking conditioning satisfies C3.

    If w is rank-0 in (κ*ψ)*φ but ¬ψ w, then κ'(w) = κ(w) + 1
    (¬ψ-worlds are penalized by revise). But the hypothesis gives
    a witness v₀ with φ v₀, ψ v₀, κ(v₀) = κ(φ), so κ'(v₀) =
    κ(v₀) − κ(ψ) ≤ κ(φ) ≤ κ(w) < κ(w) + 1 = κ'(w), contradicting
    w being rank-minimal among φ-worlds in κ'. -/
theorem ranking_satisfies_C3 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C3 := by
  intro φ ψ _ _ hφ hNφ hψ hNψ hbel
  unfold beliefSet at hbel ⊢
  simp only [Set.mem_setOf_eq] at hbel ⊢
  intro w hw
  by_contra hψw
  -- Step 1: w must satisfy φ (¬φ-worlds have rank ≥ 1 in any revise)
  have hφw : φ w := by
    by_contra hNφw
    have : ((κ.revise ψ hψ hNψ).revise φ hφ hNφ).rank w ≥ 1 := by
      unfold revise conditionα; simp only [if_neg hNφw]
      have := rankProp_le_rank (κ.revise ψ hψ hNψ) (fun w => ¬φ w) hNφ w hNφw
      omega
    omega
  -- Step 2: rank 0 at φ-world means κ'(w) = κ'.rankProp(φ)
  have h_outer : ((κ.revise ψ hψ hNψ).revise φ hφ hNφ).rank w =
      (κ.revise ψ hψ hNψ).rank w - (κ.revise ψ hψ hNψ).rankProp φ hφ := by
    unfold revise conditionα; simp only [if_pos hφw]
  have h_ge := rankProp_le_rank (κ.revise ψ hψ hNψ) φ hφ w hφw
  -- κ'(w) = κ'.rankProp φ
  have h_κ'w_eq : (κ.revise ψ hψ hNψ).rank w = (κ.revise ψ hψ hNψ).rankProp φ hφ := by
    omega
  -- Step 3: ¬ψ w means κ'(w) = κ(w) + 1
  have h_Nψ : (κ.revise ψ hψ hNψ).rank w = κ.rank w + 1 := by
    unfold revise conditionα; simp only [if_neg hψw]
    have := rankProp_le_rank κ (fun w => ¬ψ w) hNψ w hψw
    omega
  -- Step 4: find v₀ — a min-rank φ-world, which satisfies ψ by hypothesis
  have hne : (Finset.univ.filter (fun w => φ w)).Nonempty := by
    obtain ⟨w₁, hw₁⟩ := hφ; exact ⟨w₁, Finset.mem_filter.mpr ⟨Finset.mem_univ w₁, hw₁⟩⟩
  obtain ⟨v₀, hv₀_mem, hv₀_eq⟩ := Finset.exists_mem_eq_inf' hne κ.rank
  have hφv₀ := (Finset.mem_filter.mp hv₀_mem).2
  have hv₀_rank : κ.rank v₀ = κ.rankProp φ hφ := by unfold rankProp; exact hv₀_eq.symm
  -- v₀ has rank 0 in κ.revise φ, so ψ v₀ by hypothesis
  have hψv₀ : ψ v₀ := by
    apply hbel; show (κ.revise φ hφ hNφ).rank v₀ = 0
    unfold revise conditionα; simp only [if_pos hφv₀]
    rw [hv₀_rank]; exact Nat.sub_self _
  -- Step 5: κ'(v₀) = κ(v₀) - κ(ψ)
  have h_κ'v₀ : (κ.revise ψ hψ hNψ).rank v₀ = κ.rank v₀ - κ.rankProp ψ hψ := by
    unfold revise conditionα; simp only [if_pos hψv₀]
  -- Step 6: κ'.rankProp(φ) ≤ κ'(v₀) ≤ κ(v₀) = κ.rankProp(φ) ≤ κ(w)
  have h_rp_le := rankProp_le_rank (κ.revise ψ hψ hNψ) φ hφ v₀ hφv₀
  have h_rpφ_le_w := rankProp_le_rank κ φ hφ w hφw
  -- Contradiction: κ(w) + 1 ≤ κ(v₀) - κ(ψ) ≤ κ(v₀) = κ.rankProp(φ) ≤ κ(w)
  omega

set_option maxHeartbeats 800000 in
/-- **Theorem**: Ranking conditioning satisfies C4.

    The hypothesis gives v₀ with rank 0 in κ*φ and ψ v₀. We show
    v₀ also has rank 0 in (κ*ψ)*φ: since ψ v₀, κ'(v₀) =
    κ(v₀) − κ(ψ), and this is minimal among φ-worlds in κ' because
    φ∧ψ-worlds have κ' ≥ κ(φ) − κ(ψ) = κ'(v₀) and φ∧¬ψ-worlds
    have κ' = κ(w) + 1 > κ(φ) ≥ κ'(v₀). -/
theorem ranking_satisfies_C4 [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) : κ.satisfies_C4 := by
  intro φ ψ _ _ hφ hNφ hψ hNψ hNbel
  unfold beliefSet at hNbel ⊢
  simp only [Set.mem_setOf_eq] at hNbel ⊢
  push_neg at hNbel ⊢
  -- hNbel : ∃ w, (κ.revise φ).rank w = 0 ∧ ψ w
  obtain ⟨v₀, hv₀_rank, hψv₀⟩ := hNbel
  -- Step 1: φ v₀
  have hφv₀ : φ v₀ := by
    by_contra h
    have : (κ.revise φ hφ hNφ).rank v₀ ≥ 1 := by
      unfold revise conditionα; simp only [if_neg h]
      have := rankProp_le_rank κ (fun w => ¬φ w) hNφ v₀ h
      omega
    omega
  -- Step 2: κ(v₀) = κ.rankProp φ
  have hv₀_eq : κ.rank v₀ = κ.rankProp φ hφ := by
    have h1 : (κ.revise φ hφ hNφ).rank v₀ = κ.rank v₀ - κ.rankProp φ hφ := by
      unfold revise conditionα; simp only [if_pos hφv₀]
    have h2 := rankProp_le_rank κ φ hφ v₀ hφv₀
    omega
  -- Step 3: κ'(v₀) = κ(v₀) - κ(ψ) (since ψ v₀)
  have h_κ'v₀ : (κ.revise ψ hψ hNψ).rank v₀ = κ.rank v₀ - κ.rankProp ψ hψ := by
    unfold revise conditionα; simp only [if_pos hψv₀]
  -- Step 4: v₀ achieves the minimum rank among φ-worlds under κ'
  have h_v₀_min : (κ.revise ψ hψ hNψ).rankProp φ hφ = (κ.revise ψ hψ hNψ).rank v₀ := by
    apply Nat.le_antisymm
    · exact rankProp_le_rank (κ.revise ψ hψ hNψ) φ hφ v₀ hφv₀
    · unfold rankProp; apply Finset.le_inf'; intro u hu
      have hφu := (Finset.mem_filter.mp hu).2
      have h_u_ge := rankProp_le_rank κ φ hφ u hφu
      by_cases hψu : ψ u
      · -- ψ u: κ'(u) = κ(u) - κ(ψ) ≥ κ(v₀) - κ(ψ) = κ'(v₀)
        have h_κ'u : (κ.revise ψ hψ hNψ).rank u = κ.rank u - κ.rankProp ψ hψ := by
          unfold revise conditionα; simp only [if_pos hψu]
        rw [h_κ'v₀, h_κ'u, hv₀_eq]
        exact Nat.sub_le_sub_right h_u_ge _
      · -- ¬ψ u: κ'(u) = κ(u) + 1 > κ(v₀) - κ(ψ) = κ'(v₀)
        have h_κ'u : (κ.revise ψ hψ hNψ).rank u = κ.rank u + 1 := by
          unfold revise conditionα; simp only [if_neg hψu]
          have := rankProp_le_rank κ (fun w => ¬ψ w) hNψ u hψu
          omega
        rw [h_κ'v₀, h_κ'u, hv₀_eq]; omega
  -- Step 5: v₀ has rank 0 in (κ.revise ψ).revise φ
  refine ⟨v₀, ?_, hψv₀⟩
  have h_final : ((κ.revise ψ hψ hNψ).revise φ hφ hNφ).rank v₀ =
      (κ.revise ψ hψ hNψ).rank v₀ - (κ.revise ψ hψ hNψ).rankProp φ hφ := by
    unfold revise conditionα; simp only [if_pos hφv₀]
  rw [h_final, h_v₀_min]
  exact Nat.sub_self _

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
