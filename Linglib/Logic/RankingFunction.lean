import Linglib.Core.Order.Plausibility
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ranking Functions and Iterated Belief Revision

[halpern-2003] [darwiche-pearl-1997] [spohn-1988]

Ranking functions (ordinal conditional functions, OCFs) provide a
qualitative, ordinal approach to belief revision that serves as the
quantitative semantics for System P + Rational Monotonicity.

[spohn-1988] introduced ranking functions as ordinal-valued measures
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

6. **Revision** (§2): Spohn revision with canonical firmness κ(¬φ) + 1
   and the belief set of a ranking. Its iterated-revision postulates are
   in `Logic/BeliefRevision/Iterated.lean`, where it is `BeliefRevision.spohn`.

See `Spohn1988` for a verified
concrete instance demonstrating evidence strength, commutativity
(Theorem 4), and the connection to `NormalityOrder`.

## Bridge to Probability ([spohn-1988] §7)

Ranking conditioning is the ordinal analogue of Bayesian conditioning.
The structural parallel (min/+ for ordinals mirrors product/sum for
probabilities):

| Probability (ℚ, ·, Σ)         | Ranking (ℕ, min, +)              |
|-------------------------------|----------------------------------|
| P(A) = Σ_{w∈A} P(w)          | κ(A) = min_{w∈A} κ(w)           |
| P(A|B) = P(A∩B)/P(B)         | κ(w|A) = κ(w) - κ(A)            |
| P(A∩B) = P(A)·P(B|A)         | κ(A∩B) = κ(A) + κ(B|A)          |
| P(A∩B) = P(A)·P(B) (indep.)  | κ(A∩B) = κ(A) + κ(B) (indep.)   |

-/


open Core.Order (PlausibilityOrder PreferentialConsequence rationalMonotonicity)

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Ranking Functions
-- ══════════════════════════════════════════════════════════════════════

/-- A ranking function (ordinal conditional function) on worlds.

    κ : W → ℕ assigns each world a degree of disbelief.
    Normalization: some world has rank 0 (the agent considers at least
    one world possible).

    [spohn-1988], Definition 4 uses ordinals in the general case;
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

    [spohn-1988], Definition 5: κ(w|A) = κ(w) - κ(A) for w ∈ A.
    This is the primitive from which conditioning derives. -/
noncomputable def aPart [Fintype W] (κ : RankingFunction W) (φ : W → Prop)
    [DecidablePred φ] (hφ : ∃ w, φ w) (w : W) : ℕ :=
  κ.rank w - κ.rankProp φ hφ

/-- [spohn-1988], Theorem 2(a): For any proposition, either it
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

/-- [spohn-1988], Theorem 2(b): The rank of a disjunction is
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
  toPreorder := Preorder.lift κ.rank
  smooth := fun φ w hφw => by
    classical
    show ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧
      ∀ u, φ u → κ.rank u ≤ κ.rank v → κ.rank v ≤ κ.rank u
    -- Among φ-worlds with rank ≤ κ(w), find one with minimal rank (via `Nat.find`).
    let minRank := Nat.find (⟨κ.rank w, w, hφw, Nat.le_refl _, rfl⟩ :
      ∃ n, ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧ κ.rank v = n)
    obtain ⟨v, hφv, hvw, hvrank⟩ := Nat.find_spec (⟨κ.rank w, w, hφw, Nat.le_refl _, rfl⟩ :
      ∃ n, ∃ v, φ v ∧ κ.rank v ≤ κ.rank w ∧ κ.rank v = n)
    refine ⟨v, hφv, hvw, ?_⟩
    intro u hφu huv
    -- huv : κ(u) ≤ κ(v), need: κ(v) ≤ κ(u)
    -- If κ(u) < κ(v) = minRank, that contradicts minimality of minRank
    by_contra h
    push Not at h
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
    Core.Order.Normality.connected κ.toPlausibilityOrder.toPreorder := by
  intro w v
  show κ.rank w ≤ κ.rank v ∨ κ.rank v ≤ κ.rank w
  omega

-- ══════════════════════════════════════════════════════════════════════
-- § 1b. Conditioning Operations
-- ══════════════════════════════════════════════════════════════════════

/-- A,α-conditionalization: revise κ by evidence φ with firmness α.

    [spohn-1988], Definition 6: κ_{A,α}(w) = κ(w|A) for w ∈ A,
    and α + κ(w|Ā) for w ∈ Ā. The parameter α controls how firmly
    the evidence is believed:

    - α = 0: neutral update (evidence doesn't change relative
      plausibility of ¬φ-worlds vs φ-worlds)
    - α > 0: φ-worlds become more plausible than ¬φ-worlds by
      at least α ranks
    - Large α: very firm belief in the evidence

    [goldszmidt-pearl-1996] call this **J-conditioning** (after
    Jeffrey); the operation is identical under the name change α = j.

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
      push Not at h
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
-- § 2. Revision
-- ══════════════════════════════════════════════════════════════════════

/-- The belief set of a ranking function: propositions true at all
    rank-0 worlds. These are the agent's current beliefs. -/
def beliefSet (κ : RankingFunction W) : Set (W → Prop) :=
  { ψ | ∀ w, κ.rank w = 0 → ψ w }

/-- Spohn revision: α-conditionalization with canonical firmness
    α = κ(¬φ) + 1.

    This is the standard belief-revision operator for ranking functions
    ([spohn-1988]). The firmness is determined by the current
    ranking, not a free parameter: the agent revises just firmly enough
    to make φ believed (the success postulate). On a contingent φ it is
    [darwiche-pearl-1997]'s operator `BeliefRevision.spohn`
    (`RankingFunction.revise_rank`). -/
noncomputable def revise [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w) : RankingFunction W :=
  have : DecidablePred (fun w => ¬φ w) := fun w => instDecidableNot
  κ.conditionα φ hφ hNφ (κ.rankProp (fun w => ¬φ w) hNφ + 1)

/-- `rankProp` is ≤ any satisfying world's rank. -/
theorem rankProp_le_rank [Fintype W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hsat : ∃ w, φ w) (w : W) (hw : φ w) :
    κ.rankProp φ hsat ≤ κ.rank w := by
  unfold rankProp
  exact Finset.inf'_le κ.rank (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Independence ([spohn-1988], Definition 8)
-- ══════════════════════════════════════════════════════════════════════

/-- Two propositions are **independent** with respect to κ iff
    κ(φ ∩ ψ) = κ(φ) + κ(ψ).

    [spohn-1988], Definition 8 (simplified from σ-fields to
    propositions). This is the ordinal analogue of probabilistic
    independence P(A ∩ B) = P(A) · P(B): where probability uses
    multiplication, ranking uses addition. -/
def independent [Fintype W] (κ : RankingFunction W)
    (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    [DecidablePred (fun w => φ w ∧ ψ w)]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w)
    (hφψ : ∃ w, φ w ∧ ψ w) : Prop :=
  κ.rankProp (fun w => φ w ∧ ψ w) hφψ = κ.rankProp φ hφ + κ.rankProp ψ hψ

/-- **L-conditioning**: shift-based belief revision.

    [goldszmidt-pearl-1996], Eqs. 29–30: L-conditioning with l ≥ 0
    keeps φ-worlds at their original rank and shifts ¬φ-worlds up by l.
    Unlike J-conditioning (`conditionα`), L-conditioning is commutative:
    κ_{A,l₁}_{B,l₂} = κ_{B,l₂}_{A,l₁}.

    This is the κ(φ) = 0 specialization of the general L-conditioning
    (G&P Eq. 32). The general form subtracts κ(φ) from all worlds first,
    but the precondition `h0 : ∃ w, φ w ∧ κ.rank w = 0` guarantees
    κ(φ) = 0, so the subtraction vanishes for φ-worlds. -/
noncomputable def lCondition [Fintype W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (h0 : ∃ w, φ w ∧ κ.rank w = 0) (l : ℕ) : RankingFunction W where
  rank w := if φ w then κ.rank w else κ.rank w + l
  normalized := by
    obtain ⟨w₀, hφ, hr⟩ := h0
    exact ⟨w₀, show _ = 0 by rw [if_pos hφ]; exact hr⟩

/-- **AGM success postulate** (K*2): after revision by φ, the evidence
    φ is believed (all rank-0 worlds satisfy φ).

    [goldszmidt-pearl-1996] §6: ranking revision satisfies the AGM
    postulates. The proof is direct: ¬φ-worlds receive rank ≥ α =
    κ(¬φ) + 1 ≥ 1, so they cannot be rank-0 in the revised ranking. -/
theorem revise_success [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hφ : ∃ w, φ w) (hNφ : ∃ w, ¬φ w) :
    φ ∈ (κ.revise φ hφ hNφ).beliefSet := by
  intro w hw
  by_contra hNφw
  have : (κ.revise φ hφ hNφ).rank w ≥ 1 := by
    unfold revise conditionα; simp only [if_neg hNφw]
    have := rankProp_le_rank κ (fun w => ¬φ w) hNφ w hNφw
    omega
  omega

end RankingFunction

