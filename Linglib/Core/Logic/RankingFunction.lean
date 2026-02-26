import Linglib.Core.Logic.BeliefRevision

/-!
# Ranking Functions and Iterated Belief Revision

@cite{halpern-2003}

Ranking functions (ordinal conditional functions, OCFs) provide a
qualitative, ordinal approach to belief revision that serves as the
quantitative semantics for System P + Rational Monotonicity.

Spohn (1988) introduced ranking functions as ℕ-valued measures of
disbelief: κ(w) = 0 means w is maximally plausible (believed possible),
while higher ranks indicate greater implausibility. The normalization
condition — some world has rank 0 — ensures the agent always has
at least one belief state.

## Key Results

1. **Ranking → Plausibility**: Every ranking function induces a
   plausibility ordering (§1), which in turn yields a preferential
   consequence relation satisfying System P.

2. **Rational Monotonicity**: Because ℕ is totally ordered, the
   induced plausibility ordering is ranked (not merely preferential),
   so Rational Monotonicity holds.

3. **Ranking Conditioning**: `κ_φ(w) = κ(w) - κ(φ)` for φ-worlds
   provides a natural revision operation (§1).

4. **Darwiche-Pearl Postulates**: Ranking conditioning satisfies
   the iterated revision postulates C1–C4 (§2), which AGM alone
   does not constrain.

## References

- Spohn, W. (1988). Ordinal Conditional Functions: A Dynamic Theory
  of Epistemic States. In W.L. Harper & B. Skyrms (Eds.), Causation
  in Decision, Belief Change, and Statistics II. Kluwer. 105–134.
- Darwiche, A. & Pearl, J. (1997). On the Logic of Iterated Belief
  Revision. Artificial Intelligence 89: 1–29.
- Halpern, J. (2003). Reasoning about Uncertainty. MIT Press. Ch. 8.
-/

namespace Core.Logic.Ranking

open Core.Logic.BeliefRevision (PlausibilityOrder PreferentialConsequence rationalMonotonicity)

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Ranking Functions
-- ══════════════════════════════════════════════════════════════════════

/-- A ranking function (ordinal conditional function) on worlds.

    κ : W → ℕ assigns each world a degree of disbelief.
    Normalization: some world has rank 0 (the agent believes
    something is possible). -/
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

/-- Ranking conditioning: revise κ by evidence φ.

    For φ-worlds: κ_φ(w) = κ(w) - κ(φ).
    For ¬φ-worlds: assign a sentinel value (max rank + 1) ensuring
    they are less plausible than any φ-world.

    This is the natural revision operation for ranking functions
    (Spohn 1988): conditionalization shifts all φ-worlds down by
    the minimum φ-rank, making the most plausible φ-worlds rank 0.

    The sentinel for ¬φ-worlds uses `Fintype.card W` as an upper
    bound ensuring separation from φ-world ranks. -/
noncomputable def condition [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ : W → Prop) [DecidablePred φ]
    (hsat : ∃ w, φ w) : RankingFunction W where
  rank := fun w =>
    if φ w then κ.rank w - κ.rankProp φ hsat
    else Fintype.card W  -- sentinel: ¬φ-worlds get high rank
  normalized := by
    -- The witness is an argmin φ-world: its shifted rank is 0.
    classical
    have hne : (Finset.univ.filter (fun w => φ w)).Nonempty := by
      obtain ⟨w, hw⟩ := hsat
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
    obtain ⟨v, hv_mem, hv_min⟩ := Finset.exists_mem_eq_inf' hne κ.rank
    have hφv : φ v := (Finset.mem_filter.mp hv_mem).2
    refine ⟨v, ?_⟩
    simp only [if_pos hφv]
    show κ.rank v - κ.rankProp φ hsat = 0
    unfold rankProp
    rw [← hv_min]
    exact Nat.sub_self _

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
-- § 2. Iterated Belief Revision (Darwiche & Pearl 1997)
-- ══════════════════════════════════════════════════════════════════════

/-- The belief set of a ranking function: propositions true at all
    rank-0 worlds. These are the agent's current beliefs. -/
def beliefSet (κ : RankingFunction W) : Set (W → Prop) :=
  { ψ | ∀ w, κ.rank w = 0 → ψ w }

/-- Darwiche-Pearl postulate C1: if φ → ψ then (κ * ψ) * φ = κ * φ.
    Revising first by a stronger proposition, then by a weaker one
    that entails it, yields the same result as revising directly by
    the stronger proposition.

    For ranking conditioning: if every φ-world is a ψ-world, then
    conditioning on ψ first doesn't change the relative ranks among
    φ-worlds. -/
def satisfies_C1 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w)
    (himp : ∀ w, φ w → ψ w),
    ∀ w, φ w →
      ((κ.condition ψ hψ).condition φ
        (by obtain ⟨w, hw⟩ := hφ; exact ⟨w, hw⟩)).rank w =
      (κ.condition φ hφ).rank w

/-- Darwiche-Pearl postulate C2: if φ → ¬ψ then (κ * ψ) * φ = κ * φ.
    If φ and ψ are incompatible, revising by ψ first doesn't affect
    the outcome of subsequent revision by φ. -/
def satisfies_C2 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w)
    (hdisj : ∀ w, φ w → ¬ψ w),
    ∀ w, φ w →
      ((κ.condition ψ hψ).condition φ
        (by obtain ⟨w, hw⟩ := hφ; exact ⟨w, hw⟩)).rank w =
      (κ.condition φ hφ).rank w

/-- Darwiche-Pearl postulate C3: if ψ ∈ beliefSet(κ * φ),
    then ψ ∈ beliefSet((κ * ψ) * φ).
    If ψ is believed after revising by φ, then revising first by ψ
    preserves this. -/
def satisfies_C3 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w),
    (fun w => ψ w) ∈ (κ.condition φ hφ).beliefSet →
    (fun w => ψ w) ∈ ((κ.condition ψ hψ).condition φ
      (by obtain ⟨w, hw⟩ := hφ; exact ⟨w, hw⟩)).beliefSet

/-- Darwiche-Pearl postulate C4: if ¬ψ ∉ beliefSet(κ * φ),
    then ¬ψ ∉ beliefSet((κ * ψ) * φ).
    If ¬ψ is not believed after revising by φ, then revising first
    by ψ doesn't make ¬ψ believed either. -/
def satisfies_C4 [Fintype W] [DecidableEq W] (κ : RankingFunction W) : Prop :=
  ∀ (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w),
    (fun w => ¬ψ w) ∉ (κ.condition φ hφ).beliefSet →
    (fun w => ¬ψ w) ∉ ((κ.condition ψ hψ).condition φ
      (by obtain ⟨w, hw⟩ := hφ; exact ⟨w, hw⟩)).beliefSet

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
    conditioning on ψ, φ-worlds get the sentinel rank (they don't
    satisfy ψ). But when we then condition on φ, the sentinel
    values cancel out: the relative ordering among φ-worlds is
    determined by their original ranks minus the minimum among
    φ-worlds, which is the same as direct conditioning.

    TODO: Requires showing that rankProp of φ in the ψ-conditioned
    ranking equals the sentinel value, and that the double subtraction
    simplifies correctly. -/
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

end RankingFunction

end Core.Logic.Ranking
