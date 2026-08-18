import Linglib.Phonology.HarmonicGrammar.OTLimit
import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Realization problems and the cumulativity gap

Harmonic Grammar with non-negative weights is strictly more expressive than
Optimality Theory ([pater-2009]; [coetzee-pater-2011]): every OT-realizable
input→output mapping is HG-realizable via exponentially separated weights,
but sums of low-weight violations can overpower a single high-weight
violation — *cumulativity* — which no ranking expresses. The gap is
systemic, appearing only when several inputs constrain a shared grammar.

## Main definitions

- `RealizationProblem`: inputs, per-input candidates, violation profiles, and
  the target mapping a grammar must realize.
- `RealizationProblem.IsHGRealizable`, `RealizationProblem.IsOTRealizable`:
  realizability by a non-negative weighting / by a constraint ranking.
- `RealizationProblem.ercs`: the problem's winner–loser ERCs, one comparative
  row per input and competitor ([prince-2002]).

## Main results

- `RealizationProblem.realizedByRanking_iff_satisfiedBy`: OT-realization is
  ERC satisfaction, so OT-realizability is consistency of the problem's
  ERC set (`isOTRealizable_iff_linearExtensions_nonempty`; [prince-2002]).
- `RealizationProblem.IsOTRealizable.isHGRealizable`: OT ⊆ HG.
- `hg_strictly_contains_ot`: the containment is strict — the witness is
  [coetzee-pater-2011]'s abstract Lyman's Law instance (eq 18-19, after
  [ito-mester-1986]).
-/

namespace HarmonicGrammar

open Constraints Finset OptimalityTheory

variable {Input Output : Type*} {n : ℕ}

/-! ### Realization problems -/

/-- A multi-input optimization problem: a target mapping that a single
    grammar must realize for every input simultaneously. -/
structure RealizationProblem (Input : Type*) (Output : Type*) (n : ℕ) where
  /-- The set of inputs the grammar handles. -/
  inputs : Finset Input
  /-- Candidate set for each input. -/
  cands : Input → Finset Output
  /-- Violation profile: `vp i o k` is the count of constraint `k` violations
      incurred by output `o` from input `i`. -/
  vp : Input → Output → Fin n → ℕ
  /-- The output the grammar must select for each input. -/
  target : Input → Output
  /-- Each target output is in its input's candidate set. -/
  target_mem : ∀ i ∈ inputs, target i ∈ cands i

namespace RealizationProblem

/-- `w` *HG-realizes* the target: for every input, the target strictly
    minimizes the weighted violation sum among candidates. -/
def realizedByWeighting (P : RealizationProblem Input Output n) (w : Fin n → ℝ) : Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    weightedViolations w (P.vp i (P.target i)) <
    weightedViolations w (P.vp i o)

/-- Some non-negative weighting realizes the target. Non-negativity is
    [pater-2009]'s standard HG; [coetzee-pater-2011] §4.4 discusses negative
    weights. -/
def IsHGRealizable (P : RealizationProblem Input Output n) : Prop :=
  ∃ w : Fin n → ℝ, (∀ k, 0 ≤ w k) ∧ P.realizedByWeighting w

/-- `σ` *OT-realizes* the target: for every input, the target strictly
    lex-dominates every alternative under the ranking `σ`. -/
def realizedByRanking (P : RealizationProblem Input Output n) (σ : Ranking n) : Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    toLex (fun k : Fin n => P.vp i (P.target i) (σ k)) <
    toLex (fun k : Fin n => P.vp i o (σ k))

/-- Some constraint ranking realizes the target. -/
def IsOTRealizable (P : RealizationProblem Input Output n) : Prop :=
  ∃ σ : Ranking n, P.realizedByRanking σ

instance [DecidableEq Output] (P : RealizationProblem Input Output n) (σ : Ranking n) :
    Decidable (P.realizedByRanking σ) := by
  unfold realizedByRanking; infer_instance

instance [DecidableEq Output] (P : RealizationProblem Input Output n) :
    Decidable P.IsOTRealizable := by
  unfold IsOTRealizable; infer_instance

/-- `σ` OT-realizes `P` iff for every input the target is the unique
    `Tableau.optimal` of the σ-permuted tableau. -/
theorem realizedByRanking_iff_optimal [DecidableEq Output]
    (P : RealizationProblem Input Output n) (σ : Ranking n) :
    P.realizedByRanking σ ↔ ∀ i (hi : i ∈ P.inputs),
      Tableau.optimal ⟨P.cands i, fun o => toLex (fun k => P.vp i o (σ k)),
        ⟨P.target i, P.target_mem i hi⟩⟩ = {P.target i} := by
  refine ⟨fun h i hi => ?_, fun h i hi o ho hne => ?_⟩
  · exact (Tableau.optimal_eq_singleton_iff (P.target_mem i hi)).mpr
      fun o ho hne => h i hi o ho hne
  · exact (Tableau.optimal_eq_singleton_iff (P.target_mem i hi)).mp (h i hi) o ho hne

/-! ### OT-realization is ERC satisfaction -/

/-- The winner–loser ERCs of a systemic problem: one comparative row per input
    and non-target candidate ([prince-2002]). -/
def ercs [DecidableEq Output] (P : RealizationProblem Input Output n) : Finset (ERC n) :=
  P.inputs.biUnion fun i => ((P.cands i).erase (P.target i)).image fun o =>
    ercOfProfiles (P.vp i (P.target i)) (P.vp i o)

theorem mem_ercs [DecidableEq Output] {P : RealizationProblem Input Output n} {α : ERC n} :
    α ∈ P.ercs ↔ ∃ i ∈ P.inputs, ∃ o ∈ P.cands i, o ≠ P.target i ∧
      ercOfProfiles (P.vp i (P.target i)) (P.vp i o) = α := by
  simp only [ercs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase]
  tauto

/-- OT-realization is ERC satisfaction ([prince-2002]): provided no
    competitor ties the target's violation profile, `σ` realizes the target
    iff `σ` satisfies every winner–loser ERC. -/
theorem realizedByRanking_iff_satisfiedBy [DecidableEq Output]
    {P : RealizationProblem Input Output n} {σ : Ranking n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
      P.vp i (P.target i) ≠ P.vp i o) :
    P.realizedByRanking σ ↔ ∀ α ∈ P.ercs, α.SatisfiedBy σ := by
  constructor
  · intro h α hα
    obtain ⟨i, hi, o, ho, hone, rfl⟩ := mem_ercs.mp hα
    exact (satisfiedBy_ercOfProfiles_iff_le σ _ _).mpr (h i hi o ho hone).le
  · intro h i hi o ho hone
    refine lt_of_le_of_ne ((satisfiedBy_ercOfProfiles_iff_le σ _ _).mp
      (h _ (mem_ercs.mpr ⟨i, hi, o, ho, hone, rfl⟩))) fun heq => hvp i hi o ho hone ?_
    exact funext fun c => by simpa using congrFun (toLex_inj.mp heq) (σ.symm c)

/-- OT-realizability is consistency of the problem's ERC set
    ([prince-2002]). -/
theorem isOTRealizable_iff_linearExtensions_nonempty [DecidableEq Output]
    {P : RealizationProblem Input Output n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
      P.vp i (P.target i) ≠ P.vp i o) :
    P.IsOTRealizable ↔ (ERC.linearExtensions P.ercs).Nonempty :=
  exists_congr fun _ => (realizedByRanking_iff_satisfiedBy hvp).trans
    ERC.mem_linearExtensions.symm

end RealizationProblem

/-! ### Forward containment — OT ⊆ HG -/

/-- Permuting weights is dual to permuting constraints. -/
private theorem weightedViolations_perm_reindex
    (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (v : Fin n → ℕ) :
    weightedViolations (fun j => w (σ.symm j)) v =
    weightedViolations w (v ∘ σ) := by
  simp only [weightedViolations, Function.comp_apply]
  rw [← Equiv.sum_comp σ (fun j => w (σ.symm j) * (v j : ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  simp [Equiv.symm_apply_apply]

/-- Forward containment: an OT-realizable problem is HG-realizable, via
    exponentially separated weights permuted by the ranking
    (`lex_imp_lower_violations`, with separation bound the supremum of the
    finitely many violation counts). -/
theorem RealizationProblem.IsOTRealizable.isHGRealizable
    {P : RealizationProblem Input Output n} (h : P.IsOTRealizable) : P.IsHGRealizable := by
  obtain ⟨σ, hσ⟩ := h
  set M := (P.inputs.sup fun i => (P.cands i).sup fun o => Finset.univ.sup (P.vp i o)) + 1
  have hbound : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, ∀ k, P.vp i o k ≤ M := fun i hi o ho k =>
    ((Finset.le_sup (Finset.mem_univ k)).trans
      ((Finset.le_sup (f := fun o => Finset.univ.sup (P.vp i o)) ho).trans
        (Finset.le_sup (f := fun i => (P.cands i).sup fun o => Finset.univ.sup (P.vp i o))
          hi))).trans (Nat.le_succ _)
  refine ⟨fun j => expWeights n M (σ.symm j), fun k => (expWeights_pos n M (σ.symm k)).le, ?_⟩
  intro i hi o ho hne
  rw [weightedViolations_perm_reindex σ, weightedViolations_perm_reindex σ]
  apply lex_imp_lower_violations _ M
  · intro k
    exact ⟨hbound i hi (P.target i) (P.target_mem i hi) (σ k), hbound i hi o ho (σ k)⟩
  · exact expWeights_separated n M (Nat.succ_pos _)
  · exact hσ i hi o ho hne

/-! ### Strict containment — the cumulativity gap -/

/-- The cumulativity gap: HG with non-negative weights strictly contains OT.
    The inline witness is [coetzee-pater-2011]'s abstract Lyman's Law
    instance (eq 18-19, after [ito-mester-1986]): faithful candidates
    violating `{M1}`, `{M2}`, `{M1, M2}` against an unfaithful `{F}`, with
    the third input alone targeted unfaithful. Weights `[3, 2, 2]` realize
    this (`2 + 2 > 3` on the third input only), while the winner–loser ERCs
    `F ≫ M1`, `F ≫ M2`, and "some markedness constraint above `F`" are
    inconsistent. -/
theorem hg_strictly_contains_ot :
    ∃ (Input Output : Type) (n : ℕ) (P : RealizationProblem Input Output n),
      P.IsHGRealizable ∧ ¬ P.IsOTRealizable := by
  refine ⟨Fin 3, Bool, 3,
    { inputs := Finset.univ
      cands := fun _ => Finset.univ
      vp := fun i b => if b then ![![0, 1, 0], ![0, 0, 1], ![0, 1, 1]] i else ![1, 0, 0]
      target := ![true, true, false]
      target_mem := fun _ _ => Finset.mem_univ _ },
    ⟨![3, 2, 2], fun k => by fin_cases k <;> norm_num, ?_⟩, ?_⟩
  · intro i _ o _ hne
    simp only [weightedViolations, Fin.sum_univ_three]
    fin_cases i <;> cases o <;>
      first
      | (exfalso; exact hne rfl)
      | norm_num [Matrix.cons_val_two, Matrix.tail_cons]
  · rintro ⟨σ, hσ⟩
    rw [RealizationProblem.realizedByRanking_iff_satisfiedBy (by decide)] at hσ
    have h₁ : σ.toRel 0 1 := (simpleERC_satisfiedBy_toRel_iff 0 1 σ).mp
      (hσ _ (RealizationProblem.mem_ercs.mpr
        ⟨0, Finset.mem_univ _, false, Finset.mem_univ _, by decide, by decide⟩))
    have h₂ : σ.toRel 0 2 := (simpleERC_satisfiedBy_toRel_iff 0 2 σ).mp
      (hσ _ (RealizationProblem.mem_ercs.mpr
        ⟨1, Finset.mem_univ _, false, Finset.mem_univ _, by decide, by decide⟩))
    have h₃ := hσ _ (RealizationProblem.mem_ercs.mpr
      ⟨2, Finset.mem_univ _, true, Finset.mem_univ _, by decide, rfl⟩)
    obtain ⟨w, hwW, hdom⟩ := (ERC.satisfiedBy_iff_dominance σ _).mp h₃ 0 (by decide)
    fin_cases w
    · exact absurd hwW (by decide)
    · exact absurd h₁ (not_le.mpr hdom)
    · exact absurd h₂ (not_le.mpr hdom)

end HarmonicGrammar
