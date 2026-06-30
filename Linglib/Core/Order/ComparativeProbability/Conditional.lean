import Linglib.Core.Order.ComparativeProbability.Systems
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Conditional Plausibility and Probabilistic Update

[halpern-2003] axiomatizes conditional plausibility measures,
generalizing Bayesian conditioning, Popper spaces, Jeffrey's rule,
and imaging under a single algebraic framework (Cond1–Cond4).

This file formalizes:
1. **Conditional probability measures** (Popper space axioms P1–P4)
2. **The ratio construction** (Halpern Thm 3.3.1): FinAddMeasure → CondMeasure
3. **Jeffrey's rule**: update under uncertain evidence, packaged as a
   finitely additive measure (`jeffreyMeasure`)

## Conditioning across linglib

Several conditioning operations elsewhere in linglib are instances of
conditional plausibility: `PMF.condProbSet` (`BayesianSemantics`) is the same
ratio construction as `toCondMeasure`; `InfoState.update` (`Dynamic/Core/Update`)
is the eliminative special case where P(A|B) ∈ {0, 1}; Spohn ranking
conditionalization ([spohn-1988], `Core/Logic/RankingFunction`) is its
order-of-magnitude analogue. Bayesian conditioning is the point-partition
special case of Jeffrey's rule (`bayesian_is_jeffrey`).
-/

namespace ComparativeProbability

/-! ### Conditional probability measure (Popper space) -/

/-- A conditional probability measure: P(A | B) axiomatized directly.

    Extends `FinAddMeasure` with a conditional component satisfying
    Popper's axioms ([halpern-2003], Ch. 3, Cond1–Cond4). A set B is
    **normal** if P(B|B) ≠ 0; for normal B, P(B|B) = 1. The only
    abnormal set (for finite W with positive singletons) is ∅. -/
structure CondMeasure (W : Type*) extends FinAddMeasure ℚ W where
  /-- Conditional measure: `condMu A B = P(A | B)` -/
  condMu : Set W → Set W → ℚ
  /-- P1: non-negativity -/
  cond_nonneg : ∀ A B, 0 ≤ condMu A B
  /-- P2: normalization — P(B|B) = 1 for normal B -/
  cond_norm : ∀ B, condMu B B ≠ 0 → condMu B B = 1
  /-- P3: conditional additivity -/
  cond_additive : ∀ A₁ A₂ B, Disjoint A₁ A₂ →
    condMu (A₁ ∪ A₂) B = condMu A₁ B + condMu A₂ B
  /-- P4: chain rule — P(A ∩ B | C) = P(A | B ∩ C) · P(B | C) -/
  cond_chain : ∀ A B C, condMu (A ∩ B) C = condMu A (B ∩ C) * condMu B C
  /-- Conditioning sees only the part inside the evidence: P(A|B) = P(A ∩ B|B) -/
  cond_inter : ∀ A B, condMu A B = condMu (A ∩ B) B
  /-- Unconditional connection: P(A | Ω) = μ(A) -/
  cond_univ : ∀ A, condMu A Set.univ = mu A

namespace CondMeasure

variable {W : Type*}

/-- Conditional comparison: A ≿_B C iff P(A|B) ≥ P(C|B). -/
def condGe (m : CondMeasure W) (A C B : Set W) : Prop :=
  m.condMu A B ≥ m.condMu C B

/-- Posterior measure given evidence B: P_B(A) := P(A|B). -/
def posterior (m : CondMeasure W) (B : Set W) : Set W → ℚ :=
  fun A => m.condMu A B

/-- Bayes' theorem: P(A|B) · P(B) = P(B|A) · P(A).
    Follows from the chain rule applied in two directions:
    P(A ∩ B | Ω) = P(A | B) · P(B | Ω) = P(B | A) · P(A | Ω). -/
theorem bayes (m : CondMeasure W) (A B : Set W) :
    m.condMu A B * m.condMu B Set.univ =
    m.condMu B A * m.condMu A Set.univ := by
  have h1 := m.cond_chain A B Set.univ
  have h2 := m.cond_chain B A Set.univ
  simp only [Set.inter_univ] at h1 h2
  rw [← h1, ← h2, Set.inter_comm]

/-- For normal `B`, `P(Ω|B) = 1`. -/
theorem condMu_univ_of_normal (m : CondMeasure W) {B : Set W}
    (hB : m.condMu B B ≠ 0) : m.condMu Set.univ B = 1 := by
  rw [m.cond_inter Set.univ B, Set.univ_inter]
  exact m.cond_norm B hB

end CondMeasure

/-! ### Ratio construction (Halpern Theorem 3.3.1) -/

/-- Construct conditional probability via the ratio P(A|B) = μ(A ∩ B)/μ(B).

    [halpern-2003], Theorem 3.3.1: every finitely additive measure extends
    to a conditional measure satisfying P1–P4 via this construction.
    When μ(B) = 0, P(A|B) = 0 (B is "abnormal" in Popper's sense).

    In Lean's ℚ arithmetic, division by zero yields 0, so the abnormal
    case is handled automatically. -/
noncomputable def FinAddMeasure.toCondMeasure {W : Type*}
    (m : FinAddMeasure ℚ W) : CondMeasure W where
  toFinAddMeasure := m
  condMu := fun A B => m.mu (A ∩ B) / m.mu B
  cond_nonneg := fun A B => div_nonneg (m.nonneg _) (m.nonneg _)
  cond_norm := fun B hne => by
    simp only [Set.inter_self] at hne ⊢
    exact div_self fun h => hne (by rw [h, div_zero])
  cond_additive := fun A₁ A₂ B hdisj => by
    rw [Set.union_inter_distrib_right, m.additive (A₁ ∩ B) (A₂ ∩ B)
      (hdisj.mono Set.inter_subset_left Set.inter_subset_left), add_div]
  cond_chain := fun A B C => by
    -- Ratio algebra a/c = (a/b)·(b/c): when μ(B∩C)=0 both sides vanish, else cancel.
    rw [Set.inter_assoc]
    by_cases hBC : m.mu (B ∩ C) = 0
    · have hABC : m.mu (A ∩ (B ∩ C)) = 0 :=
        le_antisymm (hBC ▸ m.mu_mono Set.inter_subset_right) (m.nonneg _)
      simp [hABC, hBC]
    · rw [div_mul_div_comm, mul_comm (m.mu (A ∩ (B ∩ C))), mul_div_mul_left _ _ hBC]
  cond_inter := fun A B => by rw [Set.inter_assoc, Set.inter_self]
  cond_univ := fun A => by simp [Set.inter_univ, m.total, div_one]

/-! ### Jeffrey's rule -/

/-- An evidence partition: pairwise-disjoint cells covering the space, with new
    probability assignments summing to 1. -/
structure EvidencePartition (W : Type*) where
  /-- The partition cells -/
  cells : List (Set W)
  /-- New probability for each cell -/
  weights : List ℚ
  /-- Cells and weights are aligned -/
  aligned : cells.length = weights.length
  /-- Cells are pairwise disjoint -/
  disjointCells : cells.Pairwise Disjoint
  /-- Cells cover the space -/
  exhaustive : cells.foldr (· ∪ ·) ∅ = Set.univ
  /-- Weights are non-negative -/
  weights_nonneg : ∀ q ∈ weights, 0 ≤ q
  /-- Weights sum to 1 -/
  weights_sum : weights.sum = 1

/-- Jeffrey's rule ([jeffrey-1965]; [halpern-2003] §3.4): update with uncertain
    evidence, P'(A) = Σᵢ P(A | Eᵢ) · qᵢ. -/
def jeffreyUpdate {W : Type*} (m : CondMeasure W)
    (ev : EvidencePartition W) : Set W → ℚ :=
  fun A => ((ev.cells.zip ev.weights).map (fun p => m.condMu A p.1 * p.2)).sum

theorem jeffreyUpdate_nonneg {W : Type*} (m : CondMeasure W)
    (ev : EvidencePartition W) (A : Set W) :
    0 ≤ jeffreyUpdate m ev A :=
  List.sum_nonneg fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (m.cond_nonneg A p.1) (ev.weights_nonneg p.2 (List.of_mem_zip hp).2)

theorem jeffreyUpdate_additive {W : Type*} (m : CondMeasure W)
    (ev : EvidencePartition W) (A B : Set W) (hAB : Disjoint A B) :
    jeffreyUpdate m ev (A ∪ B) = jeffreyUpdate m ev A + jeffreyUpdate m ev B := by
  simp only [jeffreyUpdate]
  induction ev.cells.zip ev.weights with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, List.sum_cons, ih, m.cond_additive A B p.1 hAB]; ring

/-- Jeffrey update is normalized when every cell is normal. -/
theorem jeffreyUpdate_total {W : Type*} (m : CondMeasure W)
    (ev : EvidencePartition W) (hnorm : ∀ E ∈ ev.cells, m.condMu E E ≠ 0) :
    jeffreyUpdate m ev Set.univ = 1 := by
  simp only [jeffreyUpdate]
  rw [List.map_congr_left fun p hp => by
      rw [m.condMu_univ_of_normal (hnorm p.1 (List.of_mem_zip hp).1), one_mul],
    List.map_snd_zip (le_of_eq ev.aligned.symm), ev.weights_sum]

/-- **Jeffrey's rule yields a measure**: for a partition of normal cells, the
    Jeffrey update is a finitely additive probability measure. -/
def jeffreyMeasure {W : Type*} (m : CondMeasure W) (ev : EvidencePartition W)
    (hnorm : ∀ E ∈ ev.cells, m.condMu E E ≠ 0) : FinAddMeasure ℚ W where
  mu := jeffreyUpdate m ev
  nonneg := jeffreyUpdate_nonneg m ev
  additive := jeffreyUpdate_additive m ev
  total := jeffreyUpdate_total m ev hnorm

/-- Bayesian conditioning is Jeffrey conditioning with the partition `{B, Bᶜ}`
    and weights `1, 0`. -/
theorem bayesian_is_jeffrey {W : Type*} (m : CondMeasure W) (B A : Set W) :
    m.condMu A B = jeffreyUpdate m
      { cells := [B, Bᶜ], weights := [1, 0],
        aligned := rfl,
        disjointCells := List.pairwise_pair.mpr disjoint_compl_right,
        exhaustive := by
          rw [List.foldr_cons, List.foldr_cons, List.foldr_nil,
            Set.union_empty, Set.union_compl_self],
        weights_nonneg := fun q hq => by
          rcases List.mem_pair.mp hq with rfl | rfl <;> norm_num,
        weights_sum := by norm_num } A := by
  simp [jeffreyUpdate]

/-! ### Conditional plausibility and epistemic comparison -/

/-- A conditional measure induces a conditional epistemic comparison:
    A ≿_B C iff P(A|B) ≥ P(C|B). This conditional comparison is reflexive
    for each fixed B. -/
theorem condMeasure_reflexive_per_evidence {W : Type*}
    (m : CondMeasure W) (B : Set W) :
    Reflexive (fun A C => m.condGe A C B) :=
  fun _ => le_refl _

end ComparativeProbability
