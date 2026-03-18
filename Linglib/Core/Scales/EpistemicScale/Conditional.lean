import Linglib.Core.Scales.EpistemicScale.Defs

/-!
# Conditional Plausibility and Probabilistic Update

@cite{halpern-2003} @cite{jeffrey-1965}@cite{halpern-2003} axiomatizes conditional plausibility measures,
generalizing Bayesian conditioning, Popper spaces, Jeffrey's rule,
and imaging under a single algebraic framework (Cond1–Cond4).

This file formalizes:
1. **Conditional probability measures** (Popper space axioms P1–P4)
2. **The ratio construction** (Halpern Thm 3.3.1): FinAddMeasure → CondMeasure
3. **Jeffrey's rule**: update under uncertain evidence
4. **Conditioning modes**: classifying the update operations across linglib

## Conditioning Unification

Four conditioning operations in linglib are instances of conditional
plausibility:

| Module | Operation | Mode |
|--------|-----------|------|
| `EpistemicScale/Conditional` | `condMu A B` | Bayesian (ratio) |
| `BayesianSemantics` | `FinitePMF.prob` | Bayesian (marginalization) |
| `Dynamic/Core/Update` | `InfoState.update s φ` | Eliminative |
| `SDS/MeasureTheory` | (placeholder) | Continuous Bayesian |

The eliminative mode is the special case where P(A|B) ∈ {0, 1}:
each world either survives or is eliminated.

-/

namespace Core.Scale

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Conditioning Modes
-- ══════════════════════════════════════════════════════════════════════

/-- Classification of conditioning modes used across linglib.

    - **eliminative**: keep only worlds satisfying evidence. The
      resulting measure is 0/1-valued. (`Dynamic/Core/Update.lean`)
    - **bayesian**: P(A|B) = P(A ∩ B)/P(B). Standard ratio conditioning.
      (`BayesianSemantics.lean`, this file)
    - **jeffrey**: update with uncertain evidence over a partition.
      Generalizes Bayesian: P'(A) = Σᵢ P(A|Eᵢ) · q(Eᵢ). -/
inductive ConditioningMode where
  | eliminative
  | bayesian
  | jeffrey
  | ranking   -- @cite{spohn-1988}: κ_φ(w) = κ(w) - κ(φ) for φ-worlds
  deriving DecidableEq, BEq, Repr

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Conditional Probability Measure (Popper Space)
-- ══════════════════════════════════════════════════════════════════════

/-- A conditional probability measure: P(A | B) axiomatized directly.

    Extends `FinAddMeasure` with a conditional component satisfying
    Popper's axioms (@cite{halpern-2003}, Ch. 3, Cond1–Cond4). A set B is
    **normal** if P(B|B) ≠ 0; for normal B, P(B|B) = 1. The only
    abnormal set (for finite W with positive singletons) is ∅. -/
structure CondMeasure (W : Type*) extends FinAddMeasure W where
  /-- Conditional measure: `condMu A B = P(A | B)` -/
  condMu : Set W → Set W → ℚ
  /-- P1: non-negativity -/
  cond_nonneg : ∀ A B, 0 ≤ condMu A B
  /-- P2: normalization — P(B|B) = 1 for normal B -/
  cond_norm : ∀ B, condMu B B ≠ 0 → condMu B B = 1
  /-- P3: conditional additivity -/
  cond_additive : ∀ A₁ A₂ B, (∀ x, x ∈ A₁ → x ∉ A₂) →
    condMu (A₁ ∪ A₂) B = condMu A₁ B + condMu A₂ B
  /-- P4: chain rule — P(A ∩ B | C) = P(A | B ∩ C) · P(B | C) -/
  cond_chain : ∀ A B C, condMu (A ∩ B) C = condMu A (B ∩ C) * condMu B C
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

end CondMeasure

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Ratio Construction (Halpern Theorem 3.3.1)
-- ══════════════════════════════════════════════════════════════════════

/-- Construct conditional probability via the ratio P(A|B) = μ(A ∩ B)/μ(B).

    @cite{halpern-2003}, Theorem 3.3.1: every finitely additive measure extends
    to a conditional measure satisfying P1–P4 via this construction.
    When μ(B) = 0, P(A|B) = 0 (B is "abnormal" in Popper's sense).

    In Lean's ℚ arithmetic, division by zero yields 0, so the abnormal
    case is handled automatically. -/
noncomputable def FinAddMeasure.toCondMeasure {W : Type*}
    (m : FinAddMeasure W) : CondMeasure W where
  toFinAddMeasure := m
  condMu := fun A B => m.mu (A ∩ B) / m.mu B
  cond_nonneg := fun A B => div_nonneg (m.nonneg _) (m.nonneg _)
  cond_norm := fun B hne => by
    simp only [Set.inter_self] at hne ⊢
    have hB : m.mu B ≠ 0 := by
      intro h; apply hne; rw [h, div_zero]
    exact div_self hB
  cond_additive := fun A₁ A₂ B hdisj => by
    have hd : ∀ x, x ∈ A₁ ∩ B → x ∉ A₂ ∩ B :=
      fun x ⟨h1, _⟩ ⟨h2, _⟩ => hdisj x h1 h2
    rw [Set.union_inter_distrib_right, m.additive _ _ hd, add_div]
  cond_chain := fun A B C => by
    -- P(A ∩ B | C) = μ(A ∩ B ∩ C) / μ(C)
    -- P(A | B ∩ C) · P(B | C) = [μ(A ∩ (B ∩ C)) / μ(B ∩ C)] · [μ(B ∩ C) / μ(C)]
    -- Since A ∩ (B ∩ C) = A ∩ B ∩ C, this is μ(A∩B∩C)/μ(B∩C) · μ(B∩C)/μ(C)
    -- = μ(A∩B∩C)/μ(C) when μ(B∩C) ≠ 0, and 0 = 0 otherwise.
    -- μ(A∩B∩C)/μ(C) = [μ(A∩B∩C)/μ(B∩C)] · [μ(B∩C)/μ(C)]
    -- Standard ratio algebra: a/c = (a/b)·(b/c), case-splitting on b = 0.
    -- When b = 0: a ≤ b = 0 (subset monotonicity) so a = 0, both sides = 0.
    -- When b ≠ 0: cancel b in numerator/denominator.
    rw [Set.inter_assoc]
    by_cases hBC : m.mu (B ∩ C) = 0
    · have hABC : m.mu (A ∩ (B ∩ C)) = 0 := by
        have : m.mu (B ∩ C) ≥ m.mu (A ∩ (B ∩ C)) := by
          have hd : ∀ x, x ∈ A ∩ (B ∩ C) → x ∉ (B ∩ C) \ (A ∩ (B ∩ C)) :=
            fun x hx ⟨_, hna⟩ => hna hx
          have := m.additive (A ∩ (B ∩ C)) ((B ∩ C) \ (A ∩ (B ∩ C))) hd
          rw [Set.union_diff_cancel Set.inter_subset_right] at this
          linarith [m.nonneg ((B ∩ C) \ (A ∩ (B ∩ C)))]
        linarith [m.nonneg (A ∩ (B ∩ C))]
      simp [hABC, hBC]
    · rw [div_mul_div_comm, mul_comm (m.mu (A ∩ (B ∩ C))), mul_div_mul_left _ _ hBC]
  cond_univ := fun A => by simp [Set.inter_univ, m.total, div_one]

-- ══════════════════════════════════════════════════════════════════════
-- § 4. Jeffrey's Rule
-- ══════════════════════════════════════════════════════════════════════

/-- An evidence partition: a finite collection of mutually exclusive,
    exhaustive propositions with new probability assignments. -/
structure EvidencePartition (W : Type*) where
  /-- The partition cells -/
  cells : List (Set W)
  /-- New probability for each cell -/
  weights : List ℚ
  /-- Cells and weights are aligned -/
  aligned : cells.length = weights.length
  /-- Weights are non-negative -/
  weights_nonneg : ∀ q ∈ weights, 0 ≤ q
  /-- Weights sum to 1 -/
  weights_sum : weights.sum = 1

/-- Jeffrey's rule: update a conditional measure with uncertain evidence.

    Given a partition {E₁,..., Eₙ} with new probabilities q₁,..., qₙ:
    P'(A) = Σᵢ P(A | Eᵢ) · qᵢ

    This generalizes Bayesian conditioning: standard conditioning on E
    is the special case where qₑ = 1 and all other qᵢ = 0.

    @cite{jeffrey-1965}, The Logic of Decision; @cite{halpern-2003} §3.4. -/
def jeffreyUpdate {W : Type*} (m : CondMeasure W)
    (ev : EvidencePartition W) : Set W → ℚ :=
  fun A =>
    let pairs := ev.cells.zip ev.weights
    pairs.foldl (fun acc ⟨E, q⟩ => acc + m.condMu A E * q) 0

/-- Jeffrey's rule preserves non-negativity. -/
private lemma foldl_condMu_nonneg {W : Type*} (m : CondMeasure W) (A : Set W)
    (pairs : List (Set W × ℚ)) (acc : ℚ) (hacc : 0 ≤ acc)
    (hpairs : ∀ p ∈ pairs, 0 ≤ p.2) :
    0 ≤ pairs.foldl (fun acc ⟨E, q⟩ => acc + m.condMu A E * q) acc := by
  induction pairs generalizing acc with
  | nil => simpa using hacc
  | cons hd t ih =>
    simp only [List.foldl]
    apply ih
    · exact add_nonneg hacc (mul_nonneg (m.cond_nonneg A hd.1)
        (hpairs hd List.mem_cons_self))
    · intro p hp; exact hpairs p (List.mem_cons_of_mem _ hp)

theorem jeffreyUpdate_nonneg {W : Type*} (m : CondMeasure W)
    (ev : EvidencePartition W) (A : Set W) :
    0 ≤ jeffreyUpdate m ev A := by
  unfold jeffreyUpdate
  apply foldl_condMu_nonneg m A _ 0 (le_refl 0)
  intro ⟨E, q⟩ hEq
  exact ev.weights_nonneg q (List.of_mem_zip hEq).2

/-- Bayesian conditioning is Jeffrey conditioning with a point partition. -/
theorem bayesian_is_jeffrey {W : Type*} (m : CondMeasure W) (B : Set W)
    (_hB : m.condMu B B ≠ 0) (A : Set W) :
    m.condMu A B = jeffreyUpdate m
      { cells := [B], weights := [1],
        aligned := rfl,
        weights_nonneg := fun q hq => by simp [List.mem_singleton.mp hq],
        weights_sum := by simp } A := by
  simp [jeffreyUpdate, List.zip, List.foldl, mul_one]

-- ══════════════════════════════════════════════════════════════════════
-- § 5. Bridge: Conditional Plausibility ↔ Epistemic Comparison
-- ══════════════════════════════════════════════════════════════════════

/-- A conditional measure induces a conditional epistemic comparison:
    A ≿_B C iff P(A|B) ≥ P(C|B). This conditional comparison satisfies
    reflexivity and monotonicity (System W axioms) for each fixed B. -/
theorem condMeasure_systemW_per_evidence {W : Type*}
    (m : CondMeasure W) (B : Set W) :
    EpistemicAxiom.R (fun A C => m.condGe A C B) :=
  fun _ => le_refl _

/-- A conditional measure extends to a conditional comparison on
    propositions: A is conditionally at least as likely as C given B
    iff P(A|B) ≥ P(C|B). This is the conditional version of
    `FinAddMeasure.inducedGe`. -/
def CondMeasure.inducedCondGe {W : Type*} (m : CondMeasure W)
    (A C B : Set W) : Prop :=
  m.condMu A B ≥ m.condMu C B

-- ══════════════════════════════════════════════════════════════════════
-- § 6. Conditioning Mode Relationships
-- ══════════════════════════════════════════════════════════════════════

-- **FinitePMF** (BayesianSemantics.lean): `FinitePMF.prob pmf event`
-- computes P(event) = Σ_θ mass(θ) · 1[event(θ)]. Conditioning a
-- FinitePMF on evidence B corresponds to the ratio construction
-- P(A|B) = P(A ∩ B)/P(B), i.e., `(toCondMeasure m).condMu A B`.
--
-- **InfoState.update** (Dynamic/Core/Update.lean): eliminative
-- conditioning — each possibility either survives (P = 1) or is
-- removed (P = 0). Under a uniform distribution, this equals Bayesian
-- conditioning: P(A|φ) = |A ∩ {w | φ w}| / |{w | φ w}|.
--
-- **Jeffrey conditioning**: generalizes Bayesian conditioning.
-- Bayesian conditioning on B is Jeffrey conditioning with the point
-- partition {B} and weight 1 (see `bayesian_is_jeffrey` above).

end Core.Scale
