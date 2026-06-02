import Linglib.Core.Logic.Aristotelian.Basic
import Linglib.Core.Probability.Finite

/-!
# Probabilistic Aristotelian relations

When `W` carries a probability measure `μ : PMF W`, the four Aristotelian
relations generalise to linear (in)equalities on `P_μ[φ] := μ {w | φ w = true}`:

| Boolean relation       | Probabilistic counterpart |
|------------------------|---------------------------|
| `IsContradictory φ ψ`  | `P[φ] + P[ψ] = 1`         |
| `IsContrary φ ψ`       | `P[φ] + P[ψ] ≤ 1`         |
| `IsSubcontrary φ ψ`    | `P[φ] + P[ψ] ≥ 1`         |
| `IsSubaltern φ ψ`      | `P[φ] ≤ P[ψ]`             |

The discrete case (`μ a ∈ {0,1}`) recovers Definition 1 of
[demey-smessaert-2018]. The main results are the transfer theorems: a
Boolean Aristotelian relation implies its probabilistic counterpart under every
`μ` (the converse fails).
-/

namespace Aristotelian

open scoped ENNReal

variable {W : Type*} [Fintype W]

/-! ### Probability of a Boolean predicate -/

/-- The probability of `φ : W → Bool` under `μ : PMF W`, i.e. `μ {w | φ w = true}`. -/
noncomputable def boolProb (μ : PMF W) (φ : W → Bool) : ℝ≥0∞ :=
  PMF.probOfSet μ {w | φ w = true}

@[inherit_doc boolProb]
notation "P[" φ " ; " μ "]" => boolProb μ φ

/-- The PMF sums to 1 over the finite sample space. -/
private lemma pmf_sum_univ (μ : PMF W) : ∑ x, μ x = (1 : ℝ≥0∞) := by
  have h : ∑ x, μ x = (∑' x, μ x : ℝ≥0∞) :=
    (tsum_eq_sum (f := μ) (s := Finset.univ)
      (fun x hx => absurd (Finset.mem_univ x) hx)).symm
  rw [h, PMF.tsum_coe]

/-- Total probability: `P[φ] + P[¬φ] = 1`. -/
theorem boolProb_add_compl (μ : PMF W) (φ : W → Bool) :
    boolProb μ φ + boolProb μ (fun w => !φ w) = 1 := by
  classical
  unfold boolProb PMF.probOfSet
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
  have hsum : ∀ x, ({w | φ w = true} : Set W).indicator μ x +
                   ({w | (!φ w) = true} : Set W).indicator μ x = μ x := by
    intro x
    cases hφ : φ x
    · simp [Set.indicator, hφ]
    · simp [Set.indicator, hφ]
  rw [Finset.sum_congr rfl (fun x _ => hsum x)]
  exact pmf_sum_univ μ

/-! ### Probabilistic Aristotelian relations (Definition 1, convex form) -/

/-- Probabilistic contradictoriness: `P[φ] + P[ψ] = 1`. -/
def ProbContradictory (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ + boolProb μ ψ = 1

/-- Probabilistic contrariety: `P[φ] + P[ψ] ≤ 1`. -/
def ProbContrary (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ + boolProb μ ψ ≤ 1

/-- Probabilistic subcontrariety: `P[φ] + P[ψ] ≥ 1`. -/
def ProbSubcontrary (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ + boolProb μ ψ ≥ 1

/-- Probabilistic subalternation: `P[φ] ≤ P[ψ]`. -/
def ProbSubaltern (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ ≤ boolProb μ ψ

/-! ### Transfer theorems: Boolean ⇒ Probabilistic (for every μ) -/

/-- Boolean contradictoriness transfers to every measure (`ψ` is pointwise `!φ`). -/
theorem ProbContradictory.of_isContradictory {φ ψ : W → Bool}
    (h : IsContradictory φ ψ) (μ : PMF W) :
    ProbContradictory μ φ ψ := by
  obtain ⟨hAnd, hOr⟩ := isContradictory_iff_forall.mp h
  have hPointwise : ∀ w, ψ w = !φ w := by
    intro w
    have h1 := hAnd w
    have h2 := hOr w
    cases hφ : φ w
    · cases hψ : ψ w
      · exfalso; exact h2.elim (fun h => by rw [hφ] at h; exact Bool.noConfusion h)
                                (fun h => by rw [hψ] at h; exact Bool.noConfusion h)
      · simp [hφ]
    · cases hψ : ψ w
      · simp [hφ]
      · exfalso; exact h1 ⟨hφ, hψ⟩
  have hψ_eq : ψ = (fun w => !φ w) := funext hPointwise
  unfold ProbContradictory
  rw [hψ_eq]
  exact boolProb_add_compl μ φ

/-- Boolean subalternation transfers to every measure (PMF monotonicity). -/
theorem ProbSubaltern.of_isSubaltern {φ ψ : W → Bool}
    (h : IsSubaltern φ ψ) (μ : PMF W) :
    ProbSubaltern μ φ ψ := by
  obtain ⟨hle, _⟩ := isSubaltern_iff_forall.mp h
  unfold ProbSubaltern boolProb PMF.probOfSet
  apply MeasureTheory.OuterMeasure.mono
  intro w hw
  exact hle w hw

/-- Boolean contrariety transfers to every measure. -/
theorem ProbContrary.of_isContrary {φ ψ : W → Bool}
    (h : IsContrary φ ψ) (μ : PMF W) :
    ProbContrary μ φ ψ := by
  classical
  obtain ⟨hAnd, _⟩ := isContrary_iff_forall.mp h
  unfold ProbContrary boolProb PMF.probOfSet
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
  have hbnd : ∀ x ∈ Finset.univ,
      ({w | φ w = true} : Set W).indicator μ x +
      ({w | ψ w = true} : Set W).indicator μ x ≤ μ x := by
    intro x _
    by_cases hφ : φ x = true
    · by_cases hψ : ψ x = true
      · exact absurd ⟨hφ, hψ⟩ (hAnd x)
      · simp [Set.indicator, hφ, hψ]
    · by_cases hψ : ψ x = true
      · simp [Set.indicator, hφ, hψ]
      · simp [Set.indicator, hφ, hψ]
  calc (∑ x, (({w | φ w = true} : Set W).indicator μ x +
              ({w | ψ w = true} : Set W).indicator μ x))
      ≤ ∑ x, μ x := Finset.sum_le_sum hbnd
    _ = 1 := pmf_sum_univ μ

/-- Boolean subcontrariety transfers to every measure. -/
theorem ProbSubcontrary.of_isSubcontrary {φ ψ : W → Bool}
    (h : IsSubcontrary φ ψ) (μ : PMF W) :
    ProbSubcontrary μ φ ψ := by
  classical
  obtain ⟨_, hOr⟩ := isSubcontrary_iff_forall.mp h
  unfold ProbSubcontrary boolProb PMF.probOfSet
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
  have hbnd : ∀ x ∈ Finset.univ,
      μ x ≤ ({w | φ w = true} : Set W).indicator μ x +
            ({w | ψ w = true} : Set W).indicator μ x := by
    intro x _
    rcases hOr x with hφ | hψ
    · simp [Set.indicator, hφ]
    · by_cases hφ' : φ x = true
      · simp [Set.indicator, hφ', hψ]
      · simp [Set.indicator, hφ', hψ]
  calc (1 : ℝ≥0∞)
      = ∑ x, μ x := (pmf_sum_univ μ).symm
    _ ≤ ∑ x, (({w | φ w = true} : Set W).indicator μ x +
              ({w | ψ w = true} : Set W).indicator μ x) :=
        Finset.sum_le_sum hbnd

end Aristotelian
