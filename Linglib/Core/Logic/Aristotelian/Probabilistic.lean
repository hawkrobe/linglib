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
noncomputable abbrev boolProb (μ : PMF W) (φ : W → Bool) : ℝ≥0∞ :=
  PMF.probOfSet μ {w | φ w = true}

/-- Total probability: `P[φ] + P[¬φ] = 1`, via `PMF.probOfSet_compl_add`. -/
theorem boolProb_add_compl (μ : PMF W) (φ : W → Bool) :
    boolProb μ φ + boolProb μ (fun w => !φ w) = 1 := by
  classical
  have hset : {w | (!φ w) = true} = {w | φ w = true}ᶜ := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]; cases φ w <;> simp
  show μ.probOfSet {w | φ w = true} + μ.probOfSet {w | (!φ w) = true} = 1
  rw [hset]; exact μ.probOfSet_compl_add _

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

/-- Boolean contradictoriness transfers to every measure: `{ψ}` is the complement of `{φ}`. -/
theorem ProbContradictory.of_isContradictory {φ ψ : W → Bool}
    (h : IsContradictory φ ψ) (μ : PMF W) : ProbContradictory μ φ ψ := by
  classical
  obtain ⟨hAnd, hOr⟩ := isContradictory_iff_forall.mp h
  have hset : {w | ψ w = true} = {w | φ w = true}ᶜ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    exact ⟨fun hψ hφ => hAnd w ⟨hφ, hψ⟩, fun hφ => (hOr w).resolve_left hφ⟩
  show μ.probOfSet {w | φ w = true} + μ.probOfSet {w | ψ w = true} = 1
  rw [hset]; exact μ.probOfSet_compl_add _

omit [Fintype W] in
/-- Boolean subalternation transfers to every measure (`probOfSet` monotonicity). -/
theorem ProbSubaltern.of_isSubaltern {φ ψ : W → Bool}
    (h : IsSubaltern φ ψ) (μ : PMF W) : ProbSubaltern μ φ ψ :=
  μ.probOfSet_mono fun w hw => le_iff_forall.mp h.le w hw

/-- Boolean contrariety transfers to every measure: `{φ} ⊆ {ψ}ᶜ`, so `P[φ] ≤ 1 - P[ψ]`. -/
theorem ProbContrary.of_isContrary {φ ψ : W → Bool}
    (h : IsContrary φ ψ) (μ : PMF W) : ProbContrary μ φ ψ := by
  classical
  have hsub : {w | φ w = true} ⊆ {w | ψ w = true}ᶜ :=
    fun w hw hw' => disjoint_iff_forall.mp h.1 w ⟨hw, hw'⟩
  calc boolProb μ φ + boolProb μ ψ
      ≤ μ.probOfSet {w | ψ w = true}ᶜ + boolProb μ ψ := by
        gcongr; exact μ.probOfSet_mono hsub
    _ = 1 := by rw [add_comm]; exact μ.probOfSet_compl_add _

/-- Boolean subcontrariety transfers to every measure: `{ψ}ᶜ ⊆ {φ}`, so `1 - P[ψ] ≤ P[φ]`. -/
theorem ProbSubcontrary.of_isSubcontrary {φ ψ : W → Bool}
    (h : IsSubcontrary φ ψ) (μ : PMF W) : ProbSubcontrary μ φ ψ := by
  classical
  have hsub : {w | ψ w = true}ᶜ ⊆ {w | φ w = true} :=
    fun w hw => (codisjoint_iff_forall.mp h.2 w).resolve_right hw
  show (1 : ℝ≥0∞) ≤ boolProb μ φ + boolProb μ ψ
  calc (1 : ℝ≥0∞)
      = boolProb μ ψ + μ.probOfSet {w | ψ w = true}ᶜ := (μ.probOfSet_compl_add _).symm
    _ ≤ boolProb μ ψ + boolProb μ φ := by gcongr; exact μ.probOfSet_mono hsub
    _ = boolProb μ φ + boolProb μ ψ := add_comm _ _

end Aristotelian
