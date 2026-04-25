import Linglib.Core.Logic.Opposition.Aristotelian
import Linglib.Core.Probability.PMFFin

/-!
# Probabilistic Aristotelian relations

When the model class `W` is equipped with a probability measure `μ : PMF W`,
the four Aristotelian relations have natural probabilistic generalisations
as linear (in)equalities on the probabilities `P_μ[φ] := μ({w | φ w = true})`:

| Boolean Aristotelian relation | Probabilistic counterpart |
|-------------------------------|---------------------------|
| `Contradictory φ ψ`           | `P[φ] + P[ψ] = 1`         |
| `Contrary φ ψ`                | `P[φ] + P[ψ] ≤ 1`         |
| `Subcontrary φ ψ`             | `P[φ] + P[ψ] ≥ 1`         |
| `Subaltern φ ψ`               | `P[φ] ≤ P[ψ]`             |

This is the convex extension of the Boolean Aristotelian geometry: the discrete
case (each `μ a ∈ {0,1}`) recovers Definition 1 of @cite{demey-smessaert-2018}
exactly; the convex case is what Bayesian listeners actually compute.

## Why this matters for RSA / Bayesian-pragmatic models

The Tessler–Tenenbaum–Goodman 2022 syllogistic model (and any RSA-style
Bayesian-pragmatic model that reasons about quantifier inference) computes a
posterior `μ : PMF W` over states given premises, then evaluates conclusion
probabilities `P_μ[c]`. The Belief Alignment / State Communication / Literal
Speaker utilities are functionals of these `P_μ[c]` values across the
conclusion space — and those values are jointly constrained by the
probabilistic Aristotelian inequalities. Subalternation `P[All A-C] ≤
P[Some A-C]` for the *same* posterior μ is a constraint the speaker model
respects automatically.

## Transfer theorems

The key result of this file: **if `φ` and `ψ` stand in a Boolean Aristotelian
relation, then they stand in the corresponding probabilistic relation under
every probability measure `μ`.** The Boolean → probabilistic direction is free;
the converse fails (μ-specific equalities can hold without Boolean entailment).
For example, two Boolean-`Unconnected` predicates `φ`, `ψ` can satisfy
`P_μ[φ] + P_μ[ψ] = 1` for a particular μ that happens to allocate measure
exactly to `{φ ∨ ψ}` and zero to `{¬φ ∧ ¬ψ}`, without being Boolean-contradictory.

## Related literature

The probabilistic-square tradition is distinct from the Logica Universalis
"abstract Aristotelian diagrams" tradition that this file specializes. Pfeifer
and collaborators (Pfeifer 2006, Pfeifer & Sanfilippo subsequent work) develop
probabilistic squares of opposition based on coherent conditional probability;
that line gives a different (conditional, not absolute) reading of the four
inequalities. The version here is the **unconditional / absolute** form,
appropriate for RSA-style models where the posterior `μ : PMF W` over states
is the object of study. (Bib entries for the Pfeifer line not yet in linglib;
add when a consumer needs the conditional version.)
-/

namespace Core.Opposition

open scoped ENNReal

variable {W : Type*} [Fintype W]

-- ============================================================================
-- §1. Probability of a Boolean predicate
-- ============================================================================

/-- The probability of a Boolean predicate `φ : W → Bool` under `μ : PMF W`,
    i.e. `μ({w | φ w = true})`. Built on `PMFFin.probOfSet`. -/
noncomputable def boolProb (μ : PMF W) (φ : W → Bool) : ℝ≥0∞ :=
  PMF.probOfSet μ {w | φ w = true}

@[inherit_doc boolProb]
notation "P[" φ " ; " μ "]" => boolProb μ φ

/-- Total probability: `P[φ] + P[¬φ] = 1`. The basic conservation law.
    Proof: convert each side to a Finset sum via `toOuterMeasure_apply_fintype`,
    then observe that the two indicators are pointwise complementary and sum to
    `μ x` at every x; PMF totality (`tsum_coe`) closes the result. -/
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
  have : ∑ x, μ x = (∑' x, μ x : ℝ≥0∞) :=
    (tsum_eq_sum (f := μ) (s := Finset.univ)
      (fun x h => absurd (Finset.mem_univ x) h)).symm
  rw [this, PMF.tsum_coe]

-- ============================================================================
-- §2. Probabilistic Aristotelian relations (Definition 1, convex form)
-- ============================================================================

/-- Probabilistic contradictoriness: `P[φ] + P[ψ] = 1`. Discrete case
    recovers `Contradictory`. -/
def ProbContradictory (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ + boolProb μ ψ = 1

/-- Probabilistic contrariety: `P[φ] + P[ψ] ≤ 1`, with strict inequality
    possible. Discrete case recovers `Contrary` (where `P[φ] + P[ψ] < 1`
    when neither holds at some world). -/
def ProbContrary (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ + boolProb μ ψ ≤ 1

/-- Probabilistic subcontrariety: `P[φ] + P[ψ] ≥ 1`. Discrete case recovers
    `Subcontrary` (where `P[φ] + P[ψ] > 1` when both hold at some world). -/
def ProbSubcontrary (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ + boolProb μ ψ ≥ 1

/-- Probabilistic subalternation: `P[φ] ≤ P[ψ]`. Discrete case (Boolean
    `Subaltern φ ψ`) implies this for *every* μ via monotonicity of `μ`. -/
def ProbSubaltern (μ : PMF W) (φ ψ : W → Bool) : Prop :=
  boolProb μ φ ≤ boolProb μ ψ

-- ============================================================================
-- §3. Transfer theorems: Boolean ⇒ Probabilistic (for every μ)
-- ============================================================================

/-- Boolean contradictoriness implies probabilistic contradictoriness for
    every probability measure. Direct from `boolProb_add_compl` once we
    note that `Contradictory φ ψ` makes ψ pointwise `!φ`. -/
theorem Contradictory.toProb {φ ψ : W → Bool}
    (h : Contradictory φ ψ) (μ : PMF W) :
    ProbContradictory μ φ ψ := by
  -- Show ψ = (fun w => !φ w) as Boolean functions, then apply boolProb_add_compl
  have hPointwise : ∀ w, ψ w = !φ w := by
    intro w
    have h1 := h.1 w
    have h2 := h.2 w
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

/-- Boolean subalternation implies probabilistic subalternation: if `φ ⊨ ψ`
    holds pointwise, then `P_μ[φ] ≤ P_μ[ψ]` for every μ (PMF monotonicity). -/
theorem Subaltern.toProb {φ ψ : W → Bool}
    (h : Subaltern φ ψ) (μ : PMF W) :
    ProbSubaltern μ φ ψ := by
  unfold ProbSubaltern boolProb PMF.probOfSet
  apply MeasureTheory.OuterMeasure.mono
  intro w hw
  exact h.1 w hw

/-- Boolean contrariety implies probabilistic contrariety: if `φ` and `ψ`
    cannot both be true, then `P[φ] + P[ψ] ≤ 1`. At each x, the two
    indicators sum to at most `μ x` (both nonzero would mean φ ∧ ψ at x). -/
theorem Contrary.toProb {φ ψ : W → Bool}
    (h : Contrary φ ψ) (μ : PMF W) :
    ProbContrary μ φ ψ := by
  classical
  unfold ProbContrary boolProb PMF.probOfSet
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
  have hbnd : ∀ x ∈ Finset.univ,
      ({w | φ w = true} : Set W).indicator μ x +
      ({w | ψ w = true} : Set W).indicator μ x ≤ μ x := by
    intro x _
    by_cases hφ : φ x = true
    · by_cases hψ : ψ x = true
      · exact absurd ⟨hφ, hψ⟩ (h.1 x)
      · simp [Set.indicator, hφ, hψ]
    · by_cases hψ : ψ x = true
      · simp [Set.indicator, hφ, hψ]
      · simp [Set.indicator, hφ, hψ]
  have htotal : ∑ x, μ x = (1 : ℝ≥0∞) := by
    have : ∑ y, μ y = (∑' y, μ y : ℝ≥0∞) :=
      (tsum_eq_sum (f := μ) (s := Finset.univ)
        (fun y hy => absurd (Finset.mem_univ y) hy)).symm
    rw [this, PMF.tsum_coe]
  calc (∑ x, (({w | φ w = true} : Set W).indicator μ x +
              ({w | ψ w = true} : Set W).indicator μ x))
      ≤ ∑ x, μ x := Finset.sum_le_sum hbnd
    _ = 1 := htotal

/-- Boolean subcontrariety implies probabilistic subcontrariety: if `φ ∨ ψ`
    is valid, then `P[φ] + P[ψ] ≥ 1`. At each x, the indicator sum is at
    least `μ x` (at least one of φ, ψ is true at x by `h.2`). -/
theorem Subcontrary.toProb {φ ψ : W → Bool}
    (h : Subcontrary φ ψ) (μ : PMF W) :
    ProbSubcontrary μ φ ψ := by
  classical
  unfold ProbSubcontrary boolProb PMF.probOfSet
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
  have hbnd : ∀ x ∈ Finset.univ,
      μ x ≤ ({w | φ w = true} : Set W).indicator μ x +
            ({w | ψ w = true} : Set W).indicator μ x := by
    intro x _
    rcases h.2 x with hφ | hψ
    · simp [Set.indicator, hφ]
    · by_cases hφ' : φ x = true
      · simp [Set.indicator, hφ', hψ]
      · simp [Set.indicator, hφ', hψ]
  have htotal : (1 : ℝ≥0∞) = ∑ x, μ x := by
    have : ∑ y, μ y = (∑' y, μ y : ℝ≥0∞) :=
      (tsum_eq_sum (f := μ) (s := Finset.univ)
        (fun y hy => absurd (Finset.mem_univ y) hy)).symm
    rw [this, PMF.tsum_coe]
  calc (1 : ℝ≥0∞)
      = ∑ x, μ x := htotal
    _ ≤ ∑ x, (({w | φ w = true} : Set W).indicator μ x +
              ({w | ψ w = true} : Set W).indicator μ x) :=
        Finset.sum_le_sum hbnd

end Core.Opposition
