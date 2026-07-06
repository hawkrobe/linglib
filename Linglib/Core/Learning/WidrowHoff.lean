import Linglib.Core.Learning.RescorlaWagner
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi

/-!
# The Widrow-Hoff (LMS) learning rule
[widrow-hoff-1960] [rescorla-wagner-1972]

The delta rule for a linear map between real coordinate spaces: on observing
an input-output pair `(x, y)`, add the rank-one error-driven correction
`x' ↦ ⟨x, x'⟩ • (y − W x)`, scaled by a learning rate. On binary cue vectors
with uniform salience one step reproduces one Rescorla-Wagner trial
(`whUpdate_single_eq_rescorlaWagner_update`) — Widrow-Hoff is the real-valued
member of the error-driven family.

## Main declarations

* `whCorrection`, `whUpdate`: the correction and the `η`-scaled step.
* `whUpdate_eq_self_iff`: a step fixes `W` iff its correction vanishes.
* `whUpdate_single_eq_rescorlaWagner_update`: on binary cues with uniform
  salience a Widrow-Hoff step is a `Core.RescorlaWagner` trial.
* `whUpdate_single_eq_self_of_blocked`: blocking transfers through the
  specialization; overshadowing does not (non-uniform salience has no channel
  in binary cue coding).
-/

namespace Core

variable {k n : ℕ}

/-- The **Widrow-Hoff correction** on observing `(x, y)`: the rank-one
    error-driven update direction `x' ↦ ⟨x', x⟩ • (y − W x)`
    ([widrow-hoff-1960]'s `xᵀ(y − ŷ)`). -/
def whCorrection (x : Fin k → ℝ) (y : Fin n → ℝ)
    (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (Fintype.linearCombination ℝ x).smulRight (y - W x)

@[simp] theorem whCorrection_apply (x : Fin k → ℝ) (y : Fin n → ℝ)
    (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (x' : Fin k → ℝ) :
    whCorrection x y W x' = (∑ l, x' l * x l) • (y - W x) := rfl

/-- One **Widrow-Hoff step** on the observation `(x, y)` with learning
    rate `η`. -/
def whUpdate (η : ℝ) (x : Fin k → ℝ) (y : Fin n → ℝ)
    (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  W + η • whCorrection x y W

/-- A step fixes `W` iff the observation's correction vanishes. -/
theorem whUpdate_eq_self_iff {η : ℝ} (hη : η ≠ 0) (x : Fin k → ℝ)
    (y : Fin n → ℝ) (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    whUpdate η x y W = W ↔ whCorrection x y W = 0 := by
  unfold whUpdate
  constructor
  · intro h
    have h' : W + η • whCorrection x y W = W + 0 := by simpa using h
    exact (smul_eq_zero.mp (add_left_cancel h')).resolve_left hη
  · intro h
    rw [h, smul_zero, add_zero]

/-- On a binary cue vector with uniform salience, one Widrow-Hoff step
    reproduces one Rescorla-Wagner trial, reading cue `l`'s weight off the map
    at the `l`-th basis vector ([rescorla-wagner-1972]). Non-uniform salience
    has no channel in binary cue coding, so overshadowing is out of scope
    while blocking transfers (`whUpdate_single_eq_self_of_blocked`). -/
theorem whUpdate_single_eq_rescorlaWagner_update
    (rw : RescorlaWagner (Fin k)) (hsal : ∀ c, rw.salience c = 1)
    (present : Finset (Fin k)) (V : Fin k → ℝ) (l : Fin k) :
    whUpdate rw.learnRate (fun c => if c ∈ present then (1:ℝ) else 0)
        ((fun _ => rw.maxCond) : Fin 1 → ℝ)
        ((Fintype.linearCombination ℝ V).smulRight fun _ => 1)
        (Pi.single l 1) 0
      = rw.update present V l := by
  have hsum : (∑ l', if l' ∈ present then V l' else 0) = ∑ c ∈ present, V c := by
    simp [Finset.sum_ite_mem, Finset.univ_inter]
  have hind : (∑ x, if x ∈ present then (if x = l then (1:ℝ) else 0) else 0)
      = if l ∈ present then (1:ℝ) else 0 := by
    have hswap : ∀ x, (if x ∈ present then (if x = l then (1:ℝ) else 0) else 0)
        = if x = l then (if x ∈ present then (1:ℝ) else 0) else 0 := fun x => by
      split_ifs <;> simp_all
    simp only [hswap]
    rw [Finset.sum_ite_eq' Finset.univ l fun x => if x ∈ present then (1:ℝ) else 0]
    simp
  unfold whUpdate RescorlaWagner.update RescorlaWagner.predictionError
  simp only [LinearMap.add_apply, LinearMap.smul_apply, whCorrection_apply,
             LinearMap.smulRight_apply, Fintype.linearCombination_apply,
             Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
             Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul,
             zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsal,
             hsum]
  rw [hind]
  split_ifs with h <;> ring

/-- **Blocking transfers** to Widrow-Hoff: when the outcome is already fully
    predicted on the trial, the step leaves every cue weight unchanged —
    `Core.RescorlaWagner.no_learning_at_equilibrium` through the
    specialization ([ellis-2006]). -/
theorem whUpdate_single_eq_self_of_blocked
    (rw : RescorlaWagner (Fin k)) (hsal : ∀ c, rw.salience c = 1)
    (present : Finset (Fin k)) (V : Fin k → ℝ) (l : Fin k)
    (h_total : ∑ c ∈ present, V c = rw.maxCond) :
    whUpdate rw.learnRate (fun c => if c ∈ present then (1:ℝ) else 0)
        ((fun _ => rw.maxCond) : Fin 1 → ℝ)
        ((Fintype.linearCombination ℝ V).smulRight fun _ => 1)
        (Pi.single l 1) 0
      = V l := by
  rw [whUpdate_single_eq_rescorlaWagner_update rw hsal present V l]
  exact rw.no_learning_at_equilibrium present V h_total l

end Core
