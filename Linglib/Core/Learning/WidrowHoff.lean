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
* `sum_whCorrection_eq_zero_iff`: the orthogonality principle — the weighted
  total correction vanishes iff the residuals are orthogonal to every input
  direction.
* `whUpdate_single_eq_rescorlaWagner_update`: on binary cues with uniform
  salience a Widrow-Hoff step is a `Core.RescorlaWagner` trial.
* `whUpdate_single_eq_self_of_blocked`: blocking transfers through the
  specialization; overshadowing does not (non-uniform salience has no channel
  in binary cue coding).
-/

namespace Core

variable {k n : ℕ}

/-- The **Widrow-Hoff correction** on observing `(x, y)` is the rank-one
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

private theorem sum_mul_comm {k : ℕ} (x y : Fin k → ℝ) :
    ∑ l, x l * y l = Fintype.linearCombination ℝ x y := by
  rw [Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, mul_comm]

/-- Every linear functional on `Fin k → ℝ` is a linear combination of its
    basis values. -/
private theorem eq_linearCombination (w : (Fin k → ℝ) →ₗ[ℝ] ℝ) :
    w = Fintype.linearCombination ℝ
      (fun l => w fun j' => if l = j' then 1 else 0) := by
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.pi_apply_eq_sum_univ w s, Fintype.linearCombination_apply]

private theorem sum_whCorrection_apply {m : ℕ} (x : Fin m → Fin k → ℝ)
    (y : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (s' : Fin k → ℝ) (j : Fin n) :
    (∑ i, q i • whCorrection (x i) (y i) W) s' j
      = ∑ i, q i * ((y i j - W (x i) j)
          * Fintype.linearCombination ℝ s' (x i)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, whCorrection_apply,
             Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_mul_comm s' (x i)]
  ring

/-- The error-form and residual-form pairings sum to zero. -/
private theorem errorSum_add_residSum {m : ℕ} (x : Fin m → Fin k → ℝ)
    (y : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (s' : Fin k → ℝ) (j : Fin n) :
    (∑ i, q i * ((y i j - W (x i) j)
        * Fintype.linearCombination ℝ s' (x i)))
      + ∑ i, q i * ((W (x i) j - y i j)
          * Fintype.linearCombination ℝ s' (x i)) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

/-- By the **orthogonality principle** for the Widrow-Hoff rule
    ([widrow-hoff-1960]), the weighted total correction over a family of
    observations vanishes — the rule is at a fixed point in expectation —
    iff every weighted residual column is orthogonal to every linear
    functional of the inputs. The equilibrium condition is order-invariant
    by construction, whereas the incremental trajectory is order- and
    rate-dependent. -/
theorem sum_whCorrection_eq_zero_iff {m : ℕ} (x : Fin m → Fin k → ℝ)
    (y : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (W : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∑ i, q i • whCorrection (x i) (y i) W = 0 ↔
      ∀ (j : Fin n) (w : (Fin k → ℝ) →ₗ[ℝ] ℝ),
        ∑ i, q i * ((W (x i) j - y i j) * w (x i)) = 0 := by
  constructor
  · intro h j w
    rw [eq_linearCombination w]
    have h0 := congrFun
      (LinearMap.congr_fun h (fun l => w fun j' => if l = j' then 1 else 0)) j
    rw [sum_whCorrection_apply] at h0
    simp only [LinearMap.zero_apply, Pi.zero_apply] at h0
    have hzero := errorSum_add_residSum x y q W
      (fun l => w fun j' => if l = j' then 1 else 0) j
    linarith
  · intro h
    refine LinearMap.ext fun s' => funext fun j => ?_
    rw [sum_whCorrection_apply]
    have hres := h j (Fintype.linearCombination ℝ s')
    have hzero := errorSum_add_residSum x y q W s' j
    simp only [LinearMap.zero_apply, Pi.zero_apply]
    linarith

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

/-- When the outcome is already fully predicted on the trial, the
    Widrow-Hoff step leaves every cue weight unchanged — blocking transfers
    through the specialization, as in
    `Core.RescorlaWagner.no_learning_at_equilibrium` ([ellis-2006]). -/
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
