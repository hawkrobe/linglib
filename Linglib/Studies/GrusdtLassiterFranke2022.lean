/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Pragmatics.RSA.Basic
import Linglib.Core.Probability.UniformOn

/-!
# Rational communication with conditionals

The toy model of [grusdt-lassiter-franke-2022], §2.3: three world states, each a probability
measure on the four worlds `w∅, w_A, w_C, w_AC`; four utterances; and the assertability
conditions of Table 1 — `P(C | A) ≥ θ` for the conditional, `P(C) ≥ θ` for the literal,
`P(A ∧ C) ≥ θ` for the conjunction and `P(C) > 1/2` for *likely C* — at `θ = 0.9`. The
Frank–Goodman speaker and listener over these states (`RSA.speaker`, `RSA.pragmaticListener`)
give the predictions of Table 2: the pragmatic listener who hears *if A then C* prefers `s2`,
where the conditional is the most informative assertable utterance, to `s1`, where the literal
*C* was available.

## Main definitions

* `GrusdtLassiterFranke2022.State.dist`: the three states of Table 2(a) as measures on
  `Bool × Bool`.
* `GrusdtLassiterFranke2022.Assertable`: the assertability conditions of Table 1, with the
  conditional's `P(C | A)` as `μ[C | A]`.
* `GrusdtLassiterFranke2022.S1`, `GrusdtLassiterFranke2022.L1`: the speaker and the pragmatic
  listener of Table 2.

## Main results

* `GrusdtLassiterFranke2022.ext_conditional` and its companions: Table 2(b), derived from the
  states.
* `GrusdtLassiterFranke2022.S1_s1_C`, …: the speaker shares of Table 2(d).
* `GrusdtLassiterFranke2022.L1_conditional_s2`, …: the listener posteriors of Table 2(e); in
  particular `11/16` for `s2` against `5/16` for `s1` on hearing the conditional.
* `GrusdtLassiterFranke2022.perfection_not_semantic`: at `s2` the conditional is assertable
  while *if not A then not C* is not.

## References

* [B. Grusdt, D. Lassiter and M. Franke, *Probabilistic modeling of rational communication with
  conditionals*][grusdt-lassiter-franke-2022]
-/

namespace GrusdtLassiterFranke2022

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

/-! ### World states, utterances and assertability (§2.2) -/

/-- The event that `A` holds, on worlds `(A, C) : Bool × Bool`. -/
def A : Set (Bool × Bool) := {w | w.1}

/-- The event that `C` holds. -/
def C : Set (Bool × Bool) := {w | w.2}

theorem A_eq : A = ↑({(true, true), (true, false)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A]

theorem C_eq : C = ↑({(true, true), (false, true)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [C]

theorem A_inter_C_eq : A ∩ C = ↑({(true, true)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A, C]

theorem Ac_eq : Aᶜ = ↑({(false, true), (false, false)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A]

theorem Ac_inter_Cc_eq : Aᶜ ∩ Cᶜ = ↑({(false, false)} : Finset (Bool × Bool)) := by
  ext ⟨a, c⟩; cases a <;> cases c <;> simp [A, C]

/-- The utterances of the toy example, in Table 1's order of informativity: the conjunction
*A and C*, the literal *C*, the conditional *if A then C*, and *likely C*. -/
inductive Utt
  | conjAC
  | C
  | conditional
  | likelyC
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utt := ⊤
instance : DiscreteMeasurableSpace Utt := ⟨fun _ => trivial⟩
instance : Nonempty Utt := ⟨.likelyC⟩

private theorem sum_Utt {M : Type*} [AddCommMonoid M] (f : Utt → M) :
    ∑ u, f u = f .conjAC + (f .C + (f .conditional + f .likelyC)) := by
  rw [show (Finset.univ : Finset Utt) = {.conjAC, .C, .conditional, .likelyC} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- The assertability threshold of Table 2, `θ = 0.9`. -/
noncomputable def θ : ℝ := 9 / 10

/-- Table 1: an utterance is assertable in a state `μ` when the probability it conveys reaches
the threshold — `P(A ∧ C) ≥ θ`, `P(C) ≥ θ`, `P(C | A) ≥ θ` — and *likely C* when `P(C) > 1/2`. -/
def Assertable (θ : ℝ) : Utt → Measure (Bool × Bool) → Prop
  | .conjAC, μ => θ ≤ μ.real (A ∩ C)
  | .C, μ => θ ≤ μ.real C
  | .conditional, μ => θ ≤ (μ[|A]).real C
  | .likelyC, μ => 1 / 2 < μ.real C

/-! ### The toy example (§2.3, Table 2) -/

/-- The three states of Table 2(a): in `s1` and `s3` Alex and Chris come to the party
independently, in `s2` "usually not without each other". -/
inductive State
  | s1
  | s2
  | s3
  deriving DecidableEq, Fintype

instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩
instance : Nonempty State := ⟨.s1⟩

private theorem sum_State {M : Type*} [AddCommMonoid M] (f : State → M) :
    ∑ s, f s = f .s1 + (f .s2 + f .s3) := by
  rw [show (Finset.univ : Finset State) = {.s1, .s2, .s3} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Table 2(a): the probability of each world `(A, C)` in each state. -/
noncomputable def State.cell : State → Bool × Bool → ℝ≥0
  | .s1, (true, true) => 81 / 100
  | .s1, (true, false) => 9 / 100
  | .s1, (false, true) => 9 / 100
  | .s1, (false, false) => 1 / 100
  | .s2, (true, true) => 3 / 5
  | .s2, (true, false) => 1 / 20
  | .s2, (false, true) => 1 / 20
  | .s2, (false, false) => 3 / 10
  | .s3, (true, true) => 9 / 25
  | .s3, (true, false) => 6 / 25
  | .s3, (false, true) => 6 / 25
  | .s3, (false, false) => 4 / 25

/-- A state as a probability measure on worlds. -/
noncomputable def State.dist (s : State) : Measure (Bool × Bool) :=
  Measure.sum fun w => (s.cell w : ℝ≥0∞) • Measure.dirac w

theorem State.dist_finset (s : State) (E : Finset (Bool × Bool)) :
    s.dist ↑E = ∑ w ∈ E, (s.cell w : ℝ≥0∞) := by
  rw [← sum_measure_singleton]
  exact Finset.sum_congr rfl fun w _ => Measure.sum_smul_dirac_singleton

theorem State.dist_real_finset (s : State) (E : Finset (Bool × Bool)) :
    s.dist.real ↑E = ∑ w ∈ E, (s.cell w : ℝ) := by
  rw [measureReal_def, State.dist_finset, ENNReal.toReal_sum fun _ _ => ENNReal.coe_ne_top]
  simp only [ENNReal.coe_toReal]

theorem State.sum_cell (s : State) : ∑ w, s.cell w = 1 := by
  cases s <;> simp [Fintype.sum_prod_type, State.cell] <;> norm_num

instance (s : State) : IsProbabilityMeasure s.dist :=
  (s.sum_cell ▸ hasSum_fintype s.cell).isProbabilityMeasure_sum_dirac_nnreal

/-- `P(C | A)` as a ratio of real masses. -/
theorem real_cond (s : State) : (s.dist[|A]).real C = s.dist.real (A ∩ C) / s.dist.real A := by
  rw [measureReal_def, cond_apply .of_discrete, ENNReal.toReal_mul, ENNReal.toReal_inv,
    measureReal_def, measureReal_def, div_eq_inv_mul]

/-- `P(¬C | ¬A)` as a ratio of real masses. -/
theorem real_cond_compl (s : State) :
    (s.dist[|Aᶜ]).real Cᶜ = s.dist.real (Aᶜ ∩ Cᶜ) / s.dist.real Aᶜ := by
  rw [measureReal_def, cond_apply .of_discrete, ENNReal.toReal_mul, ENNReal.toReal_inv,
    measureReal_def, measureReal_def, div_eq_inv_mul]

theorem real_A (s : State) : s.dist.real A = s.cell (true, true) + s.cell (true, false) := by
  rw [A_eq, State.dist_real_finset, Finset.sum_pair (by decide)]

theorem real_C (s : State) : s.dist.real C = s.cell (true, true) + s.cell (false, true) := by
  rw [C_eq, State.dist_real_finset, Finset.sum_pair (by decide)]

theorem real_A_inter_C (s : State) : s.dist.real (A ∩ C) = s.cell (true, true) := by
  rw [A_inter_C_eq, State.dist_real_finset, Finset.sum_singleton]

theorem real_Ac (s : State) : s.dist.real Aᶜ = s.cell (false, true) + s.cell (false, false) := by
  rw [Ac_eq, State.dist_real_finset, Finset.sum_pair (by decide)]

theorem real_Ac_inter_Cc (s : State) : s.dist.real (Aᶜ ∩ Cᶜ) = s.cell (false, false) := by
  rw [Ac_inter_Cc_eq, State.dist_real_finset, Finset.sum_singleton]

/-- The assertability extension of an utterance at the threshold `θ`. -/
def ext (u : Utt) : Set State := {s | Assertable θ u s.dist}

/-- Table 2(b): *likely C* is assertable everywhere. -/
theorem ext_likelyC : ext .likelyC = Set.univ := by
  ext s; cases s <;> simp [ext, Assertable, real_C, State.cell] <;> norm_num

/-- Table 2(b): the conditional is assertable in `s1` and `s2`, where `P(C | A)` is `9/10` and
`12/13`, and not in `s3`, where it is `3/5`. -/
theorem ext_conditional : ext .conditional = ↑({State.s1, .s2} : Finset State) := by
  ext s; cases s <;> simp [ext, Assertable, real_cond, real_A, real_A_inter_C, State.cell, θ] <;>
    norm_num

/-- Table 2(b): *C* is assertable in `s1` only. -/
theorem ext_C : ext .C = ↑({State.s1} : Finset State) := by
  ext s; cases s <;> simp [ext, Assertable, real_C, State.cell, θ] <;> norm_num

/-- Table 2(b): *A and C* is assertable nowhere. -/
theorem ext_conjAC : ext .conjAC = ∅ := by
  ext s; cases s <;> simp [ext, Assertable, real_A_inter_C, State.cell, θ] <;> norm_num

/-! ### Literal listener and speaker (Table 2(c), (d))

The Frank–Goodman model at `α = 1` without costs, against the uniform prior over the three
states: the literal listener conditions the prior on the extension, the speaker is
`RSA.speaker`, and the pragmatic listener is `RSA.pragmaticListener`. *A and C*, assertable in
no state, has the zero measure as its literal listener and drops out of the competition. -/

/-- The uniform prior over the three states. -/
noncomputable def prior : Measure State := uniformOn Set.univ

instance : IsProbabilityMeasure prior :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

theorem prior_singleton (s : State) : prior {s} = 3⁻¹ := by
  rw [prior, uniformOn_univ_apply_singleton, show Fintype.card State = 3 from rfl]; simp

theorem prior_real_singleton (s : State) : prior.real {s} = 1 / 3 := by
  rw [measureReal_def, prior_singleton, ENNReal.toReal_inv, one_div]; simp

/-- The literal listener: the prior conditioned on the utterance's extension. -/
noncomputable def L0 : Kernel Utt State := literalListener prior fun u => (ext u).indicator 1

/-- The literal listener is uniform on the extension. -/
theorem L0_apply (u : Utt) : L0 u = uniformOn (ext u) := by
  rw [L0, literalListener_indicator, Kernel.ofFunOfCountable_apply, prior, uniformOn,
    cond_cond_eq_cond_inter MeasurableSet.univ .of_discrete, Set.univ_inter]
  rfl

theorem L0_real_likelyC (s : State) : (L0 .likelyC).real {s} = 1 / 3 := by
  rw [L0_apply, ext_likelyC, ← prior, prior_real_singleton]

theorem L0_real_conjAC (s : State) : (L0 .conjAC).real {s} = 0 := by
  rw [L0_apply, ext_conjAC, uniformOn_empty_meas]; rfl

theorem L0_real_conditional_s1 : (L0 .conditional).real {.s1} = 1 / 2 := by
  rw [L0_apply, ext_conditional, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_conditional_s2 : (L0 .conditional).real {.s2} = 1 / 2 := by
  rw [L0_apply, ext_conditional, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_conditional_s3 : (L0 .conditional).real {.s3} = 0 := by
  rw [L0_apply, ext_conditional, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_C_s1 : (L0 .C).real {.s1} = 1 := by
  rw [L0_apply, ext_C, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_C_s2 : (L0 .C).real {.s2} = 0 := by
  rw [L0_apply, ext_C, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_real_C_s3 : (L0 .C).real {.s3} = 0 := by
  rw [L0_apply, ext_C, measureReal_def, uniformOn_finset_apply_singleton]
  simp

theorem L0_ne_top (u : Utt) (s : State) : L0 u {s} ≠ ⊤ := by
  rw [L0_apply]; exact measure_ne_top _ _

/-- The speaker of Table 2(d): `RSA.speaker` at `α = 1` without costs. -/
noncomputable def S1 : Kernel State Utt := speaker 1 (fun _ => 1) L0

instance : IsFiniteKernel S1 := inferInstanceAs (IsFiniteKernel (speaker _ _ _))

theorem S1_real (s : State) (u : Utt) :
    (S1 s).real {u} = (L0 u).real {s} / ∑ u', (L0 u').real {s} := by
  simp only [S1, measureReal_def, speaker_apply_singleton, ENNReal.rpow_one, mul_one]
  rw [ENNReal.toReal_div, ENNReal.toReal_sum fun u' _ => L0_ne_top u' s]

/-- Table 2(d), `s1`: `C` with share `6/11`, the conditional `3/11`, *likely C* `2/11`. -/
theorem S1_s1_C : (S1 .s1).real {.C} = 6 / 11 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s1, L0_real_conditional_s1, L0_real_likelyC]
  norm_num

theorem S1_s1_conditional : (S1 .s1).real {.conditional} = 3 / 11 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s1, L0_real_conditional_s1, L0_real_likelyC]
  norm_num

theorem S1_s1_likelyC : (S1 .s1).real {.likelyC} = 2 / 11 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s1, L0_real_conditional_s1, L0_real_likelyC]
  norm_num

/-- Table 2(d), `s2`: the conditional with share `3/5`, *likely C* `2/5`, `C` never. -/
theorem S1_s2_conditional : (S1 .s2).real {.conditional} = 3 / 5 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s2, L0_real_conditional_s2, L0_real_likelyC]
  norm_num

theorem S1_s2_likelyC : (S1 .s2).real {.likelyC} = 2 / 5 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s2, L0_real_conditional_s2, L0_real_likelyC]
  norm_num

theorem S1_s2_C : (S1 .s2).real {.C} = 0 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s2, L0_real_conditional_s2, L0_real_likelyC]
  norm_num

/-- Table 2(d), `s3`: *likely C* with certainty. -/
theorem S1_s3_likelyC : (S1 .s3).real {.likelyC} = 1 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s3, L0_real_conditional_s3, L0_real_likelyC]
  norm_num

theorem S1_s3_conditional : (S1 .s3).real {.conditional} = 0 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s3, L0_real_conditional_s3, L0_real_likelyC]
  norm_num

theorem S1_s3_C : (S1 .s3).real {.C} = 0 := by
  rw [S1_real, sum_Utt, L0_real_conjAC, L0_real_C_s3, L0_real_conditional_s3, L0_real_likelyC]
  norm_num

/-! ### The pragmatic listener (Table 2(e)) -/

/-- The pragmatic listener of Table 2(e): the posterior of `S1` against the uniform prior. -/
noncomputable def L1 : Kernel Utt State := pragmaticListener 1 (fun _ => 1) L0 prior

private theorem S1_ne_zero {s : State} {u : Utt} (h : (S1 s).real {u} ≠ 0) : S1 s {u} ≠ 0 :=
  fun h0 => h (by rw [measureReal_def, h0, ENNReal.toReal_zero])

theorem comp_conditional_ne_zero : (S1 ∘ₘ prior) {Utt.conditional} ≠ 0 :=
  comp_apply_singleton_ne_zero S1 prior (w := .s2) (by rw [prior_singleton]; norm_num)
    (S1_ne_zero (by rw [S1_s2_conditional]; norm_num))

theorem comp_C_ne_zero : (S1 ∘ₘ prior) {Utt.C} ≠ 0 :=
  comp_apply_singleton_ne_zero S1 prior (w := .s1) (by rw [prior_singleton]; norm_num)
    (S1_ne_zero (by rw [S1_s1_C]; norm_num))

theorem comp_likelyC_ne_zero : (S1 ∘ₘ prior) {Utt.likelyC} ≠ 0 :=
  comp_apply_singleton_ne_zero S1 prior (w := .s1) (by rw [prior_singleton]; norm_num)
    (S1_ne_zero (by rw [S1_s1_likelyC]; norm_num))

theorem L1_real (u : Utt) (hu : (S1 ∘ₘ prior) {u} ≠ 0) (s : State) :
    (L1 u).real {s} = (S1 s).real {u} / ∑ s', (S1 s').real {u} := by
  show ((S1†prior) u).real {s} = _
  rw [posterior_real_singleton _ _ hu, Measure.comp_real_singleton, prior_real_singleton]
  simp_rw [prior_real_singleton, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (by norm_num)]

/-- Table 2(e): hearing the conditional, the listener puts `11/16` on `s2`, `5/16` on `s1` and
nothing on `s3`. -/
theorem L1_conditional_s2 : (L1 .conditional).real {.s2} = 11 / 16 := by
  rw [L1_real _ comp_conditional_ne_zero, sum_State, S1_s1_conditional, S1_s2_conditional,
    S1_s3_conditional]
  norm_num

theorem L1_conditional_s1 : (L1 .conditional).real {.s1} = 5 / 16 := by
  rw [L1_real _ comp_conditional_ne_zero, sum_State, S1_s1_conditional, S1_s2_conditional,
    S1_s3_conditional]
  norm_num

theorem L1_conditional_s3 : (L1 .conditional).real {.s3} = 0 := by
  rw [L1_real _ comp_conditional_ne_zero, sum_State, S1_s1_conditional, S1_s2_conditional,
    S1_s3_conditional]
  norm_num

/-- Table 2(e): hearing `C`, the listener identifies `s1`. -/
theorem L1_C_s1 : (L1 .C).real {.s1} = 1 := by
  rw [L1_real _ comp_C_ne_zero, sum_State, S1_s1_C, S1_s2_C, S1_s3_C]
  norm_num

/-- Table 2(e): hearing *likely C*, the listener puts `55/87` on `s3`, `22/87` on `s2` and
`10/87` on `s1`. -/
theorem L1_likelyC_s3 : (L1 .likelyC).real {.s3} = 55 / 87 := by
  rw [L1_real _ comp_likelyC_ne_zero, sum_State, S1_s1_likelyC, S1_s2_likelyC, S1_s3_likelyC]
  norm_num

theorem L1_likelyC_s2 : (L1 .likelyC).real {.s2} = 22 / 87 := by
  rw [L1_real _ comp_likelyC_ne_zero, sum_State, S1_s1_likelyC, S1_s2_likelyC, S1_s3_likelyC]
  norm_num

theorem L1_likelyC_s1 : (L1 .likelyC).real {.s1} = 10 / 87 := by
  rw [L1_real _ comp_likelyC_ne_zero, sum_State, S1_s1_likelyC, S1_s2_likelyC, S1_s3_likelyC]
  norm_num

/-- Hearing *if A then C*, the listener prefers `s2` to `s1`: the speaker in `s1` would have
said *C* (`S1_s1_C`), so the conditional signals the state where it is the most informative
assertable utterance. -/
theorem l1_conditional_prefers_s2 :
    (L1 .conditional).real {.s1} < (L1 .conditional).real {.s2} := by
  rw [L1_conditional_s1, L1_conditional_s2]; norm_num

/-- Hearing *likely C*, the listener prefers `s3` to `s1`: in `s1` and `s2` a stronger utterance
was available. -/
theorem l1_likelyC_prefers_s3 : (L1 .likelyC).real {.s1} < (L1 .likelyC).real {.s3} := by
  rw [L1_likelyC_s1, L1_likelyC_s3]; norm_num

/-! ### Conditional perfection

The paper derives conditional perfection — hearing *if A then C* as *if not A then not C* — as
a pragmatic inference. It is absent from the assertability semantics: at `s2` the conditional is
assertable while `P(¬C | ¬A) = 6/7` falls short of `θ`. -/

theorem perfection_not_semantic :
    Assertable θ .conditional State.s2.dist ∧ ¬ θ ≤ (State.s2.dist[|Aᶜ]).real Cᶜ := by
  simp only [Assertable, real_cond, real_cond_compl, real_A, real_A_inter_C, real_Ac,
    real_Ac_inter_Cc, State.cell, θ]
  norm_num

end GrusdtLassiterFranke2022
