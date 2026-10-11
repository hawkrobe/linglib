module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Data.Multiset.Dominates
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Reference.Distinguishing

/-!
# The uniform-prior RSA model

Franke and Bergen's model has finite states, Boolean meanings, a uniform prior and no cost
(their eqs. 5–9). Here it is the pipeline of `Linglib.Pragmatics.RSA.Basic` at those arguments:
the literal listener is uniform on each choice's extension, and the speaker's and listeners'
masses reduce to informativity profiles, the multisets of extension sizes of the choices true at
a state. Findings then close by `decide`, uniformly in the rationality through
`Multiset.StrictDominates` certificates, or at a pinned natural rationality through ℕ inequalities
(`Multiset.divPowSum`).

## Main definitions

* `RSA.profile`, `RSA.fiberProfile`, `RSA.restProfile` — extension-size multisets.
* `RSA.uniformListener` — the listener of a truthful speaker at a uniform prior.
* `RSA.uniformSpeaker`, `RSA.uniformJointListener` — the pipeline at those arguments.

## Main results

* `RSA.distinguishes_ofDensity_uniformOn_iff` — a description distinguishes its referent
  under the literal listener exactly when it does under the meaning, so the referent is the
  listener's best guess.
* `RSA.uniformSpeaker_real_singleton_lt_of_card_lt`,
  `RSA.uniformSpeaker_real_singleton_lt_of_trueChoices_ssubset` — a smaller extension raises a
  true choice's share, and further true choices at a state lower it.
* `RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates` — the certificate
  register.
* `RSA.uniformJointListener_fst_real_lt_of_divPowSum`,
  `RSA.uniformJointListener_snd_real_lt_of_divPowSum` — the evaluation register.

## References

* [franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

/-! ### Informativity profiles

For a meaning `sem : C → Finset T` assigning each choice its extension, the profile of a state is
the multiset of extension sizes of the choices true there, and the fibre profile keeps the
choices heard as a given form under `obs : C → O`. The uniform speaker's masses are ratios of
inverse-power sums over these multisets. -/

section Profile

variable {T C O : Type*} [Fintype C] [DecidableEq T] (sem : C → Finset T)

/-- The choices true at a state. -/
def trueChoices (t : T) : Finset C := Finset.univ.filter (t ∈ sem ·)

@[simp] theorem mem_trueChoices {t : T} {c : C} : c ∈ trueChoices sem t ↔ t ∈ sem c := by
  simp [trueChoices]

/-- The informativity profile of a state is the multiset of extension sizes of the choices true
there. -/
def profile (t : T) : Multiset ℕ := (trueChoices sem t).val.map fun c => (sem c).card

variable [DecidableEq O] (obs : C → O)

/-- The profile restricted to choices heard as `o`. -/
def fiberProfile (o : O) (t : T) : Multiset ℕ :=
  ((trueChoices sem t).filter (obs · = o)).val.map fun c => (sem c).card

/-- The profile of true choices heard otherwise. -/
def restProfile (o : O) (t : T) : Multiset ℕ :=
  ((trueChoices sem t).filter (obs · ≠ o)).val.map fun c => (sem c).card

theorem profile_eq_fiberProfile_add_restProfile (o : O) (t : T) :
    profile sem t = fiberProfile sem obs o t + restProfile sem obs o t := by
  rw [fiberProfile, restProfile, ← Multiset.map_add, profile]
  congr 1
  rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]

theorem zero_notMem_profile (t : T) : 0 ∉ profile sem t := by
  simp only [profile, Multiset.mem_map, not_exists, not_and]
  intro c hc hcard
  rw [Finset.mem_val, trueChoices, Finset.mem_filter] at hc
  exact Finset.card_ne_zero_of_mem hc.2 hcard

theorem zero_notMem_fiberProfile (o : O) (t : T) : 0 ∉ fiberProfile sem obs o t := fun h =>
  zero_notMem_profile sem t
    (profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inl h))

theorem zero_notMem_restProfile (o : O) (t : T) : 0 ∉ restProfile sem obs o t := fun h =>
  zero_notMem_profile sem t
    (profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inr h))

/-- A nonempty fibre profile exhibits an `o`-shaped true choice — certificates carry their
own truth witnesses. -/
theorem exists_of_fiberProfile_ne_zero {o : O} {t : T} (h : fiberProfile sem obs o t ≠ 0) :
    ∃ c, obs c = o ∧ t ∈ sem c := by
  rw [fiberProfile, ne_eq, Multiset.map_eq_zero, Finset.val_eq_zero, ← ne_eq,
    ← Finset.nonempty_iff_ne_empty] at h
  obtain ⟨c, hc⟩ := h
  rw [Finset.mem_filter, trueChoices, Finset.mem_filter] at hc
  exact ⟨c, hc.2, hc.1.2⟩

/-- The real profile sum, expanded over the choices, is the sum of the informativity weights of
the choices true at the state. -/
theorem profile_invPowSum_toReal {α : ℝ} (hα : 0 ≤ α) (t : T) :
    ((profile sem t).invPowSum α).toReal
      = ∑ c, if t ∈ sem c then (((sem c).card : ℝ))⁻¹ ^ α else 0 := by
  rw [Multiset.invPowSum_toReal hα (zero_notMem_profile sem t), profile, Multiset.map_map,
    ← Finset.sum_filter, Finset.sum_eq_multiset_sum]
  rfl

theorem profile_ne_zero (hsem : ∀ t, ∃ c, t ∈ sem c) (t : T) : profile sem t ≠ 0 := by
  obtain ⟨c, hc⟩ := hsem t
  intro h
  rw [profile, Multiset.map_eq_zero, Finset.val_eq_zero] at h
  exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) (h ▸ Finset.notMem_empty c)

/-- A certificate closes the odds comparison. Strict domination of the fibre-by-rest cross
products decides it uniformly in the rationality, since the shared fibre-by-fibre terms
cancel. -/
theorem invPowSum_odds_lt_of_prodMul_strictDominates {α : ℝ} (hα : 0 < α) {o : O} {t₁ t₂ : T}
    (hcert : ((fiberProfile sem obs o t₂).prodMul (restProfile sem obs o t₁)).StrictDominates
      ((fiberProfile sem obs o t₁).prodMul (restProfile sem obs o t₂))) :
    ((fiberProfile sem obs o t₁).invPowSum α).toReal * ((profile sem t₂).invPowSum α).toReal
      < ((fiberProfile sem obs o t₂).invPowSum α).toReal
          * ((profile sem t₁).invPowSum α).toReal := by
  have hWne : ∀ t, (fiberProfile sem obs o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_fiberProfile sem obs o t)
  have hodds : (fiberProfile sem obs o t₁).invPowSum α * (restProfile sem obs o t₂).invPowSum α
      < (fiberProfile sem obs o t₂).invPowSum α * (restProfile sem obs o t₁).invPowSum α := by
    rw [← Multiset.invPowSum_prodMul hα.le, ← Multiset.invPowSum_prodMul hα.le]
    exact hcert.invPowSum_lt hα
      (Multiset.zero_notMem_prodMul (zero_notMem_fiberProfile sem obs o t₁)
        (zero_notMem_restProfile sem obs o t₂))
  rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul,
    ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (hWne t₁)
        (Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t₂)))
      (ENNReal.mul_ne_top (hWne t₂)
        (Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t₁))),
    profile_eq_fiberProfile_add_restProfile sem obs o t₁,
    profile_eq_fiberProfile_add_restProfile sem obs o t₂, Multiset.invPowSum_add,
    Multiset.invPowSum_add, mul_add, mul_add, mul_comm ((fiberProfile sem obs o t₂).invPowSum α)]
  exact ENNReal.add_lt_add_left (ENNReal.mul_ne_top (hWne t₁) (hWne t₂)) hodds

variable [Fintype T]

/-- The ℕ-cleared production mass of a choice, pooled over its true states, is its
common-denominator weight times, per true state, the product of the other states' cleared
partition sums. Pooled evaluation-register hypotheses compare these. -/
def pooledDivPowSum (D k : ℕ) (c : C) : ℕ :=
  (D / (sem c).card) ^ k
    * ∑ t ∈ sem c, ∏ t' ∈ Finset.univ.erase t, (profile sem t').divPowSum D k

theorem pooledDivPowSum_eq_sum (D k : ℕ) (c : C) :
    pooledDivPowSum sem D k c
      = ∑ t : T, if t ∈ sem c then
          (D / (sem c).card) ^ k * ∏ t' ∈ Finset.univ.erase t, (profile sem t').divPowSum D k
        else 0 := by
  rw [pooledDivPowSum, Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

/-- The ℕ-cleared posterior mass of an event of (state, latent) pairs given `c` for a
family of extensions sums, per pair, its common-denominator speaker weight times the product of
the other pairs' cleared partition sums. Family evaluation-register hypotheses compare
these. -/
def familyDivPowSum {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (sem : Λ → C → Finset T)
    (D k : ℕ) (c : C) (E : Finset (T × Λ)) : ℕ :=
  ∑ p ∈ E, (if p.1 ∈ sem p.2 c then (D / (sem p.2 c).card) ^ k else 0)
    * ∏ q ∈ Finset.univ.erase p, (profile (sem q.2) q.1).divPowSum D k

theorem familyDivPowSum_eq_sum {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (sem : Λ → C → Finset T)
    (D k : ℕ) (c : C) (E : Finset (T × Λ)) :
    familyDivPowSum sem D k c E
      = ∑ p, if p ∈ E then (if p.1 ∈ sem p.2 c then (D / (sem p.2 c).card) ^ k else 0)
          * ∏ q ∈ Finset.univ.erase p, (profile (sem q.2) q.1).divPowSum D k
        else 0 := by
  rw [familyDivPowSum, Finset.sum_ite_mem, Finset.univ_inter]

end Profile

section Weight

variable {T C : Type*} {α : ℝ} {S : Finset T}

private theorem support_nonempty {X : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {b : X → Measure T} {x : X} [IsProbabilityMeasure (b x)]
    (hS : ∀ t, b x {t} ≠ 0 ↔ t ∈ S) : S.Nonempty := by
  by_contra h
  refine one_ne_zero (α := ℝ≥0∞) ?_
  rw [← measure_univ (μ := b x), ← Finset.coe_univ, ← sum_measure_singleton]
  exact Finset.sum_eq_zero fun t _ ↦ not_not.1 fun ht ↦ h ⟨t, (hS t).1 ht⟩

private theorem weight_ne_top [DecidableEq T] (sem : C → Finset T) (hα : 0 < α)
    (hS : S.Nonempty) (c : C) :
    (if S ⊆ sem c then ((sem c).card : ℝ≥0∞)⁻¹ ^ α else 0) ≠ ∞ := by
  split_ifs with h
  exacts [ENNReal.rpow_ne_top_of_nonneg hα.le (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2
    (Finset.card_ne_zero.2 (hS.mono h)))), ENNReal.zero_ne_top]

private theorem uniformOn_univ_real_singleton_eq [Fintype T] [MeasurableSpace T]
    [DiscreteMeasurableSpace T] (t t' : T) :
    (uniformOn (Set.univ : Set T)).real {t} = (uniformOn Set.univ).real {t'} := by
  rw [uniformOn_univ_real_singleton, uniformOn_univ_real_singleton]

end Weight

variable {T C O : Type*} [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T]
  [Fintype C] [MeasurableSpace C] [DiscreteMeasurableSpace C] (sem : C → Finset T)

/-- The literal listener at a uniform prior (eq. 5) is uniform on each choice's extension. -/
noncomputable def uniformListener : Kernel C T :=
  listener (uniformOn Set.univ) (truthful fun c => ↑(sem c))

instance : IsFiniteKernel (uniformListener sem) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

theorem uniformListener_apply (c : C) : uniformListener sem c = uniformOn ↑(sem c) := by
  rw [uniformListener, listener_truthful_apply, uniformOn, uniformOn,
    cond_cond_eq_cond_inter' MeasurableSet.univ .of_discrete
      (by rw [Measure.count_apply_finite _ Set.finite_univ]; exact ENNReal.natCast_ne_top _),
    Set.univ_inter]

/-- At a uniform prior the listener of a graded meaning has masses on the states that are the
meaning's values
rescaled by the row sum, so a description distinguishes its referent under the listener exactly
when it does under the meaning. -/
theorem distinguishes_ofDensity_uniformOn_iff [Nonempty T] {U : Type*} [MeasurableSpace U]
    [Countable U] [MeasurableSingletonClass U] {m : U → T → ℝ≥0∞} {C : Finset T} {r : T}
    {u : U} (h0 : ∑ t, m u t ≠ 0) (htop : ∑ t, m u t ≠ ∞) :
    Reference.Distinguishes (fun u t ↦ Kernel.ofDensity (uniformOn Set.univ) m u {t}) C r u ↔
      Reference.Distinguishes m C r u := by
  simp_rw [Kernel.ofDensity_uniformOn_apply_singleton]
  exact Reference.distinguishes_comp_iff (φ := fun u x => x / ∑ t', m u t')
    fun _ _ h => ENNReal.div_lt_div_right h0 htop h

/-- The speaker at a uniform prior (eq. 7) is the best response to `uniformListener` at no
cost. -/
noncomputable abbrev uniformSpeaker (α : ℝ) : Kernel T C :=
  speaker α 0 (uniformListener sem) Measure.dirac

theorem uniformSpeaker_apply_singleton (α : ℝ) (t : T) (c : C) :
    uniformSpeaker sem α t {c}
      = uniformListener sem c {t} ^ α / ∑ c', uniformListener sem c' {t} ^ α := by
  simp only [uniformSpeaker, speaker_dirac_apply_singleton, Pi.zero_apply, mul_zero, neg_zero,
    Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- Speaker shares over any set of choices stay within the row's unit mass. -/
theorem sum_uniformSpeaker_real_singleton_le_one (α : ℝ) (t : T) (S : Finset C) :
    ∑ c ∈ S, (uniformSpeaker sem α t).real {c} ≤ 1 := by
  have hle : uniformSpeaker sem α t ↑S ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (speaker_apply_univ_le_one _ _ _ _ t)
  calc ∑ c ∈ S, (uniformSpeaker sem α t).real {c}
      = (uniformSpeaker sem α t).real ↑S := by
        simp_rw [measureReal_def, ← ENNReal.toReal_sum fun c _ => measure_ne_top _ _,
          sum_measure_singleton]
    _ ≤ 1 := by
        rw [measureReal_def, ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top hle

variable [DecidableEq T]

theorem uniformListener_apply_singleton (c : C) (t : T) :
    uniformListener sem c {t} = if t ∈ sem c then ((sem c).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [uniformListener_apply, uniformOn, cond_apply (sem c).measurableSet,
    Measure.count_apply_finset]
  split
  · rw [show ↑(sem c) ∩ {t} = ({t} : Set T) from
        Set.inter_eq_self_of_subset_right (by simpa using ‹t ∈ sem c›),
      Measure.count_singleton, mul_one]
  · rw [show ↑(sem c) ∩ {t} = (∅ : Set T) from by
        simpa [Set.eq_empty_iff_forall_notMem] using ‹t ∉ sem c›,
      measure_empty, mul_zero]

/-- The real share of a state under the uniform listener. -/
theorem uniformListener_real_singleton (c : C) (t : T) :
    (uniformListener sem c).real {t} = if t ∈ sem c then ((sem c).card : ℝ)⁻¹ else 0 := by
  rw [measureReal_def, uniformListener_apply_singleton]
  split <;> simp

theorem uniformListener_apply_singleton_ne_zero {c : C} {t : T} (h : t ∈ sem c) :
    uniformListener sem c {t} ≠ 0 := by
  rw [uniformListener_apply_singleton, ite_eq_left h]
  simp

theorem uniformSpeaker_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ sem c) : uniformSpeaker sem α t {c} = 0 :=
  speaker_dirac_apply_singleton_eq_zero hα (by rw [uniformListener_apply_singleton, ite_eq_right h])

theorem uniformSpeaker_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C}
    (h : t ∈ sem c) : uniformSpeaker sem α t {c} ≠ 0 :=
  speaker_dirac_apply_singleton_ne_zero hα (uniformListener_apply_singleton_ne_zero sem h)

/-- A state truly described by a single choice produces it with certainty. -/
theorem uniformSpeaker_apply_singleton_eq_one {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (hmem : t ∈ sem c) (hother : ∀ c' ≠ c, t ∉ sem c') : uniformSpeaker sem α t {c} = 1 :=
  speaker_dirac_apply_singleton_eq_one (L := uniformListener sem) hα
    (uniformListener_apply_singleton_ne_zero sem hmem) fun c' hc' => by
      rw [uniformListener_apply_singleton, ite_eq_right (hother c' hc')]

/-- A speaker over the uniform literal listener produces a choice at a state exactly when the
choice is true there. -/
theorem speaker_uniformListener_dirac_apply_singleton_ne_zero_iff {α : ℝ} (hα : 0 < α) (C' : C → ℝ)
    (t : T) (c : C) : speaker α C' (uniformListener sem) Measure.dirac t {c} ≠ 0 ↔ t ∈ sem c := by
  rw [speaker_dirac_apply_singleton_ne_zero_iff hα, uniformListener_apply_singleton]
  split_ifs with h
  · simpa using h
  · simpa using h

/-! ### A speaker who entertains several states

A speaker with a probability belief, facing the uniform literal listener at no cost, weights a
choice by the support `S` of her belief alone. She says only the choices true throughout `S`,
each with weight the inverse size of its extension to the power `α`. The speaker who knows the
state is the case `S = {t}`. -/

section Belief

variable {X : Type*} {α : ℝ} {b : X → Measure T} {x : X} [IsProbabilityMeasure (b x)]
  {S : Finset T} {c c' : C}

private theorem weight_eq (hα : 0 < α) (hS : ∀ t, b x {t} ≠ 0 ↔ t ∈ S) (c : C) :
    (b x).geomMean (fun t ↦ uniformListener sem c {t}) ^ α *
        ENNReal.ofReal (Real.exp (-(α * (0 : C → ℝ) c))) =
      if S ⊆ sem c then ((sem c).card : ℝ≥0∞)⁻¹ ^ α else 0 := by
  rw [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  split_ifs with h
  · rw [Measure.geomMean_of_forall_eq fun t ht ↦ by
      rw [uniformListener_apply_singleton, ite_eq_left (h ((hS t).1 ht))]]
  · obtain ⟨t, ht, htc⟩ := Finset.not_subset.1 h
    rw [Measure.geomMean_eq_zero_iff.2 ⟨t, (hS t).2 ht, by
      rw [uniformListener_apply_singleton, ite_eq_right htc]⟩, ENNReal.zero_rpow_of_pos hα]

variable [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]

theorem speaker_uniformListener_apply_singleton (hα : 0 < α) (hS : ∀ t, b x {t} ≠ 0 ↔ t ∈ S)
    (c : C) :
    speaker α 0 (uniformListener sem) b x {c} =
      (if S ⊆ sem c then ((sem c).card : ℝ≥0∞)⁻¹ ^ α else 0) /
        ∑ c', if S ⊆ sem c' then ((sem c').card : ℝ≥0∞)⁻¹ ^ α else 0 := by
  simp only [speaker_apply_singleton, weight_eq sem hα hS]

/-- She says only the choices true at every state she entertains, and weights each by the inverse
size of its extension to the power `α`. -/
theorem speaker_uniformListener_real_singleton (hα : 0 < α) (hS : ∀ t, b x {t} ≠ 0 ↔ t ∈ S)
    (c : C) :
    (speaker α 0 (uniformListener sem) b x).real {c} =
      (if S ⊆ sem c then ((sem c).card : ℝ)⁻¹ ^ α else 0) /
        ∑ c', if S ⊆ sem c' then ((sem c').card : ℝ)⁻¹ ^ α else 0 := by
  rw [measureReal_def, speaker_uniformListener_apply_singleton sem hα hS, ENNReal.toReal_div,
    ENNReal.toReal_sum fun c' _ ↦ weight_ne_top sem hα (support_nonempty hS) c']
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- When the choices true at every state she entertains are those true at one state, she speaks
as the speaker who knows that state. -/
theorem speaker_uniformListener_apply_eq_uniformSpeaker (hα : 0 < α)
    (hS : ∀ t, b x {t} ≠ 0 ↔ t ∈ S) {t : T} (h : ∀ c, S ⊆ sem c ↔ t ∈ sem c) :
    speaker α 0 (uniformListener sem) b x = uniformSpeaker sem α t :=
  Measure.ext_of_singleton fun c ↦ by
    simp only [speaker_uniformListener_apply_singleton sem hα hS, uniformSpeaker_apply_singleton,
      uniformListener_apply_singleton, h, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα]

end Belief

variable [DecidableEq O] (obs : C → O)

theorem sum_rpow_uniformListener {α : ℝ} (hα : 0 < α) (t : T) :
    ∑ c, uniformListener sem c {t} ^ α = (profile sem t).invPowSum α := by
  simp_rw [uniformListener_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [profile, Multiset.invPowSum, Multiset.map_map]
  rfl

/-- The speaker share of a true choice depends on the state only through its profile. -/
theorem uniformSpeaker_apply_singleton_of_profile_eq {α : ℝ} (hα : 0 < α) {t t' : T}
    (hprof : profile sem t = profile sem t') {c : C} (hmem : t ∈ sem c) (hmem' : t' ∈ sem c) :
    uniformSpeaker sem α t {c} = uniformSpeaker sem α t' {c} := by
  rw [uniformSpeaker_apply_singleton, uniformSpeaker_apply_singleton,
    sum_rpow_uniformListener sem hα, sum_rpow_uniformListener sem hα, hprof,
    uniformListener_apply_singleton, uniformListener_apply_singleton, ite_eq_left hmem,
    ite_eq_left hmem']

theorem sum_fiber_rpow_uniformListener {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (obs · = o), uniformListener sem c {t} ^ α
      = (fiberProfile sem obs o t).invPowSum α := by
  simp_rw [uniformListener_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [fiberProfile, Multiset.invPowSum, Multiset.map_map,
    show (Finset.univ.filter (obs · = o)).filter (fun c => t ∈ sem c)
      = (trueChoices sem t).filter (obs · = o) from by
    rw [trueChoices, Finset.filter_comm]]
  rfl

/-- Pooled speaker mass over an observation's fibre is a ratio of profile sums —
[franke-bergen-2020] eq. 8, structurally. -/
theorem sum_fiber_uniformSpeaker {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (obs · = o), uniformSpeaker sem α t {c}
      = (fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α := by
  simp_rw [uniformSpeaker_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul]
  rw [sum_fiber_rpow_uniformListener sem obs hα, sum_rpow_uniformListener sem hα,
    ← div_eq_mul_inv]

/-- On reals, the speaker's mass is the extension-size weight over the state's partition. -/
theorem uniformSpeaker_real_singleton {α : ℝ} (hα : 0 < α) (t : T) (c : C) :
    (uniformSpeaker sem α t).real {c}
      = (if t ∈ sem c then (((sem c).card : ℝ))⁻¹ ^ α else 0)
        / ((profile sem t).invPowSum α).toReal := by
  rw [measureReal_def, uniformSpeaker_apply_singleton, sum_rpow_uniformListener sem hα,
    ENNReal.toReal_div, uniformListener_apply_singleton, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem uniformSpeaker_real_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ sem c) : (uniformSpeaker sem α t).real {c} = 0 := by
  rw [measureReal_def, uniformSpeaker_apply_singleton_eq_zero sem hα h, ENNReal.toReal_zero]

/-- Of two states a choice is true of, the speaker uses the choice more at the state whose true
choices are jointly less informative. -/
theorem uniformSpeaker_real_singleton_lt_iff_invPowSum {α : ℝ} (hα : 0 < α) {t t' : T} {c : C}
    (h : t ∈ sem c) (h' : t' ∈ sem c) :
    (uniformSpeaker sem α t').real {c} < (uniformSpeaker sem α t).real {c} ↔
      (profile sem t).invPowSum α < (profile sem t').invPowSum α := by
  have hne (s : T) (hs : s ∈ sem c) : profile sem s ≠ 0 := fun h0 ↦ by
    rw [profile, Multiset.map_eq_zero, Finset.val_eq_zero] at h0
    exact Finset.notMem_empty c (h0 ▸ (mem_trueChoices sem).2 hs)
  have htop (s : T) : (profile sem s).invPowSum α ≠ ∞ :=
    Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem s)
  have hpos (s : T) (hs : s ∈ sem c) : 0 < ((profile sem s).invPowSum α).toReal :=
    ENNReal.toReal_pos (Multiset.invPowSum_pos hα.le (hne s hs)).ne' (htop s)
  rw [uniformSpeaker_real_singleton sem hα, uniformSpeaker_real_singleton sem hα,
    ite_eq_left h, ite_eq_left h', ← ENNReal.toReal_lt_toReal (htop t) (htop t')]
  exact div_lt_div_iff_of_pos_left
    (Real.rpow_pos_of_pos (inv_pos.2 (Nat.cast_pos.2 (Finset.card_pos.2 ⟨t, h⟩))) α)
    (hpos t' h') (hpos t h)

/-- As the rationality goes to zero the speaker chooses uniformly among the choices true at the
state. -/
theorem tendsto_uniformSpeaker_real_singleton_nhdsGT_zero (t : T) (c : C) :
    Filter.Tendsto (fun α : ℝ ↦ (uniformSpeaker sem α t).real {c}) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((if t ∈ sem c then 1 else 0) / ((trueChoices sem t).card : ℝ))) := by
  have hlim (c' : C) :
      Filter.Tendsto (fun α : ℝ ↦ if t ∈ sem c' then ((sem c').card : ℝ)⁻¹ ^ α else 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (if t ∈ sem c' then 1 else 0)) := by
    split_ifs with h
    · have hpos : (0 : ℝ) < ((sem c').card : ℝ)⁻¹ :=
        inv_pos.2 (Nat.cast_pos.2 (Finset.card_pos.2 ⟨t, h⟩))
      have := (Real.continuous_const_rpow hpos.ne').tendsto 0
      rw [Real.rpow_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact tendsto_const_nhds
  have hsum : Filter.Tendsto
      (fun α : ℝ ↦ ∑ c', if t ∈ sem c' then ((sem c').card : ℝ)⁻¹ ^ α else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((trueChoices sem t).card : ℝ)) := by
    simpa [trueChoices, Finset.sum_boole] using tendsto_finsetSum Finset.univ fun c' _ ↦ hlim c'
  by_cases h0 : (trueChoices sem t).card = 0
  · have hc : t ∉ sem c := fun h ↦ Finset.card_ne_zero_of_mem ((mem_trueChoices sem).2 h) h0
    rw [ite_eq_right hc, zero_div]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [uniformSpeaker_real_singleton sem hα, ite_eq_right hc, zero_div]
  · refine Filter.Tendsto.congr' ?_ ((hlim c).div hsum (by exact_mod_cast h0))
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [uniformSpeaker_real_singleton sem hα, profile_invPowSum_toReal sem hα.le]
    rfl

/-- Any other true choice caps a share strictly below one. -/
theorem uniformSpeaker_real_singleton_lt_one [DecidableEq C] {α : ℝ} (hα : 0 ≤ α) {t : T}
    {c c' : C} (hne : c' ≠ c) (hmem' : t ∈ sem c') : (uniformSpeaker sem α t).real {c} < 1 := by
  have hsum := sum_uniformSpeaker_real_singleton_le_one sem α t {c, c'}
  rw [Finset.sum_insert (by simpa using fun h => hne h.symm), Finset.sum_singleton] at hsum
  have hpos : 0 < (uniformSpeaker sem α t).real {c'} :=
    ENNReal.toReal_pos (uniformSpeaker_apply_singleton_ne_zero sem hα hmem')
      (measure_ne_top _ _)
  linarith

/-- Of two true choices, the one with the strictly smaller extension is produced with strictly
higher probability at every positive rationality, the qualitative claim of eq. 7 of
[franke-bergen-2020]. -/
theorem uniformSpeaker_real_singleton_lt_of_card_lt {α : ℝ} (hα : 0 < α) {t : T} {c c' : C}
    (hmem : t ∈ sem c) (hmem' : t ∈ sem c') (hcard : (sem c').card < (sem c).card) :
    (uniformSpeaker sem α t).real {c} < (uniformSpeaker sem α t).real {c'} := by
  rw [uniformSpeaker, speaker_dirac_real_singleton_lt_iff hα.le
      ⟨c, uniformListener_apply_singleton_ne_zero sem hmem⟩,
    uniformListener_apply_singleton, uniformListener_apply_singleton, ite_eq_left hmem,
    ite_eq_left hmem']
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  exact ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.2 (by exact_mod_cast hcard)) hα

/-- A state at which more choices are true gives each of them a strictly smaller share, so the
choices left unsaid count against it. -/
theorem uniformSpeaker_real_singleton_lt_of_trueChoices_ssubset {α : ℝ} (hα : 0 < α) {t t' : T}
    {c : C} (hmem : t ∈ sem c) (hsub : trueChoices sem t ⊂ trueChoices sem t') :
    (uniformSpeaker sem α t').real {c} < (uniformSpeaker sem α t).real {c} := by
  have hmono (c' : C) (h : t ∈ sem c') : t' ∈ sem c' :=
    (mem_trueChoices sem).1 (hsub.1 ((mem_trueChoices sem).2 h))
  have hpos {s : T} {c' : C} (h : s ∈ sem c') : (0 : ℝ) < ((sem c').card : ℝ)⁻¹ ^ α :=
    Real.rpow_pos_of_pos (inv_pos.2 (Nat.cast_pos.2 (Finset.card_pos.2 ⟨s, h⟩))) α
  have hnonneg (s : T) (c' : C) :
      (0 : ℝ) ≤ if s ∈ sem c' then ((sem c').card : ℝ)⁻¹ ^ α else 0 := by
    split_ifs with h
    exacts [(hpos h).le, le_rfl]
  obtain ⟨c₀, hc₀', hc₀⟩ := Finset.exists_of_ssubset hsub
  rw [mem_trueChoices] at hc₀' hc₀
  rw [uniformSpeaker_real_singleton sem hα, uniformSpeaker_real_singleton sem hα,
    ite_eq_left hmem, ite_eq_left (hmono c hmem), profile_invPowSum_toReal sem hα.le,
    profile_invPowSum_toReal sem hα.le]
  refine div_lt_div_of_pos_left (hpos hmem) (Finset.sum_pos' (fun c' _ ↦ hnonneg t c')
    ⟨c, Finset.mem_univ c, by rw [ite_eq_left hmem]; exact hpos hmem⟩)
    (Finset.sum_lt_sum (fun c' _ ↦ ?_) ⟨c₀, Finset.mem_univ c₀, ?_⟩)
  · by_cases h : t ∈ sem c'
    · rw [ite_eq_left h, ite_eq_left (hmono c' h)]
    · rw [ite_eq_right h]
      exact hnonneg t' c'
  · rw [ite_eq_right hc₀, ite_eq_left hc₀']
    exact hpos hc₀'

/-- When every true choice at a state has the same extension size, the speaker is uniform on
them, each share being `m⁻¹` at every rationality. -/
theorem uniformSpeaker_real_singleton_of_profile_replicate {α : ℝ} (hα : 0 < α) {t : T}
    {c : C} {m n : ℕ} (hprof : profile sem t = Multiset.replicate m n) (hmem : t ∈ sem c) :
    (uniformSpeaker sem α t).real {c} = (m : ℝ)⁻¹ := by
  have hcmem : (sem c).card ∈ profile sem t :=
    Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hmem⟩)
  have hn : (sem c).card = n := Multiset.eq_of_mem_replicate (hprof ▸ hcmem)
  have hn0 : n ≠ 0 := hn ▸ Finset.card_ne_zero_of_mem hmem
  have hx : (0 : ℝ) < ((n : ℝ))⁻¹ ^ α := Real.rpow_pos_of_pos (by positivity) α
  rw [uniformSpeaker_real_singleton sem hα, ite_eq_left hmem, hprof, hn,
    show ((Multiset.replicate m n).invPowSum α).toReal = m * ((n : ℝ))⁻¹ ^ α by
      rw [Multiset.invPowSum_replicate, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast],
    div_mul_eq_div_div_swap, div_self hx.ne', one_div]

/-- Exact speaker mass at a natural rationality, as a ratio of ℕ-valued common-denominator
sums. -/
theorem uniformSpeaker_real_singleton_divPowSum {k D : ℕ} [NeZero k] [NeZero D] {t : T}
    (hdvd : ∀ n ∈ profile sem t, n ∣ D) (c : C) :
    (uniformSpeaker sem k t).real {c}
      = (if t ∈ sem c then (((D / (sem c).card) ^ k : ℕ) : ℝ) else 0)
        / ((profile sem t).divPowSum D k : ℝ) := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hDk : ((D : ℝ) ^ k) ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (NeZero.ne D))
  rw [uniformSpeaker_real_singleton sem hα, Multiset.invPowSum_toReal_eq (NeZero.ne D) k hdvd]
  split
  · have hcard : (sem c).card ∣ D := hdvd _ (Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, ‹_›⟩))
    have hcard0 : ((sem c).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      fun h0 => NeZero.ne D (Nat.eq_zero_of_zero_dvd (h0 ▸ hcard))
    have hinv : (((sem c).card : ℝ))⁻¹ = ((D / (sem c).card : ℕ) : ℝ) / D := by
      rw [eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne D)),
        show (D : ℝ) = ((D / (sem c).card : ℕ) : ℝ) * ((sem c).card : ℝ) by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hcard],
        mul_comm _ ((sem c).card : ℝ), ← mul_assoc, inv_mul_cancel₀ hcard0, one_mul]
    rw [Real.rpow_natCast, hinv, div_pow, ← Nat.cast_pow, ← Nat.cast_pow, div_div_div_comm,
      div_self (Nat.cast_ne_zero.mpr (pow_ne_zero k (NeZero.ne D)) : ((D ^ k : ℕ) : ℝ) ≠ 0),
      div_one]
  · rw [zero_div, zero_div]

/-! ### The listener -/

variable [MeasurableSpace O] [MeasurableSingletonClass O]

section Joint

variable [Countable O]

/-- The joint listener at a uniform prior (eqs. 18b and 21b) hears the form of the choice of
`uniformSpeaker` and infers the state and the choice, her prior their joint. -/
noncomputable abbrev uniformJointListener (α : ℝ) : Kernel O (T × C) :=
  listener (uniformOn Set.univ ⊗ₘ uniformSpeaker sem α) fun p ↦ Measure.dirac (obs p.2)

private theorem sum_div_lt_sum_div_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {a b z : ι → ℝ}
    (hz : ∀ i, 0 < z i) :
    (∑ i, a i / z i) < (∑ i, b i / z i)
      ↔ (∑ i, a i * ∏ j ∈ Finset.univ.erase i, z j)
          < ∑ i, b i * ∏ j ∈ Finset.univ.erase i, z j := by
  have hP : (0 : ℝ) < ∏ j, z j := Finset.prod_pos fun j _ => hz j
  have key : ∀ f : ι → ℝ, (∑ i, f i / z i) * ∏ j, z j
      = ∑ i, f i * ∏ j ∈ Finset.univ.erase i, z j := by
    intro f
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_mul_eq_mul_div, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← mul_assoc,
      mul_div_assoc, div_self (hz i).ne', mul_one]
  rw [← mul_lt_mul_iff_left₀ hP, key, key]

/-- At a natural rationality, pooled preference between two `o`-shaped choices is the
ℕ-valued common-denominator comparison over all states, which kernel `decide` evaluates. The
strict inequality carries its own truth witness. -/
theorem uniformJointListener_snd_real_lt_of_divPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {k D : ℕ}
    [NeZero k] [NeZero D] (hdvd : ∀ t : T, ∀ n ∈ profile sem t, n ∣ D) {o : O} {c₁ c₂ : C}
    (h₁ : obs c₁ = o) (h₂ : obs c₂ = o)
    (hlt : pooledDivPowSum sem D k c₁ < pooledDivPowSum sem D k c₂) :
    (uniformJointListener sem obs k o).snd.real {c₁}
      < (uniformJointListener sem obs k o).snd.real {c₂} := by
  rw [pooledDivPowSum_eq_sum, pooledDivPowSum_eq_sum] at hlt
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  obtain ⟨t₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))
  have hprior : ∀ c : C,
      (∑ t : T, (uniformOn (Set.univ : Set T)).real {t} * (uniformSpeaker sem k t).real {c})
      = (uniformOn (Set.univ : Set T)).real {t₀} * ∑ t : T,
          (if t ∈ sem c then (((D / (sem c).card) ^ k : ℕ) : ℝ) else 0)
            / ((profile sem t).divPowSum D k : ℝ) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [uniformOn_univ_real_singleton_eq t t₀,
      uniformSpeaker_real_singleton_divPowSum sem (hdvd t)]
  rw [uniformJointListener, listener_compProd_dirac_snd_real_lt_iff _ _ _ h₁ h₂, hprior, hprior,
    mul_lt_mul_iff_right₀ (show (0 : ℝ) < (uniformOn (Set.univ : Set T)).real {t₀} from
      ENNReal.toReal_pos (by rw [uniformOn_univ, Measure.count_singleton]; simp)
        (measure_ne_top _ _)),
    sum_div_lt_sum_div_iff fun t => by
      exact_mod_cast Multiset.divPowSum_pos (NeZero.ne D) (hdvd t) (profile_ne_zero sem hsem t)]
  simp only [ite_mul, zero_mul]
  exact_mod_cast hlt

/-- On reals, listener preference reduces to the cross-multiplied profile comparison, since
the observation marginal and the shared prior cancel. Both registers' closers enter here. -/
theorem uniformJointListener_fst_real_lt_iff_invPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {α : ℝ}
    (hα : 0 < α) {o : O} {t₁ t₂ : T} :
    ((uniformJointListener sem obs α o).fst.real {t₁}
        < (uniformJointListener sem obs α o).fst.real {t₂})
      ↔ ((fiberProfile sem obs o t₁).invPowSum α).toReal * ((profile sem t₂).invPowSum α).toReal
        < ((fiberProfile sem obs o t₂).invPowSum α).toReal
            * ((profile sem t₁).invPowSum α).toReal := by
  have hWne : ∀ t, (fiberProfile sem obs o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_fiberProfile sem obs o t)
  have hZ0 : ∀ t, (profile sem t).invPowSum α ≠ 0 := fun t =>
    (Multiset.invPowSum_pos hα.le (profile_ne_zero sem hsem t)).ne'
  have hZne : ∀ t, (profile sem t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t)
  have hμ0 : (uniformOn (Set.univ : Set T)) {t₂} ≠ 0 := by
    rw [uniformOn_univ, Measure.count_singleton]; simp
  have key : ∀ t : T,
      (∑ c ∈ Finset.univ.filter (obs · = o),
        (uniformOn (Set.univ : Set T)).real {t} * (uniformSpeaker sem α t).real {c})
        = ((uniformOn (Set.univ : Set T)) {t}
            * ((fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α)).toReal :=
    fun t => by
      rw [← Finset.mul_sum, measureReal_def,
        show (∑ c ∈ Finset.univ.filter (obs · = o), (uniformSpeaker sem α t).real {c})
          = ((fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α).toReal from by
          rw [← sum_fiber_uniformSpeaker sem obs hα,
            ENNReal.toReal_sum fun c _ => measure_ne_top _ _]
          simp_rw [measureReal_def],
        ENNReal.toReal_mul]
  rw [uniformJointListener, listener_compProd_dirac_fst_real_lt_iff, key, key, show (uniformOn (Set.univ : Set T)) {t₁} = uniformOn Set.univ {t₂} from by
      rw [uniformOn_univ, uniformOn_univ, Measure.count_singleton, Measure.count_singleton],
    ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.div_ne_top (hWne t₁) (hZ0 t₁)))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.div_ne_top (hWne t₂) (hZ0 t₂))),
    ENNReal.mul_lt_mul_iff_right hμ0 (measure_ne_top _ _),
    ENNReal.div_lt_iff (Or.inl (hZ0 t₁)) (Or.inl (hZne t₁)),
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.lt_div_iff_mul_lt (Or.inl (hZ0 t₂)) (Or.inl (hZne t₂)),
    ← ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (hWne t₁) (hZne t₂)) (ENNReal.mul_ne_top (hWne t₂) (hZne t₁)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]

/-- Strict domination of the fibre-by-rest profile products decides listener preference
uniformly in the rationality. The certificate carries its own truth witness, so a finding is a
single decided `Multiset.StrictDominates` fact. An empty fibre at `t₁` is the support case,
where any nonempty product strictly dominates `0`. -/
theorem uniformJointListener_fst_real_lt_of_prodMul_strictDominates
    (hsem : ∀ t, ∃ c, t ∈ sem c) {α : ℝ} (hα : 0 < α) {o : O} {t₁ t₂ : T}
    (hcert : ((fiberProfile sem obs o t₂).prodMul (restProfile sem obs o t₁)).StrictDominates
      ((fiberProfile sem obs o t₁).prodMul (restProfile sem obs o t₂))) :
    (uniformJointListener sem obs α o).fst.real {t₁}
      < (uniformJointListener sem obs α o).fst.real {t₂} :=
  (uniformJointListener_fst_real_lt_iff_invPowSum sem obs hsem hα).mpr
    (invPowSum_odds_lt_of_prodMul_strictDominates sem obs hα hcert)

/-- At a natural rationality, with all profile entries dividing `D`, listener preference is
the ℕ-valued common-denominator comparison, which kernel `decide` evaluates. The strict
inequality carries its own truth witness. -/
theorem uniformJointListener_fst_real_lt_of_divPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {k D : ℕ}
    [NeZero k] [NeZero D] {o : O} {t₁ t₂ : T}
    (hdvd₁ : ∀ n ∈ profile sem t₁, n ∣ D) (hdvd₂ : ∀ n ∈ profile sem t₂, n ∣ D)
    (hlt : (fiberProfile sem obs o t₁).divPowSum D k * (profile sem t₂).divPowSum D k
      < (fiberProfile sem obs o t₂).divPowSum D k * (profile sem t₁).divPowSum D k) :
    (uniformJointListener sem obs k o).fst.real {t₁}
      < (uniformJointListener sem obs k o).fst.real {t₂} := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hfsub : ∀ t, ∀ n ∈ fiberProfile sem obs o t, n ∈ profile sem t := fun t n hn =>
    profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inl hn)
  rw [uniformJointListener_fst_real_lt_iff_invPowSum sem obs hsem hα]
  have key : ∀ (m₁ m₂ : Multiset ℕ), (∀ n ∈ m₁, n ∣ D) → (∀ n ∈ m₂, n ∣ D) →
      (m₁.invPowSum k).toReal * (m₂.invPowSum k).toReal
        = (m₁.divPowSum D k * m₂.divPowSum D k : ℕ) / ((D : ℝ) ^ k) ^ 2 := by
    intro m₁ m₂ h₁ h₂
    rw [Multiset.invPowSum_toReal_eq (NeZero.ne D) k h₁,
      Multiset.invPowSum_toReal_eq (NeZero.ne D) k h₂]
    push_cast
    ring
  rw [key _ _ (fun n hn => hdvd₁ n (hfsub t₁ n hn)) hdvd₂,
    key _ _ (fun n hn => hdvd₂ n (hfsub t₂ n hn)) hdvd₁,
    div_lt_div_iff_of_pos_right (by have := NeZero.ne D; positivity)]
  exact_mod_cast hlt

end Joint

/-! ### Latent families at the uniform prior -/

/-- A pair whose state the utterance does not describe under its latent receives no mass from
the listener. -/
theorem listener_uniformOn_family_apply_singleton_eq_zero {Λ : Type*} [Fintype Λ]
    [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ] (sem : Λ → C → Finset T) {α : ℝ} (hα : 0 < α)
    {c : C} {p : T × Λ} (hp : p.1 ∉ sem p.2 c) :
    listener (uniformOn Set.univ) (fun p : T × Λ ↦ uniformSpeaker (sem p.2) α p.1) c {p} = 0 :=
  listener_apply_singleton_eq_zero (uniformSpeaker_apply_singleton_eq_zero (sem p.2) hα hp)

/-- The state marginal of the listener of a latent family at the uniform prior is positive at a
state exactly when some latent makes the choice true there. -/
theorem listener_uniformOn_family_fst_apply_singleton_ne_zero_iff {Λ : Type*} [Fintype Λ]
    [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ] (sem : Λ → C → Finset T) {α : ℝ}
    (hα : 0 < α) (C' : C → ℝ) (c : C) (t : T) :
    (listener (uniformOn Set.univ)
      (fun p : T × Λ ↦ speaker α C' (uniformListener (sem p.2)) Measure.dirac p.1) c).fst {t} ≠ 0
        ↔ ∃ l, t ∈ sem l c := by
  rw [listener_fst_apply_singleton_ne_zero_iff]
  exact exists_congr fun l ↦ by
    rw [speaker_uniformListener_dirac_apply_singleton_ne_zero_iff (sem l) hα C']
    exact and_iff_right (uniformOn_univ_singleton_ne_zero _)

/-- For a latent family at a natural rationality and the uniform prior on (state, latent)
pairs, the listener's preference between two events of pairs is the ℕ-valued common-denominator
comparison, which kernel `decide` evaluates. -/
theorem listener_uniformOn_family_real_lt_of_divPowSum {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ] [Nonempty Λ] [Nonempty T]
    (sem : Λ → C → Finset T)
    (hsem : ∀ l t, ∃ c, t ∈ sem l c) {k D : ℕ} [NeZero k] [NeZero D]
    (hdvd : ∀ l t, ∀ n ∈ profile (sem l) t, n ∣ D) {c : C} {E₁ E₂ : Finset (T × Λ)}
    (hlt : familyDivPowSum sem D k c E₁ < familyDivPowSum sem D k c E₂) :
    (listener (uniformOn Set.univ) (fun p : T × Λ ↦ uniformSpeaker (sem p.2) k p.1) c).real ↑E₁
      < (listener (uniformOn Set.univ) (fun p : T × Λ ↦ uniformSpeaker (sem p.2) k p.1) c).real
        ↑E₂ := by
  rw [familyDivPowSum_eq_sum, familyDivPowSum_eq_sum] at hlt
  have key : ∀ E : Finset (T × Λ),
      (∑ p ∈ E, (uniformOn (Set.univ : Set (T × Λ))).real {p}
        * (speaker k 0 (uniformListener (sem p.2)) Measure.dirac p.1).real {c})
      = (Fintype.card (T × Λ) : ℝ)⁻¹ * ∑ p, (if p ∈ E then
          (if p.1 ∈ sem p.2 c then (((D / (sem p.2 c).card) ^ k : ℕ) : ℝ) else 0) else 0)
            / ((profile (sem p.2) p.1).divPowSum D k : ℝ) := by
    intro E
    simp_rw [ite_div, zero_div]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [uniformOn_univ_real_singleton, uniformSpeaker_real_singleton_divPowSum (sem p.2)
      (hdvd p.2 p.1), ite_div, zero_div]
  rw [listener_real_finset_lt_iff, key, key,
    mul_lt_mul_iff_right₀ (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)),
    sum_div_lt_sum_div_iff fun p => by
    exact_mod_cast Multiset.divPowSum_pos (NeZero.ne D) (hdvd p.2 p.1)
      (profile_ne_zero (sem p.2) (hsem p.2) p.1)]
  simp only [ite_mul, zero_mul] at hlt ⊢
  exact_mod_cast hlt

end RSA
