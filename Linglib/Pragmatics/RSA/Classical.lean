import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.Profile
import Linglib.Core.Probability.UniformOn

/-!
# The classical RSA model

Finite states, Boolean meanings, a uniform prior, and no cost — the model of
[franke-bergen-2020] eqs. 5–9 — as the pipeline of `Linglib.Pragmatics.RSA.Basic` at those
arguments: the literal listener is uniform on each choice's extension, and the speaker's
and listeners' masses reduce to the informativity profiles of `Linglib.Pragmatics.RSA.Profile`.
Findings then close by `decide`: uniformly in the rationality through
`Multiset.StrictDominates` certificates, or at a pinned natural rationality through ℕ
inequalities (`Multiset.divPowSum`).

## Main definitions

* `RSA.classicalListener` — `literalListener` at a uniform prior and indicator meanings.
* `RSA.classicalSpeaker`, `RSA.classicalJointListener` — the pipeline at those arguments.

## Main results

* `RSA.classicalSpeaker_real_singleton_lt_of_card_lt` — informativity monotonicity.
* `RSA.classicalJointListener_fst_real_lt_of_prodMul_strictDominates` — the certificate
  register.
* `RSA.classicalJointListener_fst_real_lt_of_divPowSum`,
  `RSA.classicalJointListener_snd_real_lt_of_divPowSum` — the evaluation register.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {T C O : Type*} [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [DiscreteMeasurableSpace T] [Fintype C] [MeasurableSpace C] [DiscreteMeasurableSpace C]
  (sem : C → Finset T)

/-- The classical literal listener (eq. 5): uniform on each choice's extension. -/
noncomputable def classicalListener : Kernel C T :=
  literalListener (uniformOn Set.univ) fun c => (↑(sem c) : Set T).indicator 1

omit [DecidableEq T] in
theorem classicalListener_apply (c : C) : classicalListener sem c = uniformOn ↑(sem c) := by
  rw [classicalListener, literalListener_indicator, Kernel.ofFunOfCountable_apply]
  rw [uniformOn, uniformOn, cond_cond_eq_cond_inter' MeasurableSet.univ .of_discrete
    (by rw [Measure.count_apply_finite _ Set.finite_univ]; exact ENNReal.natCast_ne_top _),
    Set.univ_inter]

theorem classicalListener_apply_singleton (c : C) (t : T) :
    classicalListener sem c {t} = if t ∈ sem c then ((sem c).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [classicalListener_apply, uniformOn, cond_apply (sem c).measurableSet,
    Measure.count_apply_finset]
  split
  · rw [show ↑(sem c) ∩ {t} = ({t} : Set T) from
        Set.inter_eq_self_of_subset_right (by simpa using ‹t ∈ sem c›),
      Measure.count_singleton, mul_one]
  · rw [show ↑(sem c) ∩ {t} = (∅ : Set T) from by
        simpa [Set.eq_empty_iff_forall_notMem] using ‹t ∉ sem c›,
      measure_empty, mul_zero]

theorem classicalListener_apply_singleton_le_one (c : C) (t : T) :
    classicalListener sem c {t} ≤ 1 := by
  rw [classicalListener_apply_singleton]
  split
  · exact ENNReal.inv_le_one.mpr (by exact_mod_cast Finset.card_pos.mpr ⟨t, ‹_›⟩)
  · exact zero_le_one

theorem classicalListener_apply_singleton_ne_zero {c : C} {t : T} (h : t ∈ sem c) :
    classicalListener sem c {t} ≠ 0 := by
  rw [classicalListener_apply_singleton, if_pos h]
  simp

/-- The classical speaker (eq. 7): best response to `classicalListener` at no cost. -/
noncomputable abbrev classicalSpeaker (α : ℝ) : Kernel T C := speaker α 1 (classicalListener sem)

omit [DecidableEq T] in
theorem classicalSpeaker_apply_singleton (α : ℝ) (t : T) (c : C) :
    classicalSpeaker sem α t {c}
      = classicalListener sem c {t} ^ α / ∑ c', classicalListener sem c' {t} ^ α := by
  simp only [classicalSpeaker, speaker_apply_singleton, Pi.one_apply, mul_one]

omit [DecidableEq T] in
theorem classicalSpeaker_apply_univ_le_one (α : ℝ) (t : T) :
    classicalSpeaker sem α t Set.univ ≤ 1 :=
  Kernel.ofWeights_apply_univ_le_one _ t

/-- Every state has a true choice — the proviso making the classical speaker a probability
kernel. -/
theorem isMarkovKernel_classicalSpeaker {α : ℝ} (hα : 0 ≤ α) (hsem : ∀ t, ∃ c, t ∈ sem c) :
    IsMarkovKernel (classicalSpeaker sem α) :=
  isMarkovKernel_speaker hα (fun _ => one_ne_zero) (fun _ => ENNReal.one_ne_top) _
    (fun c t => classicalListener_apply_singleton_le_one sem c t)
    fun t => (hsem t).imp fun _ h => classicalListener_apply_singleton_ne_zero sem h

theorem classicalSpeaker_apply_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ sem c) : classicalSpeaker sem α t {c} = 0 :=
  speaker_apply_singleton_eq_zero hα (by rw [classicalListener_apply_singleton, if_neg h])

theorem classicalSpeaker_apply_singleton_ne_zero {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C}
    (h : t ∈ sem c) : classicalSpeaker sem α t {c} ≠ 0 :=
  speaker_apply_singleton_ne_zero hα (fun _ => one_ne_zero) (fun _ => ENNReal.one_ne_top)
    (fun c' => classicalListener_apply_singleton_le_one sem c' t)
    (classicalListener_apply_singleton_ne_zero sem h)

variable [DecidableEq O] (obs : C → O)

theorem sum_rpow_classicalListener {α : ℝ} (hα : 0 < α) (t : T) :
    ∑ c, classicalListener sem c {t} ^ α = (profile sem t).invPowSum α := by
  simp_rw [classicalListener_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [profile, Multiset.invPowSum, Multiset.map_map]
  rfl

theorem sum_fiber_rpow_classicalListener {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (obs · = o), classicalListener sem c {t} ^ α
      = (fiberProfile sem obs o t).invPowSum α := by
  simp_rw [classicalListener_apply_singleton, apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα,
    ← Finset.sum_filter]
  rw [fiberProfile, Multiset.invPowSum, Multiset.map_map,
    show (Finset.univ.filter (obs · = o)).filter (fun c => t ∈ sem c)
      = (trueChoices sem t).filter (obs · = o) from by
    rw [trueChoices, Finset.filter_comm]]
  rfl

/-- Pooled speaker mass over an observation's fibre is a ratio of profile sums —
[franke-bergen-2020] eq. 8, structurally. -/
theorem sum_fiber_classicalSpeaker {α : ℝ} (hα : 0 < α) (o : O) (t : T) :
    ∑ c ∈ Finset.univ.filter (obs · = o), classicalSpeaker sem α t {c}
      = (fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α := by
  simp_rw [classicalSpeaker_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul]
  rw [sum_fiber_rpow_classicalListener sem obs hα, sum_rpow_classicalListener sem hα,
    ← div_eq_mul_inv]

/-- Exact speaker mass on reals: extension-size weight over the state's partition. -/
theorem classicalSpeaker_real_singleton {α : ℝ} (hα : 0 < α) (t : T) (c : C) :
    (classicalSpeaker sem α t).real {c}
      = (if t ∈ sem c then (((sem c).card : ℝ))⁻¹ ^ α else 0)
        / ((profile sem t).invPowSum α).toReal := by
  rw [measureReal_def, classicalSpeaker_apply_singleton, sum_rpow_classicalListener sem hα,
    ENNReal.toReal_div, classicalListener_apply_singleton, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem classicalSpeaker_real_singleton_eq_zero {α : ℝ} (hα : 0 < α) {t : T} {c : C}
    (h : t ∉ sem c) : (classicalSpeaker sem α t).real {c} = 0 := by
  rw [measureReal_def, classicalSpeaker_apply_singleton_eq_zero sem hα h, ENNReal.toReal_zero]

omit [DecidableEq T] in
/-- Speaker shares over any set of choices stay within the row's unit mass. -/
theorem sum_classicalSpeaker_real_singleton_le_one (α : ℝ) (t : T) (S : Finset C) :
    ∑ c ∈ S, (classicalSpeaker sem α t).real {c} ≤ 1 := by
  have hle : classicalSpeaker sem α t ↑S ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (classicalSpeaker_apply_univ_le_one sem α t)
  calc ∑ c ∈ S, (classicalSpeaker sem α t).real {c}
      = (classicalSpeaker sem α t).real ↑S := by
        simp_rw [measureReal_def, ← ENNReal.toReal_sum fun c _ => measure_ne_top _ _,
          sum_measure_singleton]
    _ ≤ 1 := by
        rw [measureReal_def, ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top hle

/-- Competition: any other true choice caps a share strictly below one. -/
theorem classicalSpeaker_real_singleton_lt_one [DecidableEq C] {α : ℝ} (hα : 0 ≤ α) {t : T}
    {c c' : C} (hne : c' ≠ c) (hmem' : t ∈ sem c') : (classicalSpeaker sem α t).real {c} < 1 := by
  have hsum := sum_classicalSpeaker_real_singleton_le_one sem α t {c, c'}
  rw [Finset.sum_insert (by simpa using fun h => hne h.symm), Finset.sum_singleton] at hsum
  have hpos : 0 < (classicalSpeaker sem α t).real {c'} :=
    ENNReal.toReal_pos (classicalSpeaker_apply_singleton_ne_zero sem hα hmem')
      (measure_ne_top _ _)
  linarith

/-- Informativity monotonicity ([franke-bergen-2020] eq. 7's qualitative claim): between two
true choices, the one with the strictly smaller extension is produced with strictly higher
probability, at every positive rationality. -/
theorem classicalSpeaker_real_singleton_lt_of_card_lt {α : ℝ} (hα : 0 < α) {t : T} {c c' : C}
    (hmem : t ∈ sem c) (hmem' : t ∈ sem c') (hcard : (sem c').card < (sem c).card) :
    (classicalSpeaker sem α t).real {c} < (classicalSpeaker sem α t).real {c'} := by
  have hterm : classicalListener sem c {t} ^ α * (1 : C → ℝ≥0∞) c ≠ 0 :=
    mul_ne_zero (weight_rpow_ne_zero hα.le (classicalListener_apply_singleton_ne_zero sem hmem))
      one_ne_zero
  have hZ0 : (∑ u, classicalListener sem u {t} ^ α * (1 : C → ℝ≥0∞) u) ≠ 0 := fun h =>
    hterm (le_antisymm (le_trans
      (Finset.single_le_sum (f := fun u => classicalListener sem u {t} ^ α * (1 : C → ℝ≥0∞) u)
        (fun u _ => zero_le) (Finset.mem_univ c)) h.le) zero_le)
  rw [classicalSpeaker, speaker, Kernel.ofWeights_real_singleton_lt_iff t hZ0
      (ENNReal.sum_ne_top.mpr fun u _ => ENNReal.mul_ne_top
        (weight_rpow_ne_top hα.le (classicalListener_apply_singleton_le_one sem u t))
        ENNReal.one_ne_top),
    classicalListener_apply_singleton, classicalListener_apply_singleton, if_pos hmem,
    if_pos hmem']
  simp only [Pi.one_apply, mul_one]
  exact ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.2 (by exact_mod_cast hcard)) hα

/-- Softmax constant-utility invariance: when every true choice at a state has the same
extension size, the speaker is uniform on them — each share is `m⁻¹` regardless of the
rationality. -/
theorem classicalSpeaker_real_singleton_of_profile_replicate {α : ℝ} (hα : 0 < α) {t : T}
    {c : C} {m n : ℕ} (hprof : profile sem t = Multiset.replicate m n) (hmem : t ∈ sem c) :
    (classicalSpeaker sem α t).real {c} = (m : ℝ)⁻¹ := by
  have hcmem : (sem c).card ∈ profile sem t :=
    Multiset.mem_map_of_mem _ (by
      rw [Finset.mem_val, trueChoices, Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hmem⟩)
  have hn : (sem c).card = n := Multiset.eq_of_mem_replicate (hprof ▸ hcmem)
  have hn0 : n ≠ 0 := hn ▸ Finset.card_ne_zero_of_mem hmem
  have hx : (0 : ℝ) < ((n : ℝ))⁻¹ ^ α := Real.rpow_pos_of_pos (by positivity) α
  rw [classicalSpeaker_real_singleton sem hα, if_pos hmem, hprof, hn,
    show ((Multiset.replicate m n).invPowSum α).toReal = m * ((n : ℝ))⁻¹ ^ α by
      rw [Multiset.invPowSum_replicate, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast],
    div_mul_eq_div_div_swap, div_self hx.ne', one_div]

/-- Exact speaker mass at a natural rationality, as a ratio of ℕ-valued common-denominator
sums. -/
theorem classicalSpeaker_real_singleton_divPowSum {k D : ℕ} [NeZero k] [NeZero D] {t : T}
    (hdvd : ∀ n ∈ profile sem t, n ∣ D) (c : C) :
    (classicalSpeaker sem k t).real {c}
      = (if t ∈ sem c then (((D / (sem c).card) ^ k : ℕ) : ℝ) else 0)
        / ((profile sem t).divPowSum D k : ℝ) := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hDk : ((D : ℝ) ^ k) ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr (NeZero.ne D))
  rw [classicalSpeaker_real_singleton sem hα, Multiset.invPowSum_toReal_eq (NeZero.ne D) k hdvd]
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

/-! ### The classical listener -/

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty T] [Nonempty C]

/-- The classical joint listener (eqs. 18b/21b): the pragmatic listener of the classical
speaker at a uniform prior, hearing the form of the speaker's choice. -/
noncomputable abbrev classicalJointListener (α : ℝ) : Kernel O (T × C) :=
  jointListener α 1 (classicalListener sem) (uniformOn Set.univ) obs

omit [DecidableEq O] [Nonempty T] [Nonempty C] in
/-- A state truly described by an `o`-shaped choice witnesses a positive observation
marginal. -/
theorem map_comp_classicalSpeaker_ne_zero {α : ℝ} (hα : 0 ≤ α) {t : T} {c : C} {o : O}
    (hc : obs c = o) (hmem : t ∈ sem c) :
    ((classicalSpeaker sem α ∘ₘ uniformOn Set.univ).map obs) {o} ≠ 0 :=
  map_comp_speaker_ne_zero α 1 (classicalListener sem) _ obs
    (by rw [uniformOn_univ, Measure.count_singleton]; simp) hc
    (classicalSpeaker_apply_singleton_ne_zero sem hα hmem)

omit [DecidableEq T] [Nonempty T] in
private theorem uniformOn_univ_real_singleton_eq (t t' : T) :
    (uniformOn (Set.univ : Set T)).real {t} = (uniformOn Set.univ).real {t'} := by
  rw [uniformOn_univ_real_singleton, uniformOn_univ_real_singleton]

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

/-- The evaluation register for the choice posterior at a natural rationality: pooled
preference between two `o`-shaped choices is the ℕ-valued common-denominator comparison over
all states — a kernel `decide`. The strict inequality carries its own truth witness. -/
theorem classicalJointListener_snd_real_lt_of_divPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {k D : ℕ}
    [NeZero k] [NeZero D] (hdvd : ∀ t : T, ∀ n ∈ profile sem t, n ∣ D) {o : O} {c₁ c₂ : C}
    (h₁ : obs c₁ = o) (h₂ : obs c₂ = o)
    (hlt : pooledDivPowSum sem D k c₁ < pooledDivPowSum sem D k c₂) :
    (classicalJointListener sem obs k o).snd.real {c₁}
      < (classicalJointListener sem obs k o).snd.real {c₂} := by
  rw [pooledDivPowSum_eq_sum, pooledDivPowSum_eq_sum] at hlt
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))
  have hmem₀ : t₀ ∈ sem c₂ := by
    by_contra h
    exact ht₀ (if_neg h)
  have hprior : ∀ c : C,
      (∑ t : T, (uniformOn (Set.univ : Set T)).real {t} * (classicalSpeaker sem k t).real {c})
      = (uniformOn (Set.univ : Set T)).real {t₀} * ∑ t : T,
          (if t ∈ sem c then (((D / (sem c).card) ^ k : ℕ) : ℝ) else 0)
            / ((profile sem t).divPowSum D k : ℝ) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [uniformOn_univ_real_singleton_eq t t₀,
      classicalSpeaker_real_singleton_divPowSum sem (hdvd t)]
  rw [classicalJointListener, jointListener_snd_real_lt_iff _ _ _ _ _
      (map_comp_classicalSpeaker_ne_zero sem obs hα.le h₂ hmem₀) h₁ h₂, hprior, hprior,
    mul_lt_mul_iff_right₀ (show (0 : ℝ) < (uniformOn (Set.univ : Set T)).real {t₀} from
      ENNReal.toReal_pos (by rw [uniformOn_univ, Measure.count_singleton]; simp)
        (measure_ne_top _ _)),
    sum_div_lt_sum_div_iff fun t => by
      exact_mod_cast Multiset.divPowSum_pos (NeZero.ne D) (hdvd t) (profile_ne_zero sem hsem t)]
  simp only [ite_mul, zero_mul]
  exact_mod_cast hlt

/-- Listener preference reduces to the cross-multiplied profile comparison, on reals: the
observation marginal and the shared prior cancel. Both registers' closers enter here. -/
theorem classicalJointListener_fst_real_lt_iff_invPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {α : ℝ}
    (hα : 0 < α) {o : O} {t₁ t₂ : T} (h₂ : ∃ c, obs c = o ∧ t₂ ∈ sem c) :
    ((classicalJointListener sem obs α o).fst.real {t₁}
        < (classicalJointListener sem obs α o).fst.real {t₂})
      ↔ ((fiberProfile sem obs o t₁).invPowSum α).toReal * ((profile sem t₂).invPowSum α).toReal
        < ((fiberProfile sem obs o t₂).invPowSum α).toReal
            * ((profile sem t₁).invPowSum α).toReal := by
  obtain ⟨c₂, hc₂, hmem⟩ := h₂
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
        (uniformOn (Set.univ : Set T)).real {t} * (classicalSpeaker sem α t).real {c})
        = ((uniformOn (Set.univ : Set T)) {t}
            * ((fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α)).toReal :=
    fun t => by
      rw [← Finset.mul_sum, measureReal_def,
        show (∑ c ∈ Finset.univ.filter (obs · = o), (classicalSpeaker sem α t).real {c})
          = ((fiberProfile sem obs o t).invPowSum α / (profile sem t).invPowSum α).toReal from by
          rw [← sum_fiber_classicalSpeaker sem obs hα,
            ENNReal.toReal_sum fun c _ => measure_ne_top _ _]
          simp_rw [measureReal_def],
        ENNReal.toReal_mul]
  rw [classicalJointListener, jointListener_fst_real_lt_iff _ _ _ _ _
      (map_comp_classicalSpeaker_ne_zero sem obs hα.le hc₂ hmem),
    key, key, show (uniformOn (Set.univ : Set T)) {t₁} = uniformOn Set.univ {t₂} from by
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

/-- The certificate register: strict domination of the fibre-by-rest profile products
decides listener preference uniformly in the rationality. The certificate carries its own
truth witness, so a finding is a single decided `Multiset.StrictDominates` fact. An empty
fibre at `t₁` is the support case: any nonempty product strictly dominates `0`. -/
theorem classicalJointListener_fst_real_lt_of_prodMul_strictDominates
    (hsem : ∀ t, ∃ c, t ∈ sem c) {α : ℝ} (hα : 0 < α) {o : O} {t₁ t₂ : T}
    (hcert : ((fiberProfile sem obs o t₂).prodMul (restProfile sem obs o t₁)).StrictDominates
      ((fiberProfile sem obs o t₁).prodMul (restProfile sem obs o t₂))) :
    (classicalJointListener sem obs α o).fst.real {t₁}
      < (classicalJointListener sem obs α o).fst.real {t₂} :=
  (classicalJointListener_fst_real_lt_iff_invPowSum sem obs hsem hα
      (exists_of_fiberProfile_ne_zero sem obs fun h =>
        hcert.ne_zero (Multiset.prodMul_eq_zero_iff.mpr (Or.inl h)))).mpr
    (invPowSum_odds_lt_of_prodMul_strictDominates sem obs hα hcert)

/-- The evaluation register at a natural rationality: with all profile entries dividing `D`,
listener preference is the ℕ-valued common-denominator comparison — a kernel `decide`. The
strict inequality carries its own truth witness. -/
theorem classicalJointListener_fst_real_lt_of_divPowSum (hsem : ∀ t, ∃ c, t ∈ sem c) {k D : ℕ}
    [NeZero k] [NeZero D] {o : O} {t₁ t₂ : T}
    (hdvd₁ : ∀ n ∈ profile sem t₁, n ∣ D) (hdvd₂ : ∀ n ∈ profile sem t₂, n ∣ D)
    (hlt : (fiberProfile sem obs o t₁).divPowSum D k * (profile sem t₂).divPowSum D k
      < (fiberProfile sem obs o t₂).divPowSum D k * (profile sem t₁).divPowSum D k) :
    (classicalJointListener sem obs k o).fst.real {t₁}
      < (classicalJointListener sem obs k o).fst.real {t₂} := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hfsub : ∀ t, ∀ n ∈ fiberProfile sem obs o t, n ∈ profile sem t := fun t n hn =>
    profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inl hn)
  have h₂ : fiberProfile sem obs o t₂ ≠ 0 :=
    Multiset.ne_zero_of_divPowSum_ne_zero
      (Nat.mul_ne_zero_iff.mp (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt))).1
  rw [classicalJointListener_fst_real_lt_iff_invPowSum sem obs hsem hα
    (exists_of_fiberProfile_ne_zero sem obs h₂)]
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

end RSA
