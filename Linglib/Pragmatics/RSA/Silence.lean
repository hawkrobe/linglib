import Linglib.Pragmatics.RSA.Uniform

/-!
# The null message

The null message of [bergen-levy-goodman-2016]: an utterance true at every state, so that a
speaker always has a true option, and disfavored by a cost. `WithSilence U` adds it to an
utterance type, `liftMeaning` and `liftSem` give it the universal extension, and
`liftCostFactor` its own cost factor. Under the uniform literal listener the null message adds
the same weight to every row of the speaker, its cost factor times the reciprocal of the number
of states to the power of the rationality, so the share of a content utterance is its
informativity weight over the state's profile sum plus that constant
(`RSA.speaker_liftCostFactor_uniformListener_real_singleton_some`): predictions about the
content utterances are uniform in the null message's cost.

## References

* [bergen-levy-goodman-2016]
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {U W : Type*}

/-- The utterances with the null message added: `none` is the null message. -/
abbrev WithSilence (U : Type*) := Option U

/-- A meaning lifted to the null message, which is true at every world. -/
def liftMeaning (m : U → W → Prop) : WithSilence U → W → Prop
  | some u, w => m u w
  | none, _ => True

instance (m : U → W → Prop) [∀ u, DecidablePred (m u)] :
    ∀ x, DecidablePred (liftMeaning m x)
  | some _, _ => inferInstanceAs (Decidable (m _ _))
  | none, _ => .isTrue trivial

@[simp] theorem liftMeaning_some (m : U → W → Prop) (u : U) (w : W) :
    liftMeaning m (some u) w = m u w := rfl

@[simp] theorem liftMeaning_none (m : U → W → Prop) (w : W) :
    liftMeaning m none w := trivial

/-- Extensions lifted to the null message, which has the whole state space. -/
def liftSem [Fintype W] (sem : U → Finset W) : WithSilence U → Finset W
  | some u => sem u
  | none => Finset.univ

@[simp] theorem liftSem_some [Fintype W] (sem : U → Finset W) (u : U) :
    liftSem sem (some u) = sem u := rfl

@[simp] theorem liftSem_none [Fintype W] (sem : U → Finset W) :
    liftSem sem none = Finset.univ := rfl

/-- A cost factor lifted to the null message, which is weighted `κ`. -/
def liftCostFactor (κ : ℝ≥0∞) (c : U → ℝ≥0∞) : WithSilence U → ℝ≥0∞
  | some u => c u
  | none => κ

@[simp] theorem liftCostFactor_some (κ : ℝ≥0∞) (c : U → ℝ≥0∞) (u : U) :
    liftCostFactor κ c (some u) = c u := rfl

@[simp] theorem liftCostFactor_none (κ : ℝ≥0∞) (c : U → ℝ≥0∞) :
    liftCostFactor κ c none = κ := rfl

/-! ### The uniform speaker with a null message -/

section Uniform

variable {T C : Type*} [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [DiscreteMeasurableSpace T] [Fintype C] [MeasurableSpace (WithSilence C)]
  [DiscreteMeasurableSpace (WithSilence C)] (sem : C → Finset T)

theorem uniformListener_liftSem_none_apply_singleton (t : T) :
    uniformListener (liftSem sem) none {t} = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [uniformListener_apply_singleton, liftSem_none, if_pos (Finset.mem_univ t),
    Finset.card_univ]

/-- The share of a content utterance: its informativity weight over the state's profile sum
plus the null message's weight, the same at every state. -/
theorem speaker_liftCostFactor_uniformListener_real_singleton_some {α : ℝ} (hα : 0 < α)
    {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (t : T) (c : C) :
    (speaker α (liftCostFactor κ 1) (uniformListener (liftSem sem)) t).real {some c}
      = (if t ∈ sem c then (((sem c).card : ℝ))⁻¹ ^ α else 0)
        / (((profile sem t).invPowSum α).toReal + κ.toReal * ((Fintype.card T : ℝ))⁻¹ ^ α) := by
  rw [speaker_real_singleton hα.le (fun u => by cases u <;> simp [hκ])
    (fun u => uniformListener_apply_singleton_le_one _ u t), Fintype.sum_option,
    uniformListener_liftSem_none_apply_singleton, profile_invPowSum_toReal sem hα.le]
  simp only [uniformListener_apply_singleton, liftSem_some, liftCostFactor_some,
    liftCostFactor_none, Pi.one_apply, ENNReal.toReal_one, mul_one, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [add_comm, mul_comm]

end Uniform

end RSA
