module

public import Linglib.Pragmatics.RSA.Uniform

/-!
# The null message

The null message of [bergen-levy-goodman-2016]: an utterance true at every state, so that a
speaker always has a true option, and disfavored by a cost. `WithSilence U` adds it to an
utterance type, `liftMeaning` and `liftSem` give it the universal extension, and
`liftCost` its own cost. Under the uniform literal listener the null message adds
the same weight to every row of the speaker, its cost weight times the reciprocal of the number
of states to the power of the rationality, so the share of a content utterance is its
informativity weight over the state's profile sum plus that constant
(`RSA.speaker_liftCost_uniformListener_real_singleton_some`): predictions about the
content utterances are uniform in the null message's cost.

## References

* [bergen-levy-goodman-2016]
-/

@[expose] public section

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

/-- A cost lifted to the null message, which costs `k`. -/
def liftCost (k : ℝ) (C : U → ℝ) : WithSilence U → ℝ
  | some u => C u
  | none => k

@[simp] theorem liftCost_some (k : ℝ) (C : U → ℝ) (u : U) : liftCost k C (some u) = C u := rfl

@[simp] theorem liftCost_none (k : ℝ) (C : U → ℝ) : liftCost k C none = k := rfl

/-! ### The uniform speaker with a null message -/

section Uniform

variable {T C : Type*} [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [DiscreteMeasurableSpace T] [Fintype C] [MeasurableSpace (WithSilence C)]
  [DiscreteMeasurableSpace (WithSilence C)] (sem : C → Finset T)

theorem uniformListener_liftSem_none_apply_singleton (t : T) :
    uniformListener (liftSem sem) none {t} = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [uniformListener_apply_singleton, liftSem_none, ite_eq_left (Finset.mem_univ t),
    Finset.card_univ]

/-- The share of a content utterance: its informativity weight over the state's profile sum
plus the null message's weight, the same at every state. -/
theorem speaker_liftCost_uniformListener_real_singleton_some {α : ℝ} (hα : 0 < α) (k : ℝ)
    (t : T) (c : C) :
    (speaker α (liftCost k 0) (uniformListener (liftSem sem)) t).real {some c}
      = (if t ∈ sem c then (((sem c).card : ℝ))⁻¹ ^ α else 0)
        / (((profile sem t).invPowSum α).toReal
          + Real.exp (-(α * k)) * ((Fintype.card T : ℝ))⁻¹ ^ α) := by
  rw [speaker_real_singleton hα.le, Fintype.sum_option,
    uniformListener_liftSem_none_apply_singleton, profile_invPowSum_toReal sem hα.le]
  simp only [uniformListener_apply_singleton, liftSem_some, liftCost_some, liftCost_none,
    Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, mul_one, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [add_comm, mul_comm]

end Uniform

end RSA
