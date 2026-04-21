import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Prevention Semantics
@cite{sloman-barbey-hotaling-2009}

`preventSem` formalizes the SEM semantics of "prevent": B := ¬A
(Figure 4, eq. 4a). The preventer blocks an effect that would otherwise occur.

Prevention requires **inhibitory dynamics** — causal laws with negative
preconditions. This is proved by `preventSem_impossible_positive` (prevention
is vacuous in positive-only dynamics) and `preventSem_possible_inhibitory`
(prevention works with `CausalDynamics.prevention`, which wraps
`CausalLaw.inhibitory`).
-/

namespace Semantics.Causation.Prevention

open Core.StructuralEquationModel
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

/-- Semantics of "prevent" (@cite{sloman-barbey-hotaling-2009} Figure 4).

    "X prevented Y" is true iff:
    1. With the preventer present, the effect does NOT occur
    2. Without the preventer, the effect WOULD have occurred

    This is the dual of `causeSem` (@cite{nadathur-lauer-2020}): cause
    asserts the effect depends on the cause being present; prevent asserts
    the effect depends on the preventer being absent.

    Requires inhibitory dynamics (`CausalDynamics.prevention`);
    vacuous for positive dynamics (`preventSem_impossible_positive`). -/
def preventSem (dyn : CausalDynamics) (bg : Situation)
    (preventer effect : Variable) : Bool :=
  let devWith := normalDevelopment dyn (bg.extend preventer true)
  let devWithout := normalDevelopment dyn (bg.extend preventer false)
  -- Effect blocked with preventer, would occur without
  !devWith.hasValue effect true && devWithout.hasValue effect true

/-- `prevent` and `cause` are mutually exclusive: they cannot both
    hold for the same variable in the same background.

    `causeSem` requires the effect to occur WITH the cause, while
    `preventSem` requires the effect NOT to occur WITH the preventer.
    These are contradictory first conjuncts. -/
theorem prevent_cause_exclusive
    (dyn : CausalDynamics) (bg : Situation) (x e : Variable) :
    ¬(preventSem dyn bg x e = true ∧ causeSem dyn bg x e = true) := by
  intro ⟨hp, hc⟩
  simp only [preventSem, causeSem, Bool.and_eq_true, Bool.not_eq_true'] at hp hc
  exact absurd hc.1 (by rw [hp.1]; decide)

/-- **Prevention is impossible in positive-only dynamics.**

    In positive dynamics (all preconditions and effects are positive),
    `normalDevelopment` is monotone: adding variables to a situation can
    only add true values, never remove them. Since
    `trueLE (bg.extend x false) (bg.extend x true)` holds (vacuously
    for `x`, trivially for other variables), monotonicity gives:

      devWithout.hasValue e true → devWith.hasValue e true

    But `preventSem` requires `¬devWith.hasValue e true ∧ devWithout.hasValue e true`,
    which contradicts monotonicity. Prevention requires inhibitory
    (non-positive) causal laws — the structural equation must contain
    negation (@cite{sloman-barbey-hotaling-2009} eq. 4a: B := ¬A). -/
theorem preventSem_impossible_positive
    (dyn : CausalDynamics) (bg : Situation)
    (x e : Variable) (hPos : isPositiveDynamics dyn = true) :
    preventSem dyn bg x e = false := by
  simp only [preventSem]
  -- Key: trueLE (bg.extend x false) (bg.extend x true)
  have hLE : Situation.trueLE (bg.extend x false) (bg.extend x true) := by
    intro v hv
    by_cases hv_eq : v = x
    · subst hv_eq; simp [Situation.extend_hasValue_same] at hv
    · rwa [Situation.extend_hasValue_diff hv_eq] at hv ⊢
  -- Monotonicity: devWithout ⊑ devWith
  have hMono := normalDevelopment_trueLE_positive dyn _ _ 100 hPos hLE
  -- If devWithout has e=true, then devWith has e=true too (by monotonicity).
  -- This makes the two conjuncts of preventSem contradictory.
  by_cases h : (normalDevelopment dyn (bg.extend x false)).hasValue e true = true
  · -- devWithout has e=true → by monotonicity, devWith has e=true → ¬devWith is false
    have hWith := hMono e h
    simp only [hWith, Bool.not_true, Bool.false_and]
  · -- devWithout doesn't have e=true → second conjunct false
    have h' : (normalDevelopment dyn (bg.extend x false)).hasValue e true = false :=
      Bool.eq_false_iff.mpr h
    simp only [h', Bool.and_false]

/-- Witness: `preventSem` CAN return true with inhibitory dynamics.

    Uses `CausalDynamics.prevention` (@cite{sloman-barbey-hotaling-2009}
    eq. 4a: B := ¬A), which wraps `CausalLaw.inhibitory`: if x is absent,
    produce e. The law fires when x=false but not when x=true, making x
    a preventer of e.

    Together with `preventSem_impossible_positive`, this shows that the
    positivity constraint is exact: prevention requires inhibition, and
    inhibition suffices for prevention. -/
theorem preventSem_possible_inhibitory :
    ∃ (dyn : CausalDynamics) (bg : Situation) (x e : Variable),
      isPositiveDynamics dyn = false ∧
      preventSem dyn bg x e = true := by
  refine ⟨CausalDynamics.prevention (mkVar "x") (mkVar "e"),
          Situation.empty, mkVar "x", mkVar "e", ?_, ?_⟩ <;> decide

/-- `preventSem` returns true for the canonical prevention model.

    @cite{sloman-barbey-hotaling-2009} eq. 4a: B := ¬A.
    `CausalDynamics.prevention x e` wraps `CausalLaw.inhibitory x e`:
    if x is absent, e fires. So x's presence blocks e (preventSem = true). -/
theorem preventSem_prevention_model :
    let x := mkVar "x"; let e := mkVar "e"
    preventSem (CausalDynamics.prevention x e) Situation.empty x e = true := by
  decide

/-- The prevention model is not positive (it has an inhibitory law).
    The precondition `(x, false)` in `CausalLaw.inhibitory` violates
    `isPositiveDynamics`, which requires all precondition values to be `true`. -/
theorem prevention_not_positive :
    let x := mkVar "x"; let e := mkVar "e"
    isPositiveDynamics (CausalDynamics.prevention x e) = false := by
  decide

/-- Prevention with accessory: B := ¬A ∧ X.

    @cite{sloman-barbey-hotaling-2009} eq. 4b: the effect requires both
    the preventer's absence AND an accessory cause. Prevents only when
    the accessory is active. -/
theorem preventSem_with_accessory :
    let x := mkVar "x"; let acc := mkVar "acc"; let e := mkVar "e"
    preventSem (CausalDynamics.preventionWithAccessory x acc e)
      (Situation.empty.extend acc true) x e = true := by
  decide

end Semantics.Causation.Prevention
