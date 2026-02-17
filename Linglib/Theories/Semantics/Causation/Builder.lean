import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Causative Builder

Links causative verb lexical entries to their compositional semantics,
following the same pattern as `PreferentialBuilder` for attitude verbs.

## Design principle

The builder names a **force-dynamic mechanism** (Wolff 2003, Talmy 1988),
not a causal-model property. Properties like "asserts sufficiency" or
"asserts necessity" are **derived** from the builder via theorems.

| Builder | Mechanism | English verbs | N&L property (derived) |
|---------|-----------|---------------|----------------------|
| cause | Counterfactual dependence | cause | necessity |
| make | Direct sufficient guarantee | make, have, get | sufficiency |
| force | Coercive (overcome resistance) | force | sufficiency + coercion |
| enable | Barrier removal (permissive) | let, enable | sufficiency |
| prevent | Barrier addition (blocking) | prevent | preventSem |

## References

- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa 5(1), 49.
- Wolff, P. (2003). Direct causation in the linguistic coding and
  individuation of causal events. Cognition 88, 1-48.
- Talmy, L. (1988). Force dynamics in language and cognition.
  Cognitive Science 12, 49-100.
-/

namespace NadathurLauer2020.Builder

open Core.Causation
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity

/-- How a causative verb's semantics is built from causal model infrastructure.

    The builder names a **force-dynamic mechanism** (Wolff 2003), not a
    causal-model property. `toSemantics` maps each builder to its
    truth-condition function; properties like sufficiency/necessity are
    derived via theorems.

    - `cause`: Counterfactual dependence — removing cause blocks effect.
    - `make`: Direct sufficient guarantee — adding cause ensures effect.
    - `force`: Coercive sufficiency — overcome resistance, no alternatives.
    - `enable`: Permissive — remove barrier so effect can occur.
    - `prevent`: Blocking — add barrier so effect cannot occur. -/
inductive CausativeBuilder where
  /-- Counterfactual dependence: removing cause → no effect.
      Semantic function: `causeSem`. -/
  | cause
  /-- Direct sufficient guarantee: adding cause → effect.
      Semantic function: `makeSem`. -/
  | make
  /-- Coercive sufficiency: overcome resistance, no alternatives.
      Same truth conditions as `make`; distinguished by `isCoercive`. -/
  | force
  /-- Permissive: remove barrier so effect can occur.
      Same truth conditions as `make`; distinguished by `isPermissive`. -/
  | enable
  /-- Blocking: add barrier so effect cannot occur.
      Semantic function: `preventSem` (dual of `causeSem`). -/
  | prevent
  deriving DecidableEq, Repr, BEq

/-! ## Prevent semantics

`preventSem` is the dual of `causeSem`: the preventer blocks an effect
that would otherwise occur. -/

/-- Semantics of "prevent" (causative verb asserting blocking).

    "X prevented Y" is true iff:
    1. With the preventer present, the effect does NOT occur
    2. Without the preventer, the effect WOULD have occurred

    This is the dual of `causeSem`: cause asserts the effect depends on
    the cause being present; prevent asserts the effect depends on the
    preventer being absent. -/
def preventSem (dyn : CausalDynamics) (bg : Situation)
    (preventer effect : Variable) : Bool :=
  let devWith := normalDevelopment dyn (bg.extend preventer true)
  let devWithout := normalDevelopment dyn (bg.extend preventer false)
  -- Effect blocked with preventer, would occur without
  !devWith.hasValue effect true && devWithout.hasValue effect true

/-- Map a causative builder to its semantic function.

    This is the structural link between the lexical annotation and the
    formal semantics. The builder NAMES the force-dynamic mechanism;
    this function provides the actual truth-condition computation.

    Note: `force` and `enable` share `makeSem` truth conditions with `make`.
    They differ in force-dynamic properties (coercion, permissivity),
    which are captured by `isCoercive` and `isPermissive`. -/
def CausativeBuilder.toSemantics : CausativeBuilder →
    (CausalDynamics → Situation → Variable → Variable → Bool)
  | .cause => causeSem
  | .make => makeSem
  | .force => makeSem
  | .enable => makeSem
  | .prevent => preventSem

/-! ## Derived property functions

These functions derive causal-model properties from the force-dynamic
builder. They are the interface between the fine-grained builder and
Nadathur & Lauer's binary sufficiency/necessity classification. -/

/-- Does this builder assert causal sufficiency (N&L Def 23)?

    DERIVED: true for builders whose `toSemantics` maps to `makeSem`. -/
def CausativeBuilder.assertsSufficiency : CausativeBuilder → Bool
  | .make | .force | .enable => true
  | .cause | .prevent => false

/-- Does this builder assert causal necessity (N&L Def 24)?

    DERIVED: true only for `.cause`, whose `toSemantics` maps to `causeSem`. -/
def CausativeBuilder.assertsNecessity : CausativeBuilder → Bool
  | .cause => true
  | _ => false

/-- Does this builder encode coercion (overcoming resistance)?

    Force-dynamic property: `.force` encodes that the causer overcame
    the causee's resistance (Wolff 2003). -/
def CausativeBuilder.isCoercive : CausativeBuilder → Bool
  | .force => true
  | _ => false

/-- Does this builder encode permissivity (barrier removal)?

    Force-dynamic property: `.enable` encodes that the causer removed
    a barrier, allowing the effect to occur naturally (Talmy 1988). -/
def CausativeBuilder.isPermissive : CausativeBuilder → Bool
  | .enable => true
  | _ => false

/-! ## Derivation theorems

These theorems show that N&L's sufficiency/necessity classification
is derivable from the force-dynamic builder, rather than being
independently stipulated. -/

/-- All sufficiency-asserting builders (make, force, enable) compute
    truth conditions via `makeSem`. -/
theorem sufficiency_builders_use_makeSem :
    CausativeBuilder.make.toSemantics = makeSem ∧
    CausativeBuilder.force.toSemantics = makeSem ∧
    CausativeBuilder.enable.toSemantics = makeSem :=
  ⟨rfl, rfl, rfl⟩

/-- The cause builder computes truth conditions via `causeSem`. -/
theorem cause_builder_uses_causeSem :
    CausativeBuilder.cause.toSemantics = causeSem := rfl

/-- `make` and `force` have the same truth conditions.

    Both map to `makeSem`. They are distinguished by `isCoercive`:
    `force` lexically encodes coercion while `make` does not. -/
theorem make_force_same_truth_conditions :
    CausativeBuilder.make.toSemantics = CausativeBuilder.force.toSemantics := rfl

/-- `enable` and `make` have the same truth conditions.

    Both map to `makeSem`. They are distinguished by `isPermissive`:
    `enable` encodes barrier removal while `make` does not. -/
theorem enable_make_same_truth_conditions :
    CausativeBuilder.enable.toSemantics = CausativeBuilder.make.toSemantics := rfl

/-- `prevent` and `cause` are duals.

    `cause` asserts the effect depends on the cause being present;
    `prevent` asserts the effect depends on the preventer being absent.

    Formally: `preventSem` holds when effect is blocked WITH the preventer
    and would occur WITHOUT it — the mirror of `causeSem` which holds when
    effect occurs WITH the cause and wouldn't occur WITHOUT it. -/
theorem prevent_cause_duality
    (dyn : CausalDynamics) (bg : Situation) (x e : Variable) :
    preventSem dyn bg x e =
      (!((normalDevelopment dyn (bg.extend x true)).hasValue e true) &&
       (normalDevelopment dyn (bg.extend x false)).hasValue e true) := rfl

/-- At least two builders produce genuinely different truth conditions.

    Witnessed by the overdetermination scenario (lightning + arsonist):
    `makeSem` returns true (lightning sufficient) but `causeSem` returns
    false (lightning not necessary). -/
theorem builders_truth_conditionally_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      CausativeBuilder.make.toSemantics dyn s c e ≠
      CausativeBuilder.cause.toSemantics dyn s c e := by
  -- Overdetermination: lightning ∨ arsonist → fire, with arsonist in background
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  let dyn := CausalDynamics.disjunctiveCausation a b c
  let s := Situation.empty.extend b true
  use dyn, s, a, c
  simp only [CausativeBuilder.toSemantics, ne_eq]
  native_decide

/-- `make` and `force` are distinguished by coercion despite sharing truth conditions. -/
theorem make_force_distinguished_by_coercion :
    CausativeBuilder.make.isCoercive = false ∧
    CausativeBuilder.force.isCoercive = true := ⟨rfl, rfl⟩

/-- `make` and `enable` are distinguished by permissivity despite sharing truth conditions. -/
theorem make_enable_distinguished_by_permissivity :
    CausativeBuilder.make.isPermissive = false ∧
    CausativeBuilder.enable.isPermissive = true := ⟨rfl, rfl⟩

/-- Sufficiency-asserting builders all use `makeSem`.

    This is the key bridge: `assertsSufficiency` exactly characterizes
    builders whose `toSemantics` returns `makeSem`.

    TODO: The `prevent` case requires showing `preventSem ≠ makeSem`,
    which needs a witness (a model where they differ). -/
theorem assertsSufficiency_iff_makeSem (b : CausativeBuilder) :
    b.assertsSufficiency = true ↔ b.toSemantics = makeSem := by
  cases b <;> constructor <;> simp_all [CausativeBuilder.assertsSufficiency, CausativeBuilder.toSemantics]
  · -- cause: causeSem ≠ makeSem (witnessed by overdetermination scenario)
    intro h
    have ⟨dyn, s, c, e, hne⟩ := builders_truth_conditionally_distinct
    simp only [CausativeBuilder.toSemantics, h] at hne
    exact absurd rfl hne
  · -- prevent: preventSem ≠ makeSem (same witness: fire still happens with preventer)
    intro h
    have : preventSem (CausalDynamics.disjunctiveCausation (mkVar "a") (mkVar "b") (mkVar "c"))
           (Situation.empty.extend (mkVar "b") true) (mkVar "a") (mkVar "c") =
           makeSem (CausalDynamics.disjunctiveCausation (mkVar "a") (mkVar "b") (mkVar "c"))
           (Situation.empty.extend (mkVar "b") true) (mkVar "a") (mkVar "c") :=
      congrFun (congrFun (congrFun (congrFun h _) _) _) _
    revert this; native_decide

/-- When a sufficiency builder's semantics holds, the cause is
    causally sufficient for the effect.

    This is DERIVED: it follows from the fact that `makeSem` is defined
    as `causallySufficient`. -/
theorem sufficiency_implies_causallySufficient
    (dyn : CausalDynamics) (s : Situation) (c e : Variable)
    (h : CausativeBuilder.make.toSemantics dyn s c e = true) :
    causallySufficient dyn s c e = true := h

/-- When the cause builder's semantics holds, the cause is
    causally necessary for the effect.

    DERIVED from the fact that `causeSem` conjoins occurrence
    with `causallyNecessary`. -/
theorem necessity_implies_causallyNecessary
    (dyn : CausalDynamics) (s : Situation) (c e : Variable)
    (h : CausativeBuilder.cause.toSemantics dyn s c e = true) :
    causallyNecessary dyn s c e = true := by
  simp only [CausativeBuilder.toSemantics, causeSem, Bool.and_eq_true] at h
  exact h.2

end NadathurLauer2020.Builder
