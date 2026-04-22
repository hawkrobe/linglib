import Linglib.Core.Lexical.VerbClass
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.Prevention

/-!
# Causative Interpretation
@cite{nadathur-lauer-2020} @cite{sloman-barbey-hotaling-2009} @cite{talmy-1988} @cite{wolff-2003}

Maps `Causative` verb classifications to their compositional semantics
and derives N&L's sufficiency/necessity properties from the force-dynamic
mechanism.

| Causative | Mechanism | English verbs | N&L property (derived) |
|-----------|-----------|---------------|----------------------|
| cause | Counterfactual dependence | cause | necessity |
| make | Direct sufficient guarantee | make, have, get | sufficiency |
| force | Coercive (overcome resistance) | force | sufficiency + coercion |
| enable | Barrier removal (permissive) | let, enable | sufficiency |
| prevent | Barrier addition (blocking) | prevent | preventSem |
-/

-- ════════════════════════════════════════════════════
-- § Semantic interpretation
-- ════════════════════════════════════════════════════

namespace Core.Verbs

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity
open Semantics.Causation.Prevention

/-- Map a causative classification to its semantic function.

    This is the structural link between the lexical annotation and the
    formal semantics. The classification NAMES the force-dynamic mechanism;
    this function provides the actual truth-condition computation.

    Note: `force` and `enable` share `makeSem` truth conditions with `make`.
    They differ in force-dynamic properties (coercion, permissivity),
    which are captured by `isCoercive` and `isPermissive`. -/
def Causative.toSemantics : Causative →
    (CausalDynamics → Situation → Variable → Variable → Prop)
  | .cause => causeSem
  | .make => makeSem
  | .force => makeSem
  | .enable => makeSem
  | .prevent => preventSem

open Semantics.Causation.CCSelection

/-- The CC-selection mode associated with each variant.

    - `.cause` selects any necessary condition → `memberOfSufficientSet`
    - `.make`/`.force`/`.enable` select the completing condition →
      `completionOfSufficientSet`
    - `.prevent` selects the condition that blocks the effect →
      `completionOfSufficientSet` (the preventer completes the blocking set) -/
def Causative.selectionMode : Causative → CCSelectionMode
  | .cause => .memberOfSufficientSet
  | .make | .force | .enable | .prevent => .completionOfSufficientSet

end Core.Verbs

-- ════════════════════════════════════════════════════
-- § Derivation theorems
-- ════════════════════════════════════════════════════

namespace Semantics.Causation.Interpretation

open Core.Causal
open Core.Verbs
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity
open Semantics.Causation.Prevention

/-- All sufficiency-asserting variants (make, force, enable) compute
    truth conditions via `makeSem`. -/
theorem sufficiency_variants_use_makeSem :
    Causative.make.toSemantics = makeSem ∧
    Causative.force.toSemantics = makeSem ∧
    Causative.enable.toSemantics = makeSem :=
  ⟨rfl, rfl, rfl⟩

/-- The cause variant computes truth conditions via `causeSem`. -/
theorem cause_uses_causeSem :
    Causative.cause.toSemantics = causeSem := rfl

/-- `make` and `force` have the same truth conditions.

    Both map to `makeSem`. They are distinguished by `isCoercive`:
    `force` lexically encodes coercion while `make` does not. -/
theorem make_force_same_truth_conditions :
    Causative.make.toSemantics = Causative.force.toSemantics := rfl

/-- `enable` and `make` have the same truth conditions.

    Both map to `makeSem`. They are distinguished by `isPermissive`:
    `enable` encodes barrier removal while `make` does not. -/
theorem enable_make_same_truth_conditions :
    Causative.enable.toSemantics = Causative.make.toSemantics := rfl

/-- At least two variants produce genuinely different truth conditions.

    Witnessed by the overdetermination scenario (lightning + arsonist):
    `makeSem` returns true (lightning sufficient) but `causeSem` returns
    false (lightning not necessary). -/
theorem truth_conditionally_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      Causative.make.toSemantics dyn s c e ≠
      Causative.cause.toSemantics dyn s c e := by
  -- Overdetermination: lightning ∨ arsonist → fire, with arsonist in background
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  let dyn := CausalDynamics.disjunctiveCausation a b c
  let s := Situation.empty.extend b true
  refine ⟨dyn, s, a, c, ?_⟩
  intro heq
  -- makeSem holds (a sufficient for c via disjunctive law)
  have hM : Causative.make.toSemantics dyn s a c := by
    show makeSem dyn s a c; native_decide
  -- causeSem fails (a not necessary because b alone suffices)
  have hNotC : ¬ Causative.cause.toSemantics dyn s a c := by
    show ¬ causeSem dyn s a c; native_decide
  exact hNotC (heq ▸ hM)

/-- `make` and `force` are distinguished by coercion despite sharing truth conditions. -/
theorem make_force_distinguished_by_coercion :
    Causative.make.isCoercive = false ∧
    Causative.force.isCoercive = true := ⟨rfl, rfl⟩

/-- `make` and `enable` are distinguished by permissivity despite sharing truth conditions. -/
theorem make_enable_distinguished_by_permissivity :
    Causative.make.isPermissive = false ∧
    Causative.enable.isPermissive = true := ⟨rfl, rfl⟩

/-- Sufficiency-asserting variants all use `makeSem`.

    This is the key bridge: `assertsSufficiency` exactly characterizes
    variants whose `toSemantics` returns `makeSem`.

    The `prevent` case shows `preventSem ≠ makeSem` using the
    overdetermination witness (disjunctive causation model). -/
theorem assertsSufficiency_iff_makeSem (b : Causative) :
    b.assertsSufficiency = true ↔ b.toSemantics = makeSem := by
  cases b <;> constructor <;> simp_all [Causative.assertsSufficiency, Causative.toSemantics]
  · -- cause: causeSem ≠ makeSem (witnessed by overdetermination scenario)
    intro h
    have ⟨dyn, s, c, e, hne⟩ := truth_conditionally_distinct
    simp only [Causative.toSemantics, h] at hne
    exact absurd rfl hne
  · -- prevent: preventSem ≠ makeSem (witnessed by disjunctive overdetermination)
    intro h
    set dyn := CausalDynamics.disjunctiveCausation (mkVar "a") (mkVar "b") (mkVar "c")
    set s := Situation.empty.extend (mkVar "b") true
    have hPM : preventSem dyn s (mkVar "a") (mkVar "c") =
               makeSem dyn s (mkVar "a") (mkVar "c") :=
      congrFun (congrFun (congrFun (congrFun h _) _) _) _
    -- makeSem holds; preventSem doesn't (no inhibitory law)
    have hM : makeSem dyn s (mkVar "a") (mkVar "c") := by native_decide
    have hNotP : ¬ preventSem dyn s (mkVar "a") (mkVar "c") := by native_decide
    exact hNotP (hPM.symm ▸ hM)

/-- When a sufficiency variant's semantics holds, the cause is
    causally sufficient for the effect.

    This is DERIVED: it follows from the fact that `makeSem` is defined
    as `causallySufficient`. -/
theorem sufficiency_implies_causallySufficient
    (dyn : CausalDynamics) (s : Situation) (c e : Variable)
    (h : Causative.make.toSemantics dyn s c e) :
    causallySufficient dyn s c e := h

/-- When the cause variant's semantics holds, the cause is
    causally necessary for the effect.

    DERIVED from the fact that `causeSem` conjoins occurrence
    with `causallyNecessary`. -/
theorem necessity_implies_causallyNecessary
    (dyn : CausalDynamics) (s : Situation) (c e : Variable)
    (h : Causative.cause.toSemantics dyn s c e) :
    causallyNecessary dyn s c e := h.2

-- ════════════════════════════════════════════════════
-- § Bridge to CC-Selection
-- ════════════════════════════════════════════════════

/-! `Causative` encodes force-dynamic mechanisms; `CCSelectionMode`
(@cite{baglini-bar-asher-siegal-2025}) encodes which element of a causal
model the construction can select as "the cause." These are orthogonal
but connected: each variant has a canonical selection mode. -/

/-- Sufficiency variants have completion selection mode. -/
theorem sufficiency_selects_completion (b : Causative)
    (h : b.assertsSufficiency = true) :
    b.selectionMode = .completionOfSufficientSet := by
  cases b <;> simp_all [Causative.assertsSufficiency, Causative.selectionMode]

/-- Necessity variant has member selection mode. -/
theorem necessity_selects_member :
    Causative.cause.selectionMode = .memberOfSufficientSet := rfl

/-- `toSemantics` is consistent with `selectionMode.toSemantics` for
    the two canonical variants (cause, make). Force/enable share make's
    truth conditions; prevent has its own. -/
theorem selectionMode_consistent_cause :
    Causative.cause.toSemantics =
    Causative.cause.selectionMode.toSemantics := rfl

theorem selectionMode_consistent_make :
    Causative.make.toSemantics =
    Causative.make.selectionMode.toSemantics := rfl

end Semantics.Causation.Interpretation
