import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Causative Construction Selection (CC-Selection)
@cite{baglini-bar-asher-siegal-2020} @cite{baglini-bar-asher-siegal-2025} @cite{bar-asher-siegal-2026}

CC-selection (@cite{baglini-bar-asher-siegal-2025}) is the mechanism by which
causative constructions constrain which element of a causal model can be
linguistically realized as "the cause."
-/

namespace Semantics.Causation.CCSelection

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

-- ════════════════════════════════════════════════════
-- § 1. CC-Selection Mode
-- ════════════════════════════════════════════════════

/-- How a causative construction selects its cause from a causal model. -/
inductive CCSelectionMode where
  | memberOfSufficientSet
  | completionOfSufficientSet
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 2. Completion Event
-- ════════════════════════════════════════════════════

/-- Completion event: the cause completes a sufficient set AND is necessary
    in the current background (simple but-for test). -/
def completesForEffect (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Prop :=
  (normalDevelopment dyn (background.extend cause true)).hasValue effect true ∧
  ¬ (normalDevelopment dyn (background.extend cause false)).hasValue effect true

instance (dyn : CausalDynamics) (background : Situation) (cause effect : Variable) :
    Decidable (completesForEffect dyn background cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ════════════════════════════════════════════════════
-- § 3. CC-Selection Semantics
-- ════════════════════════════════════════════════════

/-- Map a CC-selection mode to its truth-condition function. -/
def CCSelectionMode.toSemantics :
    CCSelectionMode → (CausalDynamics → Situation → Variable → Variable → Prop)
  | .memberOfSufficientSet => causeSem
  | .completionOfSufficientSet => makeSem

/-- Evaluate the CC-selection constraint for a given mode. -/
def ccConstraintSatisfied (mode : CCSelectionMode)
    (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Prop :=
  match mode with
  | .memberOfSufficientSet => causeSem dyn bg cause effect
  | .completionOfSufficientSet => completesForEffect dyn bg cause effect

instance (mode : CCSelectionMode) (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) :
    Decidable (ccConstraintSatisfied mode dyn bg cause effect) := by
  unfold ccConstraintSatisfied
  cases mode
  · exact inferInstanceAs (Decidable (causeSem ..))
  · exact inferInstanceAs (Decidable (completesForEffect ..))

-- ════════════════════════════════════════════════════
-- § 4. Entailment Properties
-- ════════════════════════════════════════════════════

/-- Completion does NOT entail membership in general (causal chains witness). -/
theorem completion_not_entails_member :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      ccConstraintSatisfied .completionOfSufficientSet dyn bg c e ∧
      ¬ (ccConstraintSatisfied .memberOfSufficientSet dyn bg c e) := by
  let c := mkVar "c"
  let m := mkVar "m"
  let e := mkVar "e"
  let dyn := CausalDynamics.causalChain c m e
  use dyn, Situation.empty, c, e
  simp only [ccConstraintSatisfied]
  constructor <;> native_decide

/-- Member mode asserts Def 10b necessity. -/
theorem member_asserts_necessity (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) (h : ccConstraintSatisfied .memberOfSufficientSet dyn bg c e) :
    causallyNecessary dyn bg c e := h.2

-- ════════════════════════════════════════════════════
-- § 5. Type-Level vs Token-Level Causation
-- ════════════════════════════════════════════════════

/-- Type-level causal claim: a causal law connects cause to effect. -/
def typeLevelSufficiency (dyn : CausalDynamics) (cause effect : Variable) : Prop :=
  causallySufficient dyn Situation.empty cause effect

instance (dyn : CausalDynamics) (cause effect : Variable) :
    Decidable (typeLevelSufficiency dyn cause effect) :=
  inferInstanceAs (Decidable (causallySufficient ..))

/-- Token-level causal claim: in a specific actual situation, the cause
    brought about the effect. -/
def tokenLevelCausation (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Prop :=
  actuallyCaused dyn bg cause effect

instance (dyn : CausalDynamics) (bg : Situation) (cause effect : Variable) :
    Decidable (tokenLevelCausation dyn bg cause effect) :=
  inferInstanceAs (Decidable (actuallyCaused ..))

/-- Type-level sufficiency entails token-level causation is possible. -/
theorem type_level_enables_token_level :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      typeLevelSufficiency dyn c e ∧
      tokenLevelCausation dyn bg c e := by
  use CausalDynamics.mk [CausalLaw.simple (mkVar "c") (mkVar "e")],
      Situation.empty.extend (mkVar "c") true, mkVar "c", mkVar "e"
  constructor <;> native_decide

/-- Type-level sufficiency does NOT guarantee token-level causation. -/
theorem type_level_not_sufficient_for_token :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      typeLevelSufficiency dyn c e ∧
      ¬ tokenLevelCausation dyn bg c e := by
  use CausalDynamics.disjunctiveCausation (mkVar "c") (mkVar "b") (mkVar "e"),
      Situation.empty.extend (mkVar "c") true |>.extend (mkVar "b") true,
      mkVar "c", mkVar "e"
  constructor <;> native_decide

-- ════════════════════════════════════════════════════
-- § 6. Actualization Constraint
-- ════════════════════════════════════════════════════

/-- The actualization constraint: cause is part of the only completed
    sufficient set realized in the actual world.

    Formally identical to `completesForEffect` (sufficiency + simple
    but-for); exposed under the actualization name for use by
    @cite{baglini-bar-asher-siegal-2025} CC-selection theorems. -/
abbrev actualizationHolds (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Prop :=
  completesForEffect dyn bg cause effect

/-- Actualization fails under overdetermination. -/
theorem actualization_fails_overdetermination :
    let dyn := CausalDynamics.disjunctiveCausation (mkVar "l") (mkVar "a") (mkVar "f")
    let bg := Situation.empty.extend (mkVar "l") true |>.extend (mkVar "a") true
    ¬ actualizationHolds dyn bg (mkVar "l") (mkVar "f") := by
  native_decide

/-- Actualization holds for sole causes. -/
theorem actualization_holds_sole_cause :
    let dyn := CausalDynamics.mk [CausalLaw.simple (mkVar "c") (mkVar "e")]
    let bg := Situation.empty.extend (mkVar "c") true
    actualizationHolds dyn bg (mkVar "c") (mkVar "e") := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 7. Structural Dependency [c] D [e]
-- ════════════════════════════════════════════════════

/-- The structural dependency [c] D [e] from @cite{bar-asher-siegal-boneh-2020}. -/
structure CausalDependency where
  cause : Variable
  effect : Variable
  dynamics : CausalDynamics
  background : Situation

/-- Evaluate CC-selection on a packaged causal dependency. -/
def CausalDependency.satisfies (dep : CausalDependency)
    (mode : CCSelectionMode) : Prop :=
  ccConstraintSatisfied mode dep.dynamics dep.background dep.cause dep.effect

instance (dep : CausalDependency) (mode : CCSelectionMode) :
    Decidable (dep.satisfies mode) :=
  inferInstanceAs (Decidable (ccConstraintSatisfied ..))

/-- Check actualization for a dependency. -/
def CausalDependency.actualized (dep : CausalDependency) : Prop :=
  actualizationHolds dep.dynamics dep.background dep.cause dep.effect

instance (dep : CausalDependency) : Decidable dep.actualized :=
  inferInstanceAs (Decidable (actualizationHolds ..))

end Semantics.Causation.CCSelection
