/-
# RSA Discourse Integration

Smart constructors for building RSAScenarios from DiscourseConfig.

This file is separate from Basic.lean to avoid notation conflicts:
CommonGround.lean defines `notation:60 c " + " p => update c p` which
conflicts with Float arithmetic in Eval.lean.

## Usage

```lean
import Linglib.Theories.RSA.Core.Discourse

def myScenario := RSAScenario.discourse
  (φ := myMeaning)
  (discourse := myDiscourseConfig)
  (worldPrior := myWorldPrior)
```
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Core.DiscourseState

namespace RSA

open Core.DiscourseState

-- ============================================================================
-- QUD Configuration
-- ============================================================================

/--
Configuration for QUD/Goal-based RSA models.

Bundles the Goal type with its projection and prior.
-/
structure QUDConfig (W : Type) where
  /-- The goal/QUD type -/
  G : Type
  /-- Goal projection: are two worlds equivalent under this goal? -/
  project : G → W → W → Bool
  /-- Prior over goals -/
  prior : G → ℚ := fun _ => 1
  /-- Fintype instance for G -/
  [gFintype : Fintype G]
  /-- DecidableEq instance for G -/
  [gDecEq : DecidableEq G]
  /-- Non-negativity of prior -/
  prior_nonneg : ∀ g, 0 ≤ prior g := by intros; decide

attribute [instance] QUDConfig.gFintype QUDConfig.gDecEq

namespace QUDConfig

variable {W : Type}

/--
Trivial QUD config: all worlds are equivalent.
-/
def trivial : QUDConfig W where
  G := Unit
  project := fun _ _ _ => true
  prior_nonneg := fun _ => by decide

end QUDConfig

-- ============================================================================
-- RSAScenario Discourse Constructors
-- ============================================================================

namespace RSAScenario

/--
Create an RSAScenario from a DiscourseConfig.

This constructor takes a unified discourse configuration that bundles:
- The discourse latent variable type D
- The compatibility function (d → w → Bool)
- The prior over discourse states

The D type maps to RSAScenario.BeliefState, and the compatibility
function becomes speakerCredence.

## Example

```lean
def warstadtScenario := RSAScenario.discourse
  (φ := fun u w => if literalMeaning u w then 1 else 0)
  (discourse := {
    D := Context
    compatible := compatibleBool
    prior := contextPrior
  })
  (worldPrior := worldPrior)
```
-/
def discourse {U W : Type}
    [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (φ : U → W → ℚ)
    (discourse : DiscourseConfig W)
    (worldPrior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    : RSAScenario U W where
  BeliefState := discourse.D
  φ := fun _ _ u w => φ u w
  goalProject := fun _ _ _ => true
  speakerCredence := discourse.credence
  worldPrior := worldPrior
  beliefStatePrior := discourse.prior
  α := α
  cost := cost
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := discourse.prior_nonneg
  goalPrior_nonneg := fun _ => by decide
  speakerCredence_nonneg := fun d w => by
    simp only [DiscourseConfig.credence]
    split <;> decide
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  cost_nonneg := cost_nonneg

/--
Create an RSAScenario with both discourse and QUD configuration.

This combines DiscourseConfig (for presupposition/belief uncertainty)
with QUDConfig (for goal-sensitive interpretation).

## Example

```lean
def hyperboleScenario := RSAScenario.discourseWithQUD
  (φ := literalMeaning)
  (discourse := trivialDiscourse)
  (qud := {
    G := Goal
    project := qudEquiv
    prior := goalPrior
  })
```
-/
def discourseWithQUD {U W : Type}
    [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (φ : U → W → ℚ)
    (discourse : DiscourseConfig W)
    (qud : QUDConfig W)
    (worldPrior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    : RSAScenario U W where
  BeliefState := discourse.D
  Goal := qud.G
  φ := fun _ _ u w => φ u w
  goalProject := qud.project
  speakerCredence := discourse.credence
  worldPrior := worldPrior
  beliefStatePrior := discourse.prior
  goalPrior := qud.prior
  α := α
  cost := cost
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := discourse.prior_nonneg
  goalPrior_nonneg := qud.prior_nonneg
  speakerCredence_nonneg := fun d w => by
    simp only [DiscourseConfig.credence]
    split <;> decide
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  cost_nonneg := cost_nonneg

end RSAScenario

end RSA
