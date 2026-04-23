import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Causative Construction Selection (CC-Selection)
@cite{baglini-bar-asher-siegal-2020} @cite{baglini-bar-asher-siegal-2025} @cite{bar-asher-siegal-2026}

CC-selection is the mechanism by which causative constructions constrain
which element of a causal model can be linguistically realized as
"the cause."

Two modes:
- `memberOfSufficientSet` (verb *cause*): any necessary condition
- `completionOfSufficientSet` (CoS verbs like *open*): the completing
  condition

The legacy `CausalDynamics`-based `completesForEffect`,
`ccConstraintSatisfied`, `typeLevelSufficiency`, `tokenLevelCausation`,
`actualizationHolds`, `CausalDependency` were deleted in Phase D-H.
The polymorphic V2 versions are promoted to canonical here.
-/

namespace Semantics.Causation.CCSelection

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- How a causative construction selects its cause from a causal model. -/
inductive CCSelectionMode where
  | memberOfSufficientSet
  | completionOfSufficientSet
  deriving Repr, DecidableEq

/-- V2 `completesForEffect`: cause-as-`xC` develops effect-as-`xE`;
    cause-as-`xC_alt` does not. Polymorphic but-for completion check.
    Bool models pass `xC = xE = true`, `xC_alt = false`. -/
noncomputable def completesForEffect {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (cause : V) (xC xC_alt : α cause) (effect : V) (xE : α effect) : Prop :=
  (M.developDet (background.extend cause xC)).hasValue effect xE ∧
  ¬ (M.developDet (background.extend cause xC_alt)).hasValue effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α) (cause : V) (xC xC_alt : α cause)
    (effect : V) (xE : α effect) :
    Decidable (completesForEffect M bg cause xC xC_alt effect xE) := Classical.dec _

/-- `actualizationHolds`: alias for `completesForEffect`. -/
abbrev actualizationHolds {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α)
    (cause : V) (xC xC_alt : α cause) (effect : V) (xE : α effect) : Prop :=
  completesForEffect M bg cause xC xC_alt effect xE

end Semantics.Causation.CCSelection
