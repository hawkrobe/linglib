import Linglib.Semantics.Causation.Sufficiency
import Linglib.Semantics.Causation.Necessity

/-!
# Causative Construction Selection (CC-Selection)
[baglini-bar-asher-siegal-2020] [baglini-bar-asher-siegal-2025] [bar-asher-siegal-2026]

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

namespace Causation.CCSelection

open Causation (SEM CausalGraph Valuation DecidableValuation)

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
  SEM.causallySufficient M background cause xC effect xE ∧
  ¬ SEM.causallySufficient M background cause xC_alt effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α) (cause : V) (xC xC_alt : α cause)
    (effect : V) (xE : α effect) :
    Decidable (completesForEffect M bg cause xC xC_alt effect xE) := Classical.dec _

/-- Bool-model bridge: prove canonical `completesForEffect` from a pair of
    `developDetOn` computations (cause-on develops the effect true;
    cause-off develops it false). The computations close by `decide`. -/
theorem completesForEffect_of_developDetOn {V : Type*} [Fintype V] [DecidableEq V]
    {M : Causation.BoolSEM V} [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M]
    {bg : Valuation (fun _ : V => Bool)} {c e : V} (vs : List V) (n : ℕ)
    (h1 : (SEM.developDetOn M vs n (bg.extend c true)).hasValue e true)
    (h2 : (SEM.developDetOn M vs n (bg.extend c false)).hasValue e false) :
    completesForEffect M bg c true false e true := by
  refine ⟨SEM.developDet_hasValue_of_developDetOn_hasValue h1, fun h => ?_⟩
  have h2' := SEM.developDet_hasValue_of_developDetOn_hasValue h2
  have h' : (M.developDet (bg.extend c false)).get e = some true := h
  have h2'' : (M.developDet (bg.extend c false)).get e = some false := h2'
  exact Bool.noConfusion (Option.some.inj (h'.symm.trans h2''))

/-- Bool-model bridge, negative: the sufficiency half fails — the cause-on
    development reaches the effect `false`, so no completion. -/
theorem not_completesForEffect_of_developDetOn {V : Type*} [Fintype V] [DecidableEq V]
    {M : Causation.BoolSEM V} [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M]
    {bg : Valuation (fun _ : V => Bool)} {c e : V} (vs : List V) (n : ℕ)
    (h1 : (SEM.developDetOn M vs n (bg.extend c true)).hasValue e false) :
    ¬ completesForEffect M bg c true false e true := by
  rintro ⟨hs, -⟩
  have h1' := SEM.developDet_hasValue_of_developDetOn_hasValue h1
  have hs' : (M.developDet (bg.extend c true)).get e = some true := hs
  have h1'' : (M.developDet (bg.extend c true)).get e = some false := h1'
  exact Bool.noConfusion (Option.some.inj (hs'.symm.trans h1''))

end Causation.CCSelection
