module

public import Linglib.Semantics.Causation.Sufficiency
public import Linglib.Semantics.Causation.Necessity
public import Linglib.Semantics.Causation.SEM.Forced

/-!
# Causative construction selection

A causal model typically offers several sets of conditions each jointly sufficient for an
effect; causal selection picks one condition as "the cause", and each causative construction
constrains which conditions it can pick. On the account of Baglini and Bar-Asher Siegal, a
change-of-state verb (*open*) selects the temporally final condition of a sufficient set,
the verb *cause* selects any of its conditions, and either way the set must be the only
minimal sufficient set completed in the world of evaluation. This file defines sufficient
sets over the forced (Kleene) development of a structural equation model, the two selection
constraints, which are decidable in a finite model, alongside the older but-for completion
test `completesForEffect`.

## References

* [baglini-bar-asher-siegal-2020]
* [baglini-bar-asher-siegal-2025]
* [bar-asher-siegal-2026]
-/

@[expose] public section

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
def completesForEffect {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (background : Valuation α)
    (cause : V) (xC xC_alt : α cause) (effect : V) (xE : α effect) : Prop :=
  SEM.causallySufficient M background cause xC effect xE ∧
  ¬ SEM.causallySufficient M background cause xC_alt effect xE

instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (bg : Valuation α) (cause : V) (xC xC_alt : α cause)
    (effect : V) (xE : α effect) :
    Decidable (completesForEffect M bg cause xC xC_alt effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Sufficient sets and the selection constraints -/

section SufficientSets

variable {V : Type*} {α : V → Type*} [DecidableEq V] (M : SEM V α)
  {effect : V} {xE : α effect}

/-- A sufficient set for `effect = xE`: a situation not settling the effect that forces it. -/
def IsSufficientSet (S : Valuation α) (effect : V) (xE : α effect) : Prop :=
  S.get effect = none ∧ SEM.Forced M S effect xE

/-- A sufficient set each of whose conditions is necessary within it. -/
def IsMinimalSufficientSet (S : Valuation α) (effect : V) (xE : α effect) : Prop :=
  IsSufficientSet M S effect xE ∧ ∀ v, (S.get v).isSome → ¬ SEM.Forced M (S.remove v) effect xE

/-- `S` is the only minimal sufficient set completed in the world `w`. -/
def IsTheCompletedSet (w S : Valuation α) (effect : V) (xE : α effect) : Prop :=
  IsMinimalSufficientSet M S effect xE ∧ S ≤ w ∧
    ∀ S', IsMinimalSufficientSet M S' effect xE → S' ≤ w → S' = S

/-- The verb *cause* selects any condition of the completed sufficient set. -/
def SelectsMember (w : Valuation α) (c effect : V) (xE : α effect) : Prop :=
  ∃ S, IsTheCompletedSet M w S effect xE ∧ (S.get c).isSome

/-- A change-of-state verb selects the temporally final condition of the completed sufficient
set, `time` ordering the world's realizations. -/
def SelectsFinal (w : Valuation α) (time : V → ℕ) (c effect : V) (xE : α effect) : Prop :=
  ∃ S, IsTheCompletedSet M w S effect xE ∧ (S.get c).isSome ∧
    ∀ v, (S.get v).isSome → time v ≤ time c

/-- What a construction of the given mode may select as the cause. -/
def CCSelectionMode.Selects (mode : CCSelectionMode)
    (w : Valuation α) (time : V → ℕ) (c effect : V) (xE : α effect) : Prop :=
  match mode with
  | .memberOfSufficientSet => SelectsMember M w c effect xE
  | .completionOfSufficientSet => SelectsFinal M w time c effect xE

variable {M}

/-- The change-of-state verb entails *cause*. -/
theorem SelectsFinal.selectsMember {w : Valuation α} {time : V → ℕ} {c : V}
    (h : SelectsFinal M w time c effect xE) : SelectsMember M w c effect xE :=
  let ⟨S, hS, hc, _⟩ := h; ⟨S, hS, hc⟩

/-- Overdetermination: two completed minimal sufficient sets leave nothing selectable. -/
theorem not_selectsMember_of_two {w S₁ S₂ : Valuation α} {c : V}
    (h₁ : IsMinimalSufficientSet M S₁ effect xE) (h₂ : IsMinimalSufficientSet M S₂ effect xE)
    (hne : S₁ ≠ S₂) (hw₁ : S₁ ≤ w) (hw₂ : S₂ ≤ w) : ¬ SelectsMember M w c effect xE :=
  λ ⟨_, ⟨_, _, huniq⟩, _⟩ => hne ((huniq S₁ h₁ hw₁).trans (huniq S₂ h₂ hw₂).symm)

theorem not_selectsFinal_of_two {w S₁ S₂ : Valuation α} {time : V → ℕ} {c : V}
    (h₁ : IsMinimalSufficientSet M S₁ effect xE) (h₂ : IsMinimalSufficientSet M S₂ effect xE)
    (hne : S₁ ≠ S₂) (hw₁ : S₁ ≤ w) (hw₂ : S₂ ≤ w) : ¬ SelectsFinal M w time c effect xE :=
  λ h => not_selectsMember_of_two h₁ h₂ hne hw₁ hw₂ h.selectsMember

end SufficientSets

/-! ### Decidability -/

section Decidable

variable {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V] [DecidableValuation α]
  [∀ v, Fintype (α v)] (M : SEM V α) [M.graph.IsDAG] (w S : Valuation α) (time : V → ℕ)
  (c effect : V) (xE : α effect)

instance : Decidable (IsSufficientSet M S effect xE) := inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (IsMinimalSufficientSet M S effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (IsTheCompletedSet M w S effect xE) := by
  letI := Valuation.fintype (α := α)
  unfold IsTheCompletedSet; infer_instance

instance : Decidable (SelectsMember M w c effect xE) := by
  letI := Valuation.fintype (α := α)
  unfold SelectsMember; infer_instance

instance : Decidable (SelectsFinal M w time c effect xE) := by
  letI := Valuation.fintype (α := α)
  unfold SelectsFinal; infer_instance

end Decidable

end Causation.CCSelection
