import Linglib.Semantics.Causation.Sufficiency
import Linglib.Semantics.Causation.Necessity
import Linglib.Semantics.Causation.SEM.Forced

/-!
# Causative construction selection

A causal model typically offers several sets of conditions each jointly sufficient for an
effect; causal selection picks one condition as "the cause", and each causative construction
constrains which conditions it can pick. On the account of Baglini and Bar-Asher Siegal, a
change-of-state verb (*open*) selects the temporally final condition of a sufficient set,
the verb *cause* selects any of its conditions, and either way the set must be the only
minimal sufficient set completed in the world of evaluation. This file defines sufficient
sets over the forced (Kleene) development of a structural equation model, the two selection
constraints, and their executable fuel mirrors, alongside the older but-for completion
test `completesForEffect`.

## References

* [baglini-bar-asher-siegal-2020]
* [baglini-bar-asher-siegal-2025]
* [bar-asher-siegal-2026]
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

/-! ### Sufficient sets and the selection constraints -/

section SufficientSets

variable {V : Type*} {α : V → Type*} [DecidableEq V] (M : SEM V α) [SEM.IsDeterministic M]
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

/-! ### Fuel mirrors -/

section Fuel

variable {V : Type*} {α : V → Type*} [DecidableEq V] (M : SEM V α) [SEM.IsDeterministic M] (n : ℕ)

/-- `IsMinimalSufficientSet` with forcing replaced by its fuel form. -/
def IsMinimalSufficientSetFuel (S : Valuation α) (effect : V) (xE : α effect) : Prop :=
  (S.get effect = none ∧ SEM.ForcedFuel M S n effect xE) ∧
    ∀ v, (S.get v).isSome → ¬ SEM.ForcedFuel M (S.remove v) n effect xE

def IsTheCompletedSetFuel (w S : Valuation α) (effect : V) (xE : α effect) : Prop :=
  IsMinimalSufficientSetFuel M n S effect xE ∧ S ≤ w ∧
    ∀ S', IsMinimalSufficientSetFuel M n S' effect xE → S' ≤ w → S' = S

def SelectsMemberFuel (w : Valuation α) (c effect : V) (xE : α effect) : Prop :=
  ∃ S, IsTheCompletedSetFuel M n w S effect xE ∧ (S.get c).isSome

def SelectsFinalFuel (w : Valuation α) (time : V → ℕ) (c effect : V) (xE : α effect) : Prop :=
  ∃ S, IsTheCompletedSetFuel M n w S effect xE ∧ (S.get c).isSome ∧
    ∀ v, (S.get v).isSome → time v ≤ time c

section Decidable

variable [Fintype V] [DecidableValuation α] [∀ v, Fintype (α v)]

instance (s₁ s₂ : Valuation α) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (∀ v x, s₁.hasValue v x → s₂.hasValue v x))

instance (S : Valuation α) (effect : V) (xE : α effect) :
    Decidable (IsMinimalSufficientSetFuel M n S effect xE) := by
  unfold IsMinimalSufficientSetFuel; infer_instance

instance (w S : Valuation α) (effect : V) (xE : α effect) :
    Decidable (IsTheCompletedSetFuel M n w S effect xE) := by
  unfold IsTheCompletedSetFuel; infer_instance

instance (w : Valuation α) (c effect : V) (xE : α effect) :
    Decidable (SelectsMemberFuel M n w c effect xE) := by
  unfold SelectsMemberFuel; infer_instance

instance (w : Valuation α) (time : V → ℕ) (c effect : V) (xE : α effect) :
    Decidable (SelectsFinalFuel M n w time c effect xE) := by
  unfold SelectsFinalFuel; infer_instance

end Decidable

variable (r : CausalGraph.Ranking M.graph) (hn : ∀ v : V, r v < n)
include hn

theorem isMinimalSufficientSet_iff_fuel (S : Valuation α) (effect : V) (xE : α effect) :
    IsMinimalSufficientSet M S effect xE ↔ IsMinimalSufficientSetFuel M n S effect xE := by
  unfold IsMinimalSufficientSet IsSufficientSet IsMinimalSufficientSetFuel
  simp only [SEM.forced_iff_fuel r (hn effect)]

theorem isTheCompletedSet_iff_fuel (w S : Valuation α) (effect : V) (xE : α effect) :
    IsTheCompletedSet M w S effect xE ↔ IsTheCompletedSetFuel M n w S effect xE := by
  unfold IsTheCompletedSet IsTheCompletedSetFuel
  simp only [isMinimalSufficientSet_iff_fuel M n r hn]

theorem selectsMember_iff_fuel (w : Valuation α) (c effect : V) (xE : α effect) :
    SelectsMember M w c effect xE ↔ SelectsMemberFuel M n w c effect xE := by
  unfold SelectsMember SelectsMemberFuel
  simp only [isTheCompletedSet_iff_fuel M n r hn]

theorem selectsFinal_iff_fuel (w : Valuation α) (time : V → ℕ) (c effect : V) (xE : α effect) :
    SelectsFinal M w time c effect xE ↔ SelectsFinalFuel M n w time c effect xE := by
  unfold SelectsFinal SelectsFinalFuel
  simp only [isTheCompletedSet_iff_fuel M n r hn]

end Fuel

end Causation.CCSelection
