import Mathlib.Data.List.Basic

/-!
# Information States — Bool/List propositional algebra
@cite{ciardelli-groenendijk-roelofsen-2018}

Bool-valued characteristic functions for sets of worlds, packaged with a
small algebra of propositional operations. This is the computational
substrate that the dynamic-semantics modules (PLA, Bilateral, FileChange,
ABLE, ICDRT, TypeTheoretic, …) use as their proposition representation.

Conceptually `InfoState W = W → Bool` is just a Bool-valued
characteristic function for a subset of `W`. The set-valued counterpart
lives in `Core/Issue/Basic.lean` (`Issue W` with `Set W` propositions
+ `LowerSet`/`SetLike` infrastructure); the Bool/List version here
remains because dynamic-semantics state-update code is built around
`Bool` predicates and `List W` enumerations rather than `Set` /
`Decidable` infrastructure.

Future migration of the dynamic-semantics propositional algebra to
`Set W` is an independent project — for now this file is the canonical
home of these primitives.
-/

namespace Discourse

-- Information States

/-- An information state: worlds compatible with current information.

In standard inquisitive semantics, an info state is a SET of worlds.
Here we represent it as a characteristic function σ : W → Bool.

Semantically: σ w = true means "world w is compatible with the information".
The empty info state (σ = λ_ => false) represents inconsistent information. -/
abbrev InfoState (W : Type*) := W → Bool

/-- The absurd/inconsistent info state: no worlds are compatible. -/
def absurdState {W : Type*} : InfoState W := λ _ => false

/-- The trivial info state: all worlds are compatible (total ignorance). -/
def trivialState {W : Type*} : InfoState W := λ _ => true

/-- Check if an info state is empty (inconsistent). -/
def InfoState.isEmpty {W : Type*} (σ : InfoState W) (worlds : List W) : Bool :=
  !worlds.any σ

/-- Check if an info state is non-empty. -/
def InfoState.isNonEmpty {W : Type*} (σ : InfoState W) (worlds : List W) : Bool :=
  worlds.any σ

/-- Info state σ is a subset of σ' (σ ⊆ σ'). -/
def InfoState.subset {W : Type*} (σ σ' : InfoState W) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → σ' w

/-- Intersection of two info states. -/
def InfoState.inter {W : Type*} (σ σ' : InfoState W) : InfoState W :=
  λ w => σ w && σ' w

/-- Union of two info states. -/
def InfoState.union {W : Type*} (σ σ' : InfoState W) : InfoState W :=
  λ w => σ w || σ' w

-- Support and Entailment

/-- Info state σ supports proposition p iff σ ⊆ ⟦p⟧.

This is the fundamental relation in inquisitive semantics:
σ ⊨ p (σ supports p) iff every world in σ makes p true.

If σ is empty, it supports every proposition (ex falso quodlibet). -/
def supports {W : Type*} (σ : InfoState W) (p : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => σ w → p w

/-- Propositional entailment: p entails q iff every p-world is a q-world.

Equivalently: the info state ⟦p⟧ supports ⟦q⟧ over all worlds. -/
def propEntails {W : Type*} (p q : W → Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !p w || q w

/-- Proper containment of info states over a finite world list.
    `properlyContains σ σ' worlds` holds when σ' ⊆ σ and σ ∖ σ' ≠ ∅. -/
def properlyContains {W : Type*} (σ σ' : InfoState W) (worlds : List W) : Bool :=
  worlds.all (λ w => !σ' w || σ w) &&
  worlds.any (λ w => σ w && !σ' w)

-- Pointwise unfolds for the trivial constructors.

@[simp] theorem absurdState_apply {W : Type*} (w : W) :
    (absurdState : InfoState W) w = false := rfl

@[simp] theorem trivialState_apply {W : Type*} (w : W) :
    (trivialState : InfoState W) w = true := rfl

@[simp] theorem InfoState.inter_apply {W : Type*} (σ σ' : InfoState W) (w : W) :
    InfoState.inter σ σ' w = (σ w && σ' w) := rfl

@[simp] theorem InfoState.union_apply {W : Type*} (σ σ' : InfoState W) (w : W) :
    InfoState.union σ σ' w = (σ w || σ' w) := rfl

-- Bool/Prop characterizations of the basic predicates.

theorem propEntails_iff {W : Type*} (p q : W → Bool) (worlds : List W) :
    propEntails p q worlds = true ↔ ∀ w ∈ worlds, p w = true → q w = true := by
  unfold propEntails
  rw [List.all_eq_true]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  cases p w <;> simp

theorem supports_iff {W : Type*} (σ : InfoState W) (p : W → Bool) (worlds : List W) :
    supports σ p worlds = true ↔ ∀ w ∈ worlds, σ w = true → p w = true := by
  unfold supports
  rw [List.all_eq_true]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  cases σ w <;> simp

theorem InfoState.subset_iff {W : Type*} (σ σ' : InfoState W) (worlds : List W) :
    σ.subset σ' worlds = true ↔ ∀ w ∈ worlds, σ w = true → σ' w = true := by
  unfold InfoState.subset
  rw [List.all_eq_true]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  cases σ w <;> simp

theorem InfoState.isEmpty_iff {W : Type*} (σ : InfoState W) (worlds : List W) :
    σ.isEmpty worlds = true ↔ ∀ w ∈ worlds, σ w = false := by
  simp only [InfoState.isEmpty, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true]

theorem InfoState.isNonEmpty_iff {W : Type*} (σ : InfoState W) (worlds : List W) :
    σ.isNonEmpty worlds = true ↔ ∃ w ∈ worlds, σ w = true := by
  simp only [InfoState.isNonEmpty, List.any_eq_true]

-- Reflexivity / basic identities.

/-- Propositional entailment is reflexive. -/
theorem propEntails_refl {W : Type*} (p : W → Bool) (worlds : List W) :
    propEntails p p worlds = true := by
  rw [propEntails_iff]; intros; assumption

theorem supports_trivialState {W : Type*} (p : W → Bool) (worlds : List W)
    (h : ∀ w ∈ worlds, p w = true) :
    supports trivialState p worlds = true := by
  rw [supports_iff]; intros w hw _; exact h w hw

theorem supports_absurdState {W : Type*} (p : W → Bool) (worlds : List W) :
    supports absurdState p worlds = true := by
  rw [supports_iff]; intros _ _ h; cases h

-- InfoState algebra.

theorem InfoState.inter_comm {W : Type*} (σ σ' : InfoState W) :
    σ.inter σ' = σ'.inter σ := by funext w; simp [Bool.and_comm]

theorem InfoState.union_comm {W : Type*} (σ σ' : InfoState W) :
    σ.union σ' = σ'.union σ := by funext w; simp [Bool.or_comm]

@[simp] theorem InfoState.inter_self {W : Type*} (σ : InfoState W) :
    σ.inter σ = σ := by funext w; simp

@[simp] theorem InfoState.union_self {W : Type*} (σ : InfoState W) :
    σ.union σ = σ := by funext w; simp

@[simp] theorem InfoState.inter_absurd {W : Type*} (σ : InfoState W) :
    σ.inter absurdState = absurdState := by funext w; simp

@[simp] theorem InfoState.absurd_inter {W : Type*} (σ : InfoState W) :
    absurdState.inter σ = absurdState := by funext w; simp

@[simp] theorem InfoState.inter_trivial {W : Type*} (σ : InfoState W) :
    σ.inter trivialState = σ := by funext w; simp

@[simp] theorem InfoState.trivial_inter {W : Type*} (σ : InfoState W) :
    trivialState.inter σ = σ := by funext w; simp

@[simp] theorem InfoState.union_absurd {W : Type*} (σ : InfoState W) :
    σ.union absurdState = σ := by funext w; simp

@[simp] theorem InfoState.union_trivial {W : Type*} (σ : InfoState W) :
    σ.union trivialState = trivialState := by funext w; simp

end Discourse
