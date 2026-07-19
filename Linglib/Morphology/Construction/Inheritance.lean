/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype

/-!
# Inheritance hierarchies

The rival horn of the motivation question ([jackendoff-audring-2020] ch. 3): a
lexical entry is motivated by inheriting default properties from a more general
entry, overriding where it legislates locally. A `Hierarchy` is a single-parent
chain with acyclicity witnessed by a well-founded parent relation (the taxonomy
of [jackendoff-audring-2020]'s Figure 3.5); multiple inheritance — a node with
two schematic parents, as in their cross-classifying cases — is deferred to a
future engine and out of scope here.

Default/override lookup (`Hierarchy.value`) reads a node's local specification if
present, else the nearest ancestor's. It is computed by fuel-bounded structural
recursion saturating at `Fintype.card`, so it kernel-reduces (a
`WellFounded.fix` definition would not, blocking `decide`). Acyclicity is not
needed for the lookup laws — `card` fuel saturates any finite parent map — so
`value_eq_of_att` and `value_eq_parent` hold structurally; the well-founded
field records the taxonomy commitment and feeds later results.

Formal defaults-with-override traditions this abstracts: DATR
([evans-gazdar-1996]) and Network Morphology ([brown-hippisley-2012]).
[jackendoff-audring-2020] argue inheritance and the impoverished-entry model do
not by themselves explicate motivation — their claim, contested in the DATR
literature. The one-level default-override primitive already lives in
`Syntax/ConstructionGrammar/Inheritance.lean` (`inheritField`, child-wins); the
transitive chain walk here is new, and the shared `Option`-level override
primitive is a candidate for a future `Core/Order/` lift.

## Main declarations

- `Hierarchy` — a single-parent chain with a well-founded parent relation
- `valueFuel`, `Hierarchy.value` — fuel-bounded default/override lookup
- `Hierarchy.value_eq_of_att`, `Hierarchy.value_eq_parent` — override wins;
  path extension to the parent
-/

namespace Morphology.Construction

variable {ι β : Type*} {parent : ι → Option ι} {att : ι → Option β}

/-- A single-parent inheritance chain: `parent` links each node to its immediate
supertype (`none` at a root), with `wf` witnessing acyclicity. -/
structure Hierarchy (ι : Type*) where
  /-- The immediate-supertype map. -/
  parent : ι → Option ι
  /-- Acyclicity: the parent relation is well-founded. -/
  wf : WellFounded (fun a b => parent b = some a)

/-- Default/override lookup with a step budget: at fuel `0` only the local
specification is read; each further unit walks one step to the parent. -/
def valueFuel (parent : ι → Option ι) (att : ι → Option β) : Nat → ι → Option β
  | 0, n => att n
  | k + 1, n =>
    match att n with
    | some v => some v
    | none => (parent n).bind (valueFuel parent att k)

/-! ### Fuel monotonicity and saturation -/

/-- A local specification is read at any fuel. -/
theorem valueFuel_of_att {n : ι} {v : β} (h : att n = some v) (k : Nat) :
    valueFuel parent att k n = some v := by
  cases k with
  | zero => exact h
  | succ k => simp only [valueFuel, h]

/-- A value found within `k` steps is still found within `k + 1`. -/
theorem valueFuel_some_succ (k : Nat) (n : ι) (v : β)
    (h : valueFuel parent att k n = some v) :
    valueFuel parent att (k + 1) n = some v := by
  induction k generalizing n v with
  | zero =>
    simp only [valueFuel] at h
    simp only [valueFuel, h]
  | succ k ih =>
    simp only [valueFuel] at h ⊢
    cases hatt : att n with
    | some a => simp only [hatt] at h ⊢; exact h
    | none =>
      simp only [hatt] at h ⊢
      cases hp : parent n with
      | none => rw [hp] at h; simp at h
      | some m => simp only [hp] at h ⊢; exact ih m v h

/-- Two fuel levels giving the same lookup give the same lookup after one more
step: the recursion consumes only the previous level. -/
theorem valueFuel_succ_congr {j k : Nat}
    (h : valueFuel parent att j = valueFuel parent att k) :
    valueFuel parent att (j + 1) = valueFuel parent att (k + 1) := by
  funext n
  simp only [valueFuel, h]

/-- Once a fuel level is a fixed point, every larger level agrees with it. -/
theorem valueFuel_const_of_fixed {k : Nat}
    (hfix : valueFuel parent att k = valueFuel parent att (k + 1)) :
    ∀ m, k ≤ m → valueFuel parent att m = valueFuel parent att k := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [valueFuel_succ_congr ih, ← hfix]

section Fintype
variable [Fintype ι]

/-- The nodes whose lookup succeeds within `k` steps. -/
private def defined (parent : ι → Option ι) (att : ι → Option β) (k : Nat) : Finset ι :=
  Finset.univ.filter (fun n => (valueFuel parent att k n).isSome = true)

private theorem mem_defined {k : Nat} {n : ι} :
    n ∈ defined parent att k ↔ (valueFuel parent att k n).isSome = true := by
  simp [defined]

private theorem defined_subset_succ (k : Nat) :
    defined parent att k ⊆ defined parent att (k + 1) := by
  intro n hn
  rw [mem_defined] at hn ⊢
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hn
  simp [valueFuel_some_succ k n v hv]

private theorem defined_ssubset_of_ne {k : Nat}
    (h : valueFuel parent att k ≠ valueFuel parent att (k + 1)) :
    defined parent att k ⊂ defined parent att (k + 1) := by
  refine lt_of_le_of_ne (defined_subset_succ k) ?_
  intro hdefeq
  apply h
  funext n
  by_cases hk : (valueFuel parent att k n).isSome = true
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    rw [hv, valueFuel_some_succ k n v hv]
  · rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hk
    by_cases hk1 : (valueFuel parent att (k + 1) n).isSome = true
    · have hmem : n ∈ defined parent att k := hdefeq ▸ mem_defined.mpr hk1
      rw [mem_defined, hk] at hmem
      exact absurd hmem (by simp)
    · rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hk1
      rw [hk, hk1]

/-- **Card fuel saturates**: with `Fintype.card` fuel the lookup is a fixed
point of the one-step recursion. A monotone chain of defined-sets bounded by the
universe can strictly grow at most `card` times. -/
theorem valueFuel_card_fixed :
    valueFuel parent att (Fintype.card ι) = valueFuel parent att (Fintype.card ι + 1) := by
  by_contra hne
  have hstep : ∀ k, k ≤ Fintype.card ι →
      (defined parent att k).card < (defined parent att (k + 1)).card := by
    intro k hk
    apply Finset.card_lt_card
    apply defined_ssubset_of_ne
    intro heq
    exact hne ((valueFuel_const_of_fixed heq (Fintype.card ι) (by omega)).trans
      (valueFuel_const_of_fixed heq (Fintype.card ι + 1) (by omega)).symm)
  have hgrow : ∀ k, k ≤ Fintype.card ι + 1 → k ≤ (defined parent att k).card := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have h1 := hstep k (by omega)
      have h2 := ih (by omega)
      omega
  have hbound : (defined parent att (Fintype.card ι + 1)).card ≤ Fintype.card ι := by
    rw [defined]; exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have := hgrow (Fintype.card ι + 1) (by omega)
  omega

/-- Default/override lookup: a node's local specification if present, else the
nearest ancestor's, computed by saturating the fuel recursion at `Fintype.card`. -/
def Hierarchy.value (h : Hierarchy ι) (att : ι → Option β) (n : ι) : Option β :=
  valueFuel h.parent att (Fintype.card ι) n

/-- Override wins: a local specification is the value. -/
theorem Hierarchy.value_eq_of_att (h : Hierarchy ι) {att : ι → Option β} {n : ι} {v : β}
    (hn : att n = some v) : h.value att n = some v :=
  valueFuel_of_att hn (Fintype.card ι)

/-- Path extension: at a node with no local specification, the value is the
parent's. -/
theorem Hierarchy.value_eq_parent (h : Hierarchy ι) {att : ι → Option β} {n : ι}
    (hn : att n = none) : h.value att n = (h.parent n).bind (h.value att) := by
  show valueFuel h.parent att (Fintype.card ι) n = _
  rw [valueFuel_card_fixed]
  simp only [Hierarchy.value, valueFuel, hn]

end Fintype

/-! ### Figure 3.5: default and override

The taxonomy `Animal → Bird/Fish`, `Bird → Canary/Ostrich`: birds fly by
default, the ostrich overrides to not-fly, the canary inherits flight. A concept
hierarchy, not linguistic data — an abstract witness that override and default
inheritance compute as intended. -/

private inductive Animal
  | animal | bird | fish | canary | ostrich
  deriving DecidableEq, Fintype

private def animalParent : Animal → Option Animal
  | .animal => none
  | .bird => some .animal
  | .fish => some .animal
  | .canary => some .bird
  | .ostrich => some .bird

private def animalDepth : Animal → Nat
  | .animal => 0
  | .bird => 1
  | .fish => 1
  | .canary => 2
  | .ostrich => 2

private theorem animalParent_wf :
    WellFounded (fun a b : Animal => animalParent b = some a) := by
  have hq : WellFounded (fun a b : Animal => animalDepth a < animalDepth b) :=
    InvImage.wf animalDepth Nat.lt_wfRel.wf
  refine Subrelation.wf (fun {a b} hab => ?_) hq
  revert hab; cases a <;> cases b <;> decide

private def animalHierarchy : Hierarchy Animal where
  parent := animalParent
  wf := animalParent_wf

/-- Flight as a local specification: birds fly, the ostrich overrides. -/
private def flies : Animal → Option Bool
  | .bird => some true
  | .ostrich => some false
  | _ => none

/-- The ostrich's override and the canary's inheritance compute as intended. -/
example : animalHierarchy.value flies .ostrich = some false ∧
    animalHierarchy.value flies .canary = some true := by decide

end Morphology.Construction
