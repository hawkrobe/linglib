module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.TakeWhile

/-!
# The Agree operation as a fold over the goal sequence

This file defines the Agree operation of [deal-2025a]'s interaction/satisfaction theory as a
fold over an ordered goal sequence. The probe inspects the goals in order; from every goal that
interacts with it, it copies, and flags the goal as a goal of the probe; the first goal that
satisfies it is flagged as its satisfier and ends the search. The state the fold threads is
whatever the probe accumulates, so the operation is generic over what copying means, and a
probe specification over a feature type instantiates it with feature sets, copying the goal's
features that lie in the interaction specification.

The single-goal search of `Probe/Basic.lean` is the special case in which every interacting goal
satisfies the probe (`run_goals_eq_agree`), Multiple Agree is the insatiable case
(`insatiable_run_goals`), and a probe that finds no interacting goal leaves the state unchanged,
Agree failing without penalty ([preminger-2014]). The satisfier of the fold is always the goal
`Probe.search` finds (`run_halt`). Goal flagging, which [deal-2025a] keeps distinct from
valuation, is the list of interacting goals together with the satisfier.

## Main definitions

* `Minimalist.Probe.run`: the Agree operation, a fold over the goal sequence returning a
  `Minimalist.Probe.Result`, the state, the flagged goals and the satisfier.
* `Minimalist.Probe.inspected`: the goals up to and including the first satisfier.
* `Minimalist.Probe.Spec`: an interaction and a satisfaction feature set, denoting a probe over
  goals exposing feature sets by `Minimalist.Probe.Spec.toProbe` and run by
  `Minimalist.Probe.Spec.run`.

## Main results

* `Minimalist.Probe.run_halt`, `Minimalist.Probe.run_goals`, `Minimalist.Probe.run_state`
* `Minimalist.Probe.run_goals_eq_agree`, `Minimalist.Probe.insatiable_run_goals`
* `Minimalist.Probe.Spec.run_state_eq_biUnion`

## References

* [deal-2025a], [deal-2024]
* [hiraiwa-2001]
* [preminger-2014]
-/

@[expose] public section

namespace Minimalist

variable {α σ F : Type*}

/-- The result of running a probe over a goal sequence, the state after copying from every
interacting goal, the goals flagged as interacting, in search order, and the goal flagged as the
satisfier, if any. -/
structure Probe.Result (α σ : Type*) where
  /-- The state after copying from every interacting goal. -/
  state : σ
  /-- The goals the probe interacted with, in search order. -/
  goals : List α
  /-- The goal that satisfied the probe, if the search was satisfied. -/
  halt : Option α

namespace Probe

/-- The Agree operation over an ordered goal sequence. Each goal in turn is copied from and
flagged if it interacts, and ends the search if it satisfies. -/
def run (p : Probe α) (copy : α → σ → σ) : σ → List α → Result α σ
  | s, [] => ⟨s, [], none⟩
  | s, a :: as =>
    let s' := if p.int a then copy a s else s
    let flag := if p.int a then [a] else []
    if p.sat a then ⟨s', flag, some a⟩
    else
      let r := run p copy s' as
      ⟨r.state, flag ++ r.goals, r.halt⟩

/-- The goals a probe inspects, those before the first satisfying goal together with it. -/
def inspected (p : Probe α) (goals : List α) : List α :=
  goals.takeWhile (!p.sat ·) ++ (p.search goals).toList

variable {p : Probe α} {copy : α → σ → σ} {s : σ} {goals : List α}

@[simp] theorem run_nil : p.run copy s [] = ⟨s, [], none⟩ := rfl

/-- The satisfier of the fold is the goal the search finds. -/
@[simp] theorem run_halt : (p.run copy s goals).halt = p.search goals := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [run, search, List.find?_cons]
    cases p.sat a
    · simpa [search] using ih
    · rfl

/-- The flagged goals are the inspected goals that interact. -/
@[simp] theorem run_goals : (p.run copy s goals).goals = (p.inspected goals).filter p.int := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    cases hs : p.sat a <;> cases hi : p.int a <;>
      simp [run, inspected, search, hs, hi, ih]

/-- The state is the fold of `copy` over the flagged goals. -/
theorem run_state :
    (p.run copy s goals).state = (p.run copy s goals).goals.foldl (fun s a => copy a s) s := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    cases hs : p.sat a <;> cases hi : p.int a <;> simp [run, hs, hi, ih]

/-- An inspected goal is a member of the sequence. -/
theorem mem_of_mem_inspected {a : α} (ha : a ∈ p.inspected goals) : a ∈ goals := by
  rcases List.mem_append.mp ha with h | h
  · exact List.takeWhile_subset _ h
  · cases hs : p.search goals with
    | none => simp [hs] at h
    | some b =>
      simp only [hs, Option.toList_some, List.mem_singleton] at h
      exact h ▸ mem_of_search_eq_some hs

/-- A probe that interacts with no goal leaves the state unchanged. -/
theorem run_state_eq_of_forall_not_int (h : ∀ a ∈ goals, ¬ p.int a) :
    (p.run copy s goals).state = s := by
  rw [run_state, run_goals, List.filter_eq_nil_iff.mpr]
  · rfl
  · exact fun a ha hi => h a (mem_of_mem_inspected ha) hi

/-- When every interacting goal satisfies the probe, the flagged goals are the single goal the
probe Agrees with. -/
theorem run_goals_eq_agree (h : ∀ a, p.int a → p.sat a) :
    (p.run copy s goals).goals = (p.agree goals).toList := by
  rw [run_goals, inspected, List.filter_append, List.filter_eq_nil_iff.mpr, List.nil_append]
  · cases hs : p.search goals with
    | none => simp [agree, hs]
    | some a =>
      simp only [Option.toList_some, List.filter_cons, List.filter_nil, agree, hs,
        Option.filter_some]
      cases p.int a <;> rfl
  · intro a ha hi
    exact absurd (h a hi) (by simpa using List.mem_takeWhile_imp ha)

/-- A relativized probe flags the goal it finds. -/
theorem relativized_run_goals (f : α → Bool) :
    ((relativized f).run copy s goals).goals = ((relativized f).search goals).toList := by
  rw [run_goals_eq_agree (fun _ h => h), relativized_agree]

/-- An insatiable probe flags every interacting goal, Multiple Agree ([hiraiwa-2001]). -/
theorem insatiable_run_goals (f : α → Bool) :
    ((insatiable f).run copy s goals).goals = goals.filter f := by
  rw [run_goals, inspected, List.takeWhile_eq_self_iff.mpr (by simp),
    search_eq_none_iff.mpr (by simp [insatiable])]
  simp [insatiable]

/-! ### Feature specifications -/

/-- A probe specification over a feature type, the features the probe interacts with and the
features that satisfy it, `[INT:int, SAT:sat]` in [deal-2025a]'s notation. -/
structure Spec (F : Type*) where
  /-- The features the probe copies. -/
  int : Finset F
  /-- The features that halt the probe's search. -/
  sat : Finset F

namespace Spec

variable [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- The probe a specification denotes over goals exposing feature sets, interacting with a goal
iff it bears a feature of the interaction specification and satisfied iff it bears one of the
satisfaction specification. -/
def toProbe : Probe α :=
  ⟨fun a => decide (feats a ∩ sp.int).Nonempty, fun a => decide (feats a ∩ sp.sat).Nonempty⟩

/-- Copying from a goal adds its features that lie in the interaction specification. -/
def copyFrom (a : α) (s : Finset F) : Finset F := s ∪ (feats a ∩ sp.int)

/-- The Agree operation of a specification over a goal sequence, starting from no features. -/
def run (goals : List α) : Result α (Finset F) :=
  (sp.toProbe feats).run (sp.copyFrom feats) ∅ goals

@[simp] theorem toProbe_int (a : α) :
    (sp.toProbe feats).int a = decide (feats a ∩ sp.int).Nonempty := rfl

@[simp] theorem toProbe_sat (a : α) :
    (sp.toProbe feats).sat a = decide (feats a ∩ sp.sat).Nonempty := rfl

/-- The state a specification copies only grows. -/
theorem subset_copyFrom (a : α) (s : Finset F) : s ⊆ sp.copyFrom feats a s :=
  Finset.subset_union_left

private theorem foldl_union_eq_biUnion [DecidableEq α] (g : α → Finset F) (s : Finset F) :
    ∀ l : List α, l.foldl (fun s a => s ∪ g a) s = s ∪ l.toFinset.biUnion g
  | [] => by simp
  | a :: l => by
    rw [List.foldl_cons, foldl_union_eq_biUnion g (s ∪ g a) l, List.toFinset_cons,
      Finset.biUnion_insert, Finset.union_assoc]

/-- The copied features are the interaction-specified features of the flagged goals. -/
theorem run_state_eq_biUnion [DecidableEq α] (goals : List α) :
    (sp.run feats goals).state =
      (sp.run feats goals).goals.toFinset.biUnion (feats · ∩ sp.int) := by
  rw [Spec.run, Probe.run_state]
  have h := foldl_union_eq_biUnion (fun a => feats a ∩ sp.int) ∅
    ((sp.toProbe feats).run (sp.copyFrom feats) ∅ goals).goals
  rw [Finset.empty_union] at h
  exact h

/-- The copied features lie in the interaction specification. -/
theorem run_state_subset [DecidableEq α] (goals : List α) :
    (sp.run feats goals).state ⊆ sp.int := by
  rw [run_state_eq_biUnion]
  exact Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right

end Spec

end Probe

end Minimalist
