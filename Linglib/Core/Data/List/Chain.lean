/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Chain

/-!
# Additions to `List.IsChain`

Alphabet-generic `List.IsChain` facts not currently in mathlib, mirroring
`Mathlib/Data/List/Chain.lean`. Candidates for upstreaming.

## Main results

* `List.isChain_top` — every list is a chain for the always-true relation.
* `List.isChain_cons_iff_of_forall_rel` / `List.isChain_append_singleton_iff_of_forall_rel`
  — prepending/appending an element related to (or from) everything preserves `IsChain`.
* `List.IsChain.and` / `List.isChain_and_iff` — a chain for a conjunction relation
  is exactly a chain for each conjunct (the meet law; companion of `List.IsChain.imp`).
-/

namespace List

variable {α : Type*}

/-- Any list is a chain for the universal-true relation. The trivial
case of `IsChain` for a relation that places no constraint on adjacent
elements. -/
lemma isChain_top : ∀ (l : List α), l.IsChain (fun _ _ : α => True)
  | [] => List.isChain_nil
  | [_] => List.isChain_singleton _
  | _ :: _ :: _ => by
      rw [List.isChain_cons_cons]
      exact ⟨trivial, isChain_top _⟩

/-- Prepending an element that `R`-relates to everything preserves `IsChain`. -/
lemma isChain_cons_iff_of_forall_rel {R : α → α → Prop} {a : α} {l : List α}
    (h : ∀ b, R a b) : (a :: l).IsChain R ↔ l.IsChain R := by
  cases l with
  | nil => exact ⟨fun _ => List.isChain_nil, fun _ => List.isChain_singleton _⟩
  | cons u _ =>
    rw [List.isChain_cons_cons]
    exact ⟨And.right, fun hc => ⟨h u, hc⟩⟩

/-- Appending an element that everything `R`-relates to preserves `IsChain`. -/
lemma isChain_append_singleton_iff_of_forall_rel {R : α → α → Prop} {b : α} {l : List α}
    (h : ∀ a, R a b) : (l ++ [b]).IsChain R ↔ l.IsChain R := by
  rw [List.isChain_append]
  refine ⟨And.left, fun hc => ⟨hc, List.isChain_singleton _, ?_⟩⟩
  intro x _ y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hy
  exact h _

namespace IsChain

/-- Two `IsChain` witnesses on the same list combine into a chain for the
conjunction relation. The companion of mathlib's `List.IsChain.imp`. -/
lemma and {S T : α → α → Prop} : ∀ {l : List α},
    l.IsChain S → l.IsChain T → l.IsChain (fun a b => S a b ∧ T a b)
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | _ :: _ :: _, hS, hT => by
    rw [List.isChain_cons_cons] at hS hT ⊢
    exact ⟨⟨hS.1, hT.1⟩, hS.2.and hT.2⟩

end IsChain

/-- A list is a chain for a conjunction relation iff it is a chain for each
conjunct — the `Iff` strengthening of `IsChain.and` (the meet law for `IsChain`
over its relation argument). -/
lemma isChain_and_iff {S T : α → α → Prop} {l : List α} :
    l.IsChain (fun a b => S a b ∧ T a b) ↔ l.IsChain S ∧ l.IsChain T :=
  ⟨fun h => ⟨h.imp fun _ _ => And.left, h.imp fun _ _ => And.right⟩,
   fun ⟨hS, hT⟩ => hS.and hT⟩

end List
