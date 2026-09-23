module

public import Linglib.Syntax.Minimalist.Linearization.Cyclic
public import Linglib.Data.Examples.FoxPesetsky2005

/-!
# Fox and Pesetsky (2005): Cyclic Linearization of Syntactic Structure

This file formalizes [fox-pesetsky-2005]'s account of successive cyclicity and Holmberg's
Generalization under cyclic linearization (`Minimalist.Linearization.Consistent`). The
derivational scenarios (13)–(15) are theorems over arbitrary terminals: movement from the left
edge of a domain converges, movement from a non-edge position crashes on the pair it reorders,
and moving the edge material along restores the order. Swedish Object Shift is these scenarios
with the verb, the object and an intervener as the terminals, and the paper's sketches of its
sentences (`Sketch.phases`) predict their judgments (`rows_predicted`).

## References

* [fox-pesetsky-2005]
-/

@[expose] public section

namespace FoxPesetsky2005

open Minimalist.Linearization Data.Examples

variable {α : Type*} {X Y Z a : α}

/-! ### Derivational scenarios -/

/-- Scenario 1 (13): leftward movement from the left edge of a domain converges. -/
theorem scenario1 [DecidableEq α] (hnd : [X, a, Y, Z].Nodup) :
    Consistent [[X, Y, Z], [X, a, Y, Z]] :=
  consistent_of_forall_sublist (by simp) hnd

/-- Scenario 2 (14): leftward movement from a non-edge position reorders the moved element and
the edge, and the derivation crashes whatever else it contains. -/
theorem scenario2 : ¬ Consistent [[X, Y, Z], [Y, a, X, Z]] :=
  not_consistent_of_pair X Y ⟨[X, Y, Z], by simp, by simp⟩ ⟨[Y, a, X, Z], by simp, by simp⟩

/-- Scenario 3 (15): moving the edge material along with the non-edge element preserves their
order, so the derivation converges. -/
theorem scenario3 [DecidableEq α] (hnd : [X, Y, a, Z].Nodup) :
    Consistent [[X, Y, Z], [X, Y, a, Z]] :=
  consistent_of_forall_sublist (by simp) hnd

/-- An ordering cycle through several Spell-outs crashes as well: the crash condition is the
acyclicity of the accumulated order, not a directly contradicted pair. -/
theorem cycle {b c : α} : ¬ Consistent [[a, b], [b, c], [c, a]] := fun h ↦
  h a (.tail (.tail (.single ⟨[a, b], by simp, .refl _⟩) ⟨[b, c], by simp, .refl _⟩)
    ⟨[c, a], by simp, .refl _⟩)

/-! ### Holmberg's Generalization -/

section Holmberg

variable {S V O adv C aux XP : α}

/-- Object Shift with the verb in C (20): VP orders the verb before the object and CP keeps it
so. -/
theorem objectShift_verbToC [DecidableEq α] (hnd : [S, V, O, adv].Nodup) :
    Consistent [[V, O], [S, V, O, adv]] :=
  consistent_of_forall_sublist (by simp [List.sublist_cons_iff]) hnd

/-- Object Shift in an embedded clause (21), where the verb stays in VP: the shifted object
precedes the verb at CP against VP, and the derivation crashes. -/
theorem objectShift_embedded : ¬ Consistent [[V, O], [C, S, O, adv, V]] :=
  not_consistent_of_pair V O ⟨[V, O], by simp, by simp⟩
    ⟨[C, S, O, adv, V], by simp, by simp [List.sublist_cons_iff]⟩

/-- Object Shift under an auxiliary in C (22): the same contradiction. -/
theorem objectShift_aux : ¬ Consistent [[V, O], [S, aux, O, adv, V]] :=
  not_consistent_of_pair V O ⟨[V, O], by simp, by simp⟩
    ⟨[S, aux, O, adv, V], by simp, by simp [List.sublist_cons_iff]⟩

/-- Any VP-internal material preceding the object blocks Object Shift (24), verb movement or
not: the intervener precedes the object at VP and follows it at CP. -/
theorem objectShift_intervener : ¬ Consistent [[V, XP, O], [S, V, O, adv, XP]] :=
  not_consistent_of_pair XP O ⟨[V, XP, O], by simp, by simp⟩
    ⟨[S, V, O, adv, XP], by simp, by simp [List.sublist_cons_iff]⟩

/-- An intervener that fronts through the VP edge (26) no longer blocks Object Shift: the order
established at VP is the order at CP. -/
theorem objectShift_intervener_fronted [DecidableEq α] (hnd : [XP, V, S, O, adv].Nodup) :
    Consistent [[XP, V, O], [XP, V, S, O, adv]] :=
  consistent_of_forall_sublist (by simp [List.sublist_cons_iff]) hnd

end Holmberg

/-! ### The Swedish data -/

/-- The terminals of the paper's Object Shift sketches. -/
inductive Terminal
  | S | V | O | adv | C | aux | XP
  deriving DecidableEq, Repr

/-- The paper's sketch of an Object Shift sentence's derivation: which of (20)–(22), (24) and
(26) the sentence instantiates. -/
inductive Sketch
  /-- (20): the finite verb moves to C. -/
  | verbToC
  /-- (21): an embedded clause, whose complementizer keeps the verb in VP. -/
  | embedded
  /-- (22): an auxiliary moves to C and the verb stays in VP. -/
  | auxiliary
  /-- (24): a first object or particle precedes the object in VP. -/
  | intervener
  /-- (26): the intervener fronts through the VP edge. -/
  | intervenerFronted
  deriving DecidableEq, Repr

namespace Sketch

open Terminal

/-- The VP and CP snapshots as the paper draws them. -/
def phases : Sketch → List (List Terminal)
  | verbToC => [[V, O], [S, V, O, adv]]
  | embedded => [[V, O], [C, S, O, adv, V]]
  | auxiliary => [[V, O], [S, aux, O, adv, V]]
  | intervener => [[V, XP, O], [S, V, O, adv, XP]]
  | intervenerFronted => [[XP, V, O], [XP, V, S, O, adv]]

/-- The feature values naming the sketches in the example data. -/
def table : List (String × Sketch) :=
  [("verbToC", verbToC), ("embedded", embedded), ("auxiliary", auxiliary),
    ("intervener", intervener), ("intervenerFronted", intervenerFronted)]

end Sketch

/-- The paper's Swedish sentences are acceptable exactly when their sketches linearize. -/
theorem rows_predicted : ∀ ex ∈ Examples.all, ∀ s ∈ ex.parse? "sketch" Sketch.table,
    (ex.judgment = .acceptable ↔ Consistent s.phases) := by
  decide

end FoxPesetsky2005
