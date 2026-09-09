import Linglib.Syntax.Minimalist.Linearization.Cyclic
import Linglib.Data.Examples.FoxPesetsky2005

/-!
# Fox and Pesetsky (2005): Cyclic Linearization of Syntactic Structure

This file formalizes [fox-pesetsky-2005]'s account of successive cyclicity and Holmberg's
Generalization. Spell-out linearizes each domain as the derivation builds it, its ordering
statements are never deleted, and a derivation converges only if they cohere
(`Minimalist.Linearization.Consistent`). The paper's derivational scenarios are theorems over
arbitrary terminals: movement from the left edge of a domain converges (`scenario1`),
movement from a non-edge position crashes on the pair it reorders (`scenario2`), and moving
the edge material along restores the order (`scenario3`). Object Shift in Swedish is these
scenarios with the verb, the object and an intervener as the terminals: it converges only when
the verb, and any other VP-internal material preceding the object, leaves VP as well
(`objectShift_verbToC`, `objectShift_embedded`, `objectShift_intervener`,
`objectShift_intervener_fronted`), and `rows_predicted` computes convergence for the paper's
Swedish sentences from their configurations.

## Implementation notes

Spell-out domains are lists of terminals and a derivation is its list of snapshots, so the
scenarios quantify over any type of labels; the consistent cases need the final snapshot to be
duplicate-free. The Swedish rows record the paper's analysis of each sentence, whether the
verb moves to C, whether an auxiliary occupies C instead, whether a first object or particle
precedes the object in VP, and whether that intervener fronts through the VP edge, and
`Config.phases` builds the VP and CP snapshots of the paper's sketches from them.

## References

* [fox-pesetsky-2005]
* [chomsky-2000]
* [chomsky-2001]
-/

namespace FoxPesetsky2005

open Minimalist.Linearization Data.Examples

variable {α : Type*} {X Y Z a : α}

/-! ### Derivational scenarios -/

/-- Scenario 1: leftward movement from the left edge of a domain converges. -/
theorem scenario1 [DecidableEq α] (hnd : [X, a, Y, Z].Nodup) :
    Consistent [[X, Y, Z], [X, a, Y, Z]] := by
  refine consistent_of_forall_sublist (λ p hp => ?_) hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (((List.Sublist.refl [Y, Z]).cons a).cons_cons X)
  · exact List.Sublist.refl _

/-- Scenario 2: leftward movement from a non-edge position reorders the moved element and the
edge, and the derivation crashes whatever else it contains. -/
theorem scenario2 : ¬ Consistent [[X, Y, Z], [Y, a, X, Z]] :=
  not_consistent_of_pair List.mem_cons_self (by simp)
    (((List.nil_sublist [Z]).cons_cons Y).cons_cons X)
    ((((List.nil_sublist [Z]).cons_cons X).cons a).cons_cons Y)

/-- Scenario 3: moving the edge material along with the non-edge element preserves their order,
so the derivation converges. -/
theorem scenario3 [DecidableEq α] (hnd : [X, Y, a, Z].Nodup) :
    Consistent [[X, Y, Z], [X, Y, a, Z]] := by
  refine consistent_of_forall_sublist (λ p hp => ?_) hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ((((List.Sublist.refl [Z]).cons a).cons_cons Y).cons_cons X)
  · exact List.Sublist.refl _

/-- An ordering cycle through several Spell-outs crashes as well: the crash condition is the
acyclicity of the accumulated order, not a directly contradicted pair. -/
theorem cycle {b c : α} : ¬ Consistent [[a, b], [b, c], [c, a]] := λ h =>
  h a (.tail (.tail (.single ⟨[a, b], by simp, List.Sublist.refl _⟩) ⟨[b, c], by simp,
    List.Sublist.refl _⟩) ⟨[c, a], by simp, List.Sublist.refl _⟩)

/-! ### Holmberg's Generalization -/

section Holmberg

variable {S V O adv C aux XP : α}

/-- Object Shift with the verb in C: VP orders the verb before the object and CP keeps it so. -/
theorem objectShift_verbToC [DecidableEq α] (hnd : [S, V, O, adv].Nodup) :
    Consistent [[V, O], [S, V, O, adv]] := by
  refine consistent_of_forall_sublist (λ p hp => ?_) hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ((((List.nil_sublist [adv]).cons_cons O).cons_cons V).cons S)
  · exact List.Sublist.refl _

/-- Object Shift in an embedded clause, where the verb stays in VP: the shifted object precedes
the verb at CP against VP, and the derivation crashes. -/
theorem objectShift_embedded : ¬ Consistent [[V, O], [C, S, O, adv, V]] :=
  not_consistent_of_pair List.mem_cons_self (by simp) (List.Sublist.refl _)
    ((((((List.nil_sublist []).cons_cons V).cons adv).cons_cons O).cons S).cons C)

/-- Object Shift under an auxiliary in C: the same contradiction. -/
theorem objectShift_aux : ¬ Consistent [[V, O], [S, aux, O, adv, V]] :=
  not_consistent_of_pair List.mem_cons_self (by simp) (List.Sublist.refl _)
    ((((((List.nil_sublist []).cons_cons V).cons adv).cons_cons O).cons aux).cons S)

/-- Any VP-internal material preceding the object blocks Object Shift, verb movement or not:
the intervener precedes the object at VP and follows it at CP. -/
theorem objectShift_intervener : ¬ Consistent [[V, XP, O], [S, V, O, adv, XP]] :=
  not_consistent_of_pair List.mem_cons_self (by simp)
    ((((List.nil_sublist []).cons_cons O).cons_cons XP).cons V)
    ((((((List.nil_sublist []).cons_cons XP).cons adv).cons_cons O).cons V).cons S)

/-- An intervener that fronts through the VP edge no longer blocks Object Shift: the order
established at VP is the order at CP. -/
theorem objectShift_intervener_fronted [DecidableEq α] (hnd : [XP, V, S, O, adv].Nodup) :
    Consistent [[XP, V, O], [XP, V, S, O, adv]] := by
  refine consistent_of_forall_sublist (λ p hp => ?_) hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (((((List.nil_sublist [adv]).cons_cons O).cons S).cons_cons V).cons_cons XP)
  · exact List.Sublist.refl _

end Holmberg

/-! ### The Swedish data -/

/-- The terminals of the paper's Object Shift sketches. -/
inductive Label
  | S
  | V
  | O
  | adv
  | C
  | aux
  | XP
  deriving DecidableEq, Repr

/-- The paper's analysis of an Object Shift sentence: whether the finite verb moves to C,
whether an auxiliary occupies C instead, whether a first object or particle precedes the object
in VP, and whether that intervener fronts through the VP edge. -/
structure Config where
  verbToC : Bool
  aux : Bool
  intervener : Bool
  intervenerMoved : Bool
  deriving DecidableEq, Repr

namespace Config

/-- The VP snapshot: an intervener that will front has first moved to the VP edge. -/
def vp (c : Config) : List Label :=
  if c.intervener then (if c.intervenerMoved then [.XP, .V, .O] else [.V, .XP, .O]) else [.V, .O]

/-- The CP snapshot after Object Shift. -/
def cp (c : Config) : List Label :=
  (if c.verbToC then (if c.intervenerMoved then [.XP, .V, .S] else [.S, .V])
    else if c.aux then [.S, .aux] else [.C, .S]) ++
  [.O, .adv] ++ (if c.verbToC then [] else [.V]) ++
  (if c.intervener ∧ ¬ c.intervenerMoved then [.XP] else [])

/-- The derivation's snapshots. -/
def phases (c : Config) : List (List Label) := [c.vp, c.cp]

end Config

structure Row where
  config : Config
  judgment : Features.Judgment
  deriving DecidableEq

def yesNoTable : List (String × Bool) := [("yes", true), ("no", false)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let v ← ex.parse? "verbToC" yesNoTable
  let x ← ex.parse? "aux" yesNoTable
  let i ← ex.parse? "intervener" [("none", false), ("firstObject", true), ("particle", true)]
  let m ← ex.parse? "intervenerMoved" yesNoTable
  pure ⟨⟨v, x, i, m⟩, ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The paper's Swedish sentences are acceptable exactly when their derivations linearize. -/
theorem rows_predicted : ∀ r ∈ rows, (r.judgment = .acceptable ↔ Consistent r.config.phases) := by
  decide

end FoxPesetsky2005
