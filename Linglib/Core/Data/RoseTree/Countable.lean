/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Basic
import Mathlib.Data.W.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Countable.Basic

/-!
# Countability of rose trees

A rose tree over a countable type is countable: it injects into the W-type over the countable
label type `Option (Option α)`, where `some (some a)` is a node whose one child is its list of
children, `none` the empty list and `some none` a cons cell with two children.
-/

namespace RoseTree

variable {α : Type*}

/-- The branching signature of the W-type encoding. -/
private def wArity : Option (Option α) → Type
  | some (some _) => Unit
  | none => Empty
  | some none => Bool

mutual
private def toW : RoseTree α → WType (wArity (α := α))
  | .node a cs => ⟨some (some a), fun _ => toWList cs⟩
private def toWList : List (RoseTree α) → WType (wArity (α := α))
  | [] => ⟨none, Empty.elim⟩
  | c :: cs => ⟨some none, fun b => bif b then toW c else toWList cs⟩
end

mutual
private theorem toW_injective : ∀ {t t' : RoseTree α}, toW t = toW t' → t = t'
  | .node _ cs, .node _ cs', h => by
    obtain ⟨h1, h2⟩ := WType.mk.inj h
    cases h1
    rw [toWList_injective (congr_fun (eq_of_heq h2) ())]
private theorem toWList_injective :
    ∀ {cs cs' : List (RoseTree α)}, toWList cs = toWList cs' → cs = cs'
  | [], [], _ => rfl
  | [], _ :: _, h => by exact absurd (WType.mk.inj h).1 (by simp)
  | _ :: _, [], h => by exact absurd (WType.mk.inj h).1 (by simp)
  | c :: cs, c' :: cs', h => by
    obtain ⟨-, h2⟩ := WType.mk.inj h
    have h3 := congr_fun (eq_of_heq h2)
    rw [toW_injective (t := c) (t' := c') (by simpa using h3 true),
      toWList_injective (cs := cs) (cs' := cs') (by simpa using h3 false)]
end

instance [Countable α] : Countable (RoseTree α) := by
  classical
  let _ := Encodable.ofCountable α
  have _ : ∀ a, Fintype (wArity (α := α) a) := fun a => by
    rcases a with _ | (_ | _)
    · exact inferInstanceAs (Fintype Empty)
    · exact inferInstanceAs (Fintype Bool)
    · exact inferInstanceAs (Fintype Unit)
  have _ : ∀ a, Encodable (wArity (α := α) a) := fun a => by
    rcases a with _ | (_ | _)
    · exact inferInstanceAs (Encodable Empty)
    · exact inferInstanceAs (Encodable Bool)
    · exact inferInstanceAs (Encodable Unit)
  exact Function.Injective.countable fun _ _ h => toW_injective h

end RoseTree
