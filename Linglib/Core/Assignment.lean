/-!
# Variable Assignments

Framework-neutral variable assignment infrastructure shared by static
semantics (Montague/Heim & Kratzer), dynamic semantics (DRT, DPL, CDRT),
and the cylindric algebra formalism.

An `Assignment E` maps natural number indices to entities of type `E`.
The `update` operation `g[n↦d]` modifies a single register, leaving
all others fixed. These operations satisfy the cylindric set algebra
axioms (@cite{henkin-monk-tarski-1971}).
-/

universe u

namespace Core

/-- Variable assignment: function from indices to entities.

This is the canonical assignment type used across the library:
- Montague semantics (static variable binding)
- DRT, DPL, CDRT (dynamic discourse referents)
- Cylindric algebra (abstract coordinate functions) -/
abbrev Assignment (E : Type u) := Nat → E

namespace Assignment

/-- Assignment update `g[n↦d]`: set register `n` to value `d`,
preserving all other registers. -/
def update {E : Type u} (g : Assignment E) (n : Nat) (d : E) : Assignment E :=
  fun m => if m = n then d else g m

@[simp] theorem update_at {E : Type u} (g : Assignment E) (n : Nat) (d : E) :
    (g.update n d) n = d := by simp [update]

@[simp] theorem update_ne {E : Type u} (g : Assignment E) {n m : Nat} (d : E)
    (h : m ≠ n) : (g.update n d) m = g m := by simp [update, h]

theorem update_overwrite {E : Type u} (g : Assignment E) (n : Nat) (x y : E) :
    (g.update n x).update n y = g.update n y := by
  funext m; simp [update]; split <;> rfl

theorem update_comm {E : Type u} (g : Assignment E) {n m : Nat} (x y : E)
    (h : n ≠ m) : (g.update n x).update m y = (g.update m y).update n x := by
  funext k; simp [update]; by_cases hn : k = n <;> by_cases hm : k = m <;> simp_all

theorem update_self {E : Type u} (g : Assignment E) (n : Nat) :
    g.update n (g n) = g := by
  funext i; simp [update]; intro h; exact congrArg g h.symm

end Assignment

end Core
