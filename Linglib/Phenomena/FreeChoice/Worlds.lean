import Linglib.Phenomena.FreeChoice.Atoms

/-!
# Power-set-of-atoms world models for free-choice scenarios

The standard small modal-logic models used to demonstrate free-choice
inference. A `PowerSet2World` enumerates the 2² = 4 truth assignments to
two atoms — Aloni 2022 Figure 1 (`w_∅`, `w_a`, `w_b`, `w_ab`).

This pattern is independently reinvented in `Aloni2022.lean` (as
`PermissionWorld` over coffee/tea), `Heim1992Desire.lean` (line 51, "4-world
model with two binary dimensions"), `Boylan2023.lean` (line 570),
`Roberts2023.lean` (line 301). Hoisting it here lets all of those
consume one definition.

The `holds` helper takes a typed `FCAtom` rather than a String, so
typos are caught by the compiler rather than silently producing `false`.
-/

namespace Phenomena.FreeChoice

/-- Power-set-of-{a,b}: the 4 truth assignments to two propositional atoms.

    Names follow Aloni 2022 Figure 1 (`w_∅`, `w_a`, `w_b`, `w_ab`):
    - `nothing` = `w_∅`: neither `a` nor `b`
    - `onlyA`   = `w_a`: only `a`
    - `onlyB`   = `w_b`: only `b`
    - `both`    = `w_ab`: both `a` and `b`
-/
inductive PowerSet2World
  | nothing
  | onlyA
  | onlyB
  | both
  deriving DecidableEq, Repr

instance : Fintype PowerSet2World where
  elems := {.nothing, .onlyA, .onlyB, .both}
  complete := by intro x; cases x <;> simp

namespace PowerSet2World

/-- Truth-table for the two-atom power set. The third atom (`c`) is
    unsatisfiable in this baseline 4-world model — embedded scenarios
    needing `c` should use a larger world type. -/
def holds : PowerSet2World → FCAtom → Bool
  | .both,    .a => true
  | .both,    .b => true
  | .onlyA,   .a => true
  | .onlyA,   .b => false
  | .onlyB,   .a => false
  | .onlyB,   .b => true
  | .nothing, .a => false
  | .nothing, .b => false
  | _,        .c => false

/-- Synonym used by Studies that prefer the predicate spelling. -/
abbrev satisfies : PowerSet2World → FCAtom → Bool := holds

end PowerSet2World

end Phenomena.FreeChoice
