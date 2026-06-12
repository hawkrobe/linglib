import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Typed atoms and small world models for free-choice scenarios

Shared scenario substrate for BSML- and QBSML-based free-choice studies
([aloni-2022], [aloni-vanormondt-2023], [yan-2023]). Replaces ad-hoc
string atoms (`"coffee"`, `"tea"`, ...) in scenario constructions, where
a typo silently compiles to `false` under the
`match p with | "coffee" => ... | _ => false` fallthrough pattern.

## Main declarations

* `FCAtom` — typed propositional atoms: `a`/`b` cover the disjuncts of
  binary FC inferences; `c` is reserved for embedded scenarios involving
  a third proposition.
* `QVar` — the shared toy variable type for quantified FC scenarios
  (QBSML); the first-order counterpart of `FCAtom`.
* `PowerSet2World` — the 2² = 4 truth assignments to two atoms
  ([aloni-2022] Figure 1: `w_∅`, `w_a`, `w_b`, `w_ab`), with the typed
  `holds` truth table.

Studies instantiate `BSMLModel`'s String-keyed `val` field by
pattern-matching on the canonical names via `FCAtom.toName`. Eliminating
the String layer entirely (making `BSMLModel.val : FCAtom → α → Bool`)
would require parameterizing `BSMLFormula` and `BSMLModel` over the atom
type — a substrate-wide refactor deferred to a separate effort.
-/

namespace Core.Logic.Modal.BSML

/-- Typed atom enum for free-choice scenarios. -/
inductive FCAtom
  /-- First disjunct (e.g. `coffee`, `Paris`, `boat`). -/
  | a
  /-- Second disjunct (e.g. `tea`, `Rome`, `bus`). -/
  | b
  /-- Third atom for embedded scenarios (negative free choice). -/
  | c
  deriving DecidableEq, Repr

instance : Fintype FCAtom where
  elems := {.a, .b, .c}
  complete := by intro x; cases x <;> simp

/-- Canonical String name of an atom. Used at `BSMLModel.val` boundaries
    where the substrate's `val : String → α → Bool` field forces String. -/
def FCAtom.toName : FCAtom → String
  | .a => "a"
  | .b => "b"
  | .c => "c"

/-- Single variable `x` — the shared toy variable type for quantified FC
    scenarios (QBSML studies); the first-order counterpart of `FCAtom`. -/
inductive QVar | x
  deriving DecidableEq, Repr, Fintype

/-- Power-set-of-{a,b}: the 4 truth assignments to two propositional atoms.

    Names follow [aloni-2022] Figure 1 (`w_∅`, `w_a`, `w_b`, `w_ab`):
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

end Core.Logic.Modal.BSML
