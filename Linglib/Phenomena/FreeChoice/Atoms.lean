import Mathlib.Data.Fintype.Basic

/-!
# Free Choice atoms — typed substrate for FC scenarios

Three typed propositional atoms shared across free-choice studies. Replaces
ad-hoc string atoms (`"coffee"`, `"tea"`, etc.) in scenario constructions
where a typo silently compiles to `false` under the
`match p with | "coffee" => ... | _ => false` fallthrough pattern endemic
to BSML- and Hamblin-style models.

`a` and `b` cover the disjuncts of binary FC inferences (`α ∨ β`, `◇(α ∨ β)`,
`◇α ∨ ◇β`). `c` is reserved for embedded scenarios involving a third
proposition (e.g. `(◇(α ∨ β) ∨ ◇c) ∧ ¬◇c` in Aloni 2022 §7 (55)).

This is **substrate-level** typing — Studies files instantiate `BSMLModel`'s
String-keyed `val` field by pattern-matching on the canonical names
(`"a"`, `"b"`, `"c"`) and routing through these atoms via per-world `holds`
helpers. Eliminating the String layer entirely (i.e., making
`BSMLModel.val : FCAtom → α → Bool`) would require parameterizing
`BSMLFormula` and `BSMLModel` over the atom type — a substrate-wide
refactor deferred to a separate effort.
-/

namespace Phenomena.FreeChoice

/-- Typed atom enum for free-choice scenarios. -/
inductive FCAtom
  /-- First disjunct (e.g. `coffee`, `Paris`, `boat`). -/
  | a
  /-- Second disjunct (e.g. `tea`, `Rome`, `bus`). -/
  | b
  /-- Third atom for embedded scenarios (Negative FC, Aloni §7 example (55)). -/
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

end Phenomena.FreeChoice
