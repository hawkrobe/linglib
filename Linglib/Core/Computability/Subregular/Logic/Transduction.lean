import Linglib.Core.Computability.Subregular.Logic.QFLogic

/-!
# Logical transductions

Quantifier-free graph-to-graph **logical transductions**: a map from an input word model to an
output word model, defined by a **copy set** and, per copy, **output formulas** (`φ_lab(xᶜ)`). A
copy set of size `k` lets the output be larger than the input (insertion); per-copy guards that
match nothing delete; relabelling copies rewrite a symbol in place.

We formalize the **order-preserving** fragment: the output is read off in the order
`(input position, copy index)`, so the output successor is induced rather than given by an explicit
`φ_succ(xᶜ, yᵈ)`. This is exactly the local fragment relevant to strict locality — relabelling,
deletion, and insertion. Non-order-preserving maps (reordering via an explicit successor formula)
are the non-local extension and are deliberately out of scope here.

Composition of transductions (`applyComp`) models an iterated derivation: each step is a local
transduction; the composite is a regular function (closed under composition in `SFST`) though not
in general itself quantifier-free.

## Main definitions

* `Subregular.Logic.Transduction` — copy count + per-copy guarded output clauses.
* `Transduction.apply` — run a transduction, producing the output string (computable).
* `Transduction.applyComp` — composition of two transductions (one cyclic derivation step on top
  of another).

## Implementation notes

A clause is a one-variable QF guard paired with an output symbol; per copy, the first clause whose
guard holds at the input position fires, and a copy with no firing clause is absent. `apply` is a
`flatMap` over input positions then copies, so it reduces under `decide`.
-/

namespace Subregular.Logic

variable {α β γ : Type*}

/-- A per-copy output clause: a quantifier-free guard (one variable, the input position) and the
output symbol emitted when it is the first matching clause. -/
abbrev Clause (α β : Type*) := QF α (Fin 1) × β

/-- A quantifier-free order-preserving logical transduction: `copies` output copies of each input
position, and for each copy an ordered list of guarded output clauses. -/
structure Transduction (α β : Type*) where
  copies : ℕ
  clause : Fin copies → List (Clause α β)

namespace Transduction
variable [DecidableEq α]

/-- The output symbols emitted at input position `n` (one per copy whose guard fires, in copy
order). -/
def emitAt (T : Transduction α β) (w : WordModel α) (n : ℕ) : List β :=
  (List.finRange T.copies).filterMap fun c =>
    (T.clause c).findSome? fun cl => if cl.1.Realize w (fun _ => n) then some cl.2 else none

/-- Run the transduction: emit, left to right, the licensed copies of every input position. -/
def apply (T : Transduction α β) (w : WordModel α) : WordModel β :=
  (List.range w.length).flatMap (T.emitAt w)

@[simp] theorem apply_nil (T : Transduction α β) : T.apply [] = [] := rfl

/-- Composition of transductions — one cyclic derivation step after another. The composite is a
regular function (closed under composition in `SFST`), though not in general quantifier-free. -/
def applyComp (T₂ : Transduction β γ) (T₁ : Transduction α β) [DecidableEq β]
    (w : WordModel α) : WordModel γ :=
  T₂.apply (T₁.apply w)

end Transduction

/-! ### Worked examples: feature change, deletion, epenthesis, and a cycle -/

section Example

private inductive Sym | a | b | c
  deriving DecidableEq

open Term QF

private def x : Term (Fin 1) := var 0
private def isA (t : Term (Fin 1)) : QF Sym (Fin 1) := .atom (.label .a t)
/-- Any non-`a` symbol of the demo alphabet. -/
private def nonA (t : Term (Fin 1)) : QF Sym (Fin 1) :=
  .disj (.atom (.label .b t)) (.atom (.label .c t))
/-- The variable position is flanked by `a`s. -/
private def flankedA : QF Sym (Fin 1) := .conj (isA x.pred) (isA x.succ)

/-- **Relabelling** — rewrite `b → c` between `a`s: the `b → c` clause precedes the faithful
`b → b` clause, so it wins in that context. -/
private def relabelBC : Transduction Sym Sym where
  copies := 1
  clause _ := [(flankedA.conj (.atom (.label .b x)), .c), (.atom (.label .b x), .b),
               (.atom (.label .a x), .a), (.atom (.label .c x), .c)]

example : relabelBC.apply [Sym.a, .b, .a] = [Sym.a, .c, .a] := by decide

/-- **Deletion** — delete `b` between `a`s: `b` is emitted only when *not* flanked, so a flanked
`b` matches no clause and is dropped. -/
private def deleteFlanked : Transduction Sym Sym where
  copies := 1
  clause _ := [(.atom (.label .a x), .a), (.atom (.label .c x), .c),
               (QF.conj (.atom (.label .b x)) flankedA.neg, .b)]

example : deleteFlanked.apply [Sym.a, .b, .a] = [Sym.a, .a] := by decide

/-- **Insertion** — insert `a` after a final non-`a` symbol: copy 0 is faithful, copy 1 emits `a`
only after a final non-`a` (a copy with no firing clause is absent). -/
private def insertA : Transduction Sym Sym where
  copies := 2
  clause k :=
    if k = 0 then
      [(.atom (.label .a x), .a), (.atom (.label .b x), .b), (.atom (.label .c x), .c)]
    else
      [(nonA x |>.conj (QF.final x), .a)]

example : insertA.apply [Sym.a, .b] = [Sym.a, .b, .a] := by decide

/-- **Composition** — relabelling then insertion. On `abab`: the first `b` (between `a`s) becomes
`c`, the final `b` does not, then the final non-`a` triggers insertion. -/
example : insertA.applyComp relabelBC [Sym.a, .b, .a, .b] = [Sym.a, .c, .a, .b, .a] := by
  decide

end Example

end Subregular.Logic
