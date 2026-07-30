/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.QF

/-!
# Quantifier-free logical transductions

String-to-string **logical transductions** in the quantifier-free fragment ([chandlee-2014],
[chandlee-jardine-2019]): a map defined by a **copy set** and, per copy, an ordered list of
guarded output clauses, where each guard is a `Subregular.QF` formula at the input position. A
copy set of size `k` lets the output be larger than the input (insertion); guards that match
nothing delete; relabelling copies rewrite a symbol in place.

We formalize the **order-preserving** fragment: the output is read off in the order
`(input position, copy index)`, so the output successor is induced rather than given by an
explicit successor formula. This is exactly the fragment relevant to strict locality —
relabelling, deletion, and insertion. Non-order-preserving maps (reordering via an explicit
output successor) are the non-local extension and are deliberately out of scope here.

Composition of transductions (`applyComp`) models an iterated derivation: each step is a local
transduction, though the composite is not in general itself quantifier-free.

## Main definitions

* `Subregular.Transduction`: copy count + per-copy guarded output clauses.
* `Transduction.apply`: run a transduction, producing the output string (computable).
* `Transduction.applyComp`: composition of two transductions (one cyclic derivation step on top
  of another).
* `Transduction.LeftLocal`: every guard backward-bounded by `r`.

## Main results

* `Transduction.emitAt_eq_of_agree`: a left-local transduction emits the same block at positions
  whose bounded left contexts agree.

## Implementation notes

A clause is a quantifier-free guard paired with an output symbol; per copy, the first clause
whose guard holds at the input position fires, and a copy with no firing clause is absent.
`apply` is a `flatMap` over input positions then copies, so it reduces under `decide`.
-/

namespace Subregular

variable {α β γ : Type*}

/-- A per-copy output clause: a quantifier-free guard at the input position and the output symbol
emitted when it is the first matching clause. -/
abbrev Clause (α β : Type*) := QF α × β

/-- A quantifier-free order-preserving logical transduction: `copies` output copies of each input
position, and for each copy an ordered list of guarded output clauses. -/
structure Transduction (α β : Type*) where
  copies : ℕ
  clause : Fin copies → List (Clause α β)

namespace Transduction
variable [DecidableEq α]

/-- The output symbols emitted at input position `n` (one per copy whose guard fires, in copy
order). -/
def emitAt (T : Transduction α β) (w : List α) (n : ℕ) : List β :=
  (List.finRange T.copies).filterMap fun c =>
    (T.clause c).findSome? fun cl => if cl.1.Realize w n then some cl.2 else none

/-- Run the transduction: emit, left to right, the licensed copies of every input position. -/
def apply (T : Transduction α β) (w : List α) : List β :=
  (List.range w.length).flatMap (T.emitAt w)

@[simp] theorem apply_nil (T : Transduction α β) : T.apply [] = [] := rfl

/-- Composition of transductions — one cyclic derivation step after another; the composite is
not in general itself quantifier-free. -/
def applyComp (T₂ : Transduction β γ) (T₁ : Transduction α β) [DecidableEq β]
    (w : List α) : List γ :=
  T₂.apply (T₁.apply w)

/-! ### Left-local transductions -/

/-- A transduction is **left-local** with radius `r` if every clause guard is backward-bounded by
`r`: the output at a position is determined by that position and the `r` symbols before it. -/
def LeftLocal (r : ℕ) (T : Transduction α β) : Prop :=
  ∀ c, ∀ cl ∈ T.clause c, cl.1.BackBounded r

/-- Pointwise congruence for `List.findSome?`: agreeing on the list's members suffices. -/
private theorem findSome?_congr {γ δ : Type*} {f g : γ → Option δ} :
    ∀ {l : List γ}, (∀ x ∈ l, f x = g x) → l.findSome? f = l.findSome? g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [List.findSome?_cons, List.findSome?_cons, h a List.mem_cons_self]
    cases g a with
    | none => exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | some b => rfl

/-- A left-local transduction emits the same block at positions whose bounded left contexts
agree: every clause guard is backward-bounded, so its firing is determined by that context. -/
theorem emitAt_eq_of_agree {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) {w w' : List α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?)
    (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    T.emitAt w n = T.emitAt w' n' := by
  unfold Transduction.emitAt
  apply List.filterMap_congr
  intro c _
  apply findSome?_congr
  intro cl hcl
  have hb := hT c cl hcl
  by_cases h : cl.1.Realize w n
  · rw [if_pos h, if_pos ((QF.BackBounded.realize_congr hn hn' hlbl hedge hb).mp h)]
  · rw [if_neg h,
      if_neg (fun hh => h ((QF.BackBounded.realize_congr hn hn' hlbl hedge hb).mpr hh))]

end Transduction

/-! ### Worked examples: feature change, deletion, epenthesis, and a cycle -/

section Example

private inductive Sym | a | b | c
  deriving DecidableEq

private def x : Term := .var
private def isA (t : Term) : QF Sym := .label .a t
/-- Any non-`a` symbol of the demo alphabet. -/
private def nonA (t : Term) : QF Sym := .disj (.label .b t) (.label .c t)
/-- The position is flanked by `a`s. -/
private def flankedA : QF Sym := .conj (isA x.pred) (isA x.succ)

/-- **Relabelling** — rewrite `b → c` between `a`s: the `b → c` clause precedes the faithful
`b → b` clause, so it wins in that context. -/
private def relabelBC : Transduction Sym Sym where
  copies := 1
  clause _ := [(flankedA.conj (.label .b x), .c), (.label .b x, .b),
               (.label .a x, .a), (.label .c x, .c)]

example : relabelBC.apply [Sym.a, .b, .a] = [Sym.a, .c, .a] := by decide

/-- **Deletion** — delete `b` between `a`s: `b` is emitted only when *not* flanked, so a flanked
`b` matches no clause and is dropped. -/
private def deleteFlanked : Transduction Sym Sym where
  copies := 1
  clause _ := [(.label .a x, .a), (.label .c x, .c),
               (QF.conj (.label .b x) flankedA.neg, .b)]

example : deleteFlanked.apply [Sym.a, .b, .a] = [Sym.a, .a] := by decide

/-- **Insertion** — insert `a` after a final non-`a` symbol: copy 0 is faithful, copy 1 emits `a`
only after a final non-`a` (a copy with no firing clause is absent). -/
private def insertA : Transduction Sym Sym where
  copies := 2
  clause k :=
    if k = 0 then
      [(.label .a x, .a), (.label .b x, .b), (.label .c x, .c)]
    else
      [(nonA x |>.conj (QF.final x), .a)]

example : insertA.apply [Sym.a, .b] = [Sym.a, .b, .a] := by decide

/-- **Composition** — relabelling then insertion. On `abab`: the first `b` (between `a`s) becomes
`c`, the final `b` does not, then the final non-`a` triggers insertion. -/
example : insertA.applyComp relabelBC [Sym.a, .b, .a, .b] = [Sym.a, .c, .a, .b, .a] := by
  decide

end Example

end Subregular
