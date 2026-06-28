import Linglib.Core.Computability.Subregular.Logic.QFLogic

/-!
# Logical transductions

Quantifier-free graph-to-graph **logical transductions** ([dolatian-2020], after Courcelle and
Engelfriet & Hoogeboom): a phonological process as a map from an input word model to an output
word model, defined by a **copy set** and, per copy, **output formulas** (Dolatian's `φ_lab(xᶜ)`).
A copy set of size `k` lets the output be larger than the input (epenthesis); per-copy guards that
match nothing delete (deletion); relabelling copies change features (feature change).

We formalize the **order-preserving** fragment: the output is read off in the order
`(input position, copy index)`, so the output successor is induced rather than given by an explicit
`φ_succ(xᶜ, yᵈ)`. This is exactly the local fragment relevant to strict locality — feature change,
deletion, and epenthesis. Non-order-preserving processes (metathesis via an explicit successor
formula) are the non-local extension and are deliberately out of scope here.

Cyclic / interactionist phonology is **composition** of transductions (`applyComp`): each cycle is
a local transduction; the whole derivation is their composite (a regular function — closed under
composition in `SFST` — though not in general itself quantifier-free).

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

private inductive Seg | p | t | d | j | a
  deriving DecidableEq

open Term QF

private def x : Term (Fin 1) := var 0
private def vowelAt (t : Term (Fin 1)) : QF Seg (Fin 1) := .atom (.label .a t)
/-- A consonant: any non-vowel symbol of the demo alphabet. -/
private def consAt (t : Term (Fin 1)) : QF Seg (Fin 1) :=
  .disj (.atom (.label .p t)) (.disj (.atom (.label .t t))
    (.disj (.atom (.label .d t)) (.atom (.label .j t))))
/-- The variable position is intervocalic (flanked by vowels), quantifier-free. -/
private def interV : QF Seg (Fin 1) := .conj (vowelAt x.pred) (vowelAt x.succ)

/-- **Feature change** — intervocalic stop voicing `t → d`: the `t → d` clause precedes the
faithful `t → t` clause, so it wins between vowels. -/
private def voicing : Transduction Seg Seg where
  copies := 1
  clause _ := [(interV.conj (.atom (.label .t x)), .d), (.atom (.label .t x), .t),
               (.atom (.label .p x), .p), (.atom (.label .a x), .a), (.atom (.label .d x), .d)]

example : voicing.apply [Seg.p, .a, .t, .a] = [Seg.p, .a, .d, .a] := by decide

/-- **Deletion** — intervocalic glide `j` deletion: `j` is emitted only when *not* intervocalic, so
an intervocalic `j` matches no clause and is dropped. -/
private def glideDeletion : Transduction Seg Seg where
  copies := 1
  clause _ := [(.atom (.label .p x), .p), (.atom (.label .a x), .a), (.atom (.label .t x), .t),
               (.atom (.label .d x), .d), (QF.conj (.atom (.label .j x)) interV.neg, .j)]

example : glideDeletion.apply [Seg.p, .a, .j, .a] = [Seg.p, .a, .a] := by decide

/-- **Epenthesis** — insert a final vowel after a word-final consonant: copy 0 is faithful, copy 1
emits `a` only after a final consonant. -/
private def finalEpenthesis : Transduction Seg Seg where
  copies := 2
  clause c :=
    if c = 0 then
      [(.atom (.label .p x), .p), (.atom (.label .t x), .t), (.atom (.label .d x), .d),
       (.atom (.label .j x), .j), (.atom (.label .a x), .a)]
    else
      [(consAt x |>.conj (QF.final x), .a)]

example : finalEpenthesis.apply [Seg.p, .a, .t] = [Seg.p, .a, .t, .a] := by decide

/-- **Cyclicity** — composition of two local transductions: intervocalic voicing then final
epenthesis. On `atat`: the first `t` voices (between vowels), the final `t` does not, then the
final consonant triggers epenthesis. -/
example : finalEpenthesis.applyComp voicing [Seg.a, .t, .a, .t] = [Seg.a, .d, .a, .t, .a] := by
  decide

end Example

end Subregular.Logic
