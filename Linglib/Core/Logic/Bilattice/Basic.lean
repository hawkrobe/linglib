import Mathlib.Order.Basic
import Mathlib.Data.Bool.Basic

/-!
# Evidential bilattices over a chain
[fitting-1994] [schoter-1996]

A *bilattice* carries two orders on one carrier — a *truth* order `≤_t` and an
*information/knowledge* order `≤_k` ([fitting-1994]). The *evidential* bilattices
([schoter-1996]) are the ones of the form `S ⊙ S` for a chain `S`: a value is a
pair `(for, against)` of degrees of evidence, with

* `≤_t` truer  = more evidence-for, less evidence-against;
* `≤_k` more informative = more evidence both ways;
* `neg` (truth inversion) swaps the two coordinates;
* `conf` (knowledge inversion, the *conflation*) complements each coordinate.

With `S = Bool` this is Belnap's `FOUR`; with `S = Fin 3` (the chain `0 < ½ < 1`)
it is [schoter-1996]'s 9-valued `PRESUP` (see `Studies.Schoter1996`). This file
is the shared substrate; concrete bilattices and their linguistic uses live in
the consuming `Studies` files.

## Main definitions

* `Bilattice.Evidential S := S × S` — the evidential bilattice over a chain `S`
* `Evidential.tLE`/`kLE`/`neg`/`conf`/`Consistent` — the two orders, negation,
  conflation, and the consistent (`x ≤_k −x`, non-glut) fragment
* `Bilattice.FOUR := Evidential Bool` — Belnap's four-valued bilattice
-/

namespace Bilattice

/-- The evidential bilattice over a chain `S`: values are `(for, against)`
pairs ([schoter-1996]'s `S ⊙ S`). -/
abbrev Evidential (S : Type*) := S × S

namespace Evidential

variable {S : Type*} [Preorder S]

/-- Truth order: more evidence-for and less evidence-against. -/
@[reducible] def tLE (x y : Evidential S) : Prop := x.1 ≤ y.1 ∧ y.2 ≤ x.2
/-- Knowledge order: more evidence both ways. -/
@[reducible] def kLE (x y : Evidential S) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2
/-- Negation: truth inversion, swaps the coordinates. -/
def neg : Evidential S → Evidential S := Prod.swap
/-- Conflation `−`: knowledge inversion, complements each coordinate by `compl`,
which is intended to be the order-reversing involution on the chain `S`
(`(! ·)` for `Bool`, `Fin.rev` for `Fin n`). -/
def conf (compl : S → S) (x : Evidential S) : Evidential S := (compl x.2, compl x.1)
/-- The consistent (non-glut) fragment: `x ≤_k −x` ([fitting-1994]). -/
@[reducible] def Consistent (compl : S → S) (x : Evidential S) : Prop :=
  kLE x (conf compl x)

end Evidential

/-- Belnap's four-valued bilattice `FOUR = Bool ⊙ Bool`, `(for, against)` over
`Bool`. -/
abbrev FOUR := Evidential Bool

namespace FOUR

/-- `⊥`: neither — no information (a truth-value gap). -/
def U : FOUR := (false, false)
/-- `true`. -/
def T : FOUR := (true, false)
/-- `false`. -/
def F : FOUR := (false, true)
/-- `⊤`: both — inconsistent (a truth-value glut). -/
def I : FOUR := (true, true)

/-- Conflation on `FOUR` (Boolean complement). -/
@[reducible] def conf (x : FOUR) : FOUR := Evidential.conf (! ·) x
/-- The consistent (non-glut) fragment of `FOUR` — equivalently `x ≠ I`. -/
@[reducible] def Consistent (x : FOUR) : Prop := Evidential.Consistent (! ·) x

@[simp] theorem consistent_iff (x : FOUR) : Consistent x ↔ x ≠ I := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> decide

end FOUR

end Bilattice
