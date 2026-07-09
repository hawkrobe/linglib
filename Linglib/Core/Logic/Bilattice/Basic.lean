import Linglib.Core.Logic.Bilattice.Product

/-!
# Evidential bilattices over a chain
[fitting-1994] [schoter-1996]

The *evidential* bilattices ([schoter-1996]) are the diagonal Ginsberg–Fitting
products `S ⊙ S` over a chain `S` (`Core.Logic.Bilattice.Product`): a value is
a pair `(for, against)` of degrees of evidence, with

* `≤` truer = more evidence-for, less evidence-against (the truth order);
* `≤ₖ` more informative = more evidence both ways (the knowledge order);
* `Product.neg` (truth inversion) swaps the two coordinates;
* `conf` (knowledge inversion, the *conflation*) complements each coordinate.

With `S = Bool` this is [belnap-1977]'s `FOUR`, whose logic is developed as a
bilattice by [arieli-avron-1996]; with `S = Fin 3` (the chain `0 < ½ < 1`) it
is [schoter-1996]'s 9-valued `PRESUP` (see `Studies.Schoter1996`).

## Main definitions

* `Bilattice.Evidential S := S ⊙ S` — the evidential bilattice over a chain `S`
* `Evidential.conf`/`Consistent` — conflation and the consistent (`x ≤ₖ −x`,
  non-glut) fragment
* `Bilattice.FOUR := Evidential Bool` — Belnap's four-valued bilattice
-/

namespace Bilattice

/-- The evidential bilattice over a chain `S`: the diagonal product `S ⊙ S`,
values are `(for, against)` pairs ([schoter-1996]). -/
abbrev Evidential (S : Type*) := Product S S

namespace Evidential

variable {S : Type*}

/-- Conflation `−`: knowledge inversion, complements each coordinate by `compl`,
which is intended to be the order-reversing involution on the chain `S`
(`(! ·)` for `Bool`, `Fin.rev` for `Fin n`). -/
def conf (compl : S → S) (x : Evidential S) : Evidential S :=
  .mk (compl x.con) (compl x.pro)

/-- The consistent (non-glut) fragment: `x ≤ₖ −x` ([fitting-1994]). -/
@[reducible] def Consistent [Preorder S] (compl : S → S) (x : Evidential S) : Prop :=
  x ≤ₖ conf compl x

/-- The classical fragment: `x = −x`, the fixed points of conflation
([fitting-1994]; [schoter-1996]'s `CLAS`). -/
@[reducible] def IsClassical (compl : S → S) (x : Evidential S) : Prop :=
  x = conf compl x

/-- Over an order-reversing involution `compl`, consistency reduces to a single
inequality: the evidence-against is below the complement of the evidence-for
([schoter-1996]'s `CONS = {⟨a, b⟩ | a ≤ b′}`). -/
theorem consistent_iff_con_le [Preorder S] {compl : S → S} (hanti : Antitone compl)
    (hinv : Function.Involutive compl) {x : Evidential S} :
    Consistent compl x ↔ x.con ≤ compl x.pro := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  have h' := hanti h
  rw [hinv x.pro] at h'
  exact h'

end Evidential

/-- [belnap-1977]'s four-valued bilattice `FOUR = Bool ⊙ Bool`, `(for, against)`
over `Bool`. -/
abbrev FOUR := Evidential Bool

namespace FOUR

/-- `⊥`: neither — no information (a truth-value gap). -/
def U : FOUR := .mk false false
/-- `true`. -/
def T : FOUR := .mk true false
/-- `false`. -/
def F : FOUR := .mk false true
/-- `⊤`: both — inconsistent (a truth-value glut). -/
def I : FOUR := .mk true true

/-- Conflation on `FOUR` (Boolean complement). -/
@[reducible] def conf (x : FOUR) : FOUR := Evidential.conf (! ·) x
/-- The consistent (non-glut) fragment of `FOUR` — equivalently `x ≠ I`. -/
@[reducible] def Consistent (x : FOUR) : Prop := Evidential.Consistent (! ·) x
/-- The classical fragment of `FOUR` — equivalently `{F, T}`. -/
@[reducible] def IsClassical (x : FOUR) : Prop := Evidential.IsClassical (! ·) x

@[simp] theorem consistent_iff (x : FOUR) : Consistent x ↔ x ≠ I := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> decide

/-- The classical fragment of `FOUR` is `{F, T}` ([fitting-1994];
[schoter-1996]). -/
@[simp] theorem isClassical_iff (x : FOUR) : IsClassical x ↔ x = F ∨ x = T := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> decide

end FOUR

end Bilattice
