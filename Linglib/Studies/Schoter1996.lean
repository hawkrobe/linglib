import Linglib.Core.Logic.Bilattice.Basic
import Mathlib.Order.Fin.Basic

/-!
# Schöter's evidential bilattices: `PRESUP` and the evidential progression
[schoter-1996]

[schoter-1996]'s Evidential Bilattice Logic analyzes natural-language entailment,
implicature, and presupposition by climbing a progression of evidential
bilattices `S ⊙ S` (`Bilattice.Evidential`): `classical ⊂` Kleene-3 `⊂ FOUR ⊂
PRESUP`. A value is a pair `(for, against)` of degrees of evidence drawn from a
chain `S`.

This file is the second consumer of the `Bilattice` substrate (the first is
`Studies.Fitting1994`, which shows Kleene-3 = the consistent fragment of `FOUR`).
It adds the top of Schöter's progression:

* **`PRESUP := Evidential (Fin 3)`** — evidence from the 3-chain `0 < ½ < 1`,
  adding *defeasible* (presumed) values `P⁺`/`P⁻` above `FOUR`.
* **`embed : FOUR → PRESUP`** — `FOUR` is a sub-bilattice of `PRESUP`
  (order-preserving in both `≤` and `≤ₖ`): Schöter's "`FOUR` is a sublattice
  of all bilattices."
* the presupposition gap `U` and a defeasible presumption `P⁺` are both
  *consistent* (non-glut); only the overdefined `I` is excluded — so the
  gap-based presupposition logic survives and gains a defeasible layer.

Scope: the value space and the progression. Schöter's inference apparatus
(assertion/evaluation/inference, evidential links, the implemented engine,
`FOEBL`/`FOMEBL`) is out of scope.
-/

open Bilattice

namespace Schoter1996

-- UNVERIFIED: whether "PRESUP" is Schöter's own label for the 9-valued
-- bilattice or a formalization-local name for it.
/-- Schöter's `PRESUP`: the evidential bilattice over the 3-chain `Fin 3 ~
{0, ½, 1}` — `FOUR` with defeasible/presumed values added. -/
abbrev PRESUP := Evidential (Fin 3)

namespace PRESUP

/-- `⊥`: no information (a presupposition gap). -/
def U : PRESUP := .mk 0 0
/-- Definite truth (full evidence for, none against). -/
def T : PRESUP := .mk 2 0
/-- Definite falsity. -/
def F : PRESUP := .mk 0 2
/-- Inconsistent / overdefined (a glut). -/
def I : PRESUP := .mk 2 2
/-- Presumably true: defeasible (`½`) evidence for, none against. -/
def Pplus : PRESUP := .mk 1 0
/-- Presumably false. -/
def Pminus : PRESUP := .mk 0 1

/-- Conflation on `PRESUP`, complementing on the chain by `Fin.rev`. -/
@[reducible] def conf (x : PRESUP) : PRESUP := Evidential.conf Fin.rev x
/-- The consistent (non-glut) fragment of `PRESUP`. -/
@[reducible] def Consistent (x : PRESUP) : Prop := Evidential.Consistent Fin.rev x

end PRESUP

/-- `Bool ↪ Fin 3`: `false ↦ 0` (no evidence), `true ↦ 2` (full evidence). -/
def boolToFin3 : Bool → Fin 3 := fun b => if b then 2 else 0

/-- The embedding of `FOUR` into `PRESUP` (definite values only). -/
def embed (x : FOUR) : PRESUP := .mk (boolToFin3 x.pro) (boolToFin3 x.con)

/-- **`FOUR ⊂ PRESUP`, truth order**: the embedding preserves and reflects `≤`. -/
theorem embed_le (x y : FOUR) : x ≤ y ↔ embed x ≤ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

/-- **`FOUR ⊂ PRESUP`, knowledge order**: the embedding preserves and reflects
`≤ₖ`. -/
theorem embed_kLE (x y : FOUR) : x ≤ₖ y ↔ embed x ≤ₖ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

/-- A presupposition gap (`U`) and a defeasible presumption (`P⁺`) are both
*consistent*; only the overdefined glut `I` is excluded. So `PRESUP` keeps the
gap-based presupposition logic and layers defeasible values on top. -/
theorem gap_and_presumption_consistent :
    PRESUP.Consistent PRESUP.U ∧ PRESUP.Consistent PRESUP.Pplus
      ∧ ¬ PRESUP.Consistent PRESUP.I := by
  decide

end Schoter1996
