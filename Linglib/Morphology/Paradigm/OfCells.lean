import Linglib.Morphology.Paradigm.Basic
import Linglib.Syntax.Agreement.Paradigm

/-!
# Agreement tables as ordered-cell paradigms
[corbett-1998] [bobaljik-2012]

The descriptive agreement table (`Agreement.Paradigm`, keyed by
person/number/gender cells) and the theoretical ordered-cell object
(`Morphology.Paradigm n F`, indexed by `Fin n`) are the same data under a
choice of cell ordering. `toParadigm` transports the former onto the
latter, reading off each ordered cell's exponent.

## Main declarations

* `Agreement.Paradigm.toParadigm` — transport a cell-keyed table onto the
  `n`-cell ordered paradigm along an indexing `Fin n → Agreement.Cell`
-/

namespace Agreement.Paradigm

variable {Exp : Type*} [DecidableEq Exp] {n : ℕ}

/-- Transport a descriptive agreement table onto the ordered-cell
`Morphology.Paradigm`: given an indexing `e` of the `n` ordered cells by
agreement-feature cells, read off each cell's exponent (`none` where the
table is defective for that cell). -/
def toParadigm (e : Fin n → Agreement.Cell) (p : Agreement.Paradigm Exp) :
    Morphology.Paradigm n (Option Exp) :=
  fun i => p.realize (e i)

@[simp] theorem toParadigm_apply (e : Fin n → Agreement.Cell)
    (p : Agreement.Paradigm Exp) (i : Fin n) :
    p.toParadigm e i = p.realize (e i) :=
  rfl

end Agreement.Paradigm
