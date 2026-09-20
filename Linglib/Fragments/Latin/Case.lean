import Mathlib.Data.Fintype.Basic
import Linglib.Syntax.Case.Basic

/-!
# Latin case

The traditional description of Latin has six cases: nominative, vocative, accusative, genitive,
dative and ablative. The vocative is a form of address standing outside the clause, and it is
distinct from the nominative only in the singular of non-neuter second-declension nouns
(`Latin.Declension`).

The ablative continues three cases that were once distinct, an ablative, a locative and an
instrumental, and it expresses source, location and instrument accordingly. A separate locative
survives for names of towns and a few nouns such as *domī* 'at home'. The goal of motion is
expressed by the accusative, there being no allative. Blake takes Latin as his running example
of an inflectional case system.

## References

* [blake-1994]
-/

namespace Latin.Case

/-- The six cases of the traditional description, in the order of the school paradigms. -/
inductive Value where
  | nom
  | voc
  | acc
  | gen
  | dat
  | abl
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each case. -/
def Value.toLabel : Value → Case
  | .nom => .nom
  | .voc => .voc
  | .acc => .acc
  | .gen => .gen
  | .dat => .dat
  | .abl => .abl

/-- The comparative case functions a case expresses. The ablative expresses location and
instrument beside source, and the accusative the goal of motion beside the direct object. -/
def Value.functions : Value → Finset Case
  | .abl => {.abl, .loc, .inst}
  | .acc => {.acc, .all}
  | v => {v.toLabel}

/-- The Latin cases under their comparative labels. -/
def inventory : Finset Case := Finset.univ.image Value.toLabel

/-- Every case function some Latin case expresses. -/
def functions : Finset Case := Finset.univ.biUnion Value.functions

theorem toLabel_injective : Function.Injective Value.toLabel := by decide

/-- Every case expresses the function it is labelled for. -/
theorem toLabel_mem_functions (v : Value) : v.toLabel ∈ v.functions := by
  cases v <;> decide

theorem inventory_subset_functions : inventory ⊆ functions := by decide

end Latin.Case
