module

public import Linglib.Syntax.Case.Basic

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

@[expose] public section

namespace Latin.Case

/-- The nominative. -/
def nom : Case.Labelled := .single .nom

/-- The vocative. -/
def voc : Case.Labelled := .single .voc

/-- The accusative, which expresses the goal of motion as well as the direct object. -/
def acc : Case.Labelled := ⟨.acc, {.acc, .all}, by decide⟩

/-- The genitive. -/
def gen : Case.Labelled := .single .gen

/-- The dative. -/
def dat : Case.Labelled := .single .dat

/-- The ablative, which expresses location and instrument as well as source. -/
def abl : Case.Labelled := ⟨.abl, {.abl, .loc, .inst}, by decide⟩

/-- The six cases, in the order of the school paradigms. -/
def cases : Finset Case.Labelled := {nom, voc, acc, gen, dat, abl}

/-- The cases under their labels. -/
def inventory : Finset Case := cases.image (·.label)

/-- Every function some case expresses. -/
def functions : Finset Case := cases.biUnion (·.functions)

theorem inventory_subset_functions : inventory ⊆ functions :=
  Case.Labelled.image_label_subset_biUnion_functions cases

end Latin.Case
