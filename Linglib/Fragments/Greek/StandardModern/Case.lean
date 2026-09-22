module

public import Linglib.Syntax.Case.Basic

/-!
# Modern Greek case

Standard Modern Greek has four cases: nominative, accusative, genitive and vocative. The dative
of Ancient Greek (`Greek.Ancient.Case`) is gone, and the indirect object of a ditransitive is a
genitive, beside a prepositional phrase in *se* with the accusative
([michelioudakis-sitaridou-2010]). Blake gives the system, vocative aside, as a three-case
nominative–accusative–genitive system ([blake-1994]).

## References

* [blake-1994]
* [michelioudakis-sitaridou-2010]
-/

@[expose] public section

namespace Greek.StandardModern.Case

/-- The nominative. -/
def nom : Case.Labelled := .single .nom

/-- The accusative. -/
def acc : Case.Labelled := .single .acc

/-- The genitive, which expresses the indirect object as well as the possessor. -/
def gen : Case.Labelled := ⟨.gen, {.gen, .dat}, by decide⟩

/-- The vocative. -/
def voc : Case.Labelled := .single .voc

/-- The four cases. -/
def cases : Finset Case.Labelled := {nom, acc, gen, voc}

/-- The cases under their labels. -/
def inventory : Finset Case := cases.image (·.label)

/-- Every function some case expresses. -/
def functions : Finset Case := cases.biUnion (·.functions)

theorem inventory_subset_functions : inventory ⊆ functions :=
  Case.Labelled.image_label_subset_biUnion_functions cases

/-- The dative function outlives the dative case. -/
theorem functions_eq_insert_dat : functions = insert .dat inventory := by decide

end Greek.StandardModern.Case
