module

public import Linglib.Syntax.Case.Basic

/-!
# Ancient Greek case

Ancient Greek has five cases: nominative, vocative, accusative, genitive and dative. Its dative
does not correspond closely to the Latin dative. Greek has no ablative, and of the functions of
the Latin ablative the genitive expresses source, while the dative expresses location and
instrument beside the indirect object, so that the Greek dative is the more comprehensive case.
Blake gives the system, vocative aside, as the four-case stage of his hierarchy.

## References

* [blake-1994]
-/

@[expose] public section

namespace Greek.Ancient.Case

/-- The nominative. -/
def nom : Case.Labelled := .single .nom

/-- The vocative. -/
def voc : Case.Labelled := .single .voc

/-- The accusative. -/
def acc : Case.Labelled := .single .acc

/-- The genitive, which expresses source as well as the possessor. -/
def gen : Case.Labelled := ⟨.gen, {.gen, .abl}, by decide⟩

/-- The dative, which expresses location and instrument as well as the indirect object. -/
def dat : Case.Labelled := ⟨.dat, {.dat, .loc, .inst}, by decide⟩

/-- The five cases. -/
def cases : Finset Case.Labelled := {nom, voc, acc, gen, dat}

/-- The cases under their labels. -/
def inventory : Finset Case := cases.image (·.label)

/-- Every function some case expresses. -/
def functions : Finset Case := cases.biUnion (·.functions)

theorem inventory_subset_functions : inventory ⊆ functions :=
  Case.Labelled.image_label_subset_biUnion_functions cases

end Greek.Ancient.Case
