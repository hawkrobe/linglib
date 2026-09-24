module

public import Linglib.Syntax.Case.Basic

/-!
# German case

This file defines the German case inventory and the cells of a German case paradigm. German has
four cases, the nominative, the accusative, the genitive and the dative. The noun itself shows
little of them: a regular noun adds *-(e)s* in the genitive singular of the masculine and the
neuter and *-n* in the dative plural, and nothing else. Case is marked chiefly on the determiners
and the adjectives of the noun phrase, together with its gender and number, as Durrell describes
(`German.Determiners`, `German.Adjectives`). Blake gives the system as the four-case stage of his
hierarchy.

## Main definitions

* `German.Case.inventory`: the four cases.
* `German.Case.Cell`, `German.Case.forms`: a case of the inventory, and the forms of the four in
  the order of the school paradigms.

## References

* [durrell-2011]
* [blake-1994]
-/

@[expose] public section

namespace German.Case

/-- The inventory is the four cases. -/
def inventory : Finset Case := {.nom, .acc, .gen, .dat}

/-- A cell of a paradigm is one of the four cases. -/
abbrev Cell : Type := inventory

/-- `cell c` is the cell of the case `c`. -/
abbrev cell (c : Case) (h : c ∈ inventory := by decide) : Cell := ⟨c, h⟩

/-- `forms nom acc gen dat` assigns each cell its form; the one cell not named is the dative. -/
def forms {α : Type*} (nom acc gen dat : α) (c : Cell) : α :=
  match c.1 with
  | .nom => nom
  | .acc => acc
  | .gen => gen
  | _ => dat

end German.Case
