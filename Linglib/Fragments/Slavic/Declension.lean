module

public import Linglib.Fragments.Slavic.Case
public import Mathlib.Data.Fintype.Sets
public import Linglib.Syntax.Number.Basic

/-!
# Slavic declension

This file defines a declined word of a Slavic language in one number by its forms in the six
cases the Slavic languages share: nominative, accusative, genitive, locative (the prepositional
case), dative and instrumental. The vocative, which some of the languages keep, is left out. The
entries of each language are in its own `Declension` file.

## Main definitions

* `Slavic.Declension.Cell`: the six cases
* `Slavic.Declension.Paradigm`: a word in one number, by its form in each cell
-/

@[expose] public section

namespace Slavic.Declension

/-- A cell of a paradigm is one of the six cases. -/
abbrev Cell : Type := Slavic.Case.coreInventory

/-- `cell c` is the cell of the case `c`. -/
abbrev cell (c : Case) (h : c ∈ Slavic.Case.coreInventory := by decide) : Cell := ⟨c, h⟩

/-- `forms nom acc gen loc dat inst` assigns each cell its form; the one cell not named is the
instrumental. -/
def forms (nom acc gen loc dat inst : String) (c : Cell) : String :=
  match c.1 with
  | .nom => nom
  | .acc => acc
  | .gen => gen
  | .loc => loc
  | .dat => dat
  | _ => inst

/-- A declined word in one number, by its form in each cell. -/
structure Paradigm where
  /-- The word's gloss. -/
  gloss : String
  /-- The number of the forms. -/
  number : Number
  /-- The form of each cell. -/
  form : Cell → String

instance : DecidableEq Paradigm := fun a b ↦
  decidable_of_iff (a.gloss = b.gloss ∧ a.number = b.number ∧ a.form = b.form) <| by
    cases a; cases b; simp

end Slavic.Declension
