module

public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Semantics.Reference.Prominence
public import Linglib.Morphology.Word.Agree

/-!
# Agreement paradigms

This file defines the descriptive agreement paradigm, the table from feature bundles to the
exponents that realize them, and the person–number bundles such a table ranges over.

A paradigm records which forms realize which cells, as a reference grammar lists them, and
commits to no account of how the table arises: syncretism is a non-injective table and
defectiveness a partial one. The cells are the bundles of `Syntax/Agreement/Bundle.lean`,
the feature space a pronoun or a word token already carries, so a controller's `Word.phi`
indexes a paradigm directly ([corbett-1998]).

## Main definitions

* `Agreement.Bundle.pnCells` — the six person–number bundles
* `Agreement.Bundle.IsSAP`, `Agreement.Bundle.IsPlural`, `Agreement.Bundle.person` — the
  speech-act-participant and plural cells, and the person a cell bears
* `Agreement.Paradigm` — a table from bundles to exponents, with `Paradigm.realize` and
  `Paradigm.realizeFor`

## References

* [corbett-1998] — agreement paradigms and the shared feature space of pronouns and targets
* [scott-2023] — Set A and Set B person–number inflection as descriptive tables
-/

@[expose] public section

open Morphology (Word)

namespace Agreement

namespace Bundle

/-- A cell is a speech-act participant's when its person is first or second. -/
def IsSAP (b : Bundle) : Prop := b .person = ↑Person.first ∨ b .person = ↑Person.second

instance (b : Bundle) : Decidable b.IsSAP := inferInstanceAs (Decidable (_ ∨ _))

/-- A cell is plural when its number is. -/
def IsPlural (b : Bundle) : Prop := b .number = ↑Number.plural

instance (b : Bundle) : Decidable b.IsPlural := inferInstanceAs (Decidable (_ = _))

/-- The person a cell bears, third where it bears none. -/
def person (b : Bundle) : Person :=
  match b .person with
  | (p : Person) => p
  | ⊥ => .third

@[simp] theorem person_pn (p : Person) (n : Number) : (pn p n).person = p := rfl

/-- The six person–number cells a person–number paradigm ranges over. -/
def pnCells : List Bundle :=
  [.pn .first .singular, .pn .second .singular, .pn .third .singular,
    .pn .first .plural, .pn .second .plural, .pn .third .plural]

end Bundle

/-- An agreement paradigm, the descriptive table of cells and their exponents. -/
abbrev Paradigm (Exp : Type*) := List (Bundle × Exp)

namespace Paradigm

variable {Exp : Type*}

/-- The exponent realizing a cell, the first entry whose cell it is. -/
def realize (p : Paradigm Exp) (c : Bundle) : Option Exp :=
  (p.find? fun e ↦ decide (e.1 = c)).map (·.2)

/-- The exponent agreeing with a controller word. -/
def realizeFor (p : Paradigm Exp) (controller : Word) : Option Exp :=
  p.realize controller.phi

/-- The cells the paradigm distinguishes, in declaration order. -/
def cells (p : Paradigm Exp) : List Bundle := p.map (·.1)

end Paradigm

end Agreement
