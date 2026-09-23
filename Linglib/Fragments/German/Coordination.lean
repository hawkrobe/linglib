module

public import Linglib.Syntax.Category.Coordinator

/-!
# German coordinators

German coordinates with free words that stand before the second coordinand: *und* 'and', *oder*
'or', and two adversative coordinators, *aber* 'but' and the corrective *sondern* 'but rather',
which requires a negated first coordinand. The emphatic conjunction is *sowohl … als auch*,
neither member of which is the plain coordinator, and the emphatic disjunction *entweder …
oder*.

## Main definitions

* `German.Coordination.und`, `German.Coordination.oder`: the conjunctive and the disjunctive
  coordinator.
* `German.Coordination.aber`, `German.Coordination.sondern`: the adversative coordinators.
* `German.Coordination.sowohlAlsAuch`, `German.Coordination.entwederOder`: the emphatic
  constructions.

## References

* [haspelmath-2007]
-/

@[expose] public section

namespace German.Coordination

/-- *und* 'and'. -/
def und : Coordinator :=
  { form := "und", gloss := "and", role := .conjunctive, kind := .free }

/-- *oder* 'or'. -/
def oder : Coordinator :=
  { form := "oder", gloss := "or", role := .disjunctive, kind := .free }

/-- *aber* 'but'. -/
def aber : Coordinator :=
  { form := "aber", gloss := "but", role := .adversative, kind := .free }

/-- *sondern* 'but rather', after a negated first coordinand. -/
def sondern : Coordinator :=
  { form := "sondern", gloss := "but rather", role := .adversative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [und, oder, aber, sondern]

/-- *sowohl … als auch* 'both … and'. -/
def sowohlAlsAuch : Coordinator.Correlative := ⟨"sowohl", "als auch", und⟩

/-- *entweder … oder* 'either … or'. -/
def entwederOder : Coordinator.Correlative := ⟨"entweder", oder.form, oder⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [sowohlAlsAuch, entwederOder]

end German.Coordination
