module

public import Linglib.Syntax.Category.Coordinator

/-!
# Tanti Dargwa coordinators

Clause coordination is not typical of Tanti Dargwa, which combines clauses mainly by
subordination with non-finite verb forms, as Sumbatova describes. Noun phrases are conjoined
with the additive enclitic *=ra* 'also, too' after each coordinand. Disjunction repeats the free
word *ja* before each alternative, which with negation gives 'neither … nor', and the enclitic
*=nu* marks contrast or cause.

## Main definitions

* `Dargwa.Coordination.ra`, `Dargwa.Coordination.ja`, `Dargwa.Coordination.nu`: the additive
  enclitic that conjoins, the disjunctive coordinator and the contrastive enclitic.

## References

* [sumbatova-2021]
-/

@[expose] public section

namespace Dargwa.Coordination

/-- *=ra* 'and', enclitic on each coordinand, also the additive 'also, too'. -/
def ra : Coordinator :=
  { form := "=ra", gloss := "and; also, too", role := .conjunctive, kind := .bound .after .clitic,
    alsoAdditive := true }

/-- *ja* 'or', repeated before each alternative. -/
def ja : Coordinator :=
  { form := "ja", gloss := "or", role := .disjunctive, kind := .free }

/-- *=nu* 'but; because', enclitic. -/
def nu : Coordinator :=
  { form := "=nu", gloss := "but; because", role := .adversative, kind := .bound .after .clitic }

/-- The coordinators. -/
def allEntries : List Coordinator := [ra, ja, nu]

end Dargwa.Coordination
