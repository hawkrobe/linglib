import Linglib.Semantics.Possession.Relationalizer
import Linglib.Semantics.Possession.Defs
import Linglib.Semantics.Quantification.Defs

/-!
# Possessive descriptions

A possessive description ([barker-1995]) is a possessor, a possession relation, and a sortal
restrictor; its possessee predicate `π restrictor relation possessor` is derived, never stored, so
a description cannot pair a predicate with an unrelated relation. The determiner that denotes
through descriptions is `Possessive.denote` (`Semantics/Definiteness/DeterminerDenotation.lean`);
the quantification over the possessed objects (`Poss`, `PossW`, `Description.toGQ`) is
`Semantics/Possession/Quantifier.lean`. Whether a possessive is definite is not settled here: the
determinate reading is one mode of quantification among those the quantifier layer parameterises
([peters-westerstahl-2006] §7.8.2, [coppock-beaver-2015] §4).

## Main declarations

* `Possession.Description`, `Description.possesseePred`.
* `Possession.asNPQ` — [barker-2011]'s possessive as a type ⟨1⟩ quantifier.

## References

* [barker-1995], [barker-2011]
* [peters-westerstahl-2006], [coppock-beaver-2015]
-/

namespace Possession

variable {E S : Type*}

/-- A possessive description ([barker-1995]): a possessor, a possession relation, and a sortal
restrictor (the noun predicate; `⊤` for a purely relational noun). -/
structure Description (E S : Type*) where
  /-- The possessor entity. -/
  possessor : E
  /-- The possession relation. -/
  relation : E → E → S → Prop
  /-- The sortal restrictor (the noun predicate). -/
  restrictor : E → S → Prop

/-- The derived possessee predicate: the restrictor conjoined with the relation applied to the
possessor. -/
def Description.possesseePred (d : Description E S) : E → S → Prop :=
  π d.restrictor d.relation d.possessor

/-- Possessive as a type ⟨1⟩ quantifier ([barker-2011]): `⟦John's⟧ = fun P ↦ ∃ y, R possessor y ∧
P y`. Not isomorphism-invariant: it depends on the identity of the possessor, not just on
cardinalities. -/
def asNPQ (possessor : E) (R : E → E → Prop) : Quantification.Quantifier E :=
  fun P => ∃ y, R possessor y ∧ P y

end Possession
