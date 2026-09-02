import Linglib.Semantics.Possession.Relationalizer
import Linglib.Semantics.Possession.Defs
import Linglib.Semantics.Quantification.Defs

/-!
# Possessive descriptions and capabilities

The `Possession` namespace for the semantics of possessive constructions,
built on the relationalizer substrate of `Semantics/Possession/Relationalizer.lean`
(`π`, `Ex`, `ExPossessor`) and the classification vocabulary of
`Semantics/Possession/Defs.lean` (`RelationType`, `Notion`). The
quantificational layer (`Poss`, `PossW`, narrowing, `descriptionGQ`) is in
`Possessive/GQ.lean`; the determiner that denotes through these descriptions is
`Possessive.denote` (`Semantics/Definiteness/DeterminerDenotation.lean`).

A possessor combines with a noun in one of two ways: a relational noun `R` takes
it as its argument, `R x` (the argument genitive), and a sortal noun `P` is first
relationalized by a free relation, `π P R x` (the modifier genitive).

## Main declarations

* `Possession.Description` — a possessor + relation + sortal restrictor; the
  possessee predicate is *derived* (`π`), never stored, so a description cannot
  be incoherent.
* `Possession.Definite` — a possessive carrying a Russellian uniqueness
  presupposition.
* `HasPossessor`, `HasPossesseePredicate`, `HasPossessionRelation`,
  `HasIotaWitness` — composable capability mixins (root namespace, `Add`/`Mul`
  idiom); description types opt into whichever axes they bear.
* `possesseeSet`, `existsUnique_possessee` — capability-polymorphic consumers.
-/

namespace Possession
variable {E S : Type*}

/-! ### Possessive descriptions -/

/-- A possessive description ([barker-1995]): a possessor, a possession
relation, and a sortal restrictor (the noun predicate; `⊤` for a purely
relational noun). The possessee predicate is *derived* (`π`), not stored — so a
description cannot bundle a predicate unrelated to its relation. -/
structure Description (E S : Type*) where
  /-- The possessor entity. -/
  possessor : E
  /-- The possession relation. -/
  relation : E → E → S → Prop
  /-- The sortal restrictor (the noun predicate). -/
  restrictor : E → S → Prop

namespace Description

/-- The derived possessee predicate: the restrictor conjoined with the relation
applied to the possessor. -/
def possesseePred (d : Description E S) : E → S → Prop :=
  π d.restrictor d.relation d.possessor

end Description

/-- A definite possessive carrying its Russellian uniqueness presupposition
("the boy's cat", "my mother"). -/
structure Definite (E S : Type*) where
  /-- The possessor entity. -/
  possessor : E
  /-- The possessee predicate (a definite description's restrictor). -/
  predicate : E → S → Prop
  /-- The possessee predicate has a unique witness at every situation. -/
  presupposition : ∀ s : S, ∃! x, predicate x s

/-! ### Bridge to type ⟨1⟩ quantifiers -/

/-- Possessive as a type ⟨1⟩ quantifier (Quantifier):
`⟦John's⟧ = fun R P ↦ ∃ y, R possessor y ∧ P y`. Not isomorphism-invariant: it
depends on the identity of the possessor, not just cardinalities. -/
def asNPQ {E : Type*} (possessor : E) (R : E → E → Prop) :
    Quantification.Quantifier E :=
  fun P => ∃ y : E, R possessor y ∧ P y

end Possession
/-! ### Composable description capabilities

Cross-cutting capability mixins for the long-run library where 20-30+ possessive
description types each implement a subset of the axes. Following the mathlib
`Add`/`Mul`/`Inv`/`Neg` idiom: many small composable classes, each one
operation; description types opt in to whichever axes they bear.

| Type | `HasPossessor` | `HasPossesseePredicate` | `HasPossessionRelation` | `HasIotaWitness` |
|---|---|---|---|---|
| `Possession.Description E S` | ✓ | ✓ | ✓ | — |
| `Possession.Definite E S`    | ✓ | ✓ | — | ✓ | -/

/-- A type whose values bundle a possessor entity. -/
class HasPossessor (α : Type*) (E : outParam Type*) where
  /-- Project the bundled possessor entity. -/
  possessor : α → E

/-- A type whose values bundle a possessee predicate `E → S → Prop`. -/
class HasPossesseePredicate (α : Type*) (E S : outParam Type*) where
  /-- Project the bundled possessee predicate. -/
  possesseePredicate : α → E → S → Prop

/-- A type whose values bundle a possession relation `E → E → S → Prop`. Distinct
from `HasPossesseePredicate`: a relational noun's R is the noun denotation
itself, while a sortal-with-π construction carries R separately. -/
class HasPossessionRelation (α : Type*) (E S : outParam Type*) where
  /-- Project the bundled possession relation. -/
  possessionRelation : α → E → E → S → Prop

/-- Prop class: a possessive description whose possessee predicate has a unique
witness at every situation. Definite possessives bear this; existential and
quantificational ones do not. -/
class HasIotaWitness (α : Type*) (E S : outParam Type*)
    [HasPossesseePredicate α E S] : Prop where
  /-- The possessee predicate has a unique witness at every situation. -/
  iotaWitness : ∀ (a : α) (s : S), ∃! x, HasPossesseePredicate.possesseePredicate a x s

namespace Possession
variable {E S : Type*}

instance : HasPossessor (Description E S) E := ⟨Description.possessor⟩
instance : HasPossesseePredicate (Description E S) E S := ⟨Description.possesseePred⟩
instance : HasPossessionRelation (Description E S) E S := ⟨Description.relation⟩

instance : HasPossessor (Definite E S) E := ⟨Definite.possessor⟩
instance : HasPossesseePredicate (Definite E S) E S := ⟨Definite.predicate⟩

/-- `Definite` carries its iota-presupposition as a structure field; the
typeclass instance just exposes it. -/
instance : HasIotaWitness (Definite E S) E S := ⟨fun a => a.presupposition⟩

end Possession
/-! ### Consuming the capabilities -/

variable {α E S : Type*}

/-- The possessee set determined by any description bundling a possessor and a
possession relation: the entities standing in the relation to the possessor. -/
def possesseeSet [HasPossessor α E] [HasPossessionRelation α E S] (a : α) :
    E → S → Prop :=
  fun y s => HasPossessionRelation.possessionRelation a (HasPossessor.possessor a) y s

/-- Any description bearing a Russellian iota-witness denotes a unique possessee
at every situation. Definite possessives inherit `∃!`-reference with no
type-specific reproof. -/
theorem existsUnique_possessee [HasPossesseePredicate α E S] [HasIotaWitness α E S]
    (a : α) (s : S) :
    ∃! y : E, HasPossesseePredicate.possesseePredicate a y s :=
  HasIotaWitness.iotaWitness a s
