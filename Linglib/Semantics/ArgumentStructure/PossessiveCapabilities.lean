import Linglib.Semantics.ArgumentStructure.Relational

/-!
# Possessive capabilities — composable mixins for possessive carriers

Cross-cutting capability mixins for the long-run library where 20-30+
possessive carriers (lexical determiners; clitics; possessive pronouns;
possessor agreement affixes; possessive classifiers; construct-state nouns;
genitive case markers; possessive adjectives; whose-wh; possessor reflexives;
external-possessor applicatives; predicative-possession heads; Wood's i*; …)
each implement a subset of the axes.

Following the mathlib `Add`/`Mul`/`Inv`/`Neg` idiom: many small composable
classes, each one operation; carriers opt in to whichever axes they bear;
consumers depend on exactly those they touch.

## Main declarations

* `HasPossessor` — accessor for a bundled carrier's possessor entity.
* `HasPossesseePredicate` — accessor for a bundled carrier's possessee
  predicate (`Pred1 E S`).
* `HasPossessionRelation` — accessor for a bundled carrier's possession
  relation (`Pred2 E S`). Distinct from `HasPossesseePredicate`: classifier
  systems carry R lexically without a separate restrictor.
* `HasIotaWitness` — Prop class: the carrier's possessee predicate has a
  Russellian unique witness at every situation. Definite possessives bear
  this; existential and quantificational ones do not.

## Carrier coverage (seed instances)

| Carrier | `HasPossessor` | `HasPossesseePredicate` | `HasPossessionRelation` | `HasIotaWitness` |
|---|---|---|---|---|
| `PossessiveSemantics E S` | ✓ | ✓ | ✓ | — |
| `DefinitePossessive E S`  | ✓ | ✓ | — | ✓ |
| `Possessive` (lexical, `Syntax/Determiner/Basic.lean`) | — | — | — | — |

Lexical determiners hold no model-level data — possessor/R/predicate are
supplied at denotation time — so they bear no bundled-carrier capability.
Future carriers (construct-state phrase, Wood's i* head, possessor reflexive,
classifier, …) plug in by picking their axes.
-/

open Semantics.ArgumentStructure.Relational

/-! ### Bundled accessors -/

/-- A carrier whose values bundle a possessor entity. Lexical determiners
(`Possessive`, where the possessor is supplied externally) do not implement
this; bundled denotational carriers (`PossessiveSemantics`, `DefinitePossessive`,
future possessive DPs) do. -/
class HasPossessor (α : Type*) (E : outParam Type*) where
  /-- Project the bundled possessor entity. -/
  possessor : α → E

/-- A carrier whose values bundle a possessee predicate `Pred1 E S` — the set
of possible possessees as a situation-relative property. -/
class HasPossesseePredicate (α : Type*) (E S : outParam Type*) where
  /-- Project the bundled possessee predicate. -/
  possesseePredicate : α → Pred1 E S

/-- A carrier whose values bundle a possession relation `Pred2 E S`. Distinct
from `HasPossesseePredicate`: a relational noun's R is the noun denotation
itself, while a sortal-with-π construction carries R separately from the
sortal predicate. Carriers without an explicitly stored R (definite possessives
that absorb R into the unique witness; classifier systems where R is the
classifier) do not implement this. -/
class HasPossessionRelation (α : Type*) (E S : outParam Type*) where
  /-- Project the bundled possession relation. -/
  possessionRelation : α → Pred2 E S

/-! ### Russellian uniqueness -/

/-- Prop class: a possessive carrier whose possessee predicate has a unique
witness at every situation. Definite possessives ("the boy's cat", "my
mother") bear this by construction; existential ("a friend of mine") and
quantificational ("every student's") do not. Future carriers bearing
Russellian uniqueness (definite DPs, familiarity-anaphoric possessives,
ι-shifted possessor reflexives) implement this. -/
class HasIotaWitness (α : Type*) (E S : outParam Type*)
    [HasPossesseePredicate α E S] : Prop where
  /-- The possessee predicate has a unique witness at every situation. -/
  iotaWitness : ∀ (a : α) (s : S),
    iotaPresupposition (HasPossesseePredicate.possesseePredicate a) s

/-! ### Seed instances -/

namespace Semantics.ArgumentStructure.Relational

variable {E S : Type*}

instance : HasPossessor (PossessiveSemantics E S) E :=
  ⟨PossessiveSemantics.possessor⟩

instance : HasPossesseePredicate (PossessiveSemantics E S) E S :=
  ⟨PossessiveSemantics.possesseePred⟩

instance : HasPossessionRelation (PossessiveSemantics E S) E S :=
  ⟨PossessiveSemantics.relation⟩

instance : HasPossessor (DefinitePossessive E S) E :=
  ⟨DefinitePossessive.possessor⟩

instance : HasPossesseePredicate (DefinitePossessive E S) E S :=
  ⟨DefinitePossessive.predicate⟩

/-- `DefinitePossessive` carries its iota-presupposition as a structure field;
the typeclass instance just exposes it. -/
instance : HasIotaWitness (DefinitePossessive E S) E S :=
  ⟨fun a => a.presupposition⟩

end Semantics.ArgumentStructure.Relational

/-! ### Consuming the capabilities

Capability-polymorphic results: stated once over the mixin classes, inherited by
every instance. This is the payoff of the `Add`/`Mul`-style design — a consumer
depends on exactly the axes it touches, and new carriers get the results for
free, with no carrier-specific reproof. -/

variable {α E S : Type*}

/-- The possessee set determined by any carrier bundling a possessor and a
possession relation: the entities standing in the relation to the possessor. -/
def possesseeSet [HasPossessor α E] [HasPossessionRelation α E S] (a : α) :
    Pred1 E S :=
  fun y s => HasPossessionRelation.possessionRelation a (HasPossessor.possessor a) y s

/-- Any carrier bearing a Russellian iota-witness denotes a unique possessee at
every situation. Definite possessives inherit `∃!`-reference with no
carrier-specific reproof. -/
theorem existsUnique_possessee [HasPossesseePredicate α E S] [HasIotaWitness α E S]
    (a : α) (s : S) :
    ∃! y : E, HasPossesseePredicate.possesseePredicate a y s :=
  HasIotaWitness.iotaWitness a s
