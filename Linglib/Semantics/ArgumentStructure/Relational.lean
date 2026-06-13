import Mathlib.Data.Fintype.Basic
import Linglib.Core.Logic.Quantification

/-!
# Possessives and relational nouns

Type-shifting operators for the analysis of possessive constructions and
relational nouns, following [barker-2011].

The relationalizer `π` takes a sortal predicate `P` and a relation `R` and
returns the relational predicate `fun x y ↦ P y ∧ R x y`. Its quasi-adjoint
`Ex` collapses a relation back to a property by existentially closing the
second argument.

The structural condition *having a relatum slot* controls three surface
phenomena — possessor licensing, antecedent bridging, and demonstrative
anaphora. They are tracked as separate predicates (`hasRelatumSlot`,
`canTakePossessor`, `canBridge`) over `NominalInterpType` because they
describe distinct linguistic facts, even though they coincide by construction.

## Main definitions

* `π P R`: Barker's relationalizer.
* `Ex R`: existential closure of a relation.
* `possessiveRelational possessor R`: applying a possessor to a relational noun.
* `possessiveSortal possessor P R`: applying a possessor to a sortal noun via `π`.
* `iotaPresupposition P`: Russellian uniqueness presupposition for definites.
* `NominalInterpType`: relational arity of a nominal denotation.
* `PossessionRelationType`: four-way Vikner-Jensen possession taxonomy.
* `HasPossessor`, `HasPossesseePredicate`, `HasPossessionRelation`,
  `HasIotaWitness`: composable capability mixins for possessive carriers.
* `possesseeSet`, `existsUnique_possessee`: capability-polymorphic consumers.

## Main statements

* `ex_pi_retraction`: `Ex` recovers a witness of `π P R` from witnesses of
  `P` and `R`.

## References

* [barker-2011]: Possessives and relational nouns
  (§6 of Portner/Heusinger/Maienborn handbook; π and Ex on pp. 184–189,
  Vikner-Jensen taxonomy reproduced in Fig 6.1 p. 185).
* [vikner-jensen-2002]: Semantic analysis of the English possessive.

## Tags

possessive, relational noun, type shifting, bridging, definite description
-/

namespace Semantics.ArgumentStructure.Relational

/-! ### Predicates and arity -/

/-- One-place predicate over entities and states. -/
abbrev Pred1 (E S : Type*) := E → S → Prop

/-- Two-place predicate over entities and states. -/
abbrev Pred2 (E S : Type*) := E → E → S → Prop

/-- Semantic arity of a nominal expression. -/
inductive SemType where
  /-- Property `Pred1`. -/
  | pred1
  /-- Relation `Pred2`. -/
  | pred2
  /-- Bare individual. -/
  | entity
  deriving DecidableEq, Repr

/-! ### Type shifters -/

section TypeShifters

variable {E S : Type*}

/-- Barker's relationalizer: `π P R x y s ↔ P y s ∧ R x y s`. -/
def π (P : Pred1 E S) (R : Pred2 E S) : Pred2 E S :=
  λ x y s => P y s ∧ R x y s

@[inherit_doc] scoped notation "relationalizer(" P ", " R ")" => π P R

/-- Existential closure of a relation in its second argument:
`Ex R x s ↔ ∃ y, R x y s`. -/
def Ex (R : Pred2 E S) : Pred1 E S :=
  λ x s => ∃ y, R x y s

/-- `Ex (π P R) z s` is witnessed whenever some `y` satisfies both `P y s`
and `R z y s`. -/
theorem ex_pi_retraction [Nonempty E]
    (P : Pred1 E S) (R : Pred2 E S) (y z : E) (s : S)
    (hP : P y s) (hR : R z y s) :
    Ex (π P R) z s :=
  ⟨y, hP, hR⟩

end TypeShifters

/-! ### Possessive constructions -/

section Possessives

variable {E S : Type*}

/-- Possessor, possessee predicate, possession relation, and a flag
recording whether the relation is lexical (vs pragmatically supplied). -/
structure PossessiveSemantics (E S : Type*) where
  possessor : E
  possesseePred : Pred1 E S
  relation : Pred2 E S
  relationIsLexical : Bool

/-- Applying a possessor to a lexically relational noun. -/
def possessiveRelational (possessor : E) (nounRel : Pred2 E S) : Pred1 E S :=
  λ y s => nounRel possessor y s

/-- Applying a possessor to a sortal noun via `π`. -/
def possessiveSortal (possessor : E) (nounPred : Pred1 E S)
    (R : Pred2 E S) : Pred1 E S :=
  λ y s => π nounPred R possessor y s

/-- Russellian uniqueness presupposition: there exists a unique `x` satisfying
`P`. -/
def iotaPresupposition (P : Pred1 E S) (s : S) : Prop :=
  ∃ x : E, P x s ∧ ∀ y : E, P y s → y = x

/-- A definite possessive carrying its uniqueness presupposition. -/
structure DefinitePossessive (E S : Type*) where
  possessor : E
  predicate : Pred1 E S
  presupposition : ∀ s : S, iotaPresupposition predicate s

/-- Demonstrative-headed nominal: `π` applied to a sortal noun with the
demonstrative supplying the relatum. -/
def naSemantics (nounPred : Pred1 E S) (R : Pred2 E S) (relatum : E) :
    Pred1 E S :=
  λ x s => π nounPred R relatum x s

/-- Bare nominal: identity on the predicate (no relatum slot). -/
def bareSemantics (nounPred : Pred1 E S) : Pred1 E S :=
  nounPred

end Possessives

/-! ### Interpretation sources and bridging -/

/-- Source of a noun's relational interpretation. -/
inductive InterpretationSource where
  /-- Noun is lexically relational (e.g. *brother*, *author*). -/
  | lexicalRelation
  /-- `π` was applied (e.g. possessive, demonstrative). -/
  | appliedPi
  /-- No relation available (bare sortal). -/
  | noRelation
  deriving DecidableEq, Repr

/-- Whether an interpretation source provides a relatum slot. -/
def CanFillRelatum : InterpretationSource → Prop
  | .lexicalRelation => True
  | .appliedPi => True
  | .noRelation => False

instance : DecidablePred CanFillRelatum := λ s => by
  cases s <;> unfold CanFillRelatum <;> infer_instance

/-! ### Vikner-Jensen possession taxonomy -/

/-- Four-way lexical taxonomy of possession relations from
[vikner-jensen-2002] §3.1.2, reproduced in Fig 6.1 of
[barker-2011]. The separate "pragmatic" interpretation
([vikner-jensen-2002] §3.1.1) is not lexical and is not one of the
four cases below. -/
inductive PossessionRelationType where
  /-- Inherent relation: lexically argument-structural (the teacher's class). -/
  | inherent
  /-- Part-whole relation (the girl's nose, the car's wheel). -/
  | partWhole
  /-- Agentive relation (the girl's poem = the poem the girl wrote). -/
  | agentive
  /-- Control relation: ownership or legal control (the girl's car). -/
  | control
  deriving DecidableEq, Repr

/-! ### Nominal interpretation type -/

/-- Interpretation type of a nominal: with or without a relatum slot. -/
inductive NominalInterpType where
  /-- `Pred1`: no relatum slot (sortal, no `π`). -/
  | pred1
  /-- `Pred2`: relatum slot (relational or `π`-shifted). -/
  | pred2
  deriving DecidableEq, Repr

namespace NominalInterpType

/-- Whether the interpretation type has a relatum slot. -/
def hasRelatumSlot : NominalInterpType → Prop
  | .pred1 => False
  | .pred2 => True

instance : DecidablePred hasRelatumSlot := λ t => by
  cases t <;> unfold hasRelatumSlot <;> infer_instance

/-- Whether the interpretation type can take a possessor argument. -/
def canTakePossessor : NominalInterpType → Prop
  | .pred1 => False
  | .pred2 => True

instance : DecidablePred canTakePossessor := λ t => by
  cases t <;> unfold canTakePossessor <;> infer_instance

/-- Whether the interpretation type can accommodate bridging. -/
def canBridge : NominalInterpType → Prop
  | .pred1 => False
  | .pred2 => True

instance : DecidablePred canBridge := λ t => by
  cases t <;> unfold canBridge <;> infer_instance

end NominalInterpType

/-! ### Bridge to type ⟨1⟩ quantifiers -/

/-- Possessive as a type ⟨1⟩ quantifier (NPQ):
`⟦John's⟧ = fun R P ↦ ∃ y, R possessor y ∧ P y`.

Possessive GQs are not isomorphism-invariant: they depend on the identity of
the possessor, not just cardinalities. -/
def possessiveAsNPQ {E : Type*} (possessor : E) (R : E → E → Bool) :
    Core.Quantification.NPQ E :=
  λ P => ∃ y : E, R possessor y = true ∧ P y

end Semantics.ArgumentStructure.Relational

/-! ## Composable carrier capabilities

Cross-cutting capability mixins for the long-run library where 20-30+ possessive
carriers (lexical determiners; clitics; possessive pronouns; possessor agreement
affixes; possessive classifiers; construct-state nouns; genitive case markers;
possessive adjectives; whose-wh; possessor reflexives; external-possessor
applicatives; predicative-possession heads; Wood's i*; …) each implement a
subset of the axes. Following the mathlib `Add`/`Mul`/`Inv`/`Neg` idiom: many
small composable classes, each one operation; carriers opt in to whichever axes
they bear; consumers depend on exactly those they touch.

| Carrier | `HasPossessor` | `HasPossesseePredicate` | `HasPossessionRelation` | `HasIotaWitness` |
|---|---|---|---|---|
| `PossessiveSemantics E S` | ✓ | ✓ | ✓ | — |
| `DefinitePossessive E S`  | ✓ | ✓ | — | ✓ |

Lexical determiners (`Syntax/Determiner/Basic.lean`'s `Possessive`) hold no
model-level data — possessor/R/predicate are supplied at denotation time — so
they bear no bundled-carrier capability. -/

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
