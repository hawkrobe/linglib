import Mathlib.Data.Fintype.Basic
import Linglib.Core.Logic.Quantification

/-!
# Possessives and relational nouns

Type-shifting operators for the analysis of possessive constructions and
relational nouns, following @cite{barker-2011}.

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

## Main statements

* `ex_pi_retraction`: `Ex` recovers a witness of `π P R` from witnesses of
  `P` and `R`.

## References

* @cite{barker-2011}: Possessives and relational nouns
  (§6 of Portner/Heusinger/Maienborn handbook; π and Ex on pp. 184–189,
  Vikner-Jensen taxonomy reproduced in Fig 6.1 p. 185).
* @cite{vikner-jensen-2002}: Semantic analysis of the English possessive.

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
@cite{vikner-jensen-2002} §3.1.2, reproduced in Fig 6.1 of
@cite{barker-2011}. The separate "pragmatic" interpretation
(@cite{vikner-jensen-2002} §3.1.1) is not lexical and is not one of the
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
