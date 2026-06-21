import Mathlib.Data.Fintype.Basic
import Linglib.Semantics.Quantification

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

The possessive-specific carriers, capability mixins, and quantificational layer
live in the unified `Possessive` namespace (`Semantics/Possessive/`), built on
this substrate.

## Main definitions

* `π P R`: Barker's relationalizer.
* `Ex R`: existential closure of a relation.
* `iotaPresupposition P`: Russellian uniqueness presupposition for definites.
* `naSemantics`, `bareSemantics`: demonstrative and bare nominal denotations.
* `NominalInterpType`: relational arity of a nominal denotation.

## Main statements

* `ex_pi_retraction`: `Ex` recovers a witness of `π P R` from witnesses of
  `P` and `R`.

## References

* [barker-2011]: Possessives and relational nouns
  (von Heusinger/Maienborn/Portner handbook, pp. 1109–1130; π and Ex at p. 1114).

## Tags

relational noun, type shifting, bridging, definite description, demonstrative
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

/-! ### Definiteness and demonstratives -/

section Definites

variable {E S : Type*}

/-- Russellian uniqueness presupposition: there exists a unique `x` satisfying
`P`. -/
def iotaPresupposition (P : Pred1 E S) (s : S) : Prop :=
  ∃ x : E, P x s ∧ ∀ y : E, P y s → y = x

/-- Demonstrative-headed nominal: `π` applied to a sortal noun with the
demonstrative supplying the relatum. -/
def naSemantics (nounPred : Pred1 E S) (R : Pred2 E S) (relatum : E) :
    Pred1 E S :=
  λ x s => π nounPred R relatum x s

/-- Bare nominal: identity on the predicate (no relatum slot). -/
def bareSemantics (nounPred : Pred1 E S) : Pred1 E S :=
  nounPred

end Definites

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

end Semantics.ArgumentStructure.Relational
