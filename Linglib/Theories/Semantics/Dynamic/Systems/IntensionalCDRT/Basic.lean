/-
# Intensional Compositional DRT (ICDRT)

Core types for Hofmann (2025) with propositional discourse referents enabling
anaphora to indefinites under negation.

## Main definitions

`IContext`, `DynProp`, `CommitmentSet`

## References

- Hofmann, L. (2025). Anaphoric accessibility with flat update. S&P.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. L&P 14.
- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
-/

import Linglib.Theories.Semantics.Dynamic.Core.Basic
import Linglib.Theories.Semantics.Dynamic.Core.Update
import Linglib.Theories.Semantics.Dynamic.Core.DiscourseRef
import Mathlib.Data.Set.Basic

namespace DynamicSemantics.IntensionalCDRT

open DynamicSemantics.Core

-- ICDRT-specific Notation

namespace ICDRTAssignment

variable {W E : Type*}

/-- Notation for individual variable lookup -/
notation g "⟦" v "⟧ᵢ" => ICDRTAssignment.indiv g v

/-- Notation for propositional variable lookup -/
notation g "⟦" p "⟧ₚ" => ICDRTAssignment.prop g p

end ICDRTAssignment

-- ICDRT Contexts (Information States)

/-- Set of assignment-world pairs (information state in flat update). -/
def IContext (W : Type*) (E : Type*) := Set (ICDRTAssignment W E × W)

instance {W E : Type*} : Membership (ICDRTAssignment W E × W) (IContext W E) := Set.instMembership
instance {W E : Type*} : EmptyCollection (IContext W E) := Set.instEmptyCollection
instance {W E : Type*} : HasSubset (IContext W E) := Set.instHasSubset
instance {W E : Type*} : Union (IContext W E) := Set.instUnion
instance {W E : Type*} : Inter (IContext W E) := Set.instInter

namespace IContext

variable {W E : Type*}

/-- The trivial context (all possibilities) -/
def univ : IContext W E := Set.univ

/-- The absurd context (no possibilities) -/
def empty : IContext W E := ∅

/-- Context is consistent (non-empty) -/
def consistent (c : IContext W E) : Prop := c.Nonempty

/-- Worlds in the context (projection) -/
def worlds (c : IContext W E) : Set W := { w | ∃ g, (g, w) ∈ c }

/-- Update with a world-predicate -/
def update (c : IContext W E) (p : W → Prop) : IContext W E :=
  { gw ∈ c | p gw.2 }

/-- Update with an assignment-world predicate -/
def updateFull (c : IContext W E) (p : ICDRTAssignment W E → W → Prop) : IContext W E :=
  { gw ∈ c | p gw.1 gw.2 }

notation:max c "⟦" p "⟧" => IContext.update c p

end IContext

-- Dynamic Propositions

/-- Context-to-context transformer (sentence denotation). -/
def DynProp (W : Type*) (E : Type*) := IContext W E → IContext W E

namespace DynProp

variable {W E : Type*}

/-- Identity (says nothing) -/
def id : DynProp W E := λ c => c

/-- Absurd (contradiction) -/
def absurd : DynProp W E := λ _ => ∅

/-- Tautology (accepts all) -/
def taut : DynProp W E := λ c => c

/-- Lift a classical proposition -/
def ofProp (p : W → Prop) : DynProp W E := λ c => c.update p

end DynProp

-- Commitment Sets

/-- Speaker's public commitments (discourse consistency requires non-empty). -/
structure CommitmentSet (W : Type*) (E : Type*) where
  context : IContext W E
  dc : Set W
  consistent : dc.Nonempty

namespace CommitmentSet

variable {W E : Type*}

/-- Initial commitment set (all worlds) -/
def initial [Nonempty W] : CommitmentSet W E where
  context := IContext.univ
  dc := Set.univ
  consistent := Set.univ_nonempty

end CommitmentSet


end DynamicSemantics.IntensionalCDRT
