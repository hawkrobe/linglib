import Mathlib.Data.Fintype.Basic
import Linglib.Core.Quantification

/-
# Possessives and Relational Nouns (Barker 2011)

Barker's type-shifting analysis: π relationalizes sortals, Ex detransitivizes relations.

## Main definitions

`π`, `ExProp`, `ExDecidable`, `PossessiveSemantics`, `possessiveRelational`, `possessiveSortal`, `naSemantics`, `bareSemantics`

## References

Barker (2011), Partee (1997), Vikner & Jensen (2002), Ahn & Zhu (2025)
-/

namespace Semantics.Lexical.Noun.Relational.Barker2011


/-- One-place predicates: E → S → Bool -/
abbrev Pred1 (E S : Type) := E → S → Bool

/-- Two-place predicates (relations): E → E → S → Bool -/
abbrev Pred2 (E S : Type) := E → E → S → Bool

/-- The semantic type of an expression, tracking arity. -/
inductive SemType where
  | pred1  -- Property: E → S → Bool
  | pred2  -- Relation: E → E → S → Bool
  | entity -- Individual: E
  deriving DecidableEq, Repr, BEq


/-- Barker's π (Relationalizer): λP.λx.λy. P(y) ∧ R(x,y) -/
def π {E S : Type} (P : Pred1 E S) (R : Pred2 E S) : Pred2 E S :=
  λ x y s => P y s && R x y s

scoped notation "relationalizer(" P ", " R ")" => π P R

/-- Ex (Existential Closure): λR.λx. ∃y. R(x,y) -/
def ExProp {E S : Type} (R : Pred2 E S) : E → S → Prop :=
  λ x s => ∃ y : E, R x y s = true

noncomputable def ExDecidable {E S : Type} [Fintype E] [DecidableEq E]
    (R : Pred2 E S) : Pred1 E S :=
  λ x s => (Fintype.elems : Finset E).toList.any (λ y => R x y s)

/-- Semantic structure of possessive phrase -/
structure PossessiveSemantics (E S : Type) where
  possessor : E
  possesseePred : Pred1 E S
  relation : Pred2 E S
  relationIsLexical : Bool

def possessiveRelational {E S : Type}
    (possessor : E) (nounRel : Pred2 E S) : Pred1 E S :=
  λ y s => nounRel possessor y s

def possessiveSortal {E S : Type}
    (possessor : E) (nounPred : Pred1 E S) (R : Pred2 E S) : Pred1 E S :=
  λ y s => (π nounPred R) possessor y s

theorem possessive_sortal_is_pi {E S : Type}
    (possessor : E) (P : Pred1 E S) (R : Pred2 E S) (y : E) (s : S) :
    possessiveSortal possessor P R y s = (π P R) possessor y s := rfl

def iotaPresupposition {E S : Type} (P : Pred1 E S) (s : S) : Prop :=
  ∃ x : E, P x s = true ∧ ∀ y : E, P y s = true → y = x

structure DefinitePossessive (E S : Type) where
  possessor : E
  predicate : Pred1 E S
  presupposition : ∀ s : S, iotaPresupposition predicate s

def naSemantics {E S : Type}
    (nounPred : Pred1 E S) (R : Pred2 E S) (relatum : E) : Pred1 E S :=
  λ x s => (π nounPred R) relatum x s

def bareSemantics {E S : Type} (nounPred : Pred1 E S) : Pred1 E S :=
  nounPred

theorem na_has_relatum_slot {E S : Type}
    (P : Pred1 E S) (R : Pred2 E S) (z x : E) (s : S) :
    naSemantics P R z x s = (P x s && R z x s) := rfl

theorem bare_has_no_relatum_slot {E S : Type}
    (P : Pred1 E S) (x : E) (s : S) :
    bareSemantics P x s = P x s := rfl

/-- Source of the relational interpretation. -/
inductive InterpretationSource where
  | lexicalRelation   -- Noun is lexically relational (brother, author)
  | appliedPi         -- π was applied (possessive/demonstrative)
  | noRelation        -- No relation available (bare sortal)
  deriving DecidableEq, Repr, BEq

def canFillRelatum : InterpretationSource → Bool
  | .lexicalRelation => true   -- Lexical slot
  | .appliedPi => true         -- π-created slot
  | .noRelation => false       -- No slot

/-- Bridging licensing follows from π-application (Ahn & Zhu 2025).

Sortal nouns: π creates slot (bridging OK); no π means no slot (blocked).
Relational nouns: lexical slot exists regardless of π. -/
theorem bridging_from_pi {E S : Type}
    (P : Pred1 E S) (R : Pred2 E S) :
    -- π always creates a relatum slot
    canFillRelatum .appliedPi = true ∧
    -- No π means no slot (for sortal nouns)
    canFillRelatum .noRelation = false ∧
    -- Lexical relations have slots
    canFillRelatum .lexicalRelation = true := by
  exact ⟨rfl, rfl, rfl⟩


/-- Vikner & Jensen's taxonomy of possession relations (Barker p. 9). -/
inductive PossessionRelationType where
  /-- Inherent: part-whole, properties (the car's speed, the table's leg) -/
  | inherent
  /-- Agentive: agent relation (John's poem = poem John wrote) -/
  | agentive
  /-- Control: ownership, legal control (John's house) -/
  | control
  /-- Pragmatic: any contextually salient relation -/
  | pragmatic
  deriving DecidableEq, Repr, BEq

/-- Lexical possession (relational noun) vs pragmatic possession (sortal noun). -/
def relationSource (isNounRelational : Bool) : String :=
  if isNounRelational then "lexical" else "pragmatic (from π)"


/-- Derivation: "John's brother" (relational noun, no π needed). -/
def derivation_johns_brother {E S : Type}
    (john : E) (brother : Pred2 E S) : Pred1 E S :=
  possessiveRelational john brother

/-- Derivation: "John's cloud" (sortal noun, π required). -/
def derivation_johns_cloud {E S : Type}
    (john : E) (cloud : Pred1 E S) (R : Pred2 E S) : Pred1 E S :=
  possessiveSortal john cloud R

/-- Derivation: Mandarin "na zuozhe" (that author; relational noun). -/
def derivation_na_author {E S : Type}
    (author : Pred2 E S) (relatum : E) : Pred1 E S :=
  λ x s => author relatum x s

/-- Derivation: Mandarin "na zuoyi" (that seat; sortal noun, π from *na*). -/
def derivation_na_seat {E S : Type}
    (seat : Pred1 E S) (R : Pred2 E S) (car : E) : Pred1 E S :=
  naSemantics seat R car

/-- Derivation: Bare Mandarin "zuoyi" (seat; no π, no bridging slot). -/
def derivation_bare_seat {E S : Type}
    (seat : Pred1 E S) : Pred1 E S :=
  bareSemantics seat


/-!
## Algebraic Structure

π and Ex form a pseudo-adjoint pair:
Ex(π(P, R)) ≈ P (when R is satisfied by some entity).
-/

/-- Retraction: Ex(π(P, R)) holds when both P(y) and R(z,y) hold. -/
theorem ex_pi_retraction {E S : Type} [Nonempty E]
    (P : Pred1 E S) (R : Pred2 E S) (y z : E) (s : S)
    (hP : P y s = true) (hR : R z y s = true) :
    ExProp (π P R) z s := by
  exact ⟨y, by simp [π, hP, hR]⟩

/-!
## Unification of Possessives, Demonstratives, and Bridging

Three questions are equivalent:
1. Can "John's N" be interpreted? (possessive licensing)
2. Can "na N" accommodate a bridging antecedent? (bridging licensing)
3. Does the interpretation of N have type Pred2? (structural question)
-/

/-- The interpretation type of a nominal -/
inductive NominalInterpType where
  /-- Pred1: No relatum slot (sortal, no π) -/
  | pred1
  /-- Pred2: Has relatum slot (relational or π-shifted) -/
  | pred2
  deriving DecidableEq, Repr, BEq

/-- Does this interpretation type have a relatum slot? -/
def NominalInterpType.hasRelatumSlot : NominalInterpType → Bool
  | .pred1 => false
  | .pred2 => true

/-- Can this interpretation type take a possessor? -/
def NominalInterpType.canTakePossessor : NominalInterpType → Bool
  | .pred1 => false  -- Need π first
  | .pred2 => true   -- Possessor fills relatum

/-- Can this interpretation type accommodate bridging? -/
def NominalInterpType.canBridge : NominalInterpType → Bool
  | .pred1 => false  -- No slot for antecedent
  | .pred2 => true   -- Antecedent fills relatum

/-- hasRelatumSlot ⟺ canTakePossessor ⟺ canBridge. -/
theorem unification_principle :
    ∀ t : NominalInterpType,
      t.hasRelatumSlot = t.canTakePossessor ∧
      t.canTakePossessor = t.canBridge := by
  intro t
  cases t <;> exact ⟨rfl, rfl⟩

/-- Bridging asymmetry = possessive asymmetry. -/
theorem bridging_is_possession (t : NominalInterpType) :
    t.canBridge = t.canTakePossessor := by
  cases t <;> rfl

/-- π always creates a relatum slot (π : Pred1 → Pred2). -/
theorem pi_creates_slot {E S : Type} (P : Pred1 E S) (R : Pred2 E S) :
    -- After π, we have a Pred2, which has a relatum slot
    -- The slot is the first argument position
    ∀ z x s, (π P R) z x s = (P x s && R z x s) := by
  intros; rfl

/-- Bridging ↔ having a relatum slot. -/
theorem structural_explanation (t : NominalInterpType) :
    t.canBridge = true ↔ t.hasRelatumSlot = true := by
  cases t <;> simp [NominalInterpType.canBridge, NominalInterpType.hasRelatumSlot]

-- ============================================================================
-- Bridge: Possessives as Type ⟨1⟩ Quantifiers (NPQ)
-- ============================================================================

/-- A possessive like "John's" produces a type ⟨1⟩ quantifier (NPQ):
    ⟦John's⟧ = λR.λP. ∃y. R(possessor, y) ∧ P(y).
    When the possessum is unique, this is a Montagovian individual.

    Possessive GQs are NON-ISOM: "John's cat" depends on the identity
    of John, not just cardinalities. This connects Barker's type-shifting
    analysis to the GQ framework in `Core.Quantification`. -/
noncomputable def possessiveAsNPQ {E : Type} [Fintype E] [DecidableEq E]
    (possessor : E) (R : E → E → Bool) :
    Core.Quantification.NPQ E :=
  λ P => (Fintype.elems : Finset E).toList.any (λ y => R possessor y && P y)

/-- When the possessum is unique, the possessive NP denotes a Montagovian
    individual: ⟦John's brother⟧ = I_{b} where b is John's unique brother.
    The Montagovian individual I_b maps any property P to P(b).
    Cross-ref: `Core.Quantification.individual`. -/
theorem possessive_individual_eval {E : Type} (b : E) :
    ∀ P : E → Bool,
      Core.Quantification.individual b P = P b := by
  intro P; rfl

end Semantics.Lexical.Noun.Relational.Barker2011
