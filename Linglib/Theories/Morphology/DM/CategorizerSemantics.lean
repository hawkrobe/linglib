import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Semantics.Lexical.Noun.Relational.Barker2011

/-!
# Categorizer Semantics @cite{adamson-2024} @cite{barker-2011}

Semantic denotations for categorizing heads (n) in Distributed Morphology,
bridging the morphosyntactic structure of DM categorizers to compositional
semantics via @cite{barker-2011}'s type-shifting framework.

@cite{adamson-2024} proposes three denotation types for n heads in Teop:

- **n_{body-part{D}}** (36): λy.λx. ROOT(x) ∧ body-part-of(x,y)
  Introduces a body-part-of relation, yielding a relational predicate
  (type ⟨e,⟨e,t⟩⟩). Equivalent to @cite{barker-2011}'s π (relationalizer).

- **n_{sortal}** (37): λx. ROOT(x)
  Bare sortal predicate (type ⟨e,t⟩). Equivalent to @cite{barker-2011}'s
  bare semantics.

- **n_{alienator}** (43): λQ.λx. ∃y. Q(y)(x)
  Existentially closes the possessor argument of a relational noun,
  yielding a property (type ⟨e,t⟩). Structurally parallel to
  @cite{barker-2011}'s Ex (existential closure).

## Key structural correspondence

The morphosyntactic features on n determine the semantic type:
- n with {D} (`selectsD = true`) → relational denotation (π)
- n without {D}, combining with a non-relational root → sortal (bare)
- n without {D}, mediating aPossession → existential closure (Ex)

This means the DM categorizer head is simultaneously:
1. A morphosyntactic object (bearing gender features, licensing possession)
2. A compositional semantic operator (determining the noun's semantic type)
-/

namespace Morphology.DM.CategorizerSemantics

open Semantics.Lexical.Noun.Relational.Barker2011

-- ============================================================================
-- § 1: Semantic Denotation Types for n Heads
-- ============================================================================

/-- The semantic type contributed by a categorizing head n.
    This determines how the root's content is composed into the noun's
    denotation (@cite{adamson-2024} §3.1). -/
inductive NSemanticType where
  /-- Relational: n introduces a relation (body-part-of, part-of, etc.).
      Result type: ⟨e,⟨e,t⟩⟩ = `Pred2`. -/
  | relational
  /-- Sortal: n simply categorizes. Result type: ⟨e,t⟩ = `Pred1`. -/
  | sortal
  /-- Alienator: n existentially closes a relational root.
      Input type: ⟨e,⟨e,t⟩⟩; result type: ⟨e,t⟩. -/
  | alienator
  deriving DecidableEq, Repr

/-- Map n-head features to the semantic type they contribute. -/
def catHeadSemanticType (ch : CatHead) (mediatesAPossession : Bool := false)
    : NSemanticType :=
  if ch.selectsD then .relational
  else if mediatesAPossession then .alienator
  else .sortal

-- ============================================================================
-- § 2: Denotation Functions
-- ============================================================================

/-- Denotation of n_{body-part{D}}: combines a root predicate with a
    body-part-of relation to yield a relational noun.

    @cite{adamson-2024} (36): ⟦nP⟧ = λy.λx. ROOT(x) ∧ body-part-of(x,y)

    This is @cite{barker-2011}'s π (relationalizer):
    π(P, R) = λx.λy. P(y) ∧ R(x,y)

    In π's convention: first arg = possessor, second arg = possessee. -/
def nBodyPartDenot {E S : Type}
    (rootPred : Pred1 E S) (bodyPartOf : Pred2 E S) : Pred2 E S :=
  π rootPred bodyPartOf

/-- Denotation of n_{sortal}: the root predicate, unchanged.

    @cite{adamson-2024} (37): ⟦nP⟧ = λx. ROOT(x) -/
def nSortalDenot {E S : Type} (rootPred : Pred1 E S) : Pred1 E S :=
  bareSemantics rootPred

/-- Denotation of n_{alienator}: existentially closes the possessor
    argument of a relational noun.

    @cite{adamson-2024} (43): ⟦n_{alienator}⟧ = λQ.λx. ∃y. Q(y)(x)

    The first argument of the input relation (the possessor) is
    existentially closed, yielding a one-place property of the
    possessee. -/
def nAlienatorDenot {E S : Type}
    (relation : Pred2 E S) (x : E) (s : S) : Prop :=
  ∃ y, relation y x s = true

-- ============================================================================
-- § 3: Bridge to Barker 2011
-- ============================================================================

/-- n_{body-part{D}} IS Barker's π: the relationalizer. -/
theorem nBodyPartDenot_eq_pi {E S : Type}
    (rootPred : Pred1 E S) (bodyPartOf : Pred2 E S) :
    nBodyPartDenot rootPred bodyPartOf = π rootPred bodyPartOf := rfl

/-- n_{sortal} IS Barker's bare semantics: identity on the root predicate. -/
theorem nSortalDenot_eq_bare {E S : Type} (rootPred : Pred1 E S) :
    nSortalDenot rootPred = bareSemantics rootPred := rfl

/-- n_{alienator} is the argument-flipped version of Barker's Ex.

    Barker's Ex closes the second argument of R(x,y):
      ExProp(R)(x)(s) = ∃y. R(x,y,s)

    The alienator closes the first argument (the possessor):
      nAlienatorDenot(R)(x)(s) = ∃y. R(y,x,s)

    Both perform existential closure; the difference is which argument
    of the relation represents the possessor vs possessee. -/
theorem nAlienatorDenot_is_ex_flipped {E S : Type}
    (R : Pred2 E S) (x : E) (s : S) :
    nAlienatorDenot R x s ↔ ExProp (λ a b t => R b a t) x s := by
  simp [nAlienatorDenot, ExProp]

/-- n with {D} produces a relational denotation; n without {D} does not. -/
theorem selectsD_iff_relational (ch : CatHead) :
    ch.selectsD = true ↔
    catHeadSemanticType ch = .relational := by
  unfold catHeadSemanticType
  cases ch.selectsD <;> simp

-- ============================================================================
-- § 4: Composition Examples (@cite{adamson-2024} §3.1)
-- ============================================================================

section TeopExample

variable {E S : Type}
variable (isSpleen : Pred1 E S)
variable (bodyPartOf : Pred2 E S)

/-- iPossession: √BINA + n_{body-part{D}} → relational noun.

    ⟦bina⟧ = λposs.λx. isSpleen(x) ∧ bodyPartOf(poss, x)
    'spleen of poss' -/
def teopSpleenIPossessed : Pred2 E S :=
  nBodyPartDenot isSpleen bodyPartOf

/-- aPossession: √BINA + n_{alienator} → existentially closed.

    ⟦bina⟧ = λx. ∃y. isSpleen(x) ∧ bodyPartOf(y, x)
    'a spleen (of some unspecified possessor)' -/
def teopSpleenAPossessed (x : E) (s : S) : Prop :=
  nAlienatorDenot (nBodyPartDenot isSpleen bodyPartOf) x s

/-- Sortal noun: √TARA + n_{sortal} → bare predicate.

    ⟦house⟧ = λx. isHouse(x)
    No possessor slot available. -/
def teopHouseSortal (isHouse : Pred1 E S) : Pred1 E S :=
  nSortalDenot isHouse

/-- With a specific possessor, the iPossessed body part reduces to a
    property (Barker's possessiveRelational). -/
theorem ipossessed_with_possessor (john : E) (x : E) (s : S) :
    teopSpleenIPossessed isSpleen bodyPartOf john x s =
    possessiveRelational john (π isSpleen bodyPartOf) x s := rfl

/-- The sortal noun has no relatum slot — it cannot directly take a
    possessor without π. -/
theorem sortal_is_pred1 (isHouse : Pred1 E S) :
    teopHouseSortal isHouse = isHouse := rfl

/-- Key insight: the SAME root (√BINA) yields different semantic types
    depending on which n head it combines with. The gender alternation
    in Teop (gender I vs gender II) corresponds to this semantic type
    alternation (relational vs sortal/alienated). -/
theorem same_root_different_types (x y : E) (s : S) :
    -- iPossessed: relational — takes a possessor argument
    teopSpleenIPossessed isSpleen bodyPartOf y x s =
      (isSpleen x s && bodyPartOf y x s) := rfl

/-- The alienator existentially closes the possessor slot. -/
theorem alienated_closes_possessor (x : E) (s : S) :
    teopSpleenAPossessed isSpleen bodyPartOf x s ↔
      ∃ z, isSpleen x s = true ∧ bodyPartOf z x s = true := by
  simp [teopSpleenAPossessed, nAlienatorDenot, nBodyPartDenot, π]

end TeopExample

-- ============================================================================
-- § 5: Morphosyntax–Semantics Correspondence
-- ============================================================================

/-! The Barker–Adamson correspondence:

| CatHead feature           | Semantic type | Barker operation |
|----------------------------|---------------|------------------|
| selectsD = true            | relational    | π                |
| selectsD = false (regular) | sortal        | bare             |
| selectsD = false (aPoss)   | alienator     | Ex               |

The genuine correspondence theorem is `selectsD_iff_relational` above:
selectsD on n ↔ relational semantic type. The sortal/alienator distinction
is secondary (determined by whether aPossession is mediated). -/

/-- The retraction property: applying the alienator to a π-relational noun
    recovers the root predicate (up to existential closure).

    nAlienatorDenot(π(P, R), x, s) ↔ ∃y. P(x,s) ∧ R(y,x,s)

    This is why "free" uses of iPossessable nouns in Jarawara are feminine:
    the root combines with n_{alienator}, existentially closing the
    possessor slot. The result is a property, which is the same type as
    n_{sortal}. Since the alienator n is plain (no gender feature), the
    noun is feminine (unmarked). -/
theorem alienator_retraction {E S : Type}
    (P : Pred1 E S) (R : Pred2 E S) (x : E) (s : S) :
    nAlienatorDenot (π P R) x s ↔ ∃ y, P x s = true ∧ R y x s = true := by
  simp [nAlienatorDenot, π]

/-- NominalInterpType from Barker 2011 corresponds to NSemanticType. -/
def NSemanticType.toBarker : NSemanticType → NominalInterpType
  | .relational => .pred2
  | .sortal     => .pred1
  | .alienator  => .pred1  -- alienator yields Pred1 (after closure)

/-- Only relational nouns (n with {D}) can directly take a possessor.
    Sortal and alienated nouns cannot — they need Barker's π first. -/
theorem possessor_requires_relational (t : NSemanticType) :
    t.toBarker.canTakePossessor = true ↔ t = .relational := by
  cases t <;> simp [NSemanticType.toBarker, NominalInterpType.canTakePossessor]

end Morphology.DM.CategorizerSemantics
