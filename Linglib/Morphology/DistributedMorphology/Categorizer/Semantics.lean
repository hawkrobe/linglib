import Linglib.Morphology.DistributedMorphology.Categorizer.Gender
import Linglib.Semantics.Possessive.Relational
import Linglib.Semantics.Possessive.Basic

/-!
# Categorizer semantics

The denotations of nominal categorizing heads: an n head is simultaneously
a morphosyntactic object (gender features, the selectional feature {D}) and
the compositional operator fixing the noun's semantic type. An n with {D}
composes a root with the body-part-of relation into a relational noun, a
sortal n is the identity on the root predicate, and the alienator n
existentially closes a relational noun's possessor — the relationalizer π,
bare interpretation, and detransitivizing Ex of the possession literature,
stated over `Semantics/Possessive/`.

## Main definitions

* `NSemanticType` — relational, sortal, alienator
* `nBodyPartDenot`, `nSortalDenot`, `nAlienatorDenot` — the three head
  denotations
* `catHeadSemanticType` — the semantic type read off a `CatHead`

## Main statements

* `selectsD_iff_relational` — {D} on n iff relational type
* `alienator_retraction` — closing π's possessor slot recovers the root
  predicate up to existential closure

## References

* [L. J. Adamson, *Gender assignment is local*][adamson-2024]
* [C. Barker, *Possessives and relational nouns*][barker-2011]
-/

namespace DistributedMorphology.CategorizerSemantics

open ArgumentStructure.Relational

/-! ### Semantic Denotation Types for n Heads -/

/-- The semantic type a nominal categorizing head contributes
([adamson-2024] §3.1). -/
inductive NSemanticType where
  /-- Relational: n introduces a relation (body-part-of, part-of, etc.).
      Result type: ⟨e,⟨e,t⟩⟩. -/
  | relational
  /-- Sortal: n simply categorizes. Result type: ⟨e,t⟩. -/
  | sortal
  /-- Alienator: n existentially closes a relational root.
      Input type: ⟨e,⟨e,t⟩⟩; result type: ⟨e,t⟩. -/
  | alienator
  deriving DecidableEq, Repr

/-- The semantic type read off a head's features. -/
def catHeadSemanticType (ch : CatHead) (mediatesAPossession : Bool := false)
    : NSemanticType :=
  if ch.selectsD then .relational
  else if mediatesAPossession then .alienator
  else .sortal

/-! ### Denotation Functions -/

/-- The denotation of n_body-part{D} — a root predicate composed with a
body-part-of relation into a relational noun ([adamson-2024] (36)),
implemented as [barker-2011]'s relationalizer π. Following π's
convention, `bodyPartOf` is possessor-first, the flip of Adamson's
notation. -/
def nBodyPartDenot {E S : Type}
    (rootPred : E → S → Prop) (bodyPartOf : E → E → S → Prop) : E → E → S → Prop :=
  π rootPred bodyPartOf

/-- The denotation of n_sortal — the identity on the root predicate
([adamson-2024] (37)). -/
def nSortalDenot {E S : Type} (rootPred : E → S → Prop) : E → S → Prop :=
  bareSemantics rootPred

/-- The denotation of n_alienator — existential closure of a relational
noun's possessor argument, yielding a one-place property of the possessee
([adamson-2024] (43): λQ.λx.∃y. Q(y)(x)). -/
def nAlienatorDenot {E S : Type}
    (relation : E → E → S → Prop) (x : E) (s : S) : Prop :=
  ∃ y, relation y x s

/-! ### Bridge to Barker 2011 -/

/-- The body-part head is Barker's relationalizer π. -/
theorem nBodyPartDenot_eq_pi {E S : Type}
    (rootPred : E → S → Prop) (bodyPartOf : E → E → S → Prop) :
    nBodyPartDenot rootPred bodyPartOf = π rootPred bodyPartOf := rfl

/-- The alienator is Barker's detransitivizing Ex applied to the flipped
relation — Ex closes the relation's second argument, the alienator its
first (the possessor). -/
theorem nAlienatorDenot_is_ex_flipped {E S : Type}
    (R : E → E → S → Prop) (x : E) (s : S) :
    nAlienatorDenot R x s ↔ Ex (λ a b t => R b a t) x s := by
  simp only [nAlienatorDenot, Ex]

/-- An n head has {D} iff its semantic type is relational. -/
theorem selectsD_iff_relational (ch : CatHead) :
    ch.selectsD = true ↔
    catHeadSemanticType ch = .relational := by
  unfold catHeadSemanticType
  cases ch.selectsD <;> simp

/-! ### Composition Examples ([adamson-2024] §3.1) -/

section TeopExample

variable {E S : Type}
variable (isSpleen : E → S → Prop)
variable (bodyPartOf : E → E → S → Prop)

/-- The iPossessed reading of Teop *bina* 'spleen' — √BINA under
n_body-part{D}, a relational noun awaiting its possessor. -/
def teopSpleenIPossessed : E → E → S → Prop :=
  nBodyPartDenot isSpleen bodyPartOf

/-- The alienated reading of *bina* — the alienator over the body-part
noun, a spleen of some existentially closed possessor. -/
def teopSpleenAPossessed (x : E) (s : S) : Prop :=
  nAlienatorDenot (nBodyPartDenot isSpleen bodyPartOf) x s

/-- Teop *inu* 'house' under the sortal n — a bare predicate with no
possessor slot ([adamson-2024] (37)). -/
def teopHouseSortal (isHouse : E → S → Prop) : E → S → Prop :=
  nSortalDenot isHouse

/-- Saturating the possessor reduces the iPossessed body part to a
property (`Possessive.viaArgument`). -/
theorem ipossessed_with_possessor (john : E) (x : E) (s : S) :
    teopSpleenIPossessed isSpleen bodyPartOf john x s =
    Possessive.viaArgument john (π isSpleen bodyPartOf) x s := rfl

/-- A sortal noun has no relatum slot and cannot take a possessor
without π. -/
theorem sortal_is_pred1 (isHouse : E → S → Prop) :
    teopHouseSortal isHouse = isHouse := rfl

/-- One root, two semantic types — the Teop gender I / gender II
alternation tracks which n √BINA combines with. -/
theorem same_root_different_types (x y : E) (s : S) :
    -- iPossessed: relational — takes a possessor argument
    teopSpleenIPossessed isSpleen bodyPartOf y x s ↔
      (isSpleen x s ∧ bodyPartOf y x s) := Iff.rfl

/-- The alienator existentially closes the possessor slot. -/
theorem alienated_closes_possessor (x : E) (s : S) :
    teopSpleenAPossessed isSpleen bodyPartOf x s ↔
      ∃ z, isSpleen x s ∧ bodyPartOf z x s := by
  simp only [teopSpleenAPossessed, nAlienatorDenot, nBodyPartDenot, π]

end TeopExample

/-! ### Morphosyntax–Semantics Correspondence -/

/-! The Barker–Adamson correspondence:

| CatHead feature           | Semantic type | Barker operation |
|----------------------------|---------------|------------------|
| selectsD = true            | relational    | π                |
| selectsD = false (regular) | sortal        | bare             |
| selectsD = false (aPoss)   | alienator     | Ex               |

The genuine correspondence theorem is `selectsD_iff_relational` above:
selectsD on n ↔ relational semantic type. The sortal/alienator distinction
is secondary (determined by whether aPossession is mediated). NB the
single-head classifier compresses [adamson-2024]'s (43), where the
alienator is a second n stacked on a {D}-less body-part n. -/

/-- Applying the alienator to a π-relational noun recovers the root
predicate up to existential closure. In Teop the alienator bears its own
gender II, which as the highest gender is what agreement sees — the
body-part noun switches gender when unpossessed ((38)–(43)) — while
Jarawara's unmarked alienating n leaves the free use feminine. -/
theorem alienator_retraction {E S : Type}
    (P : E → S → Prop) (R : E → E → S → Prop) (x : E) (s : S) :
    nAlienatorDenot (π P R) x s ↔ ∃ y, P x s ∧ R y x s := by
  simp only [nAlienatorDenot, π]

/-- The `NominalInterpType` of [barker-2011] induced by a semantic
type. -/
def NSemanticType.toBarker : NSemanticType → NominalInterpType
  | .relational => .relational
  | .sortal     => .sortal
  | .alienator  => .sortal  -- alienator yields a one-place predicate (after closure)

/-- Only relational nouns (n with {D}) can directly take a possessor.
    Sortal and alienated nouns cannot — they need Barker's π first. -/
theorem possessor_requires_relational (t : NSemanticType) :
    t.toBarker.canTakePossessor ↔ t = .relational := by
  cases t <;> simp [NSemanticType.toBarker, NominalInterpType.canTakePossessor]

end DistributedMorphology.CategorizerSemantics
