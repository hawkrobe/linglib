import Linglib.Theories.Montague.Questions.Basic

/-!
# Questions/ConjoinableTypes.lean

Conjoinable Types and Generalized Semantic Operations (G&S 1984, Section 3.1).

## Key Idea

**Conjoinable Types (CT)**: Types that "end in t" - can participate in
coordination (conjunction, disjunction) and quantification.

Recursive definition:
- `t` is conjoinable (base case)
- `<a, b>` is conjoinable iff `b` is conjoinable

## Generalized Schemata

Once we identify CT, we can define coordination and quantification
uniformly across all conjoinable types:

- **CONJ**: Generalized conjunction (∧ for t, pointwise for <a,b>)
- **DISJ**: Generalized disjunction (∨ for t, pointwise for <a,b>)
- **INCL**: Inclusion (⊆ for t, pointwise for <a,b>)
- **QUANT**: Generalized quantification (∃, ∀, etc.)

## Example: Coordinating Questions

If Q₁ and Q₂ are questions (type <s, <<s,t>,t>>), then:
- Q₁ ∧ Q₂ = λw.λp. Q₁(w)(p) ∧ Q₂(w)(p)
- Q₁ ∨ Q₂ = λw.λp. Q₁(w)(p) ∨ Q₂(w)(p)

The pointwise lifting preserves the partition structure.

## Significance

This generalizes Montague's treatment of coordination from entities to
arbitrary conjoinable types, enabling a uniform analysis of:
- Sentential coordination: "John walks and Mary talks"
- NP coordination: "John and Mary walk"
- VP coordination: "John walks and talks"
- Interrogative coordination: "Who came and what did they bring?"

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Section 3.1.
- Partee & Rooth (1983). Generalized Conjunction and Type Ambiguity.
-/

namespace Montague.Questions

-- ============================================================================
-- Conjoinable Types (CT)
-- ============================================================================

/-- Semantic types in Montague grammar.

The type system mirrors the typed lambda calculus:
- `e`: entities
- `t`: truth values (propositions)
- `s`: possible worlds
- `arr a b`: functions from a to b (<a, b> in Montague's notation) -/
inductive SemType where
  | e : SemType                       -- Entities
  | t : SemType                       -- Truth values
  | s : SemType                       -- Possible worlds
  | arr : SemType -> SemType -> SemType  -- Function types <a, b>
  deriving DecidableEq, Repr

namespace SemType

/-- A type is conjoinable iff it "ends in t".

Recursive definition from G&S 1984, p. 415:
- `t` is conjoinable (base case)
- `<a, b>` is conjoinable iff `b` is conjoinable -/
def isConjoinable : SemType -> Bool
  | .t => true
  | .arr _ b => b.isConjoinable
  | .e => false
  | .s => false

/-- Common conjoinable types -/
def ct_t : SemType := .t
def ct_et : SemType := .arr .e .t                -- <e,t> = properties
def ct_eet : SemType := .arr .e (.arr .e .t)     -- <e,<e,t>> = relations
def ct_st : SemType := .arr .s .t                -- <s,t> = propositions (intensions)
def ct_sst : SemType := .arr .s (.arr .s .t)     -- <s,<s,t>> = relations on worlds

/-- The type of Montague-style questions: <<s,t>,t> (sets of propositions) -/
def questionType : SemType := .arr (.arr .s .t) .t

/-- Questions are conjoinable -/
theorem questionType_conjoinable : questionType.isConjoinable = true := rfl

/-- Properties (<e,t>) are conjoinable -/
theorem property_conjoinable : ct_et.isConjoinable = true := rfl

/-- Entities are NOT conjoinable (coordination lifts to generalized quantifiers) -/
theorem entity_not_conjoinable : SemType.e.isConjoinable = false := rfl

/-- Worlds are NOT conjoinable -/
theorem world_not_conjoinable : SemType.s.isConjoinable = false := rfl

end SemType

-- ============================================================================
-- CONJ Schema: Generalized Conjunction
-- ============================================================================

/-!
## CONJ Schema

For conjoinable type τ:
- If τ = t: CONJ = ∧ (Boolean conjunction)
- If τ = <a, b>: CONJ_τ(f, g) = λx. CONJ_b(f(x), g(x))

This gives pointwise lifting through function types.
-/

/-- Conjunction at type t (base case). -/
def conjT (p q : Bool) : Bool := p && q

/-- Pointwise conjunction for functions.
CONJ_{<a,b>}(f, g) = λx. CONJ_b(f(x), g(x)) -/
def conjFunc {A B : Type*} (conjB : B -> B -> B) (f g : A -> B) : A -> B :=
  fun x => conjB (f x) (g x)

/-- Conjunction for properties (<e,t>): λx. P(x) ∧ Q(x) -/
def conjProperty {E : Type*} (p q : E -> Bool) : E -> Bool :=
  conjFunc conjT p q

/-- Conjunction for relations (<e,<e,t>>): λx.λy. R(x,y) ∧ S(x,y) -/
def conjRelation {E : Type*} (r s : E -> E -> Bool) : E -> E -> Bool :=
  conjFunc (conjFunc conjT) r s

/-- Conjunction for propositions (<s,t>): λw. P(w) ∧ Q(w) -/
def conjProposition {W : Type*} (p q : W -> Bool) : W -> Bool :=
  conjFunc conjT p q

/-- Conjunction for question denotations (<<s,t>,t>): λP. Q₁(P) ∧ Q₂(P) -/
def conjQuestion {W : Type*} (q1 q2 : (W -> Bool) -> Bool) : (W -> Bool) -> Bool :=
  conjFunc conjT q1 q2

/-- CONJ distributes over function application.
CONJ(f,g)(x) = CONJ(f(x), g(x)) -/
theorem conj_distributes {A B : Type*} (conjB : B -> B -> B)
    (f g : A -> B) (x : A) :
    conjFunc conjB f g x = conjB (f x) (g x) := rfl

-- ============================================================================
-- DISJ Schema: Generalized Disjunction
-- ============================================================================

/-!
## DISJ Schema

Parallel to CONJ but with disjunction:
- If τ = t: DISJ = ∨
- If τ = <a, b>: DISJ_τ(f, g) = λx. DISJ_b(f(x), g(x))
-/

/-- Disjunction at type t (base case). -/
def disjT (p q : Bool) : Bool := p || q

/-- Pointwise disjunction for functions. -/
def disjFunc {A B : Type*} (disjB : B -> B -> B) (f g : A -> B) : A -> B :=
  fun x => disjB (f x) (g x)

/-- Disjunction for properties: λx. P(x) ∨ Q(x) -/
def disjProperty {E : Type*} (p q : E -> Bool) : E -> Bool :=
  disjFunc disjT p q

/-- Disjunction for propositions: λw. P(w) ∨ Q(w) -/
def disjProposition {W : Type*} (p q : W -> Bool) : W -> Bool :=
  disjFunc disjT p q

/-- Disjunction for question denotations: λP. Q₁(P) ∨ Q₂(P) -/
def disjQuestion {W : Type*} (q1 q2 : (W -> Bool) -> Bool) : (W -> Bool) -> Bool :=
  disjFunc disjT q1 q2

-- ============================================================================
-- INCL Schema: Generalized Inclusion
-- ============================================================================

/-!
## INCL Schema

The subset/inclusion relation, generalized:
- If τ = t: INCL(p, q) = p → q (material implication = subset)
- If τ = <a, b>: INCL_τ(f, g) = ∀x. INCL_b(f(x), g(x))
-/

/-- Inclusion at type t: p ⊆ q iff p → q -/
def inclT (p q : Bool) : Bool := !p || q

/-- Pointwise inclusion for functions: f ⊆ g iff ∀x. f(x) ⊆ g(x) -/
def inclFunc {A : Type*} (inclB : Bool -> Bool -> Bool) (f g : A -> Bool)
    (domain : List A) : Bool :=
  domain.all fun x => inclB (f x) (g x)

/-- Inclusion for properties: P ⊆ Q iff ∀x. P(x) → Q(x) -/
def inclProperty {E : Type*} (p q : E -> Bool) (entities : List E) : Bool :=
  inclFunc inclT p q entities

/-- Inclusion for propositions: P ⊆ Q iff ∀w. P(w) → Q(w) -/
def inclProposition {W : Type*} (p q : W -> Bool) (worlds : List W) : Bool :=
  inclFunc inclT p q worlds

-- ============================================================================
-- QUANT Schema: Generalized Quantification
-- ============================================================================

/-!
## QUANT Schema

Quantifiers over conjoinable types:
- ∃_τ(P) = "some individual of type τ satisfies P"
- ∀_τ(P) = "all individuals of type τ satisfy P"

The key insight: quantifiers are "generalized conjunctions/disjunctions"
over a domain:
- ∃ = DISJ over all elements
- ∀ = CONJ over all elements
-/

/-- Existential quantification at type t (given a list of truth values). -/
def existsT (values : List Bool) : Bool :=
  values.any id

/-- Universal quantification at type t. -/
def forallT (values : List Bool) : Bool :=
  values.all id

/-- Existential quantification over a domain: ∃x∈D. P(x) -/
def existsOver {A : Type*} (domain : List A) (p : A -> Bool) : Bool :=
  domain.any p

/-- Universal quantification over a domain: ∀x∈D. P(x) -/
def forallOver {A : Type*} (domain : List A) (p : A -> Bool) : Bool :=
  domain.all p

/-- Existential = disjunction over all domain elements -/
theorem exists_is_disj {A : Type*} (domain : List A) (p : A -> Bool) :
    existsOver domain p = (domain.map p).any id := by
  simp [existsOver, List.any_map]

/-- Universal = conjunction over all domain elements -/
theorem forall_is_conj {A : Type*} (domain : List A) (p : A -> Bool) :
    forallOver domain p = (domain.map p).all id := by
  simp [forallOver, List.all_map]

-- ============================================================================
-- Type-Raising and Coordination
-- ============================================================================

/-!
## Type-Raising for Non-Conjoinable Types

Entities (type e) are not conjoinable. But we CAN coordinate NPs by:
1. Type-raising entities to generalized quantifiers (type <<e,t>,t>)
2. Coordinating at the GQ level

Type-raising: e → <<e,t>,t>
john ↦ λP. P(john)

Now "John and Mary" becomes:
λP. P(john) ∧ λP. P(mary) = λP. P(john) ∧ P(mary)
-/

/-- Type-raise an entity to a generalized quantifier. -/
def typeRaise {E : Type*} (e : E) : (E -> Bool) -> Bool :=
  fun p => p e

/-- Coordinated entities via type-raising.
"John and Mary" = λP. P(john) ∧ P(mary) -/
def coordinateEntities {E : Type*} (e1 e2 : E) : (E -> Bool) -> Bool :=
  conjQuestion (typeRaise e1) (typeRaise e2)

/-- Type-raising preserves reference: GQ(john)(P) = P(john) -/
theorem typeRaise_preserves {E : Type*} (e : E) (p : E -> Bool) :
    typeRaise e p = p e := rfl

/-- Coordinated entities: (john ∧ mary)(P) = P(john) ∧ P(mary) -/
theorem coordinated_both_satisfy {E : Type*} (e1 e2 : E) (p : E -> Bool) :
    coordinateEntities e1 e2 p = (p e1 && p e2) := rfl

-- ============================================================================
-- Application to Interrogatives
-- ============================================================================

/-!
## Interrogative Coordination

Questions have type <<s,t>,t> (sets of propositions), which is conjoinable.
Therefore we can directly apply CONJ and DISJ to questions.

Q₁ ∧ Q₂ = "Answer both Q₁ and Q₂"
Q₁ ∨ Q₂ = "Answer either Q₁ or Q₂"

These will be developed further in Questions/Coordination.lean.
-/

/-- Type of questions in this framework.
Questions map propositions to truth values: (W -> Bool) -> Bool -/
abbrev QuestionDen (W : Type*) := (W -> Bool) -> Bool

/-- Conjoin two question denotations.
(Q₁ ∧ Q₂)(P) = Q₁(P) ∧ Q₂(P)

Semantically: P answers (Q₁ ∧ Q₂) iff P answers both Q₁ and Q₂. -/
def questionConj {W : Type*} (q1 q2 : QuestionDen W) : QuestionDen W :=
  conjQuestion q1 q2

/-- Disjoin two question denotations.
(Q₁ ∨ Q₂)(P) = Q₁(P) ∨ Q₂(P)

Semantically: P answers (Q₁ ∨ Q₂) iff P answers Q₁ or P answers Q₂. -/
def questionDisj {W : Type*} (q1 q2 : QuestionDen W) : QuestionDen W :=
  disjQuestion q1 q2

/-- Conjunction of questions is commutative. -/
theorem questionConj_comm {W : Type*} (q1 q2 : QuestionDen W) (p : W -> Bool) :
    questionConj q1 q2 p = questionConj q2 q1 p := Bool.and_comm _ _

/-- Disjunction of questions is commutative. -/
theorem questionDisj_comm {W : Type*} (q1 q2 : QuestionDen W) (p : W -> Bool) :
    questionDisj q1 q2 p = questionDisj q2 q1 p := Bool.or_comm _ _

/-- De Morgan for question coordination: ¬(Q₁ ∧ Q₂) = ¬Q₁ ∨ ¬Q₂ -/
theorem question_deMorgan_conj {W : Type*} (q1 q2 : QuestionDen W) (p : W -> Bool) :
    !(questionConj q1 q2 p) = ((!q1 p) || (!q2 p)) := by
  unfold questionConj conjQuestion conjFunc conjT
  cases q1 p <;> cases q2 p <;> rfl

-- ============================================================================
-- The CONJ/DISJ Duality
-- ============================================================================

/-- CONJ and DISJ are De Morgan duals.

Note: !(p ∧ q) = ¬p ∨ ¬q holds pointwise. -/
theorem conj_disj_duality {A : Type*} (p q : A -> Bool) (x : A) :
    !(conjFunc conjT p q x) = (!p x || !q x) := by
  unfold conjFunc conjT
  cases p x <;> cases q x <;> rfl

/-- Universal and existential are duals via negation. -/
theorem forall_exists_duality {A : Type*} (domain : List A) (p : A -> Bool) :
    forallOver domain p = !existsOver domain (fun x => !p x) := by
  simp [forallOver, existsOver, List.all_eq_not_any_not]

end Montague.Questions
