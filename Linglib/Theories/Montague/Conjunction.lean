/-
# Generalized Conjunction (Partee & Rooth 1983)

This module formalizes Partee & Rooth's treatment of coordination semantics.

## The Core Insight

Conjunction and disjunction can be defined recursively over the type structure:
- Base case: Boolean operations at type t
- Recursive case: pointwise application at function types

This allows "and" to conjoin expressions of ANY conjoinable type, not just sentences.

## Key Definitions (from the paper)

**Conjoinable Type** (Definition 4):
  (i)  t is a conjoinable type
  (ii) if b is conjoinable, then ⟨a,b⟩ is conjoinable for any a

**Pointwise Conjunction** (Definition 5):
  - X ∩ Y = X ∧ Y  (for truth values)
  - φ ∩ ψ = λz[φ(z) ∩ ψ(z)]  (for functions into conjoinable types)

## Reference

Partee, B. & Rooth, M. (1983). Generalized Conjunction and Type Ambiguity.
In von Stechow et al. (eds.), Meaning, Use, and Interpretation. de Gruyter.
-/

import Linglib.Theories.Montague.Basic

namespace Montague

-- ============================================================================
-- Conjoinable Types (in Montague namespace, extending Ty)
-- ============================================================================

/--
A semantic type is conjoinable if it "ends in t".

Definition 4 from Partee & Rooth (1983):
  (i)  t is a conjoinable type
  (ii) if b is conjoinable, then ⟨a,b⟩ is conjoinable for any a

Intuitively: we can conjoin things that ultimately produce truth values.
-/
def Ty.isConjoinable : Ty → Bool
  | .t => true
  | .e => false
  | .s => false
  | .fn _ τ => τ.isConjoinable

-- Examples
example : Ty.isConjoinable .t = true := rfl           -- sentences
example : Ty.isConjoinable .e = false := rfl          -- entities can't be conjoined
example : Ty.isConjoinable .s = false := rfl          -- worlds can't be conjoined
example : Ty.isConjoinable (.fn .e .t) = true := rfl    -- properties: "tall and happy"
example : Ty.isConjoinable (.fn .e (.fn .e .t)) = true := rfl -- relations
example : Ty.isConjoinable (.fn .e .e) = false := rfl   -- functions to entities
example : Ty.isConjoinable (.fn .s .t) = true := rfl    -- propositions (intensional)

namespace Conjunction

-- ============================================================================
-- Generalized Conjunction
-- ============================================================================

/--
Generalized conjunction: recursively defined over conjoinable types.

Definition 5 from Partee & Rooth (1983):
  - At type t: Boolean conjunction (∧)
  - At type σ → τ: pointwise conjunction λx.(f x ∧ g x)

This is the semantic denotation of "and" at any conjoinable type.
-/
def genConj (τ : Ty) (m : Model) : m.interpTy τ → m.interpTy τ → m.interpTy τ :=
  match τ with
  | .t => fun x y => x && y
  | .e => fun x _ => x  -- Not conjoinable; return first argument
  | .s => fun x _ => x  -- Not conjoinable (worlds); return first argument
  | .fn _ τ' => fun f g => fun x => genConj τ' m (f x) (g x)

/--
Generalized disjunction: the meaning of "or" at any type.
-/
def genDisj (τ : Ty) (m : Model) : m.interpTy τ → m.interpTy τ → m.interpTy τ :=
  match τ with
  | .t => fun x y => x || y
  | .e => fun x _ => x  -- Not conjoinable; return first argument
  | .s => fun x _ => x  -- Not conjoinable (worlds); return first argument
  | .fn _ τ' => fun f g => fun x => genDisj τ' m (f x) (g x)

-- ============================================================================
-- Theorems: Type-Specific Behavior
-- ============================================================================

/-- At type t, genConj is Boolean conjunction -/
theorem genConj_at_t (m : Model) (p q : Bool) :
    genConj .t m p q = (p && q) := rfl

/-- At type e→t (properties), genConj is pointwise conjunction -/
theorem genConj_at_et (m : Model) (f g : m.Entity → Bool) :
    genConj (.fn .e .t) m f g = fun x => f x && g x := rfl

/-- At type e→e→t (relations), genConj is doubly pointwise -/
theorem genConj_at_eet (m : Model) (f g : m.Entity → m.Entity → Bool) :
    genConj (.fn .e (.fn .e .t)) m f g = fun x y => f x y && g x y := rfl

-- ============================================================================
-- Theorems: Algebraic Properties
-- ============================================================================

/-- Generalized conjunction is commutative at type t -/
theorem genConj_comm_t (m : Model) (p q : Bool) :
    genConj .t m p q = genConj .t m q p := by
  simp [genConj, Bool.and_comm]

/-- Generalized conjunction is associative at type t -/
theorem genConj_assoc_t (m : Model) (p q r : Bool) :
    genConj .t m (genConj .t m p q) r = genConj .t m p (genConj .t m q r) := by
  simp [genConj, Bool.and_assoc]

/-- Generalized disjunction is commutative at type t -/
theorem genDisj_comm_t (m : Model) (p q : Bool) :
    genDisj .t m p q = genDisj .t m q p := by
  simp [genDisj, Bool.or_comm]

-- ============================================================================
-- Theorems: P&R Key Facts
-- ============================================================================

/-!
## Partee & Rooth (1983) Key Facts

These theorems formalize the main results from the paper:

- **Fact 6a**: `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]` (pointwise definition)
- **Fact 6b**: `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)` (distribution over application)
- **Fact 6c**: `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]` (lambda distribution)
-/

/-- **Fact 6a**: Generalized conjunction IS pointwise for function types.
    `φ ∩ ψ = λz[φ(z) ∩ ψ(z)]`

    This is true by definition of `genConj` at function types. -/
theorem genConj_pointwise {m : Model} {σ τ : Ty}
    (f g : m.interpTy (σ ⇒ τ)) :
    genConj (σ ⇒ τ) m f g = fun x => genConj τ m (f x) (g x) := rfl

/-- **Fact 6b**: Generalized conjunction distributes over function application.
    `[φ ∩ ψ](α) = φ(α) ∩ ψ(α)`

    Applying the conjoined function equals conjoining the applications. -/
theorem genConj_distributes_over_app {m : Model} {σ τ : Ty}
    (f g : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    genConj (σ ⇒ τ) m f g x = genConj τ m (f x) (g x) := rfl

/-- **Fact 6c**: Lambda distribution for conjunction.
    `λv.φ ∩ λv.ψ = λv[φ ∩ ψ]`

    For extensionally equal functions, this is captured by genConj's definition.
    More precisely: if we have φ, ψ : τ that may contain a free variable v,
    then forming λv.φ and λv.ψ (both of type σ → τ) and conjoining gives
    the same result as conjoining φ and ψ under the abstraction.

    This theorem states it for the case where φ(v) and ψ(v) are already
    curried as functions f and g. -/
theorem genConj_lambda_distribution {m : Model} {σ τ : Ty}
    (f g : m.interpTy σ → m.interpTy τ) :
    genConj (σ ⇒ τ) m f g = fun v => genConj τ m (f v) (g v) := rfl

/-- **Fact 6b for disjunction**: Disjunction also distributes over application. -/
theorem genDisj_distributes_over_app {m : Model} {σ τ : Ty}
    (f g : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    genDisj (σ ⇒ τ) m f g x = genDisj τ m (f x) (g x) := rfl

/-- **Fact 6c for disjunction**: Lambda distribution for disjunction. -/
theorem genDisj_lambda_distribution {m : Model} {σ τ : Ty}
    (f g : m.interpTy σ → m.interpTy τ) :
    genDisj (σ ⇒ τ) m f g = fun v => genDisj τ m (f v) (g v) := rfl

-- ============================================================================
-- Type-Raising (for coordinating non-conjoinable types)
-- ============================================================================

/-- Type-raise an entity to a generalized quantifier.
    e → <<e,t>,t>
    john ↦ λP.P(john)

    This allows coordination of entities at the GQ level. -/
def typeRaise {m : Model} (e : m.interpTy .e) : m.interpTy ((.e ⇒ .t) ⇒ .t) :=
  fun p => p e

/-- Coordinated entities via type-raising.
    "John and Mary" = λP. P(john) ∧ P(mary) -/
def coordEntities {m : Model} (e1 e2 : m.interpTy .e) : m.interpTy ((.e ⇒ .t) ⇒ .t) :=
  genConj ((.e ⇒ .t) ⇒ .t) m (typeRaise e1) (typeRaise e2)

/-- Type-raising preserves reference: GQ(john)(P) = P(john) -/
theorem typeRaise_preserves {m : Model} (e : m.interpTy .e) (p : m.interpTy (.e ⇒ .t)) :
    typeRaise e p = p e := rfl

/-- Coordinated entities: (john ∧ mary)(P) = P(john) ∧ P(mary) -/
theorem coordEntities_both_satisfy {m : Model} (e1 e2 : m.interpTy .e)
    (p : m.interpTy (.e ⇒ .t)) :
    coordEntities e1 e2 p = (p e1 && p e2) := rfl

-- ============================================================================
-- Example: Conjoining Properties
-- ============================================================================

/-
"tall and happy" at type e→t:

⟦tall and happy⟧ = genConj (e→t) ⟦tall⟧ ⟦happy⟧
                 = λx. ⟦tall⟧(x) ∧ ⟦happy⟧(x)

Applied to John:
⟦tall and happy⟧(j) = ⟦tall⟧(j) ∧ ⟦happy⟧(j)
-/

-- Define sample predicates in the toy model
def tall_sem : toyModel.interpTy (.fn .e .t) :=
  fun x => match x with
    | .john => true
    | .mary => false
    | _ => false

def happy_sem : toyModel.interpTy (.fn .e .t) :=
  fun x => match x with
    | .john => true
    | .mary => true
    | _ => false

-- Conjoin them
def tall_and_happy : toyModel.interpTy (.fn .e .t) :=
  genConj (.fn .e .t) toyModel tall_sem happy_sem

-- Test: John is tall and happy
#eval tall_and_happy ToyEntity.john  -- true (tall ∧ happy)

-- Test: Mary is NOT tall and happy
#eval tall_and_happy ToyEntity.mary  -- false (¬tall ∧ happy = false)

/-- The conjoined predicate is pointwise conjunction -/
theorem tall_and_happy_is_pointwise :
    tall_and_happy = fun x => tall_sem x && happy_sem x := rfl

-- ============================================================================
-- Limitations: Non-Boolean Coordination
-- ============================================================================

/-
## What Generalized Conjunction Does NOT Handle

Partee & Rooth discuss several cases requiring special treatment:

1. **Collective readings** (Appendix B):
   "John and Mary met" ≠ "John met and Mary met"

   This requires plural individuals / Link's algebra, not pointwise conjunction.
   The "and" here creates a group entity, not a conjoined predicate.

2. **Non-Boolean coordination** (Section VI):
   "John and Mary are a happy couple"

   Predicates like "be a couple" take plural arguments, not conjoined individuals.

3. **Scope interactions**:
   "Every student failed or got a D"

   May have readings not predicted by simple generalized conjunction.

These cases require extensions beyond the basic schema:
- Plural/group formation (Link 1983)
- Type-shifting rules (Appendix A)
- Scope mechanisms

For now, we formalize the core distributive readings where pointwise
conjunction applies straightforwardly.
-/

-- ============================================================================
-- Integration with CCG
-- ============================================================================

/-
## How CCG Uses Generalized Conjunction

CCG contributes the SYNTAX:
- Type-raising makes "John likes" a constituent of category S/NP
- Composition builds S/NP from S/(S\NP) and (S\NP)/NP

Montague contributes the SEMANTICS:
- S/NP has type e → t
- Generalized conjunction gives: ⟦John likes⟧ ∧_{e→t} ⟦Mary hates⟧

The CCG derivation:
  John likes : S/NP    and    Mary hates : S/NP
              └──────── coordination ────────┘
                     S/NP
                       │
                     beans : NP
                       ↓
                       S

The semantic interpretation:
  ⟦John likes and Mary hates⟧ = genConj (e→t) ⟦John likes⟧ ⟦Mary hates⟧
                              = λx. likes(x,j) ∧ hates(x,m)

  ⟦John likes and Mary hates beans⟧ = likes(b,j) ∧ hates(b,m)

CCG's type-raising + composition creates the S/NP constituents.
Montague's generalized conjunction provides their semantic combination.
-/

-- ============================================================================
-- Type-Polymorphic Schemata (Model-independent)
-- ============================================================================

/-!
## Type-Polymorphic Coordination

These definitions work without a Model, using Lean's type polymorphism directly.
Useful for abstract reasoning about coordination at arbitrary types.

The G&S (1984) schemata generalize Partee & Rooth's approach.
-/

/-- Pointwise conjunction for functions (model-independent).
    CONJ_{<a,b>}(f, g) = λx. CONJ_b(f(x), g(x)) -/
def conjFunc {A B : Type*} (conjB : B → B → B) (f g : A → B) : A → B :=
  fun x => conjB (f x) (g x)

/-- Pointwise disjunction for functions (model-independent). -/
def disjFunc {A B : Type*} (disjB : B → B → B) (f g : A → B) : A → B :=
  fun x => disjB (f x) (g x)

/-- CONJ distributes over function application. -/
theorem conjFunc_distributes {A B : Type*} (conjB : B → B → B)
    (f g : A → B) (x : A) :
    conjFunc conjB f g x = conjB (f x) (g x) := rfl

/-- DISJ distributes over function application. -/
theorem disjFunc_distributes {A B : Type*} (disjB : B → B → B)
    (f g : A → B) (x : A) :
    disjFunc disjB f g x = disjB (f x) (g x) := rfl

-- ============================================================================
-- INCL Schema: Generalized Inclusion (G&S 1984)
-- ============================================================================

/-!
## INCL Schema

The subset/inclusion relation, generalized over conjoinable types:
- If τ = t: INCL(p, q) = p → q (material implication)
- If τ = <a, b>: INCL_τ(f, g) = ∀x. INCL_b(f(x), g(x))
-/

/-- Inclusion at type t: p ⊆ q iff p → q -/
def inclT (p q : Bool) : Bool := !p || q

/-- Pointwise inclusion for functions: f ⊆ g iff ∀x. f(x) ⊆ g(x) -/
def inclFunc {A : Type*} (f g : A → Bool) (domain : List A) : Bool :=
  domain.all fun x => inclT (f x) (g x)

/-- Inclusion for properties: P ⊆ Q iff ∀x. P(x) → Q(x) -/
def inclProperty {E : Type*} (p q : E → Bool) (entities : List E) : Bool :=
  inclFunc p q entities

/-- Inclusion for propositions: P ⊆ Q iff ∀w. P(w) → Q(w) -/
def inclProposition {W : Type*} (p q : W → Bool) (worlds : List W) : Bool :=
  inclFunc p q worlds

-- ============================================================================
-- QUANT Schema: Generalized Quantification (G&S 1984)
-- ============================================================================

/-!
## QUANT Schema

Quantifiers over conjoinable types. The key insight: quantifiers are
"generalized conjunctions/disjunctions" over a domain:
- ∃ = DISJ over all elements
- ∀ = CONJ over all elements
-/

/-- Existential quantification over a domain: ∃x∈D. P(x) -/
def existsOver {A : Type*} (domain : List A) (p : A → Bool) : Bool :=
  domain.any p

/-- Universal quantification over a domain: ∀x∈D. P(x) -/
def forallOver {A : Type*} (domain : List A) (p : A → Bool) : Bool :=
  domain.all p

/-- Existential = disjunction over all domain elements -/
theorem exists_is_disj {A : Type*} (domain : List A) (p : A → Bool) :
    existsOver domain p = (domain.map p).any id := by
  simp [existsOver, List.any_map]

/-- Universal = conjunction over all domain elements -/
theorem forall_is_conj {A : Type*} (domain : List A) (p : A → Bool) :
    forallOver domain p = (domain.map p).all id := by
  simp [forallOver, List.all_map]

/-- Universal and existential are duals via negation. -/
theorem forall_exists_duality {A : Type*} (domain : List A) (p : A → Bool) :
    forallOver domain p = !existsOver domain (fun x => !p x) := by
  simp [forallOver, existsOver, List.all_eq_not_any_not]

end Montague.Conjunction
