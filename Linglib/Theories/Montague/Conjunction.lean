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
  | .fn _ τ => τ.isConjoinable

-- Examples
example : Ty.isConjoinable .t = true := rfl           -- sentences
example : Ty.isConjoinable .e = false := rfl          -- entities can't be conjoined
example : Ty.isConjoinable (.fn .e .t) = true := rfl    -- properties: "tall and happy"
example : Ty.isConjoinable (.fn .e (.fn .e .t)) = true := rfl -- relations
example : Ty.isConjoinable (.fn .e .e) = false := rfl   -- functions to entities

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
  | .fn _ τ' => fun f g => fun x => genConj τ' m (f x) (g x)

/--
Generalized disjunction: the meaning of "or" at any type.
-/
def genDisj (τ : Ty) (m : Model) : m.interpTy τ → m.interpTy τ → m.interpTy τ :=
  match τ with
  | .t => fun x y => x || y
  | .e => fun x _ => x
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

end Montague.Conjunction
