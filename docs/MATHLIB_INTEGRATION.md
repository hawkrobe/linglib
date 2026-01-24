# Mathlib Integration in Linglib

This document describes how linglib uses Mathlib to avoid reinventing the wheel.

## What We Use from Mathlib

### 1. Set Theory (`Mathlib.Data.Set.Basic`)

Used in `Montague/Basic.lean` for characteristic functions:

```lean
/-- Convert a predicate (e → t) to a Set (the extension) -/
def predicateToSet {m : Model} (p : m.interpTy (.e ⇒ .t)) : Set m.Entity :=
  { x | p x = true }

/-- The extension of "sleeps" is {john} -/
theorem sleeps_extension :
    predicateToSet sleeps_sem = {ToyEntity.john} := by
  ext x
  simp only [predicateToSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  cases x <;> simp [sleeps_sem]
```

**Benefits:**
- Proper set-builder notation `{ x | P x }`
- Set membership lemmas (`Set.mem_setOf_eq`, `Set.mem_singleton_iff`)
- Clean proofs via `simp` with set lemmas

### 2. Fintype (`Mathlib.Data.Fintype.Basic`)

Imported but we use a custom `FiniteModel` class for computability.
Mathlib's `Fintype` provides theoretical foundation but `Finset.toList`
isn't always computable in the way we need for `#eval`.

## What We Keep Custom

### 1. Semantic Types (`Ty`)
Domain-specific: `e`, `t`, `σ → τ`

### 2. Models and Interpretation
Linguistic-specific: `Model`, `interpTy`

### 3. FiniteModel Class
Custom for computability:
```lean
class FiniteModel (m : Model) where
  elements : List m.Entity
  complete : ∀ x : m.Entity, x ∈ elements
```

### 4. Syntactic Theories
CCG, HPSG, Minimalism, etc. - no Mathlib equivalent

### 5. Lexical Semantics
Word meanings are domain-specific

## Trade-offs

### Using Mathlib
**Pros:**
- Proper `Set` type with rich lemma library
- Standard conventions
- Proof automation via `simp`

**Cons:**
- Larger build (663 jobs vs 62 without Mathlib)
- Some computability restrictions with `Fintype`

### Design Decision
We use Mathlib's `Set` for theoretical elegance in proofs,
but keep custom computable structures for evaluation (`#eval`).

## How Mathlib Improves Our Code

### Before (without Mathlib)
```lean
-- Had to avoid Set, use predicates directly
def inExtension (p : Entity → Bool) (x : Entity) : Bool := p x
```

### After (with Mathlib)
```lean
-- Can use proper Set notation and proofs
def predicateToSet (p : Entity → Bool) : Set Entity := { x | p x = true }

theorem sleeps_extension : predicateToSet sleeps_sem = {john} := by
  ext x; simp [predicateToSet, sleeps_sem]; cases x <;> simp
```

The Mathlib version is more mathematically natural and has cleaner proofs.
