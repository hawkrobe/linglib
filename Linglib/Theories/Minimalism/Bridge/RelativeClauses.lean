/-
# Relative Clause Semantics: A Worked Example

Demonstrates the full machinery from Minimalism/Semantics/Interface.lean
with a concrete linguistic example: "the book that John read _"

## The Derivation

```
                  DP
                 /  \
               the   NP
                    /  \
                  book  CP
                       /  \
                      Op₁  IP
                          /  \
                       John   VP
                             /  \
                           read  t₁
```

## Semantic Composition

1. **Trace interpretation**: ⟦t₁⟧^g = g(1)
2. **VP composition**: ⟦read t₁⟧^g = read(g(1))  (applied to subject later)
3. **IP composition**: ⟦John read t₁⟧^g = read(j, g(1))
4. **Predicate Abstraction at CP**: ⟦Op₁ [John read t₁]⟧^g = λx. read(j, x)
5. **Predicate Modification with head noun**: λx. book(x) ∧ read(j, x)
6. **Definite description**: ιx[book(x) ∧ read(j,x)]

## References

- Heim & Kratzer (1998) "Semantics in Generative Grammar", Ch. 7, 8
-/

import Linglib.Theories.Minimalism.Bridge.Interface
import Linglib.Theories.Minimalism.Core.Basic

namespace Minimalism.Bridge.RelativeClauses

open TruthConditional TruthConditional.Variables TruthConditional.Modification
open Minimalism.Semantics

-- ============================================================================
-- Example Model: Reading Scenario
-- ============================================================================

/--
A model for the "book that John read" example.

Domain: john, mary, book1, book2, newspaper
-/
inductive ReadEntity where
  | john
  | mary
  | book1      -- the book John read
  | book2      -- a book John didn't read
  | newspaper  -- something that isn't a book
  deriving Repr, DecidableEq, Inhabited

/-- The model for our example -/
def readModel : Model := {
  Entity := ReadEntity
  decEq := inferInstance
}

-- ============================================================================
-- Lexical Semantics
-- ============================================================================

open ReadEntity

/-- "John" denotes the entity john -/
def john_sem : readModel.interpTy .e := john

/-- "Mary" denotes the entity mary -/
def mary_sem : readModel.interpTy .e := mary

/-- "book" is true of book1 and book2 -/
def book_sem : readModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .book1 => true
    | .book2 => true
    | _ => false

/-- "read" as a relation: John read book1, Mary read book2 -/
def read_sem : readModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .book1 => true      -- John read book1
    | .mary, .book2 => true      -- Mary read book2
    | .mary, .newspaper => true  -- Mary also read the newspaper
    | _, _ => false

-- ============================================================================
-- Building the Relative Clause: "that John read _"
-- ============================================================================

/--
The trace in object position: t₁

This represents the gap in "that John read _".
The trace has index 1.
-/
def trace1 : DenotG readModel .e := interpTrace 1

/--
VP meaning: "read t₁"

⟦read t₁⟧^g = λy. read(g(1))(y) = λy. read(y, g(1))

Note: Our read_sem takes object first, then subject.
So "read t₁" is the function waiting for a subject.
-/
def vp_readTrace : DenotG readModel (.e ⇒ .t) :=
  λ g => λ subj => read_sem (trace1 g) subj

/--
IP meaning: "John read t₁"

⟦John read t₁⟧^g = read(j, g(1))
-/
def ip_johnReadTrace : DenotG readModel .t :=
  applyG vp_readTrace (constDenot john_sem)

/--
Verify IP meaning: it's true iff the trace's value was read by John
-/
theorem ip_meaning_correct (g : Assignment readModel) :
    ip_johnReadTrace g = read_sem (g 1) john := rfl

/--
CP meaning via Predicate Abstraction: "Op₁ [John read t₁]"

⟦Op₁ [John read t₁]⟧^g = λx. ⟦John read t₁⟧^{g[1↦x]}
                       = λx. read(j, x)

This creates a predicate "things that John read".
-/
def cp_relativeClause : DenotG readModel (.e ⇒ .t) :=
  predicateAbstraction 1 ip_johnReadTrace

/--
Verify CP meaning: λx. read(j, x)
-/
theorem cp_meaning_correct (g : Assignment readModel) (x : ReadEntity) :
    cp_relativeClause g x = read_sem x john := by
  simp only [cp_relativeClause, predicateAbstraction, lambdaAbsG,
             ip_johnReadTrace, applyG, vp_readTrace, constDenot, john_sem,
             trace1, interpTrace, interpPronoun, update_same]

-- ============================================================================
-- Combining with Head Noun: "book that John read"
-- ============================================================================

/-- Head noun "book" as assignment-relative (trivially constant) -/
def book_denot : DenotG readModel (.e ⇒ .t) := constDenot book_sem

/--
NP meaning: "book that John read _"

Via Predicate Modification:
⟦book [that John read _]⟧ = λx. book(x) ∧ read(j, x)
-/
def np_bookThatJohnRead : DenotG readModel (.e ⇒ .t) :=
  relativePM 1 book_denot ip_johnReadTrace

/--
The NP meaning is the intersection of "book" and "things John read"
-/
theorem np_meaning_correct (g : Assignment readModel) (x : ReadEntity) :
    np_bookThatJohnRead g x = (book_sem x && read_sem x john) := by
  simp only [np_bookThatJohnRead, relativePM, predicateModification,
             book_denot, constDenot, predicateAbstraction, lambdaAbsG,
             ip_johnReadTrace, applyG, vp_readTrace, trace1, john_sem,
             interpTrace, interpPronoun, update_same]

-- ============================================================================
-- The Definite Description: "the book that John read"
-- ============================================================================

/--
The iota operator: ιx.P(x)

Returns the unique x satisfying P, if one exists.
For computational simplicity, we search through a list of candidates.

In a proper treatment, this would use Hilbert's ε or require
a uniqueness presupposition. Here we use Option to handle
non-existence or non-uniqueness.
-/
def iota (candidates : List ReadEntity) (p : ReadEntity → Bool) : Option ReadEntity :=
  match candidates.filter p with
  | [x] => some x  -- exactly one satisfying element
  | _ => none      -- zero or multiple: presupposition failure

/-- All entities in our domain -/
def allEntities : List ReadEntity := [.john, .mary, .book1, .book2, .newspaper]

/--
"the book that John read" denotes book1

This is the unique entity satisfying:
  book(x) ∧ read(j, x)
-/
def the_book_that_john_read (g : Assignment readModel) : Option ReadEntity :=
  iota allEntities (np_bookThatJohnRead g)

/--
Main theorem: "the book that John read" denotes book1

This shows the compositional derivation yields the correct result:
- book1 is a book
- John read book1
- No other book was read by John
- Therefore ιx[book(x) ∧ read(j,x)] = book1
-/
theorem the_book_correct (g : Assignment readModel) :
    the_book_that_john_read g = some ReadEntity.book1 := by
  simp only [the_book_that_john_read, iota, allEntities, List.filter]
  -- The filter keeps only elements where book(x) ∧ read(j,x)
  simp only [np_meaning_correct]
  -- Check each entity:
  -- john: book(john) = false, so false && _ = false
  -- mary: book(mary) = false
  -- book1: book(book1) = true, read(john, book1) = true, so true
  -- book2: book(book2) = true, read(john, book2) = false, so false
  -- newspaper: book(newspaper) = false
  native_decide

-- ============================================================================
-- Properties of the Derivation
-- ============================================================================

/--
The relative clause creates the right predicate:
it's true of exactly the things John read.
-/
theorem relClause_extension (g : Assignment readModel) :
    (cp_relativeClause g book1 = true) ∧
    (cp_relativeClause g book2 = false) ∧
    (cp_relativeClause g newspaper = false) := by
  simp only [cp_meaning_correct, read_sem, and_self]

/--
The modified NP is true of exactly book1.
-/
theorem np_extension (g : Assignment readModel) :
    (np_bookThatJohnRead g book1 = true) ∧
    (np_bookThatJohnRead g book2 = false) ∧
    (np_bookThatJohnRead g john = false) := by
  simp only [np_meaning_correct, book_sem, read_sem, Bool.and_self,
             Bool.and_false, and_self]

/--
Assignment independence: the final NP meaning doesn't depend on
the assignment (all variables are bound).
-/
theorem np_assignment_independent (g₁ g₂ : Assignment readModel) :
    np_bookThatJohnRead g₁ = np_bookThatJohnRead g₂ := by
  funext x
  simp only [np_meaning_correct]

-- ============================================================================
-- Alternative: Using relativePM Directly
-- ============================================================================

/--
An equivalent formulation using the relativePM combinator directly.
This shows the interface abstracts over the composition steps.
-/
def np_bookThatJohnRead' : DenotG readModel (.e ⇒ .t) :=
  relativePM 1 (constDenot book_sem) (applyG (λ g subj => read_sem (g 1) subj) (constDenot john))

/-- The two formulations are equivalent -/
theorem np_formulations_equiv (g : Assignment readModel) :
    np_bookThatJohnRead g = np_bookThatJohnRead' g := by
  funext x
  simp only [np_bookThatJohnRead, np_bookThatJohnRead', relativePM,
             predicateModification, book_denot, constDenot, john_sem,
             predicateAbstraction, lambdaAbsG, ip_johnReadTrace,
             applyG, vp_readTrace, trace1, interpTrace, interpPronoun,
             update_same]

-- ============================================================================
-- Connection to Syntactic Structure
-- ============================================================================

/--
The syntactic structure with a trace.

This shows how the semantic derivation corresponds to the syntax:
the trace in SynObj.trace 1 is interpreted via interpTrace 1.

Note: We use a simplified representation here. The key insight is that
`SynObj.trace n` in the syntax corresponds to `interpTrace n` in semantics.
-/
def traceExample : SynObj := .trace 1

/--
Extracting the trace index from a syntactic object.
-/
def getTraceIndex : SynObj → Option ℕ
  | .trace n => some n
  | .set α β _ => getTraceIndex α <|> getTraceIndex β
  | .lex _ _ => none

theorem trace_example_has_index : getTraceIndex traceExample = some 1 := rfl

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Demonstrates

### The Full Pipeline
1. **Lexical entries**: book_sem, read_sem, john_sem
2. **Trace interpretation**: interpTrace 1 yields g(1)
3. **Predicate Abstraction**: λ-binds the trace at CP
4. **Predicate Modification**: intersects with head noun
5. **Definite description**: iota selects the unique satisfier

### Theorems
- `cp_meaning_correct`: the relative clause means λx.read(j,x)
- `np_meaning_correct`: the modified NP means λx.book(x) ∧ read(j,x)
- `the_book_correct`: ιx[book(x) ∧ read(j,x)] = book1
- `np_assignment_independent`: bound variables don't leak

### Architectural Note

This module uses:
- `Minimalism.Core.Basic` for syntactic structures with traces
- `Minimalism.Bridge.Interface` for trace interpretation
- `TruthConditional.Variables` for assignments and λ-abstraction
- `TruthConditional.Modification` for Predicate Modification

The derivation shows how Minimalist LF structures (with traces and
movement) receive compositional semantic interpretations following
Heim & Kratzer's framework.
-/

end Minimalism.Bridge.RelativeClauses
