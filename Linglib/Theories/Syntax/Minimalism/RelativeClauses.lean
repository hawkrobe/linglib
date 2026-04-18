/-
# Relative Clause Semantics: A Worked Example

Demonstrates the full machinery from Interfaces/SyntaxSemantics/Minimalism/Interface.lean
with a concrete linguistic example: "the book that John read _"

## The Derivation

```
                  DP
                 / \
               the NP
                    / \
                  book CP
                       / \
                      Op₁ IP
                          / \
                       John VP
                             / \
                           read t₁
```

## Semantic Composition

1. **Trace interpretation**: ⟦t₁⟧^g = g(1)
2. **VP composition**: ⟦read t₁⟧^g = read(g(1)) (applied to subject later)
3. **IP composition**: ⟦John read t₁⟧^g = read(j, g(1))
4. **Predicate Abstraction at CP**: ⟦Op₁ [John read t₁]⟧^g = λx. read(j, x)
5. **Predicate Modification with head noun**: λx. book(x) ∧ read(j, x)
6. **Definite description**: ιx[book(x) ∧ read(j,x)]

-/

import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalism.Interface
import Linglib.Theories.Syntax.Minimalism.Core.Basic

namespace Minimalism.RelativeClauses

open Core.IntensionalLogic Core.IntensionalLogic.Variables Semantics.Composition.Modification
open Minimalism.Semantics
open Minimalism

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
def readModel : Frame := {
  Entity := ReadEntity
  Index := Unit
}

-- ============================================================================
-- Lexical Semantics
-- ============================================================================

open ReadEntity

/-- "John" denotes the entity john -/
def john_sem : readModel.Denot .e := john

/-- "Mary" denotes the entity mary -/
def mary_sem : readModel.Denot .e := mary

/-- "book" is true of book1 and book2 -/
def book_sem : readModel.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .book1 => True
    | .book2 => True
    | _ => False

/-- "read" as a relation: John read book1, Mary read book2 -/
def read_sem : readModel.Denot (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .book1 => True      -- John read book1
    | .mary, .book2 => True      -- Mary read book2
    | .mary, .newspaper => True  -- Mary also read the newspaper
    | _, _ => False

instance : DecidablePred book_sem :=
  λ x => match x with
    | .book1 | .book2 => isTrue trivial
    | .john | .mary | .newspaper => isFalse not_false

instance : ∀ (obj : ReadEntity), DecidablePred (read_sem obj)
  | .book1 => λ subj => match subj with
    | .john => isTrue trivial
    | .mary | .book1 | .book2 | .newspaper => isFalse not_false
  | .book2 => λ subj => match subj with
    | .mary => isTrue trivial
    | .john | .book1 | .book2 | .newspaper => isFalse not_false
  | .newspaper => λ subj => match subj with
    | .mary => isTrue trivial
    | .john | .book1 | .book2 | .newspaper => isFalse not_false
  | .john | .mary => λ subj => match subj with
    | .john | .mary | .book1 | .book2 | .newspaper => isFalse not_false

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
theorem ip_meaning_correct (g : Core.Assignment readModel.Entity) :
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
theorem cp_meaning_correct (g : Core.Assignment readModel.Entity) (x : ReadEntity) :
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
theorem np_meaning_correct (g : Core.Assignment readModel.Entity) (x : ReadEntity) :
    np_bookThatJohnRead g x = (book_sem x ∧ read_sem x john) := by
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
def the_book_that_john_read (_g : Core.Assignment readModel.Entity) : Option ReadEntity :=
  iota allEntities (λ x => decide (book_sem x ∧ read_sem x john))

/--
Main theorem: "the book that John read" denotes book1

This shows the compositional derivation yields the correct result:
- book1 is a book
- John read book1
- No other book was read by John
- Therefore ιx[book(x) ∧ read(j,x)] = book1
-/
theorem the_book_correct (g : Core.Assignment readModel.Entity) :
    the_book_that_john_read g = some ReadEntity.book1 := by
  simp only [the_book_that_john_read]
  native_decide

-- ============================================================================
-- Properties of the Derivation
-- ============================================================================

/--
The relative clause creates the right predicate:
it's true of exactly the things John read.
-/
theorem relClause_extension (g : Core.Assignment readModel.Entity) :
    (cp_relativeClause g book1) ∧
    (¬ cp_relativeClause g book2) ∧
    (¬ cp_relativeClause g newspaper) := by
  simp only [cp_meaning_correct, read_sem]
  exact ⟨trivial, not_false_eq_true ▸ trivial, not_false_eq_true ▸ trivial⟩

/--
The modified NP is true of exactly book1.
-/
theorem np_extension (g : Core.Assignment readModel.Entity) :
    (np_bookThatJohnRead g book1) ∧
    (¬ np_bookThatJohnRead g book2) ∧
    (¬ np_bookThatJohnRead g john) := by
  simp only [np_meaning_correct, book_sem, read_sem]
  exact ⟨⟨trivial, trivial⟩, fun ⟨_, h⟩ => h, fun ⟨h, _⟩ => h⟩

/--
Assignment independence: the final NP meaning doesn't depend on
the assignment (all variables are bound).
-/
theorem np_assignment_independent (g₁ g₂ : Core.Assignment readModel.Entity) :
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
theorem np_formulations_equiv (g : Core.Assignment readModel.Entity) :
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
the trace created via `mkTrace 1` is interpreted via `interpTrace 1`.
-/
def traceExample : SyntacticObject := mkTrace 1

/--
Extracting the trace index from a syntactic object.
-/
theorem trace_example_has_index : getTraceIndex traceExample = some 1 := rfl

end Minimalism.RelativeClauses
