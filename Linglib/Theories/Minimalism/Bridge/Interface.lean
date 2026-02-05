/-
# Minimalism-Montague Semantics Interface

Traces left by movement are interpreted as variables bound by
λ-abstraction at the landing site (Heim and Kratzer 1998).

## Architecture

This module bridges Minimalist syntax and Montague semantics:

```
Minimalism/Basic.lean          Montague/Variables.lean
       ↓                              ↓
    SynObj with traces         Assignment functions
              ↘                    ↙
         Minimalism/Semantics/Interface.lean
                     ↓
         interpTrace: traces → g(n)
         predicateAbstraction: λ-bind at landing site
```

## Rules

1. Trace Interpretation: A trace t_n is interpreted as g(n)
   ⟦t_n⟧^g = g(n)

2. Predicate Abstraction: At the landing site of movement,
   λ-abstract over the trace's index
   ⟦[CP Op_n ... t_n ...]⟧^g = λx. ⟦... t_n ...⟧^{g[n↦x]}

## Why This Lives in Minimalism/

This interface is specific to movement-based syntax because:
- Traces are a Minimalist construct (SynObj.trace in Basic.lean)
- The binding relationship between filler and gap requires LF movement
- Other frameworks (CCG, HPSG) handle long-distance dependencies differently

## References

- Heim & Kratzer (1998) "Semantics in Generative Grammar", Ch. 5, 7
- Chomsky (1995) "The Minimalist Program"
-/

import Linglib.Theories.Minimalism.Core.Basic
import Linglib.Theories.Montague.Variables
import Linglib.Theories.Montague.Modification

namespace Minimalism.Semantics

open Montague Montague.Variables Montague.Modification

-- ============================================================================
-- Trace Interpretation (H&K Ch. 5, 7)
-- ============================================================================

/--
Interpret a trace as a variable: ⟦t_n⟧^g = g(n)

Heim and Kratzer's trace interpretation rule: traces left by movement
are semantically identical to pronouns. Both are interpreted by looking up
the assignment function at the appropriate index.

The trace index n should match the index of the binder (λ-abstraction)
at the landing site of movement.
-/
def interpTrace {m : Model} (n : ℕ) : DenotG m .e :=
  interpPronoun n

/-- Traces and pronouns have the same interpretation -/
theorem interpTrace_eq_interpPronoun {m : Model} (n : ℕ) :
    interpTrace (m := m) n = interpPronoun n := rfl

-- ============================================================================
-- Predicate Abstraction (H&K Ch. 7)
-- ============================================================================

/--
Predicate Abstraction: λ-bind at the landing site of movement.

When a moved element lands at a position, it creates a λ-abstractor
that binds the trace it left behind:

  ⟦[XP Op_n YP]⟧^g = λx. ⟦YP⟧^{g[n↦x]}

where Op_n is the moved operator and YP contains the trace t_n.

This rule creates a predicate (type ⟨e,t⟩) from a proposition (type t)
by abstracting over the trace's index.
-/
def predicateAbstraction {m : Model} (n : ℕ) (body : DenotG m .t)
    : DenotG m (.e ⇒ .t) :=
  lambdaAbsG n body

/--
Generalized predicate abstraction for any result type.

This handles cases like "the book that John said Mary read _"
where the trace is embedded and the result may need further composition.
-/
def predicateAbstractionGen {m : Model} {τ : Ty} (n : ℕ) (body : DenotG m τ)
    : DenotG m (.e ⇒ τ) :=
  lambdaAbsG n body

-- ============================================================================
-- Composition of Movement Chains
-- ============================================================================

/--
Interpret a simple movement configuration:
- A trace t_n in some position
- An operator binding that trace from a higher position

Returns the predicate λx. ⟦body(t_n := x)⟧
-/
def interpMovement {m : Model} (n : ℕ)
    (bodyWithTrace : DenotG m .t) : DenotG m (.e ⇒ .t) :=
  predicateAbstraction n bodyWithTrace

/--
The binding relationship: predicate abstraction at index n binds traces at n.

When we apply a predicate-abstracted meaning to an entity,
that entity becomes the value of all traces with the same index.
-/
theorem binding_correct {m : Model} (n : ℕ) (body : DenotG m .t)
    (x : m.Entity) (g : Assignment m)
    : (predicateAbstraction n body g) x = body (g[n ↦ x]) := rfl

-- ============================================================================
-- Connection to Syntactic Objects
-- ============================================================================

/--
A semantic interpretation context pairs a model with an assignment.
-/
structure InterpContext (m : Model) where
  assignment : Assignment m

/--
The semantic type corresponding to a syntactic object.

- Traces have type e (they denote entities)
- Lexical items and merged structures need lexical lookup
-/
def synObjSemanticType : SynObj → Option Ty
  | .trace _ => some .e
  | .lex _ _ => none  -- depends on lexical entry
  | .set _ _ _ => none  -- depends on composition

/--
Interpret a trace in a syntactic object.

This extracts the trace index and interprets it via the assignment.
-/
def interpSynObjTrace {m : Model} : SynObj → Option (DenotG m .e)
  | .trace n => some (interpTrace n)
  | _ => none

-- ============================================================================
-- Theorems about Movement Interpretation
-- ============================================================================

/--
Identity of indiscernibles for traces:
traces with the same index have the same interpretation.
-/
theorem trace_index_determines_meaning {m : Model} (n : ℕ)
    : interpTrace (m := m) n = interpTrace n := rfl

/--
Different indices yield independent interpretations.
-/
theorem trace_indices_independent {m : Model} (n₁ n₂ : ℕ) (h : n₁ ≠ n₂)
    (x : m.Entity) (g : Assignment m)
    : interpTrace n₁ (g[n₂ ↦ x]) = interpTrace n₁ g := by
  simp only [interpTrace, interpPronoun]
  exact update_other g n₂ n₁ x h

/--
Predicate abstraction creates the right binding:
the abstracted variable is bound, other variables are free.
-/
theorem abstraction_binds_correct_variable {m : Model} (n : ℕ)
    (g : Assignment m) (x : m.Entity)
    : interpTrace n (g[n ↦ x]) = x := by
  simp only [interpTrace, interpPronoun]
  exact update_same g n x

-- ============================================================================
-- Integration with Predicate Modification
-- ============================================================================

/--
Relative clause interpretation combines predicate abstraction with PM.

For "the N that ... t ..."":
1. Interpret the relative clause as λx. ⟦... t_n ...⟧^{g[n↦x]}
2. Combine with the head noun via Predicate Modification

Result: λx. N(x) ∧ ⟦relative clause⟧(x)
-/
def relativePM {m : Model} (n : ℕ)
    (headNoun : DenotG m (.e ⇒ .t))
    (relClauseBody : DenotG m .t)
    : DenotG m (.e ⇒ .t) :=
  λ g => predicateModification (headNoun g) (predicateAbstraction n relClauseBody g)

/-- Relative PM is commutative (the order of N and RC doesn't matter) -/
theorem relativePM_comm {m : Model} (n : ℕ)
    (headNoun : DenotG m (.e ⇒ .t))
    (relClauseBody : DenotG m .t)
    (g : Assignment m)
    : relativePM n headNoun relClauseBody g =
      predicateModification (predicateAbstraction n relClauseBody g) (headNoun g) := by
  simp only [relativePM, predicateModification_comm]


end Minimalism.Semantics
