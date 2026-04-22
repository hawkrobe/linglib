/-
# Minimalism-Montague Semantics Interface
@cite{heim-kratzer-1998}

Traces left by movement are interpreted as variables bound by
λ-abstraction at the landing site.

## Architecture

This module bridges Minimalist syntax and Montague semantics:

```
SyntacticObjects.lean Montague/Variables.lean
       ↓ ↓
    SyntacticObject with Assignment functions
    mkTrace/isTrace ↓
              ↘ ↙
         Minimalism/Bridge/Interface.lean
                     ↓
         interpTrace: traces → g(n)
         predicateAbstraction: λ-bind at landing site
```

## Rules

1. Trace Interpretation: A trace t_n is interpreted as g(n)
   ⟦t_n⟧^g = g(n)

2. Predicate Abstraction: At the landing site of movement,
   λ-abstract over the trace's index
   ⟦[CP Op_n... t_n...]⟧^g = λx. ⟦... t_n...⟧^{g[n↦x]}

## Trace Convention

Traces are encoded as `SyntacticObject.leaf` with id ≥ 10000.
The trace index is `id - 10000`. Created via `mkTrace n`,
detected via `isTrace so`.

-/

import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Core.IntensionalLogic.Frame
import Linglib.Core.IntensionalLogic.Variables
import Linglib.Theories.Semantics.Composition.Modification

namespace Minimalism.Semantics

open Core.IntensionalLogic Core.IntensionalLogic.Variables Semantics.Composition.Modification
open Minimalism

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
def interpTrace {F : Frame} (n : ℕ) : DenotG F .e :=
  interpPronoun n

/-- Traces and pronouns have the same interpretation -/
theorem interpTrace_eq_interpPronoun {F : Frame} (n : ℕ) :
    interpTrace (F := F) n = interpPronoun n := rfl

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
def predicateAbstraction {F : Frame} (n : ℕ) (body : DenotG F .t)
    : DenotG F (.e ⇒ .t) :=
  lambdaAbsG n body

/--
Generalized predicate abstraction for any result type.

This handles cases like "the book that John said Mary read _"
where the trace is embedded and the result may need further composition.
-/
def predicateAbstractionGen {F : Frame} {τ : Ty} (n : ℕ) (body : DenotG F τ)
    : DenotG F (.e ⇒ τ) :=
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
def interpMovement {F : Frame} (n : ℕ)
    (bodyWithTrace : DenotG F .t) : DenotG F (.e ⇒ .t) :=
  predicateAbstraction n bodyWithTrace

/--
The binding relationship: predicate abstraction at index n binds traces at n.

When we apply a predicate-abstracted meaning to an entity,
that entity becomes the value of all traces with the same index.
-/
theorem binding_correct {F : Frame} (n : ℕ) (body : DenotG F .t)
    (x : F.Entity) (g : Core.Assignment F.Entity)
    : (predicateAbstraction n body g) x = body (g[n ↦ x]) := rfl

-- ============================================================================
-- Connection to Syntactic Objects
-- ============================================================================

/--
A semantic interpretation context pairs a model with an assignment.
-/
structure InterpContext (F : Frame) where
  assignment : Core.Assignment F.Entity

/--
The semantic type corresponding to a syntactic object.

- Traces have type e (they denote entities)
- Other SOs need lexical lookup
-/
def soSemanticType (so : SyntacticObject) : Option Ty :=
  match isTrace so with
  | some _ => some .e
  | none => none  -- depends on lexical entry / composition

/--
Interpret a trace in a syntactic object.

This extracts the trace index and interprets it via the assignment.
-/
def interpSOTrace {F : Frame} (so : SyntacticObject) : Option (DenotG F .e) :=
  match isTrace so with
  | some n => some (interpTrace n)
  | none => none

/--
Get the trace index from a syntactic object (searches recursively).
-/
def getTraceIndex : SyntacticObject → Option ℕ
  | .leaf tok =>
    if tok.id ≥ 10000 then some (tok.id - 10000) else none
  | .node a b => getTraceIndex a <|> getTraceIndex b

-- ============================================================================
-- Theorems about Movement Interpretation
-- ============================================================================

/--
Identity of indiscernibles for traces:
traces with the same index have the same interpretation.
-/
theorem trace_index_determines_meaning {F : Frame} (n : ℕ)
    : interpTrace (F := F) n = interpTrace n := rfl

/--
Different indices yield independent interpretations.
-/
theorem trace_indices_independent {F : Frame} (n₁ n₂ : ℕ) (h : n₁ ≠ n₂)
    (x : F.Entity) (g : Core.Assignment F.Entity)
    : interpTrace n₁ (g[n₂ ↦ x]) = interpTrace n₁ g := by
  simp only [interpTrace, interpPronoun]
  exact update_other g n₂ n₁ x h

/--
Predicate abstraction creates the right binding:
the abstracted variable is bound, other variables are free.
-/
theorem abstraction_binds_correct_variable {F : Frame} (n : ℕ)
    (g : Core.Assignment F.Entity) (x : F.Entity)
    : interpTrace n (g[n ↦ x]) = x := by
  simp only [interpTrace, interpPronoun]
  exact update_same g n x

-- ============================================================================
-- Integration with Predicate Modification
-- ============================================================================

/--
Relative clause interpretation combines predicate abstraction with PM.

For "the N that... t..."":
1. Interpret the relative clause as λx. ⟦... t_n...⟧^{g[n↦x]}
2. Combine with the head noun via Predicate Modification

Result: λx. N(x) ∧ ⟦relative clause⟧(x)
-/
def relativePM {F : Frame} (n : ℕ)
    (headNoun : DenotG F (.e ⇒ .t))
    (relClauseBody : DenotG F .t)
    : DenotG F (.e ⇒ .t) :=
  λ g => predicateModification (headNoun g) (predicateAbstraction n relClauseBody g)

/-- Relative PM is commutative (the order of N and RC doesn't matter) -/
theorem relativePM_comm {F : Frame} (n : ℕ)
    (headNoun : DenotG F (.e ⇒ .t))
    (relClauseBody : DenotG F .t)
    (g : Core.Assignment F.Entity)
    : relativePM n headNoun relClauseBody g =
      predicateModification (predicateAbstraction n relClauseBody g) (headNoun g) := by
  simp only [relativePM, predicateModification_comm]


end Minimalism.Semantics
