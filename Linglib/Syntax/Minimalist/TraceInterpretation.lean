import Linglib.Syntax.Minimalist.Basic
import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Semantics.Composition.Abstraction

/-!
# Trace Interpretation
[heim-kratzer-1998]

Traces left by movement are interpreted as variables bound by
λ-abstraction at the landing site (H&K Ch. 5, 7).

## Rules

1. Trace Interpretation: a trace t_n is interpreted as g(n)
   ⟦t_n⟧^g = g(n)

2. Predicate Abstraction (the λ-abstraction at the landing site) and the
   relative-clause denotation it feeds are framework-neutral composition rules,
   so they live in `Semantics/Composition/Abstraction.lean`; this file is the
   Minimalist trace machinery that applies them.

## Trace convention

Traces are encoded as `SyntacticObject.leaf` with id ≥ 10000.
The trace index is `id - 10000`. Created via `mkTrace n`,
detected via `isTrace so`.

-/

namespace Minimalist

open Core.Logic.Intensional Core.Logic.Intensional.Variables
open Semantics.Composition.Abstraction

-- ============================================================================
-- Trace Interpretation (H&K Ch. 5, 7)
-- ============================================================================

/-- Interpret a trace as a variable: ⟦t_n⟧^g = g(n).

    Heim and Kratzer's trace interpretation rule: traces and pronouns
    are semantically identical, looked up via the assignment function.
    The trace index n matches the binder (λ-abstraction) at the
    landing site of movement.

    `abbrev` because trace interpretation IS pronoun interpretation —
    the only difference is the syntactic source. -/
abbrev interpTrace {F : Frame} (n : ℕ) : DenotG F .e :=
  interpPronoun n

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

/-- Collect ALL trace indices in a syntactic object, as a `Multiset Nat`.

    Returning a multiset (rather than `Option Nat`) is what makes the
    operation swap-respecting: `Multiset` addition is commutative, so
    enumerating both children's traces and combining via `+` is order-
    independent. The previous `Option`-valued version with `<|>` was
    *unsoundly* sorried because `Option.orElse` is left-biased — for
    multi-trace SOs `getTraceIndexAux (mul a b)` and
    `getTraceIndexAux (mul b a)` return different values, so the
    `_respects` proposition was false-by-construction.

    Single-trace consumers should use `traceIndex?` (defined below) to
    extract the unique index. -/
private def traceIndicesAux : FreeMagma (LIToken ⊕ Nat) → Multiset ℕ
  | .of (.inl _) => 0  -- empty multiset
  | .of (.inr n) => {n}
  | .mul a b => traceIndicesAux a + traceIndicesAux b

private theorem traceIndicesAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : traceIndicesAux a = traceIndicesAux b := by
  induction h with
  | swap _ _ => simp only [traceIndicesAux]; exact add_comm _ _
  | mul_left _ _ ih => simp only [traceIndicesAux, ih]
  | mul_right _ _ ih => simp only [traceIndicesAux, ih]

/-- All trace indices appearing in an SO, as a `Multiset` (multiplicity
    preserved, order-blind). -/
def traceIndices : SyntacticObject → Multiset ℕ :=
  FreeCommMagma.lift traceIndicesAux traceIndicesAux_respects

@[simp] theorem traceIndices_leaf (tok : LIToken) :
    traceIndices (SyntacticObject.leaf tok) = 0 := rfl

@[simp] theorem traceIndices_trace (n : Nat) :
    traceIndices (SyntacticObject.trace n) = {n} := rfl

@[simp] theorem traceIndices_mul (l r : SyntacticObject) :
    traceIndices (l * r) = traceIndices l + traceIndices r := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

/-- Extract a trace index, returning `none` if the SO has no traces.
    For single-trace SOs returns the unique index; for multi-trace SOs,
    returns *some* index (the first in `Multiset.toList`'s arbitrary
    enumeration). Use `traceIndices` directly for the canonical
    multiset.

    Noncomputable because `Multiset.toList` is. -/
noncomputable def getTraceIndex (so : SyntacticObject) : Option ℕ :=
  (traceIndices so).toList.head?

-- ============================================================================
-- Theorems about Movement Interpretation
-- ============================================================================

/-- Different indices yield independent interpretations. -/
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

end Minimalist
