import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.OptimalityTheory.TCT
import Linglib.Core.Constraint.OT.Basic

/-!
# Transderivational Paradigm Uniformity — Benua 1997
@cite{benua-1997}

The paradigm-uniformity face of TCT: provides paradigm-typed
`Corr`-style API for OO-Faith constraints between a base form and a
derivative form. The asymmetric base-priority discipline lives in
`OptimalityTheory/TCT.lean` (`TCTGrammar` structure); this file is the
*compositional* face — building 3-role correspondence diagrams over
input + base + derivative, and supplying the IDENT-OO and MAX-OO
specializations to the `(.base, .derivative)` edge.

## Compared to siblings

The four ParadigmUniformity files differ only in their *anchoring
discipline* on the same `Corr.identViol` substrate:

| File | Anchoring | Polarity |
|---|---|---|
| `OptimalParadigms.lean` (M 2005) | Symmetric (no anchor) | Positive (Ident) |
| `LexicalConservatism.lean` (Steriade 2000) | Optional attestation anchor | Positive (Ident) |
| **`Transderivational.lean` (Benua 1997)** | **Base-anchored, recursive** | **Positive (Ident)** |
| `Antifaithfulness.lean` (Alderete 2001) | Symmetric or anchored | **Negative (¬Ident)** |

The architectural distinction of TCT (vs. OP / LC) is *not* in the
constraint or the lift — it is in the **evaluation discipline** (recursive
base-priority), which is captured in `TCT.TCTGrammar`'s type signatures.
-/

namespace Phonology.ParadigmUniformity.Transderivational

open Phonology.Correspondence (Corr)
open Phonology.TCT (Role)
open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: TCT Diagram constructors
-- ============================================================================

/-- Form lookup helper: select the form for a TCT role from explicit
    `input`/`base`/`derivative` lists. -/
@[inline] def Role.formOf {α : Type*} (input base derivative : List α) :
    Role → List α
  | .input      => input
  | .base       => base
  | .derivative => derivative

/-- The general TCT diagram constructor: the three forms plus an explicit
    OO correspondence relation `ooEdge` between base and derivative
    positions (with a well-formedness proof `hOO`). The IO relations
    (input-base, input-derivative) are the parallel-pair correspondence;
    only the OO relation carries the morphological alignment a study
    specifies (e.g. the Sundanese infix — see `Studies/Benua1997.lean`).
    The reverse directions are recovered by `Corr.edge`. -/
def diagramWithEdge {α : Type}
    (input base derivative : List α)
    (ooEdge : Finset (ℕ × ℕ))
    (hOO : ∀ p ∈ ooEdge, p.1 < base.length ∧ p.2 < derivative.length) :
    Corr Role α where
  form := Role.formOf input base derivative
  edge r₁ r₂ :=
    match r₁, r₂ with
    | .base, .derivative => ooEdge
    | .input, .base       =>
        (Finset.range (min input.length base.length)).image fun i => (i, i)
    | .input, .derivative =>
        (Finset.range (min input.length derivative.length)).image fun i => (i, i)
    | _, _ => ∅
  edge_lt_length := by
    intro r₁ r₂ p hmem
    match r₁, r₂, hmem with
    | .base, .derivative, h => exact hOO p h
    | .input, .base, h =>
        simp only [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact ⟨lt_of_lt_of_le hi (min_le_left _ _),
               lt_of_lt_of_le hi (min_le_right _ _)⟩
    | .input, .derivative, h =>
        simp only [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact ⟨lt_of_lt_of_le hi (min_le_left _ _),
               lt_of_lt_of_le hi (min_le_right _ _)⟩
    | .input, .input, h => exact absurd h (Finset.notMem_empty _)
    | .base, .base, h => exact absurd h (Finset.notMem_empty _)
    | .base, .input, h => exact absurd h (Finset.notMem_empty _)
    | .derivative, .base, h => exact absurd h (Finset.notMem_empty _)
    | .derivative, .input, h => exact absurd h (Finset.notMem_empty _)
    | .derivative, .derivative, h => exact absurd h (Finset.notMem_empty _)

/-- The parallel-pair specialization: the OO edge is the parallel `(i, i)`
    correspondence up to `min base.length derivative.length`. For
    morphological re-alignment use `diagramWithEdge`. -/
def diagram {α : Type} (input base derivative : List α) : Corr Role α :=
  Corr.diagram
    (fun | .input => input | .base => base | .derivative => derivative)
    (· ≠ ·)

-- ============================================================================
-- § 2: IDENT-OO and MAX-OO specializations
-- ============================================================================

variable {α : Type*}

/-- IDENT-OO: featural identity of corresponding base and derivative
    positions. The load-bearing constraint of @cite{benua-1997}'s
    misapplication unification — high-ranked IDENT-OO forces overapplication
    (Sundanese nasal harmony, Ch 3) and underapplication (Tiberian Hebrew
    spirantization, Ch 4) as duals of one mechanism. -/
def identOOViol [DecidableEq α] (c : Corr Role α) : ℕ :=
  c.identViol .base .derivative

/-- MAX-OO: every base position has a derivative correspondent. Penalizes
    truncation in the derivative relative to the base. -/
def maxOOViol (c : Corr Role α) : ℕ :=
  c.maxViol .base .derivative

/-- DEP-OO: every derivative position has a base correspondent. Penalizes
    epenthesis in the derivative relative to the base. -/
def depOOViol (c : Corr Role α) : ℕ :=
  c.depViol .base .derivative

-- ============================================================================
-- § 3: NamedConstraint bridges
-- ============================================================================

/-- Wrap IDENT-OO as a `NamedConstraint`. -/
def toIdentOOConstraint (α : Type) [DecidableEq α] : NamedConstraint (Corr Role α) :=
  Corr.toIdentConstraint .base .derivative "OO"

/-- Wrap MAX-OO as a `NamedConstraint`. -/
def toMaxOOConstraint (α : Type) : NamedConstraint (Corr Role α) :=
  Corr.toMaxConstraint .base .derivative "OO"

/-- Wrap DEP-OO as a `NamedConstraint`. -/
def toDepOOConstraint (α : Type) : NamedConstraint (Corr Role α) :=
  Corr.toDepConstraint .base .derivative "OO"

-- ============================================================================
-- § 4: Identity sanity check
-- ============================================================================

/-- When the derivative is identical to the base, IDENT-OO is satisfied
    (zero violations). The "perfect uniformity" baseline — paradigmatic
    identity is the trivial case where there is nothing to misapply. -/
theorem identOO_when_equal {α : Type} [DecidableEq α]
    (input shared : List α) :
    identOOViol (diagram input shared shared) = 0 := by
  have hedge : (diagram input shared shared).edge Role.base Role.derivative =
      (Finset.range (min shared.length shared.length)).image (fun i => (i, i)) := by
    simp only [diagram]
    exact Corr.diagram_edge_pos _ _ (by decide)
  unfold identOOViol Corr.identViol
  rw [hedge, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact fun h => h rfl

end Phonology.ParadigmUniformity.Transderivational
