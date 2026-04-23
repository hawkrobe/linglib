import Linglib.Theories.Phonology.OptimalityTheory.Correspondence
import Linglib.Theories.Phonology.OptimalityTheory.TCT
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

/-- The general TCT diagram constructor: takes the three forms plus an
    explicit OO correspondence relation `ooEdge ⊆ Fin base.length × Fin derivative.length`
    (subject to a well-formedness proof).

    The `(.input, .base)` and `(.input, .derivative)` IO edges are filled
    in trivially as the parallel-pair correspondence (one-to-one up to
    `min` length); only the OO edge requires the morphological alignment
    that a study file specifies.

    This is the **load-bearing constructor** for paradigmatic phonology
    studies that involve infixation, truncation, reduplication, or any
    non-identity morphological mapping — the OO edge is *not* generally
    parallel-pair (the singular [ɲĩãr] base maps to non-adjacent
    positions in the plural [ɲ-ar-ĩãr]). See
    `Phenomena/Phonology/Studies/Benua1997.lean` for the canonical
    Sundanese example. -/
def diagramWithEdge {α : Type}
    (input base derivative : List α)
    (ooEdge : Finset (ℕ × ℕ))
    (hOO : ∀ p ∈ ooEdge, p.1 < base.length ∧ p.2 < derivative.length) :
    Corr Role α where
  form := Role.formOf input base derivative
  edge r₁ r₂ :=
    match r₁, r₂ with
    | .base, .derivative => ooEdge
    | .derivative, .base => ooEdge.image fun p => (p.2, p.1)
    | .input, .base       =>
        (Finset.range (min input.length base.length)).image fun i => (i, i)
    | .base, .input       =>
        (Finset.range (min input.length base.length)).image fun i => (i, i)
    | .input, .derivative =>
        (Finset.range (min input.length derivative.length)).image fun i => (i, i)
    | .derivative, .input =>
        (Finset.range (min input.length derivative.length)).image fun i => (i, i)
    | _, _ => ∅
  wf := by
    intro r₁ r₂ p hmem
    match r₁, r₂, hmem with
    | .base, .derivative, h => exact hOO p h
    | .derivative, .base, h =>
        simp only [Finset.mem_image] at h
        obtain ⟨q, hq, rfl⟩ := h
        have ⟨h1, h2⟩ := hOO q hq
        exact ⟨h2, h1⟩
    | .input, .base, h =>
        simp only [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact ⟨lt_of_lt_of_le hi (min_le_left _ _),
               lt_of_lt_of_le hi (min_le_right _ _)⟩
    | .base, .input, h =>
        simp only [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact ⟨lt_of_lt_of_le hi (min_le_right _ _),
               lt_of_lt_of_le hi (min_le_left _ _)⟩
    | .input, .derivative, h =>
        simp only [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact ⟨lt_of_lt_of_le hi (min_le_left _ _),
               lt_of_lt_of_le hi (min_le_right _ _)⟩
    | .derivative, .input, h =>
        simp only [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact ⟨lt_of_lt_of_le hi (min_le_right _ _),
               lt_of_lt_of_le hi (min_le_left _ _)⟩
    | .input, .input, h => exact absurd h (Finset.notMem_empty _)
    | .base, .base, h => exact absurd h (Finset.notMem_empty _)
    | .derivative, .derivative, h => exact absurd h (Finset.notMem_empty _)

/-- The parallel-pair specialization: when the OO edge is the parallel
    `(i, i)` correspondence up to `min base.length derivative.length`.
    Convenient for cases where base and derivative have no morphological
    re-alignment (rare in paradigm phonology — most studies need
    `diagramWithEdge` with an explicit alignment). -/
def diagram {α : Type} (input base derivative : List α) : Corr Role α :=
  diagramWithEdge input base derivative
    ((Finset.range (min base.length derivative.length)).image fun i => (i, i))
    (by
      intro p hmem
      simp only [Finset.mem_image, Finset.mem_range] at hmem
      obtain ⟨i, hi, rfl⟩ := hmem
      exact ⟨lt_of_lt_of_le hi (min_le_left _ _),
             lt_of_lt_of_le hi (min_le_right _ _)⟩)

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
  unfold identOOViol Corr.identViol
  show ((((Finset.range (min shared.length shared.length)).image
            (fun i => (i, i)))).filter
          (fun p => shared[p.1]? ≠ shared[p.2]?)).card = 0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact fun h => h rfl

end Phonology.ParadigmUniformity.Transderivational
