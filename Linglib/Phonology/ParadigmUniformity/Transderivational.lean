import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.OptimalityTheory.TCT
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic

/-!
# Transderivational Paradigm Uniformity — Benua 1997
[benua-1997]

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

namespace OptimalityTheory.ParadigmUniformity.Transderivational

open OptimalityTheory.Correspondence (Corr)
open OptimalityTheory.TCT (Role)
open Constraints OptimalityTheory

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
    | .base, .derivative =>
        -- Lift the ℕ-indexed `ooEdge` into the `Fin`-indexed storage using `hOO`.
        ooEdge.attach.image fun p => (⟨p.1.1, (hOO p.1 p.2).1⟩, ⟨p.1.2, (hOO p.1 p.2).2⟩)
    | .input, .base       => Corr.diagDiag input.length base.length
    | .input, .derivative => Corr.diagDiag input.length derivative.length
    | _, _ => ∅

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
    positions. The load-bearing constraint of [benua-1997]'s
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
      Corr.diagDiag shared.length shared.length := by
    simp only [diagram]
    exact Corr.diagram_edge_pos _ _ (by decide)
  unfold identOOViol Corr.identViol
  rw [hedge, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  have hpq : (p.1 : ℕ) = (p.2 : ℕ) := (Corr.mem_diagDiag p.1 p.2).mp hp
  simp only [not_not]
  exact congrArg (fun i : Fin shared.length => shared[i]) (Fin.ext hpq)

end OptimalityTheory.ParadigmUniformity.Transderivational
