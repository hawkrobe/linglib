import Linglib.Theories.Semantics.Dynamic.State

/-!
# @cite{farkas-bruce-2010} Assertion Adapter

@cite{farkas-bruce-2010}

Wraps the existing `Semantics.Dynamic.State.DiscourseState` with
bridge theorems for Farkas & Bruce's model. The model separates individual
discourse commitments (dcS, dcL) from the common ground (cg), with
assertions going through a "table" stage before reaching the CG.

## Key Properties

- **Separates commitment from belief**: dcS (speaker's commitments) ≠ cg.
  Assertion first adds to dcS and pushes an issue; acceptance moves to cg.
- **No retraction**: once in the CG, propositions stay (monotonic).
- **No source marking**: commits are tracked per-participant but without
  Gunlogson-style source tags.

## Architecture

This file is an ADAPTER: it wraps the existing `DiscourseState` type
from `Theories/Semantics/Dynamic/State.lean` rather than redefining it.

-/

namespace Pragmatics.Assertion.FarkasAdapter

open Semantics.Dynamic.State
open Core.CommonGround (ContextSet)
open Core.Proposition (BProp)

-- ════════════════════════════════════════════════════
-- § 1. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- Assertion adds to dcS, not directly to cg.
    This is the key F&B insight: assertion first commits the speaker,
    then the listener can accept (moving to cg) or reject. -/
theorem assert_adds_to_dcS {W : Type*} (ds : DiscourseState W) (p : BProp W) :
    (ds.assertDeclarative p).dcS = p :: ds.dcS := rfl

/-- Assertion does not immediately change the common ground. -/
theorem assert_preserves_cg {W : Type*} (ds : DiscourseState W) (p : BProp W) :
    (ds.assertDeclarative p).cg = ds.cg := rfl

/-- Assertion is not stable: it pushes an issue onto the table. -/
theorem assert_not_stable {W : Type*} (ds : DiscourseState W) (p : BProp W) :
    (ds.assertDeclarative p).isStable = false := by
  simp only [DiscourseState.assertDeclarative, DiscourseState.pushIssue,
             DiscourseState.addToDcS, DiscourseState.isStable]
  rfl

/-- Acceptance moves the proposition to the common ground. -/
theorem accept_adds_to_cg {W : Type*} (ds : DiscourseState W) (p : BProp W) :
    ((ds.assertDeclarative p).acceptTop).cg = p :: ds.cg := by
  simp only [DiscourseState.assertDeclarative, DiscourseState.pushIssue,
             DiscourseState.addToDcS, DiscourseState.acceptTop]
  rfl

/-- After acceptance, the state returns to stable (table is popped). -/
theorem accept_restores_stability {W : Type*} (ds : DiscourseState W) (p : BProp W)
    (hStable : ds.isStable = true) :
    ((ds.assertDeclarative p).acceptTop).isStable = true := by
  simp only [DiscourseState.assertDeclarative, DiscourseState.pushIssue,
             DiscourseState.addToDcS, DiscourseState.acceptTop,
             DiscourseState.isStable] at *
  exact hStable

end Pragmatics.Assertion.FarkasAdapter
