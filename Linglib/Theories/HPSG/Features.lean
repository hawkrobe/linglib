/-
# HPSG Feature System

General feature types and constraints for HPSG.
This is reusable machinery, not specific to any phenomenon.

## HPSG Architecture

HPSG represents linguistic objects as typed feature structures (AVMs).
Features are organized into:
- HEAD features (shared between head and phrase)
- VALENCE features (subcategorization)
- NONLOCAL features (unbounded dependencies)

This file defines the feature types. Phrase structure rules and
unification are in Basic.lean.
-/

import Linglib.Core.Basic

namespace HPSG

-- ============================================================================
-- HEAD Features
-- ============================================================================

/-- Verb form features -/
inductive VForm' where
  | finite
  | infinitive
  | gerund
  | pastParticiple
  | presentParticiple
  deriving Repr, DecidableEq

/-- The INV(erted) feature - crucial for subject-aux inversion -/
inductive Inv where
  | plus   -- [INV +]: inverted clause (aux before subject)
  | minus  -- [INV -]: non-inverted clause (subject before aux)
  deriving Repr, DecidableEq

/-- Head features bundle -/
structure HeadFeatures' where
  vform : VForm' := .finite
  inv : Inv := .minus
  aux : Bool := false
  deriving Repr, DecidableEq

-- ============================================================================
-- Word Order Predicates
-- ============================================================================

/-- Find the position of the first auxiliary -/
def findAuxPosition (ws : List Word) : Option Nat :=
  ws.findIdx? (·.cat == Cat.Aux)

/-- Find the position of the first subject (non-wh DP) -/
def findSubjectPosition (ws : List Word) : Option Nat :=
  ws.findIdx? λ w => w.cat == Cat.D && !w.features.wh

/-- Auxiliary precedes subject -/
def auxPrecedesSubject (ws : List Word) : Bool :=
  match findAuxPosition ws, findSubjectPosition ws with
  | some a, some s => a < s
  | _, _ => false

/-- Subject precedes auxiliary -/
def subjectPrecedesAux (ws : List Word) : Bool :=
  match findAuxPosition ws, findSubjectPosition ws with
  | some a, some s => s < a
  | _, _ => false

-- ============================================================================
-- INV Feature and Word Order
-- ============================================================================

/-- [INV +] correlates with aux-before-subject order -/
def invPlusImpliesAuxFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .plus → auxPrecedesSubject ws = true

/-- [INV -] correlates with subject-before-aux order -/
def invMinusImpliesSubjectFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .minus → subjectPrecedesAux ws = true

-- ============================================================================
-- Basic Theorems
-- ============================================================================

/-- INV+ and INV- are mutually exclusive -/
theorem inv_exclusive (i : Inv) : i = .plus ∨ i = .minus := by
  cases i <;> simp

/-- If we have aux-first order, INV+ is possible -/
theorem aux_first_allows_inv_plus (ws : List Word)
    (h : auxPrecedesSubject ws = true) :
    invPlusImpliesAuxFirst .plus ws := by
  intro _; exact h

/-- If we have subject-first order, INV- is possible -/
theorem subject_first_allows_inv_minus (ws : List Word)
    (h : subjectPrecedesAux ws = true) :
    invMinusImpliesSubjectFirst .minus ws := by
  intro _; exact h

end HPSG
