/-
# Minimalist Scope Theory: QR and Scope Economy

Formalization of quantifier scope in the Minimalist tradition.

## Core Mechanisms

1. **Quantifier Raising (QR)**: Covert A'-movement of quantifiers to adjoin to TP/CP
2. **Scope Economy (Fox 2000)**: QR only applies if it yields a distinct interpretation
3. **Locality**: QR is clause-bounded and blocked by certain structural barriers

## Scope Freezing in Minimalism

Inverse scope is unavailable when:
- **Possessor**: Quantifier inside possessor DP cannot escape (DP is a phase/barrier)
- **Double Object**: Indirect object c-commands direct object; QR would violate locality
- **Passive**: By-phrase is an adjunct; QR from adjuncts is blocked

## References

- May (1985). Logical Form.
- Fox (2000). Economy and Scope.
- Bruening (2001). QR obeys Superiority.
- Szabolcsi (2010). Quantification.
-/

import Linglib.Core.Interface
import Linglib.Theories.Syntax.Minimalism.Core.Phase

namespace Minimalism.Phenomena.Scope

open ScopeTheory

-- Structural Positions

/-- Structural positions relevant for scope -/
inductive Position where
  | specTP      -- Subject position (Spec-TP)
  | specVP      -- Object position (Spec-vP or complement of V)
  | adjunct     -- Adjunct position (by-phrase, PP modifier)
  | embedded    -- Inside a DP (possessor, PP complement)
  | complement  -- Clausal complement
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A quantifier with its structural position -/
structure PositionedQuantifier where
  quantifier : String
  position : Position
  /-- Is this inside another DP? -/
  insideDP : Bool := false
  /-- Is this in a double object construction? -/
  inDoubleObject : Bool := false
  deriving Repr

-- QR Operation

/--
Quantifier Raising (QR) as covert movement.

QR adjoins a quantifier to a clausal node (TP or CP),
allowing it to take scope over material it c-commands at LF.
-/
structure QROperation where
  /-- The quantifier being raised -/
  target : PositionedQuantifier
  /-- Landing site -/
  landingSite : Position
  /-- Does this create a new scope relation? -/
  createsNewScope : Bool
  deriving Repr

-- Locality Constraints on QR

/--
Barriers to QR movement.

Following phase theory and earlier barrier theory, certain nodes
block extraction/QR.
-/
inductive QRBarrier where
  | dpPhase       -- DP is a phase; QR cannot escape
  | clauseBoundary -- QR is clause-bounded (cannot cross CP)
  | adjunctIsland -- QR from adjuncts is blocked
  | superiority   -- QR cannot cross a c-commanding quantifier (Bruening)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Check if QR is blocked for a given quantifier -/
def qrIsBlocked (q : PositionedQuantifier) : Option QRBarrier :=
  if q.insideDP then some .dpPhase
  else if q.position == .adjunct then some .adjunctIsland
  else if q.position == .embedded then some .dpPhase
  else none

/-- Check if QR over another quantifier violates superiority -/
def violatesSuperiority (lower upper : PositionedQuantifier) : Bool :=
  -- In double object, IO c-commands DO; QR of DO over IO violates superiority
  lower.inDoubleObject && upper.inDoubleObject

-- Scope Economy (Fox 2000)

/--
Scope Economy: QR is only licensed if it creates a truth-conditional difference.

"Covert scope-shifting operations are blocked if they don't have
a semantic effect (i.e., if they yield a logically equivalent interpretation)."
-/
structure ScopeEconomy where
  /-- Surface scope interpretation -/
  surfaceInterpretation : String
  /-- Would-be inverse interpretation -/
  inverseInterpretation : String
  /-- Are they truth-conditionally equivalent? -/
  equivalent : Bool
  deriving Repr

/-- QR is blocked by economy if interpretations are equivalent -/
def economyBlocksQR (e : ScopeEconomy) : Bool :=
  e.equivalent

-- ============================================================================
-- Phase Theory Derivation of QR Barriers
-- ============================================================================

section PhaseBridge

open Minimalism

/-- DP-as-barrier follows from PIC: D is a phase head (under the extended
    phase inventory), so material inside DP's complement is frozen for QR.

    This derives the previously-stipulated `QRBarrier.dpPhase` from
    deeper principles: if D is a phase head, then PIC makes
    DP-internal material inaccessible to operations outside DP.

    The SO is decomposed as `node (leaf tok) b` — the head is a leaf
    (the D lexical item) and `b` is the complement. PIC freezes the
    complement domain, not the head/edge. -/
theorem dp_phase_barrier_from_pic (tok : LIToken) (b : SyntacticObject)
    (h : labelCat (.node (.leaf tok) b) = some .D)
    (h_phase : isDPhaseHead (.node (.leaf tok) b) = true) :
    ∀ (strength : PICStrength) (goal : SyntacticObject),
      contains b goal →
      phaseImpenetrable strength (.node (.leaf tok) b) goal := by
  intro strength goal hcontains
  cases strength <;> exact hcontains

end PhaseBridge

end Minimalism.Phenomena.Scope
