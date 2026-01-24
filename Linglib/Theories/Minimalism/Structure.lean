/-
# Minimalist Clause Structure

Basic phrase structure and linearization for the Minimalist Program.
This is general machinery, not specific to any phenomenon.

## The Clause Structure

```
     CP
    /  \
Spec,CP  C'
        /  \
       C    TP
           /  \
      Spec,TP  T'
              /  \
             T    vP
                  ...
```

Subject is in Spec,TP. T hosts tense/auxiliaries. C hosts complementizers.
-/

import Linglib.Core.Basic

namespace Minimalism

-- ============================================================================
-- Structural Positions
-- ============================================================================

/-- Positions in the clause structure -/
inductive Position where
  | specCP   -- Specifier of CP (wh-movement target)
  | headC    -- Head of CP (complementizer position)
  | specTP   -- Specifier of TP (subject position)
  | headT    -- Head of TP (auxiliary/tense position)
  | specvP   -- Specifier of vP (external argument base position)
  | headv    -- Head of vP (light verb)
  | headV    -- Head of VP (lexical verb)
  deriving Repr, DecidableEq

-- ============================================================================
-- Dominance
-- ============================================================================

/-- CP dominates TP dominates vP dominates VP -/
def dominates : Position → Position → Bool
  | .specCP, p => p != .specCP
  | .headC, p => p != .specCP && p != .headC
  | .specTP, p => p == .specvP || p == .headv || p == .headV
  | .headT, p => p == .specvP || p == .headv || p == .headV
  | .specvP, p => p == .headv || p == .headV
  | .headv, .headV => true
  | _, _ => false

-- ============================================================================
-- Linearization (English)
-- ============================================================================

/--
Structural precedence in the base structure (no movement).
English is Spec-Head-Complement order.
-/
def structurallyPrecedes : Position → Position → Bool
  -- CP level
  | .specCP, .headC => true
  | .specCP, .specTP => true
  | .specCP, .headT => true
  | .specCP, .specvP => true
  | .specCP, .headv => true
  | .specCP, .headV => true
  | .headC, .specTP => true
  | .headC, .headT => true
  | .headC, .specvP => true
  | .headC, .headv => true
  | .headC, .headV => true
  -- TP level
  | .specTP, .headT => true    -- KEY: subject precedes T in base
  | .specTP, .specvP => true
  | .specTP, .headv => true
  | .specTP, .headV => true
  | .headT, .specvP => true
  | .headT, .headv => true
  | .headT, .headV => true
  -- vP level
  | .specvP, .headv => true
  | .specvP, .headV => true
  | .headv, .headV => true
  | _, _ => false

-- ============================================================================
-- Basic Linearization Theorems
-- ============================================================================

/-- Subject (Spec,TP) precedes T in base position -/
theorem subject_precedes_t_base :
    structurallyPrecedes .specTP .headT = true := rfl

/-- C precedes subject (Spec,TP) -/
theorem c_precedes_subject :
    structurallyPrecedes .headC .specTP = true := rfl

/-- C precedes T -/
theorem c_precedes_t :
    structurallyPrecedes .headC .headT = true := rfl

/-- Spec,CP precedes everything else -/
theorem spec_cp_is_first :
    structurallyPrecedes .specCP .headC = true ∧
    structurallyPrecedes .specCP .specTP = true ∧
    structurallyPrecedes .specCP .headT = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Head Movement
-- ============================================================================

/-- Possible positions for a head after movement -/
inductive HeadPosition where
  | base : Position → HeadPosition   -- in its base position
  | movedTo : Position → HeadPosition -- moved to another head position
  deriving Repr, DecidableEq

/-- Common case: T position (in T or moved to C) -/
inductive TPosition where
  | inT   -- T remains in its base position
  | inC   -- T has moved to C (T-to-C movement)
  deriving Repr, DecidableEq

/-- Where is T pronounced after potential movement? -/
def tPronouncedAt (tPos : TPosition) : Position :=
  match tPos with
  | .inT => .headT
  | .inC => .headC

-- ============================================================================
-- Movement Effects on Linearization
-- ============================================================================

/-- T-to-C places T in C position, which precedes Spec,TP -/
theorem t_to_c_precedes_subject :
    structurallyPrecedes (tPronouncedAt .inC) .specTP = true := rfl

/-- When T stays in T, subject precedes T -/
theorem subject_precedes_t_no_movement :
    structurallyPrecedes .specTP (tPronouncedAt .inT) = true := rfl

/-- T-to-C reverses subject-T order -/
theorem t_to_c_reverses_order :
    -- Base: subject < T
    structurallyPrecedes .specTP .headT = true ∧
    -- After T-to-C: T (in C) < subject
    structurallyPrecedes .headC .specTP = true := ⟨rfl, rfl⟩

-- ============================================================================
-- Linear Precedence Predicates
-- ============================================================================

/-- Does T precede the subject given its position? -/
def tPrecedesSubject (tPos : TPosition) : Bool :=
  structurallyPrecedes (tPronouncedAt tPos) .specTP

/-- Does the subject precede T given T's position? -/
def subjectPrecedesT (tPos : TPosition) : Bool :=
  structurallyPrecedes .specTP (tPronouncedAt tPos)

theorem t_to_c_gives_t_first : tPrecedesSubject .inC = true := rfl
theorem no_movement_gives_subj_first : subjectPrecedesT .inT = true := rfl

end Minimalism
