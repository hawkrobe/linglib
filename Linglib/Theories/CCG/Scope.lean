/-
# CCG Scope Theory

How CCG derivational structure determines available scope readings.

## Insight (Steedman 2000 Ch. 6)

In CCG, scope is determined by derivational structure, not by a separate
LF movement operation. Different derivations of the same string can yield
different scope readings:

1. Direct application: Object combines with verb first, yielding surface scope.
2. Type-raising + composition: Subject "wraps around," enabling narrow scope.

## Verb Raising vs Verb Projection Raising

In Dutch/German embedded clauses:
- Verb raising order: Object combines with embedded verb first, yielding ambiguity.
- Verb projection raising order: Matrix verb combines first, yielding surface scope only.

CCG predicts this connection between word order and scope.

## References

- Steedman (2000) "The Syntactic Process" Chapter 6
- Steedman & Baldridge (2011) "Combinatory Categorial Grammar"
-/

import Linglib.Theories.CCG.Basic
import Linglib.Theories.Core.Interfaces.ScopeTheory

namespace CCG.Scope

open CCG
open ScopeTheory

-- Derivation Structure Analysis

/--
A scope-taking element in a CCG derivation.

Scope-takers are typically:
- Quantified NPs (every, some, a, etc.)
- Negation
- Modals
- Intensional verbs
-/
structure ScopeTaker where
  /-- Identifier (e.g., "every_horse", "not") -/
  id : String
  /-- Position in surface string (for ordering) -/
  surfacePosition : Nat
  /-- Category of the scope-taker -/
  cat : Cat
  deriving Repr

/--
Derivation type for scope analysis.

Different derivation types affect scope possibilities:
- `directApp`: Standard application, gives surface scope
- `typeRaised`: Type-raising involved, enables scope flexibility
- `composed`: Composition used, enables scope inversion
-/
inductive DerivationType where
  | directApp    -- Standard forward/backward application
  | typeRaised   -- Involves type-raising
  | composed     -- Involves composition
  deriving DecidableEq, BEq, Repr

/-- Analyze derivation to determine its type -/
def analyzeDerivation : DerivStep → DerivationType
  | .lex _ => .directApp
  | .fapp d1 d2 =>
    -- If either child involves type-raising or composition, propagate
    match analyzeDerivation d1, analyzeDerivation d2 with
    | .typeRaised, _ => .typeRaised
    | _, .typeRaised => .typeRaised
    | .composed, _ => .composed
    | _, .composed => .composed
    | _, _ => .directApp
  | .bapp d1 d2 =>
    match analyzeDerivation d1, analyzeDerivation d2 with
    | .typeRaised, _ => .typeRaised
    | _, .typeRaised => .typeRaised
    | .composed, _ => .composed
    | _, .composed => .composed
    | _, _ => .directApp
  | .fcomp _ _ => .composed
  | .bcomp _ _ => .composed
  | .ftr _ _ => .typeRaised
  | .btr _ _ => .typeRaised
  | .coord d1 d2 =>
    match analyzeDerivation d1, analyzeDerivation d2 with
    | .typeRaised, _ => .typeRaised
    | _, .typeRaised => .typeRaised
    | .composed, _ => .composed
    | _, .composed => .composed
    | _, _ => .directApp

-- Scope Availability from Derivation

/--
Determine scope availability from derivation type.

Composition and type-raising enable scope flexibility.
Without them, only surface scope is available.
-/
def derivationTypeToAvailability : DerivationType → BinaryScopeAvailability
  | .directApp => .surfaceOnly
  | .typeRaised => .ambiguous
  | .composed => .ambiguous

/--
A CCG derivation annotated with scope-taker information.

This pairs a derivation with explicit information about which
elements are scope-takers and their surface positions.
-/
structure ScopedDerivation where
  /-- The CCG derivation -/
  deriv : DerivStep
  /-- Scope-taking elements (in surface order) -/
  scopeTakers : List ScopeTaker
  /-- At least two scope-takers for ambiguity -/
  hasTwoOrMore : scopeTakers.length ≥ 2 := by decide
  deriving Repr

/-- Get scope availability for a scoped derivation -/
def ScopedDerivation.availability (sd : ScopedDerivation) : BinaryScopeAvailability :=
  derivationTypeToAvailability (analyzeDerivation sd.deriv)

/-- Convert to abstract ScopeReading -/
def ScopedDerivation.toAvailableScopes (sd : ScopedDerivation) : AvailableScopes :=
  let ids := sd.scopeTakers.map (·.id)
  sd.availability.toAvailableScopes
    (ids.head!)  -- First scope-taker
    (ids.tail.head!)  -- Second scope-taker

-- HasAvailableScopes Instance

/-- Marker type for CCG scope theory -/
def CCGScopeTheory : Type := Unit

/-- CCG implements HasAvailableScopes for ScopedDerivation -/
instance : HasAvailableScopes CCGScopeTheory ScopedDerivation where
  availableScopes := ScopedDerivation.toAvailableScopes

-- Examples: Quantifier Scope

/-
Example: "Every horse didn't jump"

Two possible derivations:

1. Surface scope derivation (forall > not):
   - "every horse" combines directly with "didn't jump"
   - Standard backward application
   - Only surface scope available

2. Inverse scope derivation (not > forall):
   - "every horse" type-raises
   - Composes with negated verb
   - Inverse scope becomes available
-/

-- Surface scope derivation (simplified)
def everyHorse_surface : DerivStep :=
  .bapp (.lex ⟨"every horse", NP⟩) (.lex ⟨"didn't jump", IV⟩)

-- Inverse scope derivation (with type-raising)
def everyHorse_inverse : DerivStep :=
  let everyHorse_tr := DerivStep.ftr (.lex ⟨"every horse", NP⟩) S
  .fcomp everyHorse_tr (.lex ⟨"didn't jump", IV⟩)

#eval analyzeDerivation everyHorse_surface  -- directApp
#eval analyzeDerivation everyHorse_inverse  -- composed (from fcomp)

-- Connection to Dutch/German Word Order

/-
From Steedman (2000) §6.8 and Phenomena/ScopeWordOrder/Data.lean:

Verb raising order (object before all verbs):
- "(dat) Jan veel boeken probeert te lezen"
- Object combines with embedded verb first (via composition)
- Multiple derivations possible, yielding ambiguity

Verb projection raising order (object after matrix verb):
- "(dat) Jan probeert veel boeken te lezen"
- Matrix verb combines first
- Only one derivation, yielding surface scope only

The CCG analysis predicts this from derivational structure.
-/

/-- Verb raising derivation type -/
inductive VerbRaisingType where
  | verbRaising          -- Object + embedded verb first
  | verbProjectionRaising -- Matrix verb first
  deriving DecidableEq, BEq, Repr

/-- Verb raising type determines scope availability -/
def verbRaisingToAvailability : VerbRaisingType → BinaryScopeAvailability
  | .verbRaising => .ambiguous
  | .verbProjectionRaising => .surfaceOnly

end CCG.Scope
