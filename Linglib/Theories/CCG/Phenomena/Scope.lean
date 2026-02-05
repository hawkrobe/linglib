/-
# CCG Scope Theory

CCG derivational structure determines available scope readings (Steedman 2000 Ch. 6).
-/

import Linglib.Theories.CCG.Core.Basic
import Linglib.Core.Interfaces.ScopeTheory
import Linglib.Phenomena.Quantification.ScopeWordOrder

namespace CCG.Scope

open CCG
open ScopeTheory
open Phenomena.ScopeWordOrder

/-- A scope-taking element in a CCG derivation. -/
structure ScopeTaker where
  id : String
  surfacePosition : Nat
  cat : Cat
  deriving Repr

/-- Derivation type for scope analysis. -/
inductive DerivationType where
  | directApp    -- Standard application: surface scope only
  | typeRaised   -- Type-raising: enables scope flexibility
  | composed     -- Composition: enables scope inversion
  deriving DecidableEq, BEq, Repr

/-- Analyze derivation to determine its type. -/
def analyzeDerivation : DerivStep → DerivationType
  | .lex _ => .directApp
  | .fapp d1 d2 =>
    match analyzeDerivation d1, analyzeDerivation d2 with
    | .typeRaised, _ | _, .typeRaised => .typeRaised
    | .composed, _ | _, .composed => .composed
    | _, _ => .directApp
  | .bapp d1 d2 =>
    match analyzeDerivation d1, analyzeDerivation d2 with
    | .typeRaised, _ | _, .typeRaised => .typeRaised
    | .composed, _ | _, .composed => .composed
    | _, _ => .directApp
  | .fcomp _ _ => .composed
  | .bcomp _ _ => .composed
  | .ftr _ _ => .typeRaised
  | .btr _ _ => .typeRaised
  | .coord d1 d2 =>
    match analyzeDerivation d1, analyzeDerivation d2 with
    | .typeRaised, _ | _, .typeRaised => .typeRaised
    | .composed, _ | _, .composed => .composed
    | _, _ => .directApp

/-- Determine scope availability from derivation type. -/
def derivationTypeToAvailability : DerivationType → BinaryScopeAvailability
  | .directApp => .surfaceOnly
  | .typeRaised => .ambiguous
  | .composed => .ambiguous

/-- A CCG derivation annotated with scope-taker information. -/
structure ScopedDerivation where
  deriv : DerivStep
  scopeTakers : List ScopeTaker
  hasTwoOrMore : scopeTakers.length ≥ 2 := by decide
  deriving Repr

def ScopedDerivation.availability (sd : ScopedDerivation) : BinaryScopeAvailability :=
  derivationTypeToAvailability (analyzeDerivation sd.deriv)

def ScopedDerivation.toAvailableScopes (sd : ScopedDerivation) : AvailableScopes :=
  let ids := sd.scopeTakers.map (·.id)
  sd.availability.toAvailableScopes (ids.head!) (ids.tail.head!)

/-- Marker type for CCG scope theory. -/
def CCGScopeTheory : Type := Unit

instance : HasAvailableScopes CCGScopeTheory ScopedDerivation where
  availableScopes := ScopedDerivation.toAvailableScopes

-- Examples

def everyHorse_surface : DerivStep :=
  .bapp (.lex ⟨"every horse", NP⟩) (.lex ⟨"didn't jump", IV⟩)

def everyHorse_inverse : DerivStep :=
  let everyHorse_tr := DerivStep.ftr (.lex ⟨"every horse", NP⟩) S
  .fcomp everyHorse_tr (.lex ⟨"didn't jump", IV⟩)

#eval analyzeDerivation everyHorse_surface  -- directApp
#eval analyzeDerivation everyHorse_inverse  -- composed

-- Connection to Phenomena Data

/-- Map Phenomena.ScopeWordOrder.VerbOrder to CCG derivation type. -/
def verbOrderToDerivationType : VerbOrder → DerivationType
  | .verbRaising => .composed           -- Object + embedded verb via composition
  | .verbProjectionRaising => .directApp -- Matrix verb first, standard application

/-- Helper to convert ScopeAvailability to BinaryScopeAvailability. -/
def ScopeAvailability.toBinaryScopeAvailability : ScopeAvailability → BinaryScopeAvailability
  | .surfaceOnly => .surfaceOnly
  | .ambiguous => .ambiguous

/-- CCG prediction matches observed scope availability. -/
theorem ccg_predicts_verb_raising_scope (vo : VerbOrder) :
    derivationTypeToAvailability (verbOrderToDerivationType vo) =
    ScopeAvailability.toBinaryScopeAvailability (wordOrderToAvailability vo) := by
  cases vo <;> rfl

end CCG.Scope
