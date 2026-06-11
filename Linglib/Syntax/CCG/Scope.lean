import Linglib.Syntax.CCG.Basic
import Linglib.Features.ScopeTypes

/-!
# CCG Scope Theory

Derivation-type analysis of quantifier scope: derivations built by
composition or type-raising license scope flexibility that pure
application does not. [steedman-2000] §6.8 uses this contrast for
West Germanic verb-cluster word orders (consumed by
`Linglib.Studies.Steedman2000`); the book's fuller
account (§4.4) refines the bare derivation–scope link, which Steedman
notes overgenerates as stated.
-/

namespace CCG.Scope

open CCG
open ScopeTheory

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
  deriving DecidableEq, Repr

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

-- Examples

def everyHorse_surface : DerivStep :=
  .bapp (.lex ⟨"every horse", NP⟩) (.lex ⟨"didn't jump", IV⟩)

def everyHorse_inverse : DerivStep :=
  let everyHorse_tr := DerivStep.ftr (.lex ⟨"every horse", NP⟩) S
  .fcomp everyHorse_tr (.lex ⟨"didn't jump", IV⟩)

#guard analyzeDerivation everyHorse_surface == .directApp
#guard analyzeDerivation everyHorse_inverse == .composed

end CCG.Scope
