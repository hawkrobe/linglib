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

/-- Derivation type for scope analysis. -/
inductive DerivationType where
  | directApp    -- Standard application: surface scope only
  | typeRaised   -- Type-raising: enables scope flexibility
  | composed     -- Composition: enables scope inversion
  deriving DecidableEq, Repr

/-- Combine daughters' derivation types: type-raising dominates, then composition. -/
def DerivationType.join : DerivationType → DerivationType → DerivationType
  | .typeRaised, _ | _, .typeRaised => .typeRaised
  | .composed, _ | _, .composed => .composed
  | _, _ => .directApp

/-- Analyze a derivation to determine its type. -/
def analyzeDerivation {α : Type*} : {c : Cat α} → Derivation α c → DerivationType
  | _, .lex _ => .directApp
  | _, .fapp d1 d2 => (analyzeDerivation d1).join (analyzeDerivation d2)
  | _, .bapp d1 d2 => (analyzeDerivation d1).join (analyzeDerivation d2)
  | _, .fcomp _ _ => .composed
  | _, .bcomp _ _ => .composed
  | _, .fcompx _ _ => .composed
  | _, .ftr _ _ => .typeRaised
  | _, .btr _ _ => .typeRaised
  | _, .coord _ d1 d2 => (analyzeDerivation d1).join (analyzeDerivation d2)

/-- Determine scope availability from derivation type. -/
def derivationTypeToAvailability : DerivationType → BinaryScopeAvailability
  | .directApp => .surfaceOnly
  | .typeRaised => .ambiguous
  | .composed => .ambiguous

-- Examples

/-- Surface-scope derivation: subject and predicate combine by plain application. -/
def everyHorse_surface : Derivation Atom S :=
  .bapp (.lex ⟨"every horse", NP⟩) (.lex ⟨"didn't jump", IV⟩)

/-- Inverse-capable derivation: the type-raised subject composes with the negated
auxiliary before the verb applies. -/
def everyHorse_inverse : Derivation Atom S :=
  .fapp (.fcomp (.ftr (.lex ⟨"every horse", NP⟩) S)
    (.lex ⟨"didn't", (S \ NP) / (S \ NP)⟩)) (.lex ⟨"jump", IV⟩)

example : analyzeDerivation everyHorse_surface = .directApp := rfl
example : analyzeDerivation everyHorse_inverse = .composed := rfl

end CCG.Scope
