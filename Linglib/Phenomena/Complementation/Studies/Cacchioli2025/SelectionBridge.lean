import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Phenomena.Complementation.Typology

/-!
# Complementation-Agree Bridge: CTPClass → FeatureVal

Connects Noonan's (2007) complement-taking predicate typology (CTPClass,
in `Phenomena/Complementation/Typology.lean`) to Minimalist feature checking
(FeatureVal, in `Theories/Syntax/Minimalism/Core/Agree.lean`).

The key insight: a matrix verb's CTP class determines which clause-typing
features it checks via Agree. Realis CTPs select [+finite] (indicative);
irrealis CTPs select [-finite] (subjunctive/irrealis). This bridges the
typological generalization to the syntactic mechanism.

## Connections

- **Agree.lean**: `FeatureVal.finite`, `FeatureVal.factive` — clause-typing features
- **Typology.lean**: `CTPClass`, `ctpRealityStatus` — typological classification
- **Cacchioli (2025)**: Tigrinya prefix selection follows from CTP class → feature mapping
-/

namespace Phenomena.Complementation.SelectionBridge

open Minimalism
open Phenomena.Complementation.Typology

/-- Map CTP reality status to [±finite] selection.

    Realis CTPs (utterance, knowledge, commentative, ...) select [+finite]
    complements — indicative/realis clauses whose Fin head bears [+finite].

    Irrealis CTPs (desiderative, manipulative, modal, ...) select [-finite]
    complements — subjunctive/irrealis clauses whose Fin head bears [-finite].

    Some classes are variable (perception can take both finite and non-finite
    complements), so they return `none`. -/
def ctpToFiniteness : CTPClass → Option Bool
  | .utterance    => some true    -- "say that..." (indicative)
  | .knowledge    => some true    -- "know that..." (indicative)
  | .commentative => some true    -- "regret that..." (indicative, factive)
  | .propAttitude => some true    -- "believe that..." (indicative)
  | .desiderative => some false   -- "want to..." (subjunctive/irrealis)
  | .manipulative => some false   -- "make X do..." (irrealis)
  | .modal        => some false   -- "can/must..." (irrealis)
  | .phasal       => some false   -- "start -ing" (reduced complement)
  | .achievement  => some false   -- "manage to..." (irrealis)
  | .negative     => some false   -- "avoid -ing" (irrealis)
  | .perception   => none         -- "see X leave/leaving" (variable)
  | .pretence     => none         -- "pretend that/to..." (variable)

/-- Map CTP class to [±factive] selection.

    Factive CTPs presuppose the truth of their complement; their Force/C
    head bears [+factive]. Non-factive CTPs don't, bearing [-factive]. -/
def ctpToFactivity : CTPClass → Option Bool
  | .knowledge    => some true    -- "know that p" presupposes p
  | .commentative => some true    -- "regret that p" presupposes p
  | .perception   => some true    -- "see that p" presupposes p
  | .utterance    => some false   -- "say that p" doesn't presuppose p
  | .propAttitude => some false   -- "believe that p" doesn't presuppose p
  | .desiderative => some false   -- "want p" doesn't presuppose p
  | _             => none         -- other classes: variable or N/A

-- ============================================================================
-- Bridge theorems
-- ============================================================================

/-- Knowledge verbs select [+finite] (indicative) complements. -/
theorem knowledge_selects_finite :
    ctpToFiniteness .knowledge = some true := rfl

/-- Desiderative verbs select [-finite] (subjunctive/irrealis) complements. -/
theorem desiderative_selects_nonfinite :
    ctpToFiniteness .desiderative = some false := rfl

/-- Knowledge verbs select [+factive] complements. -/
theorem knowledge_is_factive :
    ctpToFactivity .knowledge = some true := rfl

/-- Utterance verbs select [-factive] complements. -/
theorem utterance_not_factive :
    ctpToFactivity .utterance = some false := rfl

/-- Realis CTP classes map to [+finite]. -/
theorem realis_implies_finite :
    ctpToFiniteness .utterance = some true ∧
    ctpToFiniteness .knowledge = some true ∧
    ctpToFiniteness .commentative = some true ∧
    ctpToFiniteness .propAttitude = some true := ⟨rfl, rfl, rfl, rfl⟩

/-- Irrealis CTP classes map to [-finite]. -/
theorem irrealis_implies_nonfinite :
    ctpToFiniteness .desiderative = some false ∧
    ctpToFiniteness .manipulative = some false ∧
    ctpToFiniteness .modal = some false ∧
    ctpToFiniteness .phasal = some false := ⟨rfl, rfl, rfl, rfl⟩

/-- Irrealis CTP classes always map to [-finite] when they have a value.
    The converse (realis → [+finite]) does not hold universally: phasal
    verbs are realis but take non-finite complements. -/
theorem irrealis_always_nonfinite (c : CTPClass)
    (b : Bool) (h : ctpToFiniteness c = some b)
    (hr : ctpRealityStatus c = .irrealis) : b = false := by
  cases c <;> simp_all [ctpToFiniteness, ctpRealityStatus]

end Phenomena.Complementation.SelectionBridge
