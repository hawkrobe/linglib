import Linglib.Theories.Semantics.Degree.Granularity
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Phenomena.Focus.Exclusives

/-!
# Granularity Bridge: *Just* + Degree Morphology @cite{thomas-deo-2020}

Connects the formal semantics of approximative *just* from
`Theories.Semantics.Degree.Granularity` to the *just* flavor data in
`Phenomena.Focus.Exclusives`.

The `.precisifyingEquality` flavor ("just as tall as" ≈ "exactly")
follows from `just_vacuous_iff`: the negative component of *just* is
vacuous for equatives. The `.precisifyingProximity` flavor ("just taller
than" ≈ "barely") follows from `just_rules_out`: the negative component
forces failure at coarser grains.

## References

- Thomas, W. & Deo, A. (2020). The interaction of *just* with modified
  scalar predicates. *Sinn und Bedeutung* 24.
- Deo, A. & Thomas, W. (2025). Addressing the widest answerable question.
-/

namespace Phenomena.Focus.Bridge.GranularityJust

open Semantics.Degree.Granularity
open Semantics.Degree (AdjectivalConstruction)
open Phenomena.Focus.Exclusives

-- ════════════════════════════════════════════════════
-- § 1. Construction → Flavor Derivation
-- ════════════════════════════════════════════════════

/-- Derive *just* flavor from adjectival construction type.
    Thomas & Deo (2020) predict:
    - comparative + just → precisifying proximity (barely)
    - equative + just → precisifying equality (exactly) -/
def justFlavorFromConstruction : AdjectivalConstruction → JustFlavor
  | .comparative => .precisifyingProximity
  | .equative => .precisifyingEquality
  | _ => .complementExclusion

-- ════════════════════════════════════════════════════
-- § 2. Per-Datum Verification
-- ════════════════════════════════════════════════════

/-- "Fafen is just older than Siri" — comparative + just = proximity. -/
theorem comparative_yields_proximity :
    justFlavorFromConstruction .comparative =
    precisifying_prox_older.flavor := rfl

/-- Equative + just = equality ("just as tall as" ≈ "exactly as tall as").
    Note: `precisifying_eq_full` ("just full") achieves equality via a
    closed-scale endpoint standard, not via equative morphology. The
    shared flavor (`.precisifyingEquality`) reflects parallel pragmatic
    effects through different compositional routes. -/
theorem equative_yields_equality :
    justFlavorFromConstruction .equative =
    precisifying_eq_full.flavor := rfl

-- ════════════════════════════════════════════════════
-- § 3. Formal Grounding
-- ════════════════════════════════════════════════════

/-- The equality reading for equatives is grounded: when the finest
    grain is the strongest (largest lo → fine entails coarse), *just*'s
    negative component is vacuous, so "just as tall as" reduces to the
    equative at finest grain. Instantiates `just_vacuous_iff`. -/
theorem equality_grounded {D G : Type*} [LinearOrder D]
    (p : G → D → Prop) (finest : G)
    (h : ∀ g, atLeastAsStrong p finest g) (μ_x : D) :
    approxJust p finest μ_x ↔ p finest μ_x :=
  just_vacuous_iff p finest h μ_x

/-- The proximity reading for comparatives is grounded: when the finest
    grain is NOT the strongest at some coarser grain g, *just* rules out
    truth at g. Instantiates `just_rules_out`. -/
theorem proximity_grounded {D G : Type*} [LinearOrder D]
    (p : G → D → Prop) (finest g : G)
    (h : ¬ atLeastAsStrong p finest g)
    (μ_x : D) (hjust : approxJust p finest μ_x) :
    ¬ p g μ_x :=
  just_rules_out p finest g h μ_x hjust

end Phenomena.Focus.Bridge.GranularityJust
