import Linglib.Theories.Semantics.Degree.Granularity
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Phenomena.Focus.Exclusives

/-!
# Granularity Bridge: *Just* + Degree Morphology @cite{thomas-deo-2020}

Connects the formal semantics of approximative *just* from
`Theories.Semantics.Degree.Granularity` to the *just* flavor data in
`Phenomena.Focus.Exclusives`.

The `.precisifyingEquality` flavor ("just as tall as" ≈ "exactly")
follows from `just_eq_reduces`: the negative component of *just* is
vacuous for equatives. The `.precisifyingProximity` flavor ("just taller
than" ≈ "barely") follows from `just_comp_rules_out_coarser`: the
negative component forces failure at coarser grains.

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

/-- The equality reading for equatives is grounded: *just*'s negative
    component is vacuous, so "just as tall as" = finest equative
    = standard equative (μ_x ≥ d_c). -/
theorem equality_grounded (μ_x d_c : Nat) :
    approxJust eqAtGran μ_x d_c ↔ eqAtGran .finest μ_x d_c :=
  just_eq_reduces μ_x d_c

/-- The proximity reading for comparatives is grounded: *just*'s
    negative component rules out coarser-grain truth. -/
theorem proximity_grounded (g : GranLevel) (hcoarser : 0 < g.ε)
    (μ_x d_c : Nat) (hjust : approxJust compAtGran μ_x d_c) :
    ¬ compAtGran g μ_x d_c :=
  just_comp_rules_out_coarser g hcoarser μ_x d_c hjust

end Phenomena.Focus.Bridge.GranularityJust
