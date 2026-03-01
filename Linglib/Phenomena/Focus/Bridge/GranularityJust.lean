import Linglib.Theories.Semantics.Degree.Granularity
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Phenomena.Focus.Exclusives

/-!
# Granularity Bridge: *Just* + Degree Morphology @cite{thomas-deo-2020}
@cite{deo-thomas-2025}

Connects the formal semantics of approximative *just* from
`Theories.Semantics.Degree.Granularity` to the *just* flavor data in
`Phenomena.Focus.Exclusives`.

The `.precisifyingEquality` flavor ("just as tall as" ≈ "exactly")
follows from `just_vacuous_iff`: the negative component of *just* is
vacuous for equatives. The `.precisifyingProximity` flavor ("just taller
than" ≈ "barely") follows from `just_rules_out`: the negative component
forces failure at coarser grains.

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

-- ════════════════════════════════════════════════════
-- § 4. Empirical Data (Thomas & Deo 2020: §3)
-- ════════════════════════════════════════════════════

/-! ### §3 data: *just* with equatives and comparatives

The paper's key empirical observations, encoded as `JustDatum` entries
from `Exclusives.lean`. Each datum has a predicted flavor and a
predicted cancellability status. -/

/-- Whether *just*'s inference can be cancelled with "but...". -/
inductive Cancellability where
  | cancellable     -- inference can be followed by "but..."
  | nonCancellable  -- "#but..." is infelicitous
  deriving Repr, DecidableEq, BEq

/-- A granularity-specific datum: example + construction + predicted
    flavor + cancellability. -/
structure GranularityDatum where
  sentence : String
  construction : AdjectivalConstruction
  predictedFlavor : JustFlavor
  cancellability : Cancellability
  paraphrase : String
  exampleNum : Nat  -- paper example number
  deriving Repr

-- §3.1 Equatives

/-- (14) "The amaryllis are just as tall as the hollyhocks"
    → precisifying equality ("exactly as tall as"). -/
def eq_amaryllis : GranularityDatum :=
  { sentence := "The amaryllis are just as tall as the hollyhocks"
  , construction := .equative
  , predictedFlavor := .precisifyingEquality
  , cancellability := .nonCancellable
  , paraphrase := "exactly as tall as"
  , exampleNum := 14 }

/-- (15) "Anna is just as old as Maria"
    → precisifying equality ("exactly as old as"). -/
def eq_anna_maria : GranularityDatum :=
  { sentence := "Anna is just as old as Maria"
  , construction := .equative
  , predictedFlavor := .precisifyingEquality
  , cancellability := .nonCancellable
  , paraphrase := "exactly as old as"
  , exampleNum := 15 }

-- §3.2 Comparatives

/-- (21) "Fafen is just older than Siri"
    → precisifying proximity ("barely older than"). -/
def comp_fafen_siri : GranularityDatum :=
  { sentence := "Fafen is just older than Siri"
  , construction := .comparative
  , predictedFlavor := .precisifyingProximity
  , cancellability := .nonCancellable
  , paraphrase := "barely/slightly older than"
  , exampleNum := 21 }

/-- (23) "#Fafen is just older than Siri, but by a lot"
    → proximity inference is non-cancellable.
    Contrast with (24): "Fafen is only older than Siri, but by a lot" (OK). -/
def comp_fafen_cancel : GranularityDatum :=
  { sentence := "#Fafen is just older than Siri, but by a lot"
  , construction := .comparative
  , predictedFlavor := .precisifyingProximity
  , cancellability := .nonCancellable
  , paraphrase := "barely older — cannot be followed by 'but by a lot'"
  , exampleNum := 23 }

/-- (25) "This album is just more expensive than that one"
    → precisifying proximity ("barely more expensive"). -/
def comp_album : GranularityDatum :=
  { sentence := "This album is just more expensive than that one"
  , construction := .comparative
  , predictedFlavor := .precisifyingProximity
  , cancellability := .nonCancellable
  , paraphrase := "barely/slightly more expensive"
  , exampleNum := 25 }

def allGranularityData : List GranularityDatum :=
  [eq_amaryllis, eq_anna_maria, comp_fafen_siri, comp_fafen_cancel, comp_album]

-- ════════════════════════════════════════════════════
-- § 5. Per-Datum Prediction Verification
-- ════════════════════════════════════════════════════

/-- All equative data points get the predicted equality flavor. -/
theorem eq_data_flavor :
    eq_amaryllis.predictedFlavor = justFlavorFromConstruction .equative ∧
    eq_anna_maria.predictedFlavor = justFlavorFromConstruction .equative :=
  ⟨rfl, rfl⟩

/-- All comparative data points get the predicted proximity flavor. -/
theorem comp_data_flavor :
    comp_fafen_siri.predictedFlavor = justFlavorFromConstruction .comparative ∧
    comp_fafen_cancel.predictedFlavor = justFlavorFromConstruction .comparative ∧
    comp_album.predictedFlavor = justFlavorFromConstruction .comparative :=
  ⟨rfl, rfl, rfl⟩

/-- All data points have non-cancellable inferences — the granularity
    contribution of *just* is at-issue (§3.3), not a cancellable
    implicature. -/
theorem all_noncancellable :
    eq_amaryllis.cancellability = .nonCancellable ∧
    eq_anna_maria.cancellability = .nonCancellable ∧
    comp_fafen_siri.cancellability = .nonCancellable ∧
    comp_fafen_cancel.cancellability = .nonCancellable ∧
    comp_album.cancellability = .nonCancellable :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Equative data match the existing `precisifying_eq_full` flavor. -/
theorem eq_data_matches_exclusives :
    eq_amaryllis.predictedFlavor = precisifying_eq_full.flavor ∧
    eq_anna_maria.predictedFlavor = precisifying_eq_full.flavor :=
  ⟨rfl, rfl⟩

/-- Comparative data match the existing `precisifying_prox_older` flavor. -/
theorem comp_data_matches_exclusives :
    comp_fafen_siri.predictedFlavor = precisifying_prox_older.flavor ∧
    comp_album.predictedFlavor = precisifying_prox_older.flavor :=
  ⟨rfl, rfl⟩

end Phenomena.Focus.Bridge.GranularityJust
