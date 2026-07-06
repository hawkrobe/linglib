import Linglib.Semantics.Degree.Granularity
import Linglib.Semantics.Degree.Discrete
import Linglib.Semantics.Degree.Gradability.Construction

/-!
# Granularity and *Just*: Degree Morphology [thomas-deo-2020]

Grounds the approximative readings of *just* with degree constructions in
the granularity semantics of `Degree.Granularity`: with
equatives the negative component of *just* is vacuous (`just_vacuous_iff`,
"just as tall as" ≈ "exactly"), while with comparatives it forces failure
at coarser grains (`just_rules_out`, "just taller than" ≈ "barely").

## Main declarations

- `equality_grounded`, `proximity_grounded`: the two readings as instances
  of the granularity lemmas
- `GranularityDatum`, `allGranularityData`: the §3 equative/comparative data
- `all_noncancellable`: the granularity contribution is at-issue (§3.3)
-/

namespace ThomasDeo2020

open Degree.Granularity
open Degree (AdjectivalConstruction)

-- ════════════════════════════════════════════════════
-- § 1. Formal Grounding
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
-- § 2. Empirical Data ([thomas-deo-2020]: §3)
-- ════════════════════════════════════════════════════

/-! ### §3 data: *just* with equatives and comparatives

Each datum records the construction type and the cancellability of the
granularity inference. -/

/-- Whether *just*'s inference can be cancelled with "but...". -/
inductive Cancellability where
  | cancellable     -- inference can be followed by "but..."
  | nonCancellable  -- "#but..." is infelicitous
  deriving Repr, DecidableEq

/-- A granularity-specific datum: example + construction + cancellability. -/
structure GranularityDatum where
  sentence : String
  construction : AdjectivalConstruction
  cancellability : Cancellability
  paraphrase : String
  exampleNum : Nat  -- paper example number
  deriving Repr, DecidableEq

-- §3.1 Equatives

/-- (14) "The amaryllis are just as tall as the hollyhocks"
    ≈ "exactly as tall as". -/
def eq_amaryllis : GranularityDatum :=
  { sentence := "The amaryllis are just as tall as the hollyhocks"
  , construction := .equative
  , cancellability := .nonCancellable
  , paraphrase := "exactly as tall as"
  , exampleNum := 14 }

/-- (15) "Anna is just as old as Maria" ≈ "exactly as old as". -/
def eq_anna_maria : GranularityDatum :=
  { sentence := "Anna is just as old as Maria"
  , construction := .equative
  , cancellability := .nonCancellable
  , paraphrase := "exactly as old as"
  , exampleNum := 15 }

-- §3.2 Comparatives

/-- (21) "Fafen is just older than Siri" ≈ "barely older than". -/
def comp_fafen_siri : GranularityDatum :=
  { sentence := "Fafen is just older than Siri"
  , construction := .comparative
  , cancellability := .nonCancellable
  , paraphrase := "barely/slightly older than"
  , exampleNum := 21 }

/-- (23) "#Fafen is just older than Siri, but by a lot"
    — the proximity inference is non-cancellable.
    Contrast with (24): "Fafen is only older than Siri, but by a lot" (OK). -/
def comp_fafen_cancel : GranularityDatum :=
  { sentence := "#Fafen is just older than Siri, but by a lot"
  , construction := .comparative
  , cancellability := .nonCancellable
  , paraphrase := "barely older — cannot be followed by 'but by a lot'"
  , exampleNum := 23 }

/-- (25) "This album is just more expensive than that one"
    ≈ "barely more expensive". -/
def comp_album : GranularityDatum :=
  { sentence := "This album is just more expensive than that one"
  , construction := .comparative
  , cancellability := .nonCancellable
  , paraphrase := "barely/slightly more expensive"
  , exampleNum := 25 }

def allGranularityData : List GranularityDatum :=
  [eq_amaryllis, eq_anna_maria, comp_fafen_siri, comp_fafen_cancel, comp_album]

-- ════════════════════════════════════════════════════
-- § 3. Cancellability
-- ════════════════════════════════════════════════════

/-- The granularity contribution of *just* is at-issue (§3.3), not a
    cancellable implicature: every datum's inference is non-cancellable. -/
theorem all_noncancellable :
    ∀ d ∈ allGranularityData, d.cancellability = .nonCancellable := by
  decide

end ThomasDeo2020
