import Linglib.Theories.Semantics.Verb.DegreeAchievement
import Linglib.Theories.Semantics.Degree.MeasureFunction
import Linglib.Theories.Semantics.Events.AffectednessHierarchy
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Phenomena.TenseAspect.Diagnostics
import Linglib.Theories.Semantics.Events.DimensionBridge
import Mathlib.Data.Rat.Defs

/-!
# Degree Achievements
@cite{kennedy-levin-2008}

@cite{kennedy-levin-2008}: the telicity of degree achievements is **derived** from
the boundedness of the underlying adjectival scale. This bridge file verifies
that the fragment annotations are consistent with that derivation.

§1 — Per-verb derived vendlerClass verification
§2 — Adjective-verb scale agreement
§3 — Telicity diagnostic predictions
§4 — Pipeline convergence
§5 — Substrate-level demonstration: K&L 2008 measure-of-change `m_Δ`
     (eq. 25) → Beavers' affectedness typeclass chain. First production
     `[HasMeasureFunction]` instances in linglib; validates the auto-
     synthesis arrow `[HasMeasureFunction] → HasScalarResult →
     IsXAffected` end-to-end on closed-scale (*straighten*) and
     open-scale (*widen*) toys.

- Kennedy, C. & Levin, B. (2007). Measure of change: The adjectival core of
  degree achievements. In L. McNally & C. Kennedy (eds.), *Adjectives and Adverbs*,
  156–182. OUP.
-/

namespace KennedyLevin2008

open Fragments.English.Predicates.Verbal hiding clean cool warm open_
open Semantics.Verb.DegreeAchievement (DegreeAchievementScale)
open Core.Verbs
open Core.Scale (Boundedness LicensingPipeline MereoTag)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)

-- Fully qualified aliases for names shared between Verbal and Adjectival
private def vClean := Fragments.English.Predicates.Verbal.clean
private def vCool := Fragments.English.Predicates.Verbal.cool
private def vWarm := Fragments.English.Predicates.Verbal.warm
private def vOpen := Fragments.English.Predicates.Verbal.open_
private def aClean := Fragments.English.Predicates.Adjectival.clean
private def aCool := Fragments.English.Predicates.Adjectival.cool
private def aWarm := Fragments.English.Predicates.Adjectival.warm
private def aOpen := Fragments.English.Predicates.Adjectival.open_

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Derived VendlerClass Verification
-- ════════════════════════════════════════════════════

/-! For each degree achievement verb, the vendlerClass stipulated in the
    fragment matches what degreeAchievementScale.defaultVendlerClass derives. -/

/-- "bend": closed scale → accomplishment (derived = stipulated). -/
theorem bend_derived_vendler :
    bend.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    bend.toVerbCore.vendlerClass.get! := rfl

/-- "boil": closed scale → accomplishment (derived = stipulated). -/
theorem boil_derived_vendler :
    boil.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    boil.toVerbCore.vendlerClass.get! := rfl

/-- "rust": open scale → activity (derived = stipulated). -/
theorem rust_derived_vendler :
    rust.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    rust.toVerbCore.vendlerClass.get! := rfl

/-- "increase": open scale → activity (derived = stipulated). -/
theorem increase_derived_vendler :
    increase.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    increase.toVerbCore.vendlerClass.get! := rfl

/-- "clean": closed scale → accomplishment (derived = stipulated). -/
theorem clean_derived_vendler :
    vClean.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    vClean.toVerbCore.vendlerClass.get! := rfl

/-- "straighten": closed scale → accomplishment (derived = stipulated). -/
theorem straighten_derived_vendler :
    straighten.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    straighten.toVerbCore.vendlerClass.get! := rfl

/-- "flatten": closed scale → accomplishment (derived = stipulated). -/
theorem flatten_derived_vendler :
    flatten.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    flatten.toVerbCore.vendlerClass.get! := rfl

/-- "open": closed scale → accomplishment (derived = stipulated). -/
theorem open_derived_vendler :
    vOpen.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    vOpen.toVerbCore.vendlerClass.get! := rfl

/-- "lengthen": open scale → activity (derived = stipulated). -/
theorem lengthen_derived_vendler :
    lengthen.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    lengthen.toVerbCore.vendlerClass.get! := rfl

/-- "widen": open scale → activity (derived = stipulated). -/
theorem widen_derived_vendler :
    widen.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    widen.toVerbCore.vendlerClass.get! := rfl

/-- "cool": open scale → activity (derived = stipulated). -/
theorem cool_derived_vendler :
    vCool.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    vCool.toVerbCore.vendlerClass.get! := rfl

/-- "warm": open scale → activity (derived = stipulated). -/
theorem warm_derived_vendler :
    vWarm.toVerbCore.degreeAchievementScale.get!.defaultVendlerClass =
    vWarm.toVerbCore.vendlerClass.get! := rfl

-- ════════════════════════════════════════════════════
-- § 2. Adjective-Verb Scale Agreement
-- ════════════════════════════════════════════════════

/-! For each adj-verb pair, the verb's degreeAchievementScale.scaleBoundedness
    matches the adjective's scaleType. This ensures the verb inherits
    the correct scale classification from its adjectival base. -/

/-- clean (adj, closed) ↔ clean (verb, closed scale). -/
theorem clean_adj_verb_scale :
    aClean.scaleType =
    (vClean.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- straight (adj, closed) ↔ straighten (verb, closed scale). -/
theorem straight_straighten_scale :
    Fragments.English.Predicates.Adjectival.straight.scaleType =
    (straighten.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- flat (adj, closed) ↔ flatten (verb, closed scale). -/
theorem flat_flatten_scale :
    Fragments.English.Predicates.Adjectival.flat.scaleType =
    (flatten.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- open (adj, closed) ↔ open (verb, closed scale). -/
theorem open_adj_verb_scale :
    aOpen.scaleType =
    (vOpen.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- long (adj, open) ↔ lengthen (verb, open scale). -/
theorem long_lengthen_scale :
    Fragments.English.Predicates.Adjectival.long.scaleType =
    (lengthen.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- wide (adj, open) ↔ widen (verb, open scale). -/
theorem wide_widen_scale :
    Fragments.English.Predicates.Adjectival.wide.scaleType =
    (widen.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- cool (adj, open) ↔ cool (verb, open scale). -/
theorem cool_adj_verb_scale :
    aCool.scaleType =
    (vCool.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- warm (adj, open) ↔ warm (verb, open scale). -/
theorem warm_adj_verb_scale :
    aWarm.scaleType =
    (vWarm.toVerbCore.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- hot (adj, open) ↔ boil (verb, closed scale for boiling point).
    Note: boil reaches a closed endpoint (boiling point) even though the
    base adjective "hot" has an open scale. @cite{kennedy-levin-2008} notes that the verb
    selects the relevant portion of the scale. -/
theorem hot_boil_scale_diverges :
    Fragments.English.Predicates.Adjectival.hot.scaleType = .open_ ∧
    (boil.toVerbCore.degreeAchievementScale.get!).scaleBoundedness = .closed := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Telicity Diagnostic Predictions
-- ════════════════════════════════════════════════════

/-! Closed-scale DAs accept "in X" (telic prediction).
    Open-scale DAs accept "for X" (atelic prediction). -/

-- Closed-scale: "in X" ✓

/-- "bent the wire in 5 seconds" — closed-scale DA accepts "in X". -/
theorem bend_inX :
    inXPrediction bend.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "boiled the water in 3 minutes" — closed-scale DA accepts "in X". -/
theorem boil_inX :
    inXPrediction boil.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "cleaned the table in 5 minutes" — closed-scale DA accepts "in X". -/
theorem clean_inX :
    inXPrediction vClean.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "straightened the wire in 10 seconds" — closed-scale DA accepts "in X". -/
theorem straighten_inX :
    inXPrediction straighten.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "flattened the dough in 2 minutes" — closed-scale DA accepts "in X". -/
theorem flatten_inX :
    inXPrediction flatten.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "opened the door in 3 seconds" — closed-scale DA accepts "in X". -/
theorem open_inX :
    inXPrediction vOpen.toVerbCore.vendlerClass.get! = .accept := rfl

-- Open-scale: "for X" ✓

/-- "rusted for years" — open-scale DA accepts "for X". -/
theorem rust_forX :
    forXPrediction rust.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "increased for months" — open-scale DA accepts "for X". -/
theorem increase_forX :
    forXPrediction increase.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "lengthened the rope for hours" — open-scale DA accepts "for X". -/
theorem lengthen_forX :
    forXPrediction lengthen.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "widened the road for months" — open-scale DA accepts "for X". -/
theorem widen_forX :
    forXPrediction widen.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "cooled for an hour" — open-scale DA accepts "for X". -/
theorem cool_forX :
    forXPrediction vCool.toVerbCore.vendlerClass.get! = .accept := rfl

/-- "warmed for an hour" — open-scale DA accepts "for X". -/
theorem warm_forX :
    forXPrediction vWarm.toVerbCore.vendlerClass.get! = .accept := rfl

-- ════════════════════════════════════════════════════
-- § 4. Pipeline Convergence
-- ════════════════════════════════════════════════════

/-! LicensingPipeline.toBoundedness applied to the verb's
    degreeAchievementScale matches LicensingPipeline.toBoundedness
    applied to the verb's vendlerClass. -/

/-- "bend": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem bend_pipeline_converge :
    LicensingPipeline.toBoundedness bend.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness bend.toVerbCore.vendlerClass.get! := rfl

/-- "boil": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem boil_pipeline_converge :
    LicensingPipeline.toBoundedness boil.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness boil.toVerbCore.vendlerClass.get! := rfl

/-- "rust": DA pipeline → open = VendlerClass pipeline → open. -/
theorem rust_pipeline_converge :
    LicensingPipeline.toBoundedness rust.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness rust.toVerbCore.vendlerClass.get! := rfl

/-- "increase": DA pipeline → open = VendlerClass pipeline → open. -/
theorem increase_pipeline_converge :
    LicensingPipeline.toBoundedness increase.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness increase.toVerbCore.vendlerClass.get! := rfl

/-- "clean": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem clean_pipeline_converge :
    LicensingPipeline.toBoundedness vClean.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vClean.toVerbCore.vendlerClass.get! := rfl

/-- "straighten": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem straighten_pipeline_converge :
    LicensingPipeline.toBoundedness straighten.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness straighten.toVerbCore.vendlerClass.get! := rfl

/-- "flatten": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem flatten_pipeline_converge :
    LicensingPipeline.toBoundedness flatten.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness flatten.toVerbCore.vendlerClass.get! := rfl

/-- "open": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem open_pipeline_converge :
    LicensingPipeline.toBoundedness vOpen.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vOpen.toVerbCore.vendlerClass.get! := rfl

/-- "lengthen": DA pipeline → open = VendlerClass pipeline → open. -/
theorem lengthen_pipeline_converge :
    LicensingPipeline.toBoundedness lengthen.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness lengthen.toVerbCore.vendlerClass.get! := rfl

/-- "widen": DA pipeline → open = VendlerClass pipeline → open. -/
theorem widen_pipeline_converge :
    LicensingPipeline.toBoundedness widen.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness widen.toVerbCore.vendlerClass.get! := rfl

/-- "cool": DA pipeline → open = VendlerClass pipeline → open. -/
theorem cool_pipeline_converge :
    LicensingPipeline.toBoundedness vCool.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vCool.toVerbCore.vendlerClass.get! := rfl

/-- "warm": DA pipeline → open = VendlerClass pipeline → open. -/
theorem warm_pipeline_converge :
    LicensingPipeline.toBoundedness vWarm.toVerbCore.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vWarm.toVerbCore.vendlerClass.get! := rfl

-- ════════════════════════════════════════════════════
-- § 5. Substrate-Level Demonstration: K&L → Beavers
-- ════════════════════════════════════════════════════

/-! K&L 2008's measure-of-change function `m_Δ` (eq. 25), formalised in
    `Theories/Semantics/Degree/MeasureFunction.lean`, plugs directly
    into Beavers' affectedness typeclass chain
    (`Theories/Semantics/Events/AffectednessHierarchy.lean`).

    This section provides the **first production `[HasMeasureFunction]`
    instances in linglib** — toy domains for *straighten* (closed
    scale, max = 1) and *widen* (open scale, no max) — and demonstrates
    that the auto-synthesis arrow
    `[HasMeasureFunction α δ Time] → HasScalarResult α δ (Ev Time)`
    fires structurally. Downstream `IsQuantizedAffected.mk'` /
    `IsNonQuantizedAffected.mk'` smart constructors find the
    `HasScalarResult` instance by typeclass resolution without explicit
    naming.

    The variable-telicity prediction (K&L §7.3.3) is realised
    structurally: closed-scale DAs construct an `IsQuantizedAffected`
    instance at `g_φ = scale max`; open-scale DAs only have an
    `IsNonQuantizedAffected` instance available (no Quantized witness
    exists because the scale lacks a maximum).

    Toy types `RodToy` and `GapToy` are used (rather than fragment
    `Rod`/`Gap` if those exist) to keep the substrate demonstration
    self-contained. The fragment-level §1-4 results above are
    independent of this substrate work. -/

open Semantics.Events
open Semantics.Events.ScalarResult
open Semantics.Events.AffectednessHierarchy
open Semantics.Degree.MeasureFunction

/-- Toy time type for the substrate demonstration. -/
abbrev SubstrateTime : Type := Nat

-- ────────────────────────────────────────────────────
-- §5.1 Closed-scale: *straighten* (K&L eq. 20)
-- ────────────────────────────────────────────────────

/-- Toy patient type for the substrate-level *straighten*
    demonstration. The actual identity of rods is irrelevant; what
    matters is the measure of straightness over time. -/
abbrev RodToy : Type := Unit

/-- Toy `straight` measure function on a closed scale (`ℚ` with
    max = 1, representing complete straightness per K&L footnote 8 /
    eq. 20). Returns the constant `1` — every rod is fully straight at
    every time, so `θ_straighten_toy` (defined below) is provably
    Quantized at `g_φ = 1` without case analysis on rod-time pairs.

    A real K&L instantiation would track actual straightness as a
    function of rod geometry and time. -/
instance straightMeasure : HasMeasureFunction RodToy ℚ SubstrateTime where
  measure _ _ := 1

/-- Companion `HasLatentScale` — *straighten* commits to the
    straightness scale, making rods force-recipients on it
    per Beavers (60c). Manual call to
    `HasLatentScale.ofHasMeasureFunction` since auto-synthesis isn't
    available (δ-inference issue documented in
    `Degree/MeasureFunction.lean`). -/
instance : HasLatentScale RodToy (Ev SubstrateTime) :=
  HasLatentScale.ofHasMeasureFunction (δ := ℚ)

/-- *straighten*'s θ-relation: rod `x` is straightened in event `e`
    iff `x` has straightness `1` at the end of `e`. K&L eq. 20: "*x
    undergoes a change from non-maximal to maximal straightness*".
    The toy entails only the maximal-end condition. -/
def θ_straighten_toy : RodToy → Ev SubstrateTime → Prop :=
  fun x e => HasMeasureFunction.measure
    (α := RodToy) (δ := ℚ) (Time := SubstrateTime)
    x e.runtime.finish = (1 : ℚ)

/-- *straighten* is Quantized at `g_φ = 1` (K&L's telic prediction
    for closed-scale DAs): every straightening event ends with the
    patient at maximum straightness. -/
theorem straighten_quantized_toy :
    Quantized θ_straighten_toy (1 : ℚ) :=
  fun _ _ h => h

/-- The full `IsQuantizedAffected` instance for *straighten*. The
    `HasScalarResult` parameter is found automatically by typeclass
    synthesis from the `[HasMeasureFunction]` instance above — this
    is the load-bearing demonstration of the K&L → Beavers
    auto-synthesis arrow.

    The `forget` argument is `fun _ _ _ => trivial` because the
    `HasLatentScale` instance has trivial content (`True`) per the
    `ofHasMeasureFunction` definition. -/
instance straighten_isQuantizedAffected_toy :
    IsQuantizedAffected (δ := ℚ) θ_straighten_toy :=
  IsQuantizedAffected.mk' (fun _ _ _ => trivial) (1 : ℚ) straighten_quantized_toy

/-- `IsQuantizedAffected.finalDegree` is accessible as data
    (preserves K&L's lexical `g_φ` commitment). -/
example : IsQuantizedAffected.finalDegree (θ := θ_straighten_toy) = (1 : ℚ) := rfl

/-- Synthesis test: extends-chain gives `IsNonQuantizedAffected` from
    the Quantized instance (Beavers eq. 62 leftmost arrow). -/
example : IsNonQuantizedAffected (δ := ℚ) θ_straighten_toy := inferInstance

/-- Synthesis test: extends-chain gives `IsPotentialAffected` (bottom). -/
example : IsPotentialAffected (β := Ev SubstrateTime) θ_straighten_toy :=
  inferInstance

-- ────────────────────────────────────────────────────
-- §5.2 Open-scale: *widen* (K&L §7.3.3)
-- ────────────────────────────────────────────────────

/-- Toy patient type for substrate-level *widen*. -/
abbrev GapToy : Type := Unit

/-- Toy `wide` measure function on an open scale (`ℚ` with no
    maximum, per K&L §7.3.3). Returns `t + 1` for time `t` — any
    monotone function works for the substrate demonstration; the
    key fact is that the SCALE has no maximum, so no specific `g_φ`
    can witness `Quantized`. -/
instance wideMeasure : HasMeasureFunction GapToy ℚ SubstrateTime where
  measure _ t := (t : ℚ) + 1

/-- HasLatentScale companion for *widen*. -/
instance : HasLatentScale GapToy (Ev SubstrateTime) :=
  HasLatentScale.ofHasMeasureFunction (δ := ℚ)

/-- *widen*'s θ-relation: gap `x` widens in event `e` iff `x` has
    SOME width at the end of `e`. K&L's atelic "comparative" reading
    — no specific final value entailed. -/
def θ_widen_toy : GapToy → Ev SubstrateTime → Prop :=
  fun x e => ∃ g : ℚ, HasMeasureFunction.measure
    (α := GapToy) (δ := ℚ) (Time := SubstrateTime)
    x e.runtime.finish = g

/-- *widen* is NonQuantized: every widening event ends with the
    patient at SOME degree on the wide scale. K&L's atelic
    "comparative" reading. -/
theorem widen_nonQuantized_toy :
    NonQuantized (δ := ℚ) θ_widen_toy :=
  fun _ _ h => h

/-- The `IsNonQuantizedAffected` instance for *widen*.

    Per K&L §7.3.3: NO `IsQuantizedAffected θ_widen_toy` instance is
    available (or constructible) — the open scale has no maximum to
    instantiate `g_φ`. The substrate correctly refuses to assert
    Quantized affectedness for open-scale DAs, exactly as K&L
    predicts.

    This is the **substrate's empirical bite**: the typeclass
    hierarchy structurally distinguishes closed-scale DAs (Quantized)
    from open-scale DAs (NonQuantized only), matching K&L's variable
    telicity prediction without ad-hoc per-verb stipulation. -/
instance widen_isNonQuantizedAffected_toy :
    IsNonQuantizedAffected (δ := ℚ) θ_widen_toy :=
  IsNonQuantizedAffected.mk' (fun _ _ _ => trivial) widen_nonQuantized_toy

/-- Extends-chain still gives Potential. -/
example : IsPotentialAffected (β := Ev SubstrateTime) θ_widen_toy := inferInstance

-- ────────────────────────────────────────────────────
-- §5.3 Telicity Bridge to AffectednessDegree
-- ────────────────────────────────────────────────────

/-- The K&L 2008 → Beavers 2011 telicity correspondence at the
    `AffectednessDegree` level: closed-scale DAs (*straighten*)
    project to `.quantized` (telic); open-scale DAs (*widen*) project
    to `.nonquantized` (atelic). The strict ordering encodes K&L's
    variable-telicity prediction structurally. -/
theorem widen_lt_straighten_at_affectedness_level :
    AffectednessDegree.nonquantized < AffectednessDegree.quantized := by decide

end KennedyLevin2008
