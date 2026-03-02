import Linglib.Theories.Semantics.Lexical.Verb.DegreeAchievement
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Phenomena.TenseAspect.DiagnosticsBridge
import Linglib.Theories.Semantics.Events.DimensionBridge

/-!
# Degree Achievement Bridge
@cite{kennedy-levin-2008}

Kennedy & Levin (2007): the telicity of degree achievements is **derived** from
the boundedness of the underlying adjectival scale. This bridge file verifies
that the fragment annotations are consistent with that derivation.

§1 — Per-verb derived vendlerClass verification
§2 — Adjective-verb scale agreement
§3 — Telicity diagnostic predictions
§4 — Pipeline convergence

- Kennedy, C. & Levin, B. (2007). Measure of change: The adjectival core of
  degree achievements. In L. McNally & C. Kennedy (eds.), *Adjectives and Adverbs*,
  156–182. OUP.
-/

namespace Phenomena.TenseAspect.Bridge.DegreeAchievement

open Fragments.English.Predicates.Verbal hiding clean cool warm open_
open Semantics.Lexical.Verb.DegreeAchievement (DegreeAchievementScale)
open Semantics.Lexical.Verb.Aspect (VendlerClass Telicity)
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
    base adjective "hot" has an open scale. K&L 2007 notes that the verb
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

end Phenomena.TenseAspect.Bridge.DegreeAchievement
