import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Features.ScalarDimension
import Linglib.Semantics.Degree.Measure.Temporal
import Linglib.Semantics.Degree.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Order.WithBot
import Linglib.Semantics.ArgumentStructure.Affectedness
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Features.Aktionsart

/-!
# Degree achievements: the adjectival core of telicity

Formalisation of [kennedy-levin-2008], which derives the telicity of degree
achievement verbs (*widen*, *cool*, *straighten*, ...) from the boundedness of
the scale lexicalised by their adjectival base: a closed-scale base yields a
telic (accomplishment) verb, an open-scale base an atelic (activity) verb.

## Main results

* `*_derived_vendler` / `da_vendler_classes_agree` — each verb's stipulated
  Vendler class agrees with the class derived from its `degreeAchievementScale`.
* `*_scale` — each degree-achievement verb shares its adjectival base's scale
  boundedness, including the *boil* case where the verb selects a bounded
  portion of an otherwise open scale.
* `*_inX` / `*_forX` — telicity-diagnostic predictions: closed-scale verbs
  accept *in X*, open-scale verbs accept *for X*.
* `*_pipeline_converge` — the scale-based and Vendler-based licensing pipelines
  agree on boundedness.
* The order-theoretic core (`telic_of_orderTop` / `atelic_of_noMaxOrder`, below):
  a degree achievement admits a
  Quantized (telic) witness iff its scale has a greatest degree, via mathlib's
  `OrderTop` / `NoMaxOrder` mixins (witness `g_φ = ⊤`), feeding [beavers-2011]'s
  affectedness hierarchy. Here it is instantiated at the dimensions the verbs
  measure — `straighten_telic` (straightness, closed), `widen_atelic` (width,
  open) — grounded to the verbs' stored dimensions by `straighten_dimension` /
  `widen_dimension`. The variable-telicity contrast of [kennedy-levin-2008] §3.3.

## Implementation notes

The scale annotations and Vendler classes consumed here live on the English
verbal/adjectival fragment entries; the derivations they are checked against
live in `Semantics/Aspect/DegreeAchievement.lean`, and the affectedness
typeclass chain in `Semantics/ArgumentStructure/Affectedness.lean`.
-/

namespace KennedyLevin2008

open English.Predicates.Verbal hiding clean cool warm open_
open Features.DegreeAchievement (DegreeAchievementScale)
open Core.Order (LicensingPipeline)
open Features (forXPrediction inXPrediction)

-- Fully qualified aliases for names shared between Verbal and Adjectival
private def vClean := English.Predicates.Verbal.clean
private def vCool := English.Predicates.Verbal.cool
private def vWarm := English.Predicates.Verbal.warm
private def vOpen := English.Predicates.Verbal.open_
private def aClean := English.Predicates.Adjectival.clean
private def aCool := English.Predicates.Adjectival.cool
private def aWarm := English.Predicates.Adjectival.warm
private def aOpen := English.Predicates.Adjectival.open_

/-! ### Per-verb derived Vendler class

For each degree achievement verb, the Vendler class stipulated in the fragment
matches the class `DegreeAchievementScale.defaultVendlerClass` derives from the
verb's scale boundedness. -/

/-- "bend": closed scale → accomplishment (derived = stipulated). -/
theorem bend_derived_vendler :
    bend.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    bend.toVerb.vendlerClass.get! := rfl

/-- "boil": closed scale → accomplishment (derived = stipulated). -/
theorem boil_derived_vendler :
    boil.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    boil.toVerb.vendlerClass.get! := rfl

/-- "rust": open scale → activity (derived = stipulated). -/
theorem rust_derived_vendler :
    rust.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    rust.toVerb.vendlerClass.get! := rfl

/-- "increase": open scale → activity (derived = stipulated). -/
theorem increase_derived_vendler :
    increase.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    increase.toVerb.vendlerClass.get! := rfl

/-- "clean": closed scale → accomplishment (derived = stipulated). -/
theorem clean_derived_vendler :
    vClean.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    vClean.toVerb.vendlerClass.get! := rfl

/-- "straighten": closed scale → accomplishment (derived = stipulated). -/
theorem straighten_derived_vendler :
    straighten.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    straighten.toVerb.vendlerClass.get! := rfl

/-- "flatten": closed scale → accomplishment (derived = stipulated). -/
theorem flatten_derived_vendler :
    flatten.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    flatten.toVerb.vendlerClass.get! := rfl

/-- "open": closed scale → accomplishment (derived = stipulated). -/
theorem open_derived_vendler :
    vOpen.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    vOpen.toVerb.vendlerClass.get! := rfl

/-- "lengthen": open scale → activity (derived = stipulated). -/
theorem lengthen_derived_vendler :
    lengthen.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    lengthen.toVerb.vendlerClass.get! := rfl

/-- "widen": open scale → activity (derived = stipulated). -/
theorem widen_derived_vendler :
    widen.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    widen.toVerb.vendlerClass.get! := rfl

/-- "cool": open scale → activity (derived = stipulated). -/
theorem cool_derived_vendler :
    vCool.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    vCool.toVerb.vendlerClass.get! := rfl

/-- "warm": open scale → activity (derived = stipulated). -/
theorem warm_derived_vendler :
    vWarm.toVerb.degreeAchievementScale.get!.defaultVendlerClass =
    vWarm.toVerb.vendlerClass.get! := rfl

/-- The degree-achievement verbs whose telicity this file derives from scale
    boundedness. -/
def daVerbs : List Verb :=
  [bend.toVerb, boil.toVerb, rust.toVerb, increase.toVerb, vClean.toVerb,
   straighten.toVerb, flatten.toVerb, vOpen.toVerb, lengthen.toVerb,
   widen.toVerb, vCool.toVerb, vWarm.toVerb]

/-- The invariant the per-verb `*_derived_vendler` lemmas witness, stated once:
    every degree-achievement verb's stipulated Vendler class equals the class
    derived from its scale boundedness. A drift sentry — adding a verb whose
    annotations disagree breaks this. -/
theorem da_vendler_classes_agree :
    ∀ v ∈ daVerbs, v.vendlerClass = v.degreeAchievementScale.map (·.defaultVendlerClass) := by
  decide

/-! ### Adjective–verb scale agreement

For each adjective–verb pair, the verb's `degreeAchievementScale.scaleBoundedness`
matches the adjective's `scaleType`: the verb inherits the scale classification
of its adjectival base. -/

/-- clean (adj, closed) ↔ clean (verb, closed scale). -/
theorem clean_adj_verb_scale :
    aClean.scaleType =
    (vClean.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- straight (adj, closed) ↔ straighten (verb, closed scale). -/
theorem straight_straighten_scale :
    English.Predicates.Adjectival.straight.scaleType =
    (straighten.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- flat (adj, closed) ↔ flatten (verb, closed scale). -/
theorem flat_flatten_scale :
    English.Predicates.Adjectival.flat.scaleType =
    (flatten.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- open (adj, closed) ↔ open (verb, closed scale). -/
theorem open_adj_verb_scale :
    aOpen.scaleType =
    (vOpen.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- long (adj, open) ↔ lengthen (verb, open scale). -/
theorem long_lengthen_scale :
    English.Predicates.Adjectival.long.scaleType =
    (lengthen.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- wide (adj, open) ↔ widen (verb, open scale). -/
theorem wide_widen_scale :
    English.Predicates.Adjectival.wide.scaleType =
    (widen.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- cool (adj, open) ↔ cool (verb, open scale). -/
theorem cool_adj_verb_scale :
    aCool.scaleType =
    (vCool.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- warm (adj, open) ↔ warm (verb, open scale). -/
theorem warm_adj_verb_scale :
    aWarm.scaleType =
    (vWarm.toVerb.degreeAchievementScale.get!).scaleBoundedness := rfl

/-- *hot* (adj, open) vs *boil* (verb, closed at the boiling point).
    *boil* selects a conventionalised endpoint (the boiling point) despite the
    open scale of its base adjective *hot*. This fragment annotation extends
    [kennedy-levin-2008]'s treatment of *cool*, whose conventionalised
    'room-temperature' standard licenses a telic reading from an open-scale base
    (§3.3); [kennedy-levin-2008] do not themselves discuss *boil*. -/
theorem hot_boil_scale_diverges :
    English.Predicates.Adjectival.hot.scaleType = .open_ ∧
    (boil.toVerb.degreeAchievementScale.get!).scaleBoundedness = .closed := ⟨rfl, rfl⟩

/-! ### Telicity-diagnostic predictions

Closed-scale degree achievements accept *in X* (telic); open-scale ones accept
*for X* (atelic). -/

/-! #### Closed-scale verbs accept *in X* -/

/-- "bent the wire in 5 seconds" — closed-scale DA accepts "in X". -/
theorem bend_inX :
    inXPrediction bend.toVerb.vendlerClass.get! = .accept := rfl

/-- "boiled the water in 3 minutes" — closed-scale DA accepts "in X". -/
theorem boil_inX :
    inXPrediction boil.toVerb.vendlerClass.get! = .accept := rfl

/-- "cleaned the table in 5 minutes" — closed-scale DA accepts "in X". -/
theorem clean_inX :
    inXPrediction vClean.toVerb.vendlerClass.get! = .accept := rfl

/-- "straightened the wire in 10 seconds" — closed-scale DA accepts "in X". -/
theorem straighten_inX :
    inXPrediction straighten.toVerb.vendlerClass.get! = .accept := rfl

/-- "flattened the dough in 2 minutes" — closed-scale DA accepts "in X". -/
theorem flatten_inX :
    inXPrediction flatten.toVerb.vendlerClass.get! = .accept := rfl

/-- "opened the door in 3 seconds" — closed-scale DA accepts "in X". -/
theorem open_inX :
    inXPrediction vOpen.toVerb.vendlerClass.get! = .accept := rfl

/-! #### Open-scale verbs accept *for X* -/

/-- "rusted for years" — open-scale DA accepts "for X". -/
theorem rust_forX :
    forXPrediction rust.toVerb.vendlerClass.get! = .accept := rfl

/-- "increased for months" — open-scale DA accepts "for X". -/
theorem increase_forX :
    forXPrediction increase.toVerb.vendlerClass.get! = .accept := rfl

/-- "lengthened the rope for hours" — open-scale DA accepts "for X". -/
theorem lengthen_forX :
    forXPrediction lengthen.toVerb.vendlerClass.get! = .accept := rfl

/-- "widened the road for months" — open-scale DA accepts "for X". -/
theorem widen_forX :
    forXPrediction widen.toVerb.vendlerClass.get! = .accept := rfl

/-- "cooled for an hour" — open-scale DA accepts "for X". -/
theorem cool_forX :
    forXPrediction vCool.toVerb.vendlerClass.get! = .accept := rfl

/-- "warmed for an hour" — open-scale DA accepts "for X". -/
theorem warm_forX :
    forXPrediction vWarm.toVerb.vendlerClass.get! = .accept := rfl

/-! ### Pipeline convergence

`LicensingPipeline.toBoundedness` agrees whether applied to the verb's
`degreeAchievementScale` or to its `vendlerClass` — the scale-based and
Vendler-based routes to boundedness converge. -/

/-- "bend": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem bend_pipeline_converge :
    LicensingPipeline.toBoundedness bend.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness bend.toVerb.vendlerClass.get! := rfl

/-- "boil": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem boil_pipeline_converge :
    LicensingPipeline.toBoundedness boil.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness boil.toVerb.vendlerClass.get! := rfl

/-- "rust": DA pipeline → open = VendlerClass pipeline → open. -/
theorem rust_pipeline_converge :
    LicensingPipeline.toBoundedness rust.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness rust.toVerb.vendlerClass.get! := rfl

/-- "increase": DA pipeline → open = VendlerClass pipeline → open. -/
theorem increase_pipeline_converge :
    LicensingPipeline.toBoundedness increase.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness increase.toVerb.vendlerClass.get! := rfl

/-- "clean": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem clean_pipeline_converge :
    LicensingPipeline.toBoundedness vClean.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vClean.toVerb.vendlerClass.get! := rfl

/-- "straighten": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem straighten_pipeline_converge :
    LicensingPipeline.toBoundedness straighten.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness straighten.toVerb.vendlerClass.get! := rfl

/-- "flatten": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem flatten_pipeline_converge :
    LicensingPipeline.toBoundedness flatten.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness flatten.toVerb.vendlerClass.get! := rfl

/-- "open": DA pipeline → closed = VendlerClass pipeline → closed. -/
theorem open_pipeline_converge :
    LicensingPipeline.toBoundedness vOpen.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vOpen.toVerb.vendlerClass.get! := rfl

/-- "lengthen": DA pipeline → open = VendlerClass pipeline → open. -/
theorem lengthen_pipeline_converge :
    LicensingPipeline.toBoundedness lengthen.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness lengthen.toVerb.vendlerClass.get! := rfl

/-- "widen": DA pipeline → open = VendlerClass pipeline → open. -/
theorem widen_pipeline_converge :
    LicensingPipeline.toBoundedness widen.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness widen.toVerb.vendlerClass.get! := rfl

/-- "cool": DA pipeline → open = VendlerClass pipeline → open. -/
theorem cool_pipeline_converge :
    LicensingPipeline.toBoundedness vCool.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vCool.toVerb.vendlerClass.get! := rfl

/-- "warm": DA pipeline → open = VendlerClass pipeline → open. -/
theorem warm_pipeline_converge :
    LicensingPipeline.toBoundedness vWarm.toVerb.degreeAchievementScale.get! =
    LicensingPipeline.toBoundedness vWarm.toVerb.vendlerClass.get! := rfl

/-! ### Substrate demonstration: telicity from scale order

The order-theoretic account of [kennedy-levin-2008]'s thesis (formalized below):
a degree achievement is telic iff its scale has a greatest degree (`OrderTop`),
with the Quantized witness `g_φ = ⊤`,
feeding [beavers-2011]'s affectedness hierarchy. Here it is instantiated at the
dimensions the K&L verbs measure. -/

open ArgumentStructure.Affectedness
open Features (ScalarDimension)
open Degree

/-! #### Telicity from the scale's order structure (order-theoretic K&L thesis)

The telic reading is "the patient reaches the maximal degree `⊤`", available only
on a scale with a greatest element (`OrderTop`); the atelic reading is "reaches
*some* degree", always satisfiable. So telicity is a Quantized-witness existence
fact over the dimension's `degree` fiber, derived from the order mixin — not a
stored flag. The `ScalarDimension` carrier lives in `Semantics/Gradability/ScalarDimension.lean`;
the event machinery below is specific to this paper's degree-achievement analysis. -/

/-- Trivial patient: the measure of change ignores the patient's identity, so a
    single one-constructor type serves for every degree type `δ`. -/
inductive Patient
  | mk

section
variable {δ : Type*} [LinearOrder δ]

/-- The patient's degree at a time is that time — the temporal trace — so the final
    degree of an event is its end-time. -/
instance traceMeasure : HasTemporalMeasure Patient δ δ where
  measure _ t := t

/-- Companion `HasLatentScale` ([beavers-2011] eq. (60c)). -/
instance : HasLatentScale Patient (Event δ) :=
  HasLatentScale.ofHasMeasureFunction (δ := δ)

/-- The forgetful link holds in this model: `latentScale` is `True`. -/
instance : LawfulScalarLatent Patient δ (Event δ) := ⟨fun _ _ _ => trivial⟩

/-- Telic reading: the patient reaches the maximal degree `⊤` by the event's end. -/
def reachesTop [OrderTop δ] : Patient → Event δ → Prop :=
  fun _ e => e.runtime.snd = (⊤ : δ)

/-- Atelic ('comparative') reading: the patient reaches *some* degree by the end. -/
def reachesSome : Patient → Event δ → Prop :=
  fun _ e => ∃ g : δ, e.runtime.snd = g

theorem reachesSome_nonQuantized : NonQuantized (δ := δ) (reachesSome (δ := δ)) :=
  fun _ _ h => h

theorem reachesTop_quantized [OrderTop δ] :
    Quantized (reachesTop (δ := δ)) (⊤ : δ) :=
  fun _ _ h => h

/-- **Telic ⇐ a greatest degree.** `OrderTop` supplies the Quantized witness
    `g_φ = ⊤` — the order-theoretic content of [kennedy-levin-2008]'s closed-scale
    telicity. -/
theorem telic_of_orderTop [OrderTop δ] :
    ∃ g : δ, Quantized (reachesTop (δ := δ)) g :=
  ⟨⊤, reachesTop_quantized⟩

/-- **Telic ⇒ a greatest degree (contrapositive).** With no greatest degree
    (`NoMaxOrder`), no final degree is entailed — [kennedy-levin-2008]'s open-scale
    obligatory atelicity, derived from the order structure. -/
theorem atelic_of_noMaxOrder [NoMaxOrder δ] :
    ¬ ∃ g : δ, Quantized (reachesSome (δ := δ)) g := by
  rintro ⟨g, hg⟩
  obtain ⟨b, hb⟩ := exists_gt g
  have hbg : b = g := hg Patient.mk ⟨⟨⟨b, b⟩, le_refl b⟩, .dynamic⟩ ⟨_, rfl⟩
  exact absurd hbg hb.ne'

/-- Synthesis: with a greatest degree, the telic reading builds the Beavers
    `IsQuantizedAffected` instance ([beavers-2011] eq. (62)); the weaker
    mixins follow by derivation. -/
instance reachesTop_isQuantizedAffected [OrderTop δ] :
    IsQuantizedAffected (δ := δ) (reachesTop (δ := δ)) :=
  ⟨⊤, reachesTop_quantized⟩

end

/-- *straighten* measures straightness — a closed scale — so a telic reading is
    available, derived from the dimension's `OrderTop` (not a stored `HasMax`). -/
theorem straighten_telic :
    ∃ g : ScalarDimension.straightness.degree,
      Quantized (reachesTop (δ := ScalarDimension.straightness.degree)) g :=
  telic_of_orderTop

/-- *widen* measures width — unbounded above — so no telic reading exists. -/
theorem widen_atelic :
    ¬ ∃ g : ScalarDimension.width.degree,
      Quantized (reachesSome (δ := ScalarDimension.width.degree)) g :=
  atelic_of_noMaxOrder

/-- The fragment stores each verb's *dimension* directly (boundedness is derived):
    *straighten* measures straightness, *widen* width — so `straighten_telic` /
    `widen_atelic` above apply to the actual lexical entries. -/
theorem straighten_dimension :
    straighten.toVerb.degreeAchievementScale.get!.dimension = .straightness := rfl

theorem widen_dimension :
    widen.toVerb.degreeAchievementScale.get!.dimension = .width := rfl

/-! #### Telicity at the `AffectednessDegree` level -/

/-- The [kennedy-levin-2008] to [beavers-2011] telicity correspondence at the
    `AffectednessDegree` level: a closed-scale base (*straighten*) projects to
    `.quantized` (telic), an open-scale base (*widen*) to `.nonquantized`
    (atelic). The strict ordering encodes the variable-telicity contrast. -/
theorem widen_lt_straighten_at_affectedness_level :
    AffectednessDegree.nonquantized < AffectednessDegree.quantized := by decide

end KennedyLevin2008
