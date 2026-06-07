import Linglib.Semantics.Aspect.Dimension
import Linglib.Semantics.Degree.MeasureFunction
import Linglib.Semantics.ArgumentStructure.Affectedness.Hierarchy
import Linglib.Core.Scales.Bounds
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Order.WithBot

/-!
# Scalar telicity: telicity from the order structure of a scale

[kennedy-levin-2008]'s thesis — a degree achievement's telicity is fixed by the
boundedness of its adjectival scale — realised *order-theoretically* and connected
to [beavers-2011]'s affectedness hierarchy. "The scale has a greatest degree" is
mathlib's `OrderTop` mixin; "the scale is unbounded above" is `NoMaxOrder`; over a
degree type `δ`. A degree achievement is telic (admits a Quantized witness) **iff**
its scale has a greatest element — the witness is the maximum `g_φ = ⊤`, *derived*
from the mixin, not stipulated from a stored flag.

The measure is the patient's degree at the event's end (its temporal trace);
[beavers-2011]'s `HasScalarResult` is synthesised by `ofHasMeasureFunction`.

## Main results

* `telic_of_orderTop` — `[OrderTop δ]` ⇒ a Quantized witness exists (at `⊤`).
* `atelic_of_noMaxOrder` — `[NoMaxOrder δ]` ⇒ no Quantized witness exists.
* `Dimension` / `Dimension.degree` — a scalar dimension is the categorical
  primitive (what the adjective measures); its boundedness is the order-mixin
  profile of its degree type, not a stored flag.

## Implementation notes

Degree carriers are computable order-shapes (`WithTop ℕ` for closed, `ℕ` for
unbounded-above), so `decide` stays available; what matters is the
presence/absence of the `OrderTop` / `NoMaxOrder` mixin, not the carrier.
-/

namespace ScalarTelicity

open Semantics.ArgumentStructure.Affectedness
open Semantics.ArgumentStructure.Affectedness.Hierarchy
open Semantics.Degree.MeasureFunction

/-- Trivial patient: the measure of change ignores the patient's identity, so a
    single one-constructor type serves for every degree type `δ`. -/
inductive Patient
  | mk

section
variable {δ : Type*} [LinearOrder δ]

/-- The patient's degree at a time is that time — the temporal trace — so the
    final degree of an event is its end-time. The instance lives on the file-local
    `Patient`, so it cannot pollute resolution elsewhere. -/
instance traceMeasure : HasMeasureFunction Patient δ δ where
  measure _ t := t

/-- Companion `HasLatentScale` ([beavers-2011] eq. (60c)). -/
instance : HasLatentScale Patient (Event δ) :=
  HasLatentScale.ofHasMeasureFunction (δ := δ)

/-- Telic reading: the patient reaches the maximal degree `⊤` by the event's end.
    Available only when the scale has a greatest element (`OrderTop`). -/
def reachesTop [OrderTop δ] : Patient → Event δ → Prop :=
  fun _ e => e.runtime.snd = (⊤ : δ)

/-- Atelic ('comparative') reading: the patient reaches *some* degree by the end —
    always satisfiable, hence `NonQuantized` for any scale. -/
def reachesSome : Patient → Event δ → Prop :=
  fun _ e => ∃ g : δ, e.runtime.snd = g

theorem reachesSome_nonQuantized : NonQuantized (δ := δ) (reachesSome (δ := δ)) :=
  fun _ _ h => h

/-- With a greatest degree, the telic reading is Quantized at `⊤`: every event
    entails the patient reaches the maximum. -/
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
    (`NoMaxOrder`), *no* final degree is entailed: for any candidate `g`,
    `exists_gt` yields a strictly larger degree, realised by an event whose final
    degree is not `g`. This is [kennedy-levin-2008]'s open-scale obligatory
    atelicity, derived from the order structure. -/
theorem atelic_of_noMaxOrder [NoMaxOrder δ] :
    ¬ ∃ g : δ, Quantized (reachesSome (δ := δ)) g := by
  rintro ⟨g, hg⟩
  obtain ⟨b, hb⟩ := exists_gt g
  have hbg : b = g := hg Patient.mk ⟨⟨⟨b, b⟩, le_refl b⟩, .dynamic⟩ ⟨_, rfl⟩
  exact absurd hbg hb.ne'

/-- Synthesis: with a greatest degree, the telic reading builds the full Beavers
    `IsQuantizedAffected` instance — the `HasScalarResult` premise is found from
    `traceMeasure`, and the weaker hierarchy levels follow by the `extends` chain
    ([beavers-2011] eq. (62)). -/
instance reachesTop_isQuantizedAffected [OrderTop δ] :
    IsQuantizedAffected (δ := δ) (reachesTop (δ := δ)) :=
  IsQuantizedAffected.mk' (fun _ _ _ => trivial) ⊤ reachesTop_quantized

example [OrderTop δ] : IsNonQuantizedAffected (δ := δ) (reachesTop (δ := δ)) := inferInstance
example [OrderTop δ] : IsPotentialAffected (β := Event δ) (reachesTop (δ := δ)) := inferInstance

end

/-! ### Dimensions: boundedness as the order structure of the degree type

`Dimension` (in `Semantics/Aspect/Dimension.lean`) is the categorical primitive a
fragment stores. Its boundedness is *not* stored: each dimension has a degree type
(`Dimension.degree`) whose order-mixin profile determines it, and
`hasGreatest_degree_iff_closed` grounds the derived `Dimension.boundedness` view to
that order structure. -/

open Core.Scale (Boundedness HasGreatest hasGreatest_of_orderTop not_hasGreatest_of_noMaxOrder)

/-- The degree type for each dimension. Boundedness is structural: closed
    dimensions carry `OrderTop` (`WithTop ℕ`), unbounded-above ones `NoMaxOrder`
    (`ℕ`). The carrier is a computable order-shape, not a real magnitude — only the
    mixin matters. -/
abbrev Dimension.degree : Dimension → Type
  | .straightness | .flatness | .openness | .cleanliness | .curvature
  | .cracking | .denting | .scratching | .boiling => WithTop ℕ
  | .length | .width | .temperature | .corrosion | .quantity
  | .unspecified => ℕ

instance (d : Dimension) : LinearOrder d.degree := by cases d <;> exact inferInstance

/-- **Grounding.** The derived `Dimension.boundedness` view agrees with the order
    structure: a dimension is closed exactly when its degree type has a greatest
    element. So `boundedness` is not a free-standing table — it tracks `OrderTop` /
    `NoMaxOrder` on `Dimension.degree`. -/
theorem hasGreatest_degree_iff_closed (d : Dimension) :
    HasGreatest d.degree ↔ d.boundedness = .closed := by
  cases d
  case straightness | flatness | openness | cleanliness | curvature
    | cracking | denting | scratching | boiling =>
      show HasGreatest (WithTop ℕ) ↔ _
      exact iff_of_true hasGreatest_of_orderTop rfl
  case length | width | temperature | corrosion | quantity | unspecified =>
      show HasGreatest ℕ ↔ _
      exact iff_of_false not_hasGreatest_of_noMaxOrder (by decide)

/-- **The Kennedy–Levin thesis, as a theorem.** The computable
    `Dimension.defaultTelicity` table is exactly the order-theoretic fact: a
    dimension is telic iff its degree type has a greatest element (`OrderTop`). So
    the telicity a fragment consumes is grounded in the scale's order structure,
    not stipulated. -/
theorem defaultTelicity_telic_iff_hasGreatest (d : Dimension) :
    d.defaultTelicity = .telic ↔ HasGreatest d.degree := by
  rw [hasGreatest_degree_iff_closed]
  cases d <;> simp [Dimension.defaultTelicity, Dimension.boundedness]

/-- A closed dimension yields a telic reading (a Quantized witness at `⊤`). -/
theorem straightness_telic :
    ∃ g : Dimension.straightness.degree,
      Quantized (reachesTop (δ := Dimension.straightness.degree)) g :=
  telic_of_orderTop

/-- An unbounded-above dimension yields an atelic reading (no Quantized witness). -/
theorem width_atelic :
    ¬ ∃ g : Dimension.width.degree,
      Quantized (reachesSome (δ := Dimension.width.degree)) g :=
  atelic_of_noMaxOrder

end ScalarTelicity
