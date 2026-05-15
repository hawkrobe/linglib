import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.Incrementality
import Linglib.Theories.Semantics.Events.CumulativityPropagation

/-!
# @cite{filip-2012}: "Lexical Aspect"

Filip's handbook chapter (Binnick ed., OUP) identifies a **three-way
classification** of verb predicates beyond K89/K98's binary CUM/QUA:

1. **Telic / quantized** (QUA): *recover*, *arrive*
2. **Atelic / cumulative** (CUM): *run*, *push*
3. **Neither** (¬CUM ∧ ¬QUA): *build*, *eat*, *write* — verbs whose
   telicity is underspecified at the verb level and determined
   compositionally by the object NP

The third class's compositional behavior:
* QUA object → QUA VP: "eat two apples" (telic)
* CUM object → CUM VP: "eat apples" (atelic)
* ¬CUM ∧ ¬QUA object → ¬CUM ∧ ¬QUA VP: "drink margarita" (Moon's case)

## Main definitions

* `three_way_exhaustive` — Filip's distinctive observation: every
  predicate is CUM, QUA, or ¬CUM ∧ ¬QUA
* `not_cum_vp_of_witnesses` — ¬CUM lifts to VP under `[IsSincVerb θ]`
* `middle_ground_stable` — ¬CUM ∧ ¬QUA lifts to VP under `[IsSincVerb θ]`
  (the propagation-gap stability result; canonical typeclass-form
  public API consumed by `Studies/Moon2026.lean`)

## TODO

* The propagation-gap substrate (§ 2 below) was inlined from former
  `Theories/Semantics/Events/PropagationGap.lean` in 0.231.55 as
  single-consumer substrate. If a second paper-anchored Studies file
  consumes `middle_ground_stable`, lift back to substrate per CLAUDE.md
  Theories/ ≥ 2 consumers rule.

## References

* @cite{filip-2012} (primary)
* @cite{krifka-1998} §3.3 (CUM/QUA propagation machinery the gap rests on)
* @cite{krifka-1989} (the binary CUM/QUA antecedent Filip critiques)
* @cite{moon-2026} (canonical instance: mixed-drink nouns as concrete
  witness of the topological-source ¬CUM ∧ ¬QUA middle ground)
-/

namespace Filip2012

open _root_.Mereology
open Semantics.Events.Mereology
open Semantics.Events.ThematicRoleProperties
open Semantics.Events.Incrementality
open Semantics.Events.CumulativityPropagation

/-! ### Three-way exhaustiveness (Filip's distinctive observation) -/

/-- The three classes are exhaustive: every predicate falls into
    exactly one of CUM, QUA, or ¬CUM ∧ ¬QUA. Conceptually important:
    the middle ground is a genuine third category, not a gap in our
    analysis. -/
theorem three_way_exhaustive {α : Type*} [SemilatticeSup α]
    (P : α → Prop) :
    CUM P ∨ QUA P ∨ (¬ CUM P ∧ ¬ QUA P) := by
  by_cases hc : CUM P
  · exact .inl hc
  · by_cases hq : QUA P
    · exact .inr (.inl hq)
    · exact .inr (.inr ⟨hc, hq⟩)

/-! ### Propagation gap substrate (inlined) -/

/-! When OBJ is neither CUM nor QUA, neither `cum_propagation` nor
    `qua_propagation` fires. Under SINC + UP + CumTheta verbs the
    middle ground is **stable** — it lifts from OBJ to VP. The concrete
    witness instance is @cite{moon-2026}'s mixed drink nouns. -/

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- ¬CUM lifts from OBJ to VP (explicit-witness smart constructor):
    if two OBJ-entities x,y satisfy OBJ but their join x⊔y does not,
    the corresponding VP events e₁,e₂ also witness ¬CUM(VP).

    Proof: if CUM(VP) held, VP(e₁⊔e₂) would give ∃z. OBJ(z) ∧ θ(z, e₁⊔e₂).
    CumTheta gives θ(x⊔y, e₁⊔e₂), and UP forces z = x⊔y.
    But OBJ(x⊔y) contradicts hSum. -/
private theorem not_cum_vp_of_cumTheta_up {θ : α → β → Prop} {OBJ : α → Prop}
    (hCumTheta : CumTheta θ) (hUP : UP θ)
    {x y : α} {e₁ e₂ : β}
    (hx : OBJ x) (hy : OBJ y)
    (hθ₁ : θ x e₁) (hθ₂ : θ y e₂)
    (hSum : ¬ OBJ (x ⊔ y)) :
    ¬ CUM (VP θ OBJ) := by
  intro hCum
  have hVP₁ : VP θ OBJ e₁ := ⟨x, hx, hθ₁⟩
  have hVP₂ : VP θ OBJ e₂ := ⟨y, hy, hθ₂⟩
  obtain ⟨z, hz_obj, hz_θ⟩ := hCum e₁ e₂ hVP₁ hVP₂
  have hθ_sum := hCumTheta x y e₁ e₂ hθ₁ hθ₂
  have hz_eq := hUP z (x ⊔ y) (e₁ ⊔ e₂) hz_θ hθ_sum
  exact hSum (hz_eq ▸ hz_obj)

/-- ¬CUM ∧ ¬QUA is stable under VP formation (explicit-witness
    smart constructor): SINC's MSE maps OBJ proper part y < x to
    proper sub-event e_y < e_x, witnessing ¬QUA on the VP. -/
private theorem middle_ground_stable_of_postulates {θ : α → β → Prop} {OBJ : α → Prop}
    (hCumTheta : CumTheta θ) (hUP : UP θ) (hSinc : SINC θ)
    {a b : α} {e_a e_b : β}
    (ha : OBJ a) (hb : OBJ b)
    (hθ_a : θ a e_a) (hθ_b : θ b e_b)
    (hSum : ¬ OBJ (a ⊔ b))
    {x y : α} {e_x : β}
    (hx : OBJ x) (hy : OBJ y) (hlt : y < x)
    (hθ_x : θ x e_x) :
    ¬ CUM (VP θ OBJ) ∧ ¬ QUA (VP θ OBJ) := by
  constructor
  · exact not_cum_vp_of_cumTheta_up hCumTheta hUP ha hb hθ_a hθ_b hSum
  · intro hQua
    obtain ⟨e_y, he_y_lt, hθ_y⟩ := hSinc.mse x e_x y hθ_x hlt
    exact hQua e_x e_y ⟨x, hx, hθ_x⟩ he_y_lt ⟨y, hy, hθ_y⟩

/-- **¬CUM lifts to VP** (canonical typeclass form). `[IsSincVerb θ]`
    bundles `CumTheta` (via `IsCumThetaVerb` parent class) and `UP`. -/
theorem not_cum_vp_of_witnesses {θ : α → β → Prop} [IsSincVerb θ]
    {OBJ : α → Prop}
    {x y : α} {e₁ e₂ : β}
    (hx : OBJ x) (hy : OBJ y)
    (hθ₁ : θ x e₁) (hθ₂ : θ y e₂)
    (hSum : ¬ OBJ (x ⊔ y)) :
    ¬ CUM (VP θ OBJ) :=
  not_cum_vp_of_cumTheta_up IsCumThetaVerb.cumTheta IsSincVerb.up
    hx hy hθ₁ hθ₂ hSum

/-- **Middle-ground gap lifts** (canonical typeclass form).
    `[IsSincVerb θ]` bundles SINC + UP + CumTheta directly. The
    recommended public API for the @cite{filip-2012} propositional
    gap-propagation result. -/
theorem middle_ground_stable {θ : α → β → Prop} [IsSincVerb θ]
    {OBJ : α → Prop}
    {a b : α} {e_a e_b : β}
    (ha : OBJ a) (hb : OBJ b)
    (hθ_a : θ a e_a) (hθ_b : θ b e_b)
    (hSum : ¬ OBJ (a ⊔ b))
    {x y : α} {e_x : β}
    (hx : OBJ x) (hy : OBJ y) (hlt : y < x)
    (hθ_x : θ x e_x) :
    ¬ CUM (VP θ OBJ) ∧ ¬ QUA (VP θ OBJ) :=
  middle_ground_stable_of_postulates IsCumThetaVerb.cumTheta IsSincVerb.up
    IsSincVerb.sinc ha hb hθ_a hθ_b hSum hx hy hlt hθ_x

end Filip2012
