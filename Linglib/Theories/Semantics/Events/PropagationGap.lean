import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.Incrementality
import Linglib.Theories.Semantics.Events.CumulativityPropagation

/-!
# The Propagation Gap (¬CUM ∧ ¬QUA Objects)
@cite{filip-2012} @cite{krifka-1998} @cite{moon-2026}

When OBJ is neither CUM nor QUA, neither `cum_propagation` nor
`qua_propagation` fires. The question: does the VP inherit the
middle-ground status, or could it escape?

Answer: under appropriate conditions (CumTheta + UP for ¬CUM, SINC
for ¬QUA), the middle ground is **stable** — it transfers from OBJ
to VP. This is the propositional substrate for @cite{filip-2012}'s
three-way classification (CUM, QUA, ¬CUM ∧ ¬QUA). The concrete
witness instance is @cite{moon-2026}'s mixed drink nouns
(*martini*, *cappuccino*) — see `Phenomena/Countability/Studies/Moon2026.lean`.

These theorems concern `VP`, `CumTheta`, `UP`, `SINC` — all defined
in the K98 substrate (now split across `ThematicRoleProperties.lean`,
`StrictIncrementality.lean`, `CumulativityPropagation.lean`). Filip's
linguistic framing of the gap lives in `Studies/Filip2012.lean`,
which delegates to these theorems.


-/

namespace Semantics.Events.PropagationGap

open Mereology
open Semantics.Events.Mereology
open Semantics.Events.ThematicRoleProperties
open Semantics.Events.Incrementality
open Semantics.Events.CumulativityPropagation

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- ¬CUM lifts from OBJ to VP (explicit-witness smart constructor):
    if two OBJ-entities x,y satisfy OBJ but their join x⊔y does not,
    the corresponding VP events e₁,e₂ also witness ¬CUM(VP).

    Proof: if CUM(VP) held, VP(e₁⊔e₂) would give ∃z. OBJ(z) ∧ θ(z, e₁⊔e₂).
    CumTheta gives θ(x⊔y, e₁⊔e₂), and UP forces z = x⊔y.
    But OBJ(x⊔y) contradicts hSum.

    Public API: the typeclass-form `not_cum_vp_of_witnesses`
    below is the only exposed entry point; this `_of_cumTheta_up`
    smart constructor is `private`. -/
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
    smart constructor): if OBJ is in the middle ground and the verb
    is SINC + UP + CumTheta, the VP is also ¬CUM ∧ ¬QUA.

    ¬CUM: OBJ's CUM-failure witnesses lift through CumTheta + UP
    (via `not_cum_vp_of_cumTheta_up`).

    ¬QUA: MSE (from SINC) maps the OBJ proper part y < x to a
    proper sub-event e_y < e_x. Both VP(e_x) and VP(e_y) hold,
    so VP is not quantized.

    Public API: the typeclass-form `middle_ground_stable` below is
    the only exposed entry point; this `_of_postulates` smart
    constructor is `private`. -/
private theorem middle_ground_stable_of_postulates {θ : α → β → Prop} {OBJ : α → Prop}
    (hCumTheta : CumTheta θ) (hUP : UP θ) (hSinc : SINC θ)
    -- ¬CUM witnesses: two OBJ-entities whose join fails OBJ
    {a b : α} {e_a e_b : β}
    (ha : OBJ a) (hb : OBJ b)
    (hθ_a : θ a e_a) (hθ_b : θ b e_b)
    (hSum : ¬ OBJ (a ⊔ b))
    -- ¬QUA witnesses: an OBJ-entity with a proper part also in OBJ
    {x y : α} {e_x : β}
    (hx : OBJ x) (hy : OBJ y) (hlt : y < x)
    (hθ_x : θ x e_x) :
    ¬ CUM (VP θ OBJ) ∧ ¬ QUA (VP θ OBJ) := by
  constructor
  · exact not_cum_vp_of_cumTheta_up hCumTheta hUP ha hb hθ_a hθ_b hSum
  · intro hQua
    obtain ⟨e_y, he_y_lt, hθ_y⟩ := hSinc.mse x e_x y hθ_x hlt
    exact hQua e_x e_y ⟨x, hx, hθ_x⟩ he_y_lt ⟨y, hy, hθ_y⟩

-- ════════════════════════════════════════════════════
-- § 3. Public typeclass-form API (mathlib discipline)
-- ════════════════════════════════════════════════════

/-! The canonical public API: typeclass-form variants that consumers
    (Filip 2012 paper-anchoring, Moon 2026 mixed-drink instantiation,
    etc.) should prefer over the `_of_*` smart constructors above.
    Mathlib pattern — typeclass form is canonical, explicit-witness
    forms are smart constructors. -/

/-- **¬CUM lifts to VP** (canonical typeclass form). `[IsSincVerb θ]`
    provides the `CumTheta` (via the `IsCumThetaVerb` parent class)
    and `UP` witnesses needed for the propagation. -/
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
    `[IsSincVerb θ]` bundles the SINC + UP witnesses directly and
    inherits CumTheta via the `IsCumThetaVerb` parent class. The
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

end Semantics.Events.PropagationGap
