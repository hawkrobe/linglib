import Linglib.Theories.Semantics.Events.ThematicRoleProperties
import Linglib.Theories.Semantics.Events.Incrementality

/-!
# Cumulativity and Quantization Propagation
@cite{krifka-1998} @cite{krifka-1989} @cite{champollion-2017}

The central K98 §3.3 result: a thematic relation θ between objects and
events propagates mereological properties (CUM, QUA) from the object
NP to the VP it forms via existential closure. Plus VP formation
itself (eq. 53) and the bridge theorems linking SINC + UP to the
two propagation chains.

Topic-named (not paper-named): defines the deep substrate that
@cite{krifka-1998} §3.3 establishes, that @cite{krifka-1989}'s
nominal-reference-to-VP-aspect chain depends on, and that
@cite{champollion-2017}'s stratified-reference modernization rests on.

## Mathlib discipline: typeclass form is canonical

The public API is the typeclass-form `cum_propagation` and
`qua_propagation` (taking `[IsCumThetaVerb θ]` / `[IsSincVerb θ]`).
The explicit-witness variants (`cum_propagation_of_cumTheta`,
`qua_propagation_of_mso`, `qua_propagation_of_sinc`) are `private`
proof-factoring helpers, not part of the public API — mathlib pattern.

## Sections

1. VP formation (K98 §3.3 eq. 53)
2. CUM propagation: explicit + typeclass forms
3. QUA propagation: explicit (MSO and SINC) + typeclass forms

-/

namespace Semantics.Events.CumulativityPropagation

open Mereology
open Semantics.Events.Mereology
open Semantics.Events.ThematicRoleProperties
open Semantics.Events.Incrementality

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

-- ════════════════════════════════════════════════════
-- § 1. VP Formation (K98 §3.3 eq. 53)
-- ════════════════════════════════════════════════════

/-- VP predicate formed by existential closure over the object argument.
    @cite{krifka-1998} eq. 53: `VP_θ,OBJ = λe.∃y[OBJ(y) ∧ θ(y,e)]`.
    "eat apples" = `λe.∃y[apples(y) ∧ eat.theme(y,e)]`. -/
def VP (θ : α → β → Prop) (OBJ : α → Prop) : β → Prop :=
  fun e => ∃ y, OBJ y ∧ θ y e

-- ════════════════════════════════════════════════════
-- § 2. CUM Propagation (K98 §3.3)
-- ════════════════════════════════════════════════════

/-- **CUM propagation** (explicit-witness smart constructor): cumulative θ
    transmits CUM from NP to VP. @cite{krifka-1998} §3.3:
    CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ).

    "eat apples" is CUM because:
    - APPLES is CUM (mass/bare-plural NPs are cumulative)
    - EAT's incremental theme is cumulative (CumTheta)
    - Therefore VP = `λe.∃y[apples(y) ∧ eat(y,e)]` is CUM

    Proof: Given VP(e₁) and VP(e₂), we have y₁ with OBJ(y₁) ∧ θ(y₁,e₁)
    and y₂ with OBJ(y₂) ∧ θ(y₂,e₂). By CumTheta, θ(y₁⊔y₂, e₁⊔e₂).
    By CUM(OBJ), OBJ(y₁⊔y₂). So VP(e₁⊔e₂).

    Public API: the typeclass-form `cum_propagation` below is the
    only exposed entry point; this `_of_cumTheta` smart constructor
    is `private` (mathlib pattern: explicit-witness forms factor
    proofs but aren't part of the public API). -/
private theorem cum_propagation_of_cumTheta {θ : α → β → Prop} {OBJ : α → Prop}
    (hCum : CumTheta θ) (hObj : CUM OBJ) :
    CUM (VP θ OBJ) := by
  intro e₁ e₂ ⟨y₁, hobj₁, hθ₁⟩ ⟨y₂, hobj₂, hθ₂⟩
  exact ⟨y₁ ⊔ y₂, hObj y₁ y₂ hobj₁ hobj₂, hCum y₁ y₂ e₁ e₂ hθ₁ hθ₂⟩

-- ════════════════════════════════════════════════════
-- § 3. QUA Propagation (K98 §3.3)
-- ════════════════════════════════════════════════════

/-- **QUA propagation**: UP + MSO transmit QUA from NP to VP.
    @cite{krifka-1998} §3.3: UP(θ) ∧ MSO(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ).

    "eat two apples" is QUA because:
    - TWO-APPLES is QUA (quantized NPs have no P-proper-parts)
    - EAT's incremental theme is SINC + UP
    - Therefore VP = `λe.∃y[two-apples(y) ∧ eat(y,e)]` is QUA

    Proof: Suppose VP(e) via ⟨y, OBJ(y), θ(y,e)⟩ and e' < e.
    We must show ¬VP(e'). Suppose for contradiction VP(e') via
    ⟨z, OBJ(z), θ(z,e')⟩. By MSO, ∃ y' < y with θ(y',e').
    By UP, z = y'. So OBJ(y') with y' < y. But QUA(OBJ) says
    ¬OBJ(y'). Contradiction.

    **Functional case**: When θ is a function (not a relation) with
    `IsSumHom` + `Function.Injective`, this reduces to
    `qua_of_injective_sumHom` in `Core/Mereology.lean` via
    `qua_pullback`. The relational UP + MSO conditions collapse to
    functional injectivity + monotonicity.

    Public API: the typeclass-form `qua_propagation` below is the
    only exposed entry point; this `_of_mso` smart constructor is
    `private`. -/
private theorem qua_propagation_of_mso {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hMSO : MSO θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) := by
  intro e e' ⟨y, hobj, hθ⟩ hlt ⟨z, hobj_z, hθ_z⟩
  obtain ⟨y', hy'_lt, hθ_y'⟩ := hMSO y e e' hθ hlt
  have hz_eq : z = y' := hUP z y' e' hθ_z hθ_y'
  exact hQua y y' hobj hy'_lt (hz_eq ▸ hobj_z)

/-- QUA propagation from SINC + UP (explicit-witness smart constructor,
    private). In practice, incremental-theme verbs satisfy both SINC
    and UP. Public API: the typeclass form `qua_propagation` below
    is the only exposed entry point. -/
private theorem qua_propagation_of_sinc {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hSinc : SINC θ) (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation_of_mso hUP hSinc.mso hQua

-- ════════════════════════════════════════════════════
-- § 4. Public typeclass-form API (mathlib discipline)
-- ════════════════════════════════════════════════════

/-! The canonical public API: typeclass-form propagation theorems
    that consumers should prefer over the `_of_*` smart constructors
    above. Mathlib pattern — `add_assoc [Semigroup α]` is the
    canonical name; explicit-witness variants are smart constructors
    with `_of_*` suffixes when they exist at all. -/

/-- **CUM propagation** (canonical typeclass form). Fires on any
    verb θ with `[IsCumThetaVerb θ]` — including SINC and INC verbs
    via the upward instances in `StrictIncrementality.lean` /
    `GeneralIncrementality.lean`. -/
theorem cum_propagation {θ : α → β → Prop} [IsCumThetaVerb θ]
    {OBJ : α → Prop} (hObj : CUM OBJ) :
    CUM (VP θ OBJ) :=
  cum_propagation_of_cumTheta IsCumThetaVerb.cumTheta hObj

/-- **QUA propagation** (canonical typeclass form). Fires on
    `[IsSincVerb θ]` — the typeclass bundles the SINC + UP witnesses
    needed by K98 §3.3 quantization-propagation. -/
theorem qua_propagation {θ : α → β → Prop} [IsSincVerb θ]
    {OBJ : α → Prop} (hQua : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_propagation_of_sinc IsSincVerb.up IsSincVerb.sinc hQua

end Semantics.Events.CumulativityPropagation
