import Mathlib.Logic.Basic

/-!
# Scalar Result Substrate
[beavers-2011] [beavers-koontz-garboden-2020]
[rappaport-hovav-levin-2001]

Substrate primitives for the scalar-theoretic affectedness hierarchy.

Two independent typeclasses, mirroring Beavers' two empirical primitives:

- `HasScalarResult α δ β` — patient `x : α` ends event `e : β` holding
  degree `g : δ`. Drives Beavers (60a) Quantized and (60b) Non-quantized.
- `HasLatentScale α β` — patient `x` is a force-recipient at event `e`
  (related to a latent scale, no transition entailed). Drives Beavers
  (60c) Potential. The "force recipient" terminology and the
  empirical primitive originate with [rappaport-hovav-levin-2001].

Three abstract Props characterise Beavers (60a-c) on a thematic relation
`θ : α → β → Prop`. Beavers (60d) `Unspecified` (mere participation) is
not formalised — it is `True` for every binary relation and contributes
no content to the typeclass chain. The discrete `AffectednessDegree`
enum in `AffectednessHierarchy.lean` keeps `unspecified` as a level
tag; the typeclass chain bottoms at `IsPotentialAffected`.

## Mathlib decomposition

`HasScalarResult` and `HasLatentScale` are data-bearing typeclasses
(per-verb structural commitments — patient type, dimension type, event
type). The three Beavers Props are plain definitions, used as
typeclass content one layer up in
`Semantics/Events/Scalar/Affectedness.lean`.

Mathlib pattern: cf. `MeasurableSpace α` (structure) +
`MeasurableSet s` (Prop using the structure) +
`IsFiniteMeasure μ` (Prop using both).
## Why `Unspecified` is not formalised

[beavers-2011] (60d): `φ → ∃e∃θ'[θ'(x, e)]` — mere participation.
For any binary `θ : α → β → Prop`, `θ x e` IS the participation, so
the implication `θ x e → ∃ θ', θ'(x, e)` holds vacuously by taking
`θ' = θ`. A formal definition `Unspecified θ := True` (or its
β-equivalent `θ → θ`) carries no content and adds no information to
consumer proofs. The hierarchy "bottoms out" at `Potential` for
typeclass purposes; the `unspecified` enum tag in
`AffectednessHierarchy.lean` represents "no class declared," parallel
to mathlib's separation-axiom enums having more cases than
typeclasses (only `T0/T1/T2/...` are typeclasses; "non-T0" isn't).

-/

namespace ArgumentStructure.Affectedness

/-! ### HasScalarResult — result-state typeclass -/

/-- `HasScalarResult α δ β` provides the predicate
    `resultAt x g e`: "patient `x : α` ends event `e : β` holding
    degree `g : δ`."

    The primitive that [beavers-2011] eq. (60a-b) requires to
    define Quantized and Non-quantized affectedness. The "state" token
    `s` in Beavers' eq. (60) is decorative for level-typing
    (Quantized / Non-quantized are existential generalisations over `s`)
    and elided in the 3-place form here. Consumers needing `s` for
    result-XP licensing or *halfway*-modification semantics
    ([beavers-koontz-garboden-2020] §1.6.1) reintroduce it
    downstream.

    Mathlib pattern: structural typeclass with multiple type
    parameters, analogous to `Module R M`. Per-verb the dimension `δ`
    is determined by lexical content (*cool* on temperature, *widen*
    on width, *eat* on consumption); each verb's `θ : α → β → Prop`
    references the appropriate instance. -/
class HasScalarResult (α : Type*) (δ : Type*) (β : Type*) where
  /-- Patient x ends event e holding degree g on dimension δ. -/
  resultAt : α → δ → β → Prop

/-! ### HasLatentScale — force-recipient typeclass -/

/-- `HasLatentScale α β` provides the predicate `latentScale x e`:
    "patient `x : α` is a force-recipient at event `e : β`, related
    to some scale (latent), no transition entailed."

    The primitive that [beavers-2011] eq. (60c) requires to
    define Potential affectedness. Originates with
    [rappaport-hovav-levin-2001]'s "force recipient" — a verb
    that imparts force to its theme without committing to a
    specific result state (surface contact / impact verbs:
    *wipe, scrub, rub, punch, hit, kick, slap*).

    Independent from `HasScalarResult`: a verb may have a latent scale
    without entailing a final degree (Potential-only verbs), entail a
    final degree without an explicit force-recipient relation
    (NonQuantized verbs whose Potential is derived via the implication
    chain in §4), or both. -/
class HasLatentScale (α : Type*) (β : Type*) where
  /-- Patient x is a force-recipient at event e (latent scale relation). -/
  latentScale : α → β → Prop

/-! ### Beavers (60a-c) Affectedness Props -/

/-- [beavers-2011] eq. (60a) **Quantized**: `θ` entails patient
    `x` ends event `e` holding the SPECIFIC degree `g_φ`.
    `φ → ∃e∃s[result'(x, s, g_φ, e)]`.

    The `g_φ` is fixed by the predicate φ — Beavers' point is that
    quantized verbs *name* a specific endpoint
    (`dead` for *kill*, `broken` for *break*, `g₁₀₀°C` for
    *heat to 100°C*). Per-verb `g_φ` lives in `IsQuantizedAffected`
    as data (a typeclass field, not existentially bound), preserving
    the lexical commitment.

    Linguistic exemplars: accomplishments / achievements
    (*break, shatter, destroy, devour x*). -/
def Quantized {α δ β : Type*} [HasScalarResult α δ β]
    (θ : α → β → Prop) (g_φ : δ) : Prop :=
  ∀ x e, θ x e → HasScalarResult.resultAt x g_φ e

/-- [beavers-2011] eq. (60b) **Non-quantized**: `θ` entails patient
    `x` ends event `e` holding SOME degree (not necessarily specific).
    `φ → ∃e∃s∃g[result'(x, s, g, e)]`.

    Linguistic exemplars: degree achievements (*widen, cool, lengthen,
    cut, slice x*). -/
def NonQuantized {α δ β : Type*} [HasScalarResult α δ β]
    (θ : α → β → Prop) : Prop :=
  ∀ x e, θ x e → ∃ g : δ, HasScalarResult.resultAt x g e

/-- [beavers-2011] eq. (60c) **Potential**: `θ` entails patient
    `x` is a force-recipient at event `e` (latent scale exists, no
    transition entailed).
    `φ → ∃e∃s∃θ_scale[θ_scale(x, s, e)]`.

    Defined via the `HasLatentScale` primitive — NOT by excluded middle
    over a result state (that encoding would be vacuous, equivalent to
    `Nonempty δ` via `Classical.em`). The latent-scale relation IS the
    formal content of "force recipient" per
    [rappaport-hovav-levin-2001].

    Linguistic exemplars: surface contact / impact verbs
    (*wipe, scrub, rub, punch, hit, kick, slap x*). -/
def Potential {α β : Type*} [HasLatentScale α β]
    (θ : α → β → Prop) : Prop :=
  ∀ x e, θ x e → HasLatentScale.latentScale x e

/-! ### Implication Chain (Beavers eq. 62) -/

/-! [beavers-2011] eq. (62) — *The Affectedness Hierarchy*:
    `quantized → non-quantized → potential`. Each level entails the
    next-weaker. The Quantized → Non-quantized step is direct; the
    Non-quantized → Potential step requires a forgetful link from
    `HasScalarResult` to `HasLatentScale` (since they are independent
    typeclasses by design — see §2 docstring rationale). -/

/-- Quantized entails Non-quantized: a specific final degree witnesses
    the existential. [beavers-2011] eq. (62) leftmost arrow. -/
theorem nonQuantized_of_quantized {α δ β : Type*} [HasScalarResult α δ β]
    {θ : α → β → Prop} {g_φ : δ}
    (h : Quantized θ g_φ) : NonQuantized (δ := δ) θ :=
  fun x e hxe => ⟨g_φ, h x e hxe⟩

/-- Non-quantized entails Potential under a forgetful link: if the
    `HasScalarResult` instance can be projected to a
    `HasLatentScale` instance (i.e., having a result state at any
    degree implies being a force-recipient), then NonQuantized lifts
    to Potential. [beavers-2011] eq. (62) middle arrow.

    The link witness `forget` is the explicit assumption that
    "patient ends event with some result state" implies "patient is a
    force-recipient at the event." This always holds in the
    canonical model (a result-bearing event is, a fortiori,
    force-receiving) but is stated as a hypothesis here to keep the
    typeclasses formally independent. -/
theorem potential_of_nonQuantized {α δ β : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    {θ : α → β → Prop}
    (forget : ∀ (x : α) (e : β), (∃ g : δ, HasScalarResult.resultAt x g e) →
              HasLatentScale.latentScale x e)
    (h : NonQuantized (δ := δ) θ) : Potential θ :=
  fun x e hxe => forget x e (h x e hxe)

end ArgumentStructure.Affectedness
