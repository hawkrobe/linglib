import Linglib.Theories.Semantics.Events.ScalarResult
import Mathlib.Order.Basic

/-!
# Beavers' Affectedness Hierarchy: Typeclass Chain
@cite{beavers-2011} @cite{beavers-koontz-garboden-2020}

The mathlib-style typeclass `extends` chain encoding @cite{beavers-2011}'s
implicational affectedness hierarchy (eq. 62):

    quantized → non-quantized → potential

Each level extends the next-weaker (mathlib pattern: cf.
`T0Space → T1Space → T2Space → ...` for separation axioms,
`Semigroup → Monoid → Group → CommGroup` for algebraic hierarchies).

The chain bottoms at `IsPotentialAffected`. Beavers' eq. (60d)
`Unspecified` (mere participation, vacuous for any binary θ) is not
formalised as a typeclass — see `ScalarResult.lean` §"Why Unspecified
is not formalised" for the rationale. The `AffectednessDegree` enum
keeps `unspecified` as a level tag for case analysis (parallel to
mathlib's `T0/T1/T2/...` hierarchy where "non-T0" exists as a state
but is not a typeclass).

## Mathlib decomposition

- `AffectednessDegree` enum (4 cases) + `LinearOrder` instance via
  `Function.Injective.linearOrder strength` — full ordered API.
- 3 typeclasses with `extends` chain:
  - `IsPotentialAffected θ` (Prop) — content: `Potential θ`
    (requires `[HasLatentScale α β]`)
  - `IsNonQuantizedAffected θ` (Prop) extends `IsPotentialAffected θ`
    via the `forget` link from `HasScalarResult` to `HasLatentScale`
  - `IsQuantizedAffected θ` (**Type**) extends `IsNonQuantizedAffected θ`
    with `finalDegree : δ` field + `isQuantized : Quantized θ finalDegree`
    proof. Type-valued (mathlib pattern: cf. `MetricSpace`) so that the
    lexically-named final degree `g_φ` is preserved as data, not lost
    to existential closure.
- Smart constructor `IsQuantizedAffected.mk'` that takes `(g_φ, h)` and
  derives the parent fields via the `ScalarResult` implication chain.

## Sections

1. `AffectednessDegree` enum + manual `LE`/`LT`/`Decidable` instances
   via a `strength : AffectednessDegree → Nat` projection (the enum
   was moved here from `Verb/Affectedness.lean` during the Phase 1b
   refactor; full `LinearOrder` deferred until a consumer needs it)
2. Typeclass extends chain (`IsPotentialAffected → IsNonQuantizedAffected → IsQuantizedAffected`)
3. Smart constructors

-/

namespace Semantics.Events.AffectednessHierarchy

open Semantics.Events.ScalarResult

-- ════════════════════════════════════════════════════
-- § 1. AffectednessDegree enum (Beavers 4-level scale)
-- ════════════════════════════════════════════════════

/-- @cite{beavers-2011} eq. (62) — *The Affectedness Hierarchy*: four
    degrees of affectedness, defined by increasingly weaker truth
    conditions about what change occurs in the patient.

    Each degree is an existential generalisation over the `result'`
    relation (formalised in `ScalarResult.lean`):
    - `quantized`:    φ → ∃e∃s[result'(x, s, g_φ, e)]    (specific result state g_φ)
    - `nonquantized`: φ → ∃e∃s∃g[result'(x, s, g, e)]   (some result state)
    - `potential`:    φ → ∃e∃s∃θ[θ(x, s, e)]            (force recipient, latent scale)
    - `unspecified`:  φ → ∃e∃θ'[θ'(x, e)]               (mere participation; not formalised)

    The hierarchy forms a total order by truth-conditional entailment.
    Constructor order matches strength (weakest first): `unspecified <
    potential < nonquantized < quantized`. -/
inductive AffectednessDegree where
  /-- Mere participation: no scale commitment (e.g., perception verbs *see, smell*). -/
  | unspecified
  /-- Force recipient: latent scale exists (e.g., surface contact *hit, wipe*). -/
  | potential
  /-- Some result state entailed (e.g., degree achievements *cool, widen*). -/
  | nonquantized
  /-- Specific final degree entailed (e.g., accomplishments *break, destroy*). -/
  | quantized
  deriving DecidableEq, Repr, Inhabited

namespace AffectednessDegree

/-- Numeric strength: higher index = stronger truth conditions.
    Bridge to `Nat` for the order instances. -/
def strength : AffectednessDegree → Nat
  | .unspecified => 0
  | .potential => 1
  | .nonquantized => 2
  | .quantized => 3

instance : LE AffectednessDegree where
  le a b := a.strength ≤ b.strength

instance : LT AffectednessDegree where
  lt a b := a.strength < b.strength

instance (a b : AffectednessDegree) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.strength ≤ b.strength))

instance (a b : AffectednessDegree) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.strength < b.strength))

end AffectednessDegree

-- ════════════════════════════════════════════════════
-- § 2. Typeclass extends chain (Beavers eq. 62)
-- ════════════════════════════════════════════════════

/-- @cite{beavers-2011} eq. (60c) **Potential affectedness**: the
    bottom of the typeclass chain. Patient is a force-recipient at
    every event of θ — content: `Potential θ` from `ScalarResult.lean`,
    parameterised over a `[HasLatentScale α β]` instance.

    Linguistic exemplars: surface contact / impact verbs
    (*hit, wipe, scrub, kick*) — what
    @cite{rappaport-hovav-levin-2001} called "force recipients"
    and @cite{beavers-koontz-garboden-2020} retain the term.

    Why this is the chain bottom (not Unspecified): Beavers' (60d)
    Unspecified is `θ x e → ∃ θ', θ'(x, e)`, vacuous for any binary
    `θ` (take `θ' = θ`). A typeclass with vacuous content is content-
    free; the hierarchy chain bottoms at the first level with real
    structure. The `AffectednessDegree.unspecified` enum case still
    exists as a level tag for "no class declared." -/
class IsPotentialAffected {α β : Type*} [HasLatentScale α β]
    (θ : α → β → Prop) : Prop where
  isPotential : Potential θ

/-- @cite{beavers-2011} eq. (60b) **Non-quantized affectedness**:
    extends Potential with a result-state commitment (some final
    degree on the scale). Content: `NonQuantized (δ := δ) θ` from
    `ScalarResult.lean`.

    Requires both `[HasScalarResult α δ β]` (for the result state)
    and `[HasLatentScale α β]` (inherited via `extends IsPotentialAffected`).
    The forgetful link from result state to force recipient is held
    by the smart constructor `mk'`.

    Linguistic exemplars: degree achievements (*widen, cool,
    lengthen*), non-quantized cutting verbs (*cut, slice*). -/
class IsNonQuantizedAffected {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    (θ : α → β → Prop) : Prop extends IsPotentialAffected θ where
  isNonQuantized : NonQuantized (δ := δ) θ

/-- @cite{beavers-2011} eq. (60a) **Quantized affectedness**: extends
    Non-quantized with the commitment to a SPECIFIC final degree
    `g_φ : δ` (lexically named by the verb).

    **Type-valued** (not Prop) — mathlib pattern: cf. `MetricSpace`
    (Type-valued because `dist` is data) vs `T2Space` (Prop). The
    final degree is data, not just an existential, preserving the
    lexical commitment Beavers (60a) makes (e.g., *break-into-shards*
    vs *break-into-dust* are distinguishable instances).

    Linguistic exemplars: accomplishments / achievements
    (*break, shatter, destroy, devour*). Note: K98 SINC verbs are a
    structurally stronger class — bijective sub-event ↔ sub-object
    correspondence — that ENTAILS Quantized given a `HasScalarResult`
    instance, but Quantized does not entail SINC. See
    `Theories/Semantics/Events/Incrementality.lean` for the bridge
    smart constructor. -/
class IsQuantizedAffected {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    (θ : α → β → Prop) extends IsNonQuantizedAffected (δ := δ) θ where
  /-- The lexically-named specific final degree `g_φ`. -/
  finalDegree : δ
  /-- Witness that θ entails patient ends event with this degree. -/
  isQuantized : Quantized θ finalDegree

-- ════════════════════════════════════════════════════
-- § 3. Smart constructors
-- ════════════════════════════════════════════════════

/-! Smart constructors that take only the level-specific witnesses and
    derive the inherited fields automatically via the `ScalarResult`
    implication chain. -/

/-- Smart constructor for `IsPotentialAffected`: just the `Potential`
    witness. -/
@[reducible]
def IsPotentialAffected.mk' {α β : Type*} [HasLatentScale α β]
    {θ : α → β → Prop} (h : Potential θ) :
    IsPotentialAffected θ where
  isPotential := h

/-- Smart constructor for `IsNonQuantizedAffected`: takes the
    `NonQuantized` witness and the forgetful `HasScalarResult →
    HasLatentScale` link; derives the inherited Potential field via
    `potential_of_nonQuantized`. -/
@[reducible]
def IsNonQuantizedAffected.mk' {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    {θ : α → β → Prop}
    (forget : ∀ (x : α) (e : β), (∃ g : δ, HasScalarResult.resultAt x g e) →
              HasLatentScale.latentScale x e)
    (h : NonQuantized (δ := δ) θ) :
    IsNonQuantizedAffected (δ := δ) θ where
  toIsPotentialAffected := IsPotentialAffected.mk' (potential_of_nonQuantized forget h)
  isNonQuantized := h

/-- Smart constructor for `IsQuantizedAffected`: takes the final degree
    `g_φ : δ`, the `Quantized θ g_φ` proof, and the forgetful link;
    derives all weaker levels via the eq. (62) hierarchy. The
    Type-valued result preserves `g_φ` as accessible data. -/
@[reducible]
def IsQuantizedAffected.mk' {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    {θ : α → β → Prop}
    (forget : ∀ (x : α) (e : β), (∃ g : δ, HasScalarResult.resultAt x g e) →
              HasLatentScale.latentScale x e)
    (g_φ : δ) (h : Quantized θ g_φ) :
    IsQuantizedAffected (δ := δ) θ where
  toIsNonQuantizedAffected :=
    IsNonQuantizedAffected.mk' forget (nonQuantized_of_quantized h)
  finalDegree := g_φ
  isQuantized := h

end Semantics.Events.AffectednessHierarchy
