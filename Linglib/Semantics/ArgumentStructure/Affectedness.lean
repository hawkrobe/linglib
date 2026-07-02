import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Mathlib.Logic.Basic
import Mathlib.Order.Basic

/-!
# Affectedness
[beavers-2011] [beavers-koontz-garboden-2020] [beavers-2010]
[rappaport-hovav-levin-2001] [dowty-1991]

[beavers-2011]'s scalar-theoretic affectedness hierarchy, in three layers:

1. **Scalar-result substrate** — two independent typeclasses, mirroring
   Beavers' two empirical primitives:
   - `HasScalarResult α δ β` — patient `x : α` ends event `e : β` holding
     degree `g : δ`. Drives Beavers (60a) Quantized and (60b) Non-quantized.
   - `HasLatentScale α β` — patient `x` is a force-recipient at event `e`
     (related to a latent scale, no transition entailed). Drives Beavers
     (60c) Potential. The "force recipient" terminology and the
     empirical primitive originate with [rappaport-hovav-levin-2001].

   Three abstract Props characterise Beavers (60a-c) on a thematic relation
   `θ : α → β → Prop`, plus the eq. (62) implication chain
   `quantized → non-quantized → potential`.

2. **Typeclass chain** — the `AffectednessDegree` enum and the mathlib-style
   `extends` chain `IsQuantizedAffected → IsNonQuantizedAffected →
   IsPotentialAffected`, with smart constructors deriving the inherited
   fields via the implication chain.

3. **EntailmentProfile projection** — `profileToDegree` projects
   [dowty-1991]'s P-Patient entailments onto `AffectednessDegree`,
   with kernel characterization and verification on canonical profiles.

## Mathlib decomposition

`HasScalarResult` and `HasLatentScale` are data-bearing typeclasses
(per-verb structural commitments — patient type, dimension type, event
type). The three Beavers Props are plain definitions, used as
typeclass content one layer up in the typeclass chain below.

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
typeclass purposes; the `unspecified` tag in the discrete
`AffectednessDegree` enum below represents "no class declared," parallel
to mathlib's separation-axiom enums having more cases than
typeclasses (only `T0/T1/T2/...` are typeclasses; "non-T0" isn't).

## As a projection of EntailmentProfile

The affectedness hierarchy is a projection of [dowty-1991]'s P-Patient
entailments onto a four-level total order measuring the strength of truth
conditions about change in the affected argument ([beavers-2010]).
`profileToDegree` projects the 10-Boolean `EntailmentProfile` onto
`AffectednessDegree`, retaining only the P-Patient features relevant to
truth-conditional strength. The projection depends on exactly 4 of the
10 features: `changeOfState`, `incrementalTheme`, `causallyAffected`,
and `stationary`. All 5 P-Agent features and `dependentExistence` are
irrelevant (`profileToDegree_depends_only_on_patient`).

This is one of three canonical projections of EntailmentProfile:

- `AgentivityNode.fromEntailmentProfile` → agentivity lattice ([grimm-2011])
- `profileToDegree` → affectedness hierarchy ([beavers-2010])  ← this file
- `PersistenceLevel.fromPatientProfile` → persistence lattice ([grimm-2011])

Each projection preserves different information and serves different
grammatical predictions:

| Projection            | Preserves              | Used for                    |
|-----------------------|------------------------|-----------------------------|
| AgentivityNode        | 4 P-Agent features     | Subject selection, case     |
| AffectednessDegree    | P-Patient strength     | MAP, direct/oblique         |
| PersistenceLevel      | Persistence pattern    | Case regions, DOM           |

## Grammatical consequence

The affectedness hierarchy predicts the **Morphosyntactic Alignment
Principle (MAP)**: when an argument alternates between direct and oblique
realization, the direct variant has truth conditions at least as strong
as the oblique. See `Studies/Beavers2010.lean`
for the empirical verification.

## Interface to root semantics

`AffectednessDegree` relates to **three** levels of change-of-state
representation in the codebase:

- `EntailmentProfile.changeOfState` — the proto-patient entailment (the projection's input)
- `MeaningComponents.changeOfState` — the surface diagnostic (`Semantics/Lexical/MeaningComponents.lean`)
- `LexKind.result` membership in a root's `Root.Kinds` — whether the root itself entails change (`Semantics/Lexical/Roots/Signature.lean`)

These are NOT the same concept. [beavers-koontz-garboden-2020] show
that surface CoS can come from either the root or the template. The
projection here operates on the proto-role level, which is the final
composed meaning — not the root-level or surface-diagnostic level.
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
    chain below), or both. -/
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
    typeclasses by design — see the docstring rationale above). -/

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

/-! ## The typeclass chain

The mathlib-style typeclass `extends` chain encoding [beavers-2011]'s
implicational affectedness hierarchy (eq. 62):

    quantized → non-quantized → potential

Each level extends the next-weaker (mathlib pattern: cf.
`T0Space → T1Space → T2Space → ...` for separation axioms,
`Semigroup → Monoid → Group → CommGroup` for algebraic hierarchies).

The chain bottoms at `IsPotentialAffected`. Beavers' eq. (60d)
`Unspecified` (mere participation, vacuous for any binary θ) is not
formalised as a typeclass — see §"Why `Unspecified` is not formalised"
in the module docstring above. The `AffectednessDegree` enum keeps
`unspecified` as a level tag for case analysis (parallel to
mathlib's `T0/T1/T2/...` hierarchy where "non-T0" exists as a state
but is not a typeclass).

Decomposition:

- `AffectednessDegree` enum (4 cases) with decidable order instances.
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
  derives the parent fields via the substrate implication chain. -/

namespace ArgumentStructure.Affectedness.Hierarchy

open ArgumentStructure.Affectedness

/-! ### AffectednessDegree enum (Beavers 4-level scale) -/

/-- [beavers-2011] eq. (62) — *The Affectedness Hierarchy*: four
    degrees of affectedness, defined by increasingly weaker truth
    conditions about what change occurs in the patient.

    Each degree is an existential generalisation over the `result'`
    relation (formalised in the scalar-result substrate above):
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

/-! ### Typeclass extends chain (Beavers eq. 62) -/

/-- [beavers-2011] eq. (60c) **Potential affectedness**: the
    bottom of the typeclass chain. Patient is a force-recipient at
    every event of θ — content: `Potential θ` from the substrate above,
    parameterised over a `[HasLatentScale α β]` instance.

    Linguistic exemplars: surface contact / impact verbs
    (*hit, wipe, scrub, kick*) — what
    [rappaport-hovav-levin-2001] called "force recipients"
    and [beavers-koontz-garboden-2020] retain the term.

    Why this is the chain bottom (not Unspecified): Beavers' (60d)
    Unspecified is `θ x e → ∃ θ', θ'(x, e)`, vacuous for any binary
    `θ` (take `θ' = θ`). A typeclass with vacuous content is content-
    free; the hierarchy chain bottoms at the first level with real
    structure. The `AffectednessDegree.unspecified` enum case still
    exists as a level tag for "no class declared." -/
class IsPotentialAffected {α β : Type*} [HasLatentScale α β]
    (θ : α → β → Prop) : Prop where
  isPotential : Potential θ

/-- [beavers-2011] eq. (60b) **Non-quantized affectedness**:
    extends Potential with a result-state commitment (some final
    degree on the scale). Content: `NonQuantized (δ := δ) θ` from
    the substrate above.

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

/-- [beavers-2011] eq. (60a) **Quantized affectedness**: extends
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
    `Semantics/Aspect/Incremental.lean` for the bridge
    smart constructor. -/
class IsQuantizedAffected {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    (θ : α → β → Prop) extends IsNonQuantizedAffected (δ := δ) θ where
  /-- The lexically-named specific final degree `g_φ`. -/
  finalDegree : δ
  /-- Witness that θ entails patient ends event with this degree. -/
  isQuantized : Quantized θ finalDegree

/-! ### Smart constructors -/

/-! Smart constructors that take only the level-specific witnesses and
    derive the inherited fields automatically via the substrate
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

end ArgumentStructure.Affectedness.Hierarchy

/-! ## The EntailmentProfile projection

The affectedness hierarchy is a projection of [dowty-1991]'s P-Patient
entailments onto a four-level total order ([beavers-2010]). The
`AffectednessDegree` enum and the typeclass `extends` chain live in the
sections above (substrate-level, referenceable by K98 verb-class
typeclasses). This section's role: project Dowty's `EntailmentProfile`
to `AffectednessDegree` and verify the projection on canonical verb
profiles. **The enum, `strength`, and `LE` instance are re-exported in
the `Profile` namespace for backward compatibility with existing
consumers.** -/

namespace ArgumentStructure.Affectedness.Profile

open _root_.ArgumentStructure (EntailmentProfile)
open _root_.ArgumentStructure.EntailmentProfile

/-! ### Re-exports from the typeclass-chain section -/

/-! The 4-level Beavers affectedness enum, declared in the Hierarchy
    section above and re-exported here for backward compatibility with
    consumers (`Beavers2010`, `BeaversUdayana2022`, `StapsRooryck2024`). -/
export ArgumentStructure.Affectedness.Hierarchy (AffectednessDegree)

namespace AffectednessDegree
export ArgumentStructure.Affectedness.Hierarchy.AffectednessDegree
  (unspecified potential nonquantized quantized strength)
end AffectednessDegree

/-! ### Projection: EntailmentProfile → AffectednessDegree -/

/-- Project an EntailmentProfile onto the affectedness hierarchy.

    This is the canonical P-Patient projection: it retains truth-conditional
    strength while discarding the specific identity of the entailments.

    The projection depends on exactly 4 of the 10 features:
    - `changeOfState` and `incrementalTheme` (distinguish quantized/nonquantized)
    - `causallyAffected` and `stationary` (distinguish potential/unspecified)

    All 5 P-Agent features and `dependentExistence` are irrelevant
    (`profileToDegree_depends_only_on_patient`).

    [beavers-2010] Table 5:
    | Dowty P-Patient         | Beavers entailment    |
    |-------------------------|-----------------------|
    | (a) changeOfState       | nonquantized change   |
    | (b) incrementalTheme    | totally traversed     |
    | (c) causallyAffected    | potential change       |
    | (d) stationary          | potential change       |
    | (e) dependentExistence  | (irrelevant here)     | -/
def profileToDegree (p : EntailmentProfile) : AffectednessDegree :=
  if p.incrementalTheme && p.changeOfState then .quantized
  else if p.changeOfState then .nonquantized
  else if p.causallyAffected || p.stationary then .potential
  else .unspecified

/-! ### Kernel Characterization -/

/-- The projection depends only on {CoS, IT, CA, St}.
    Profiles agreeing on these four features always map to the same degree.
    The remaining 6 features (V, S, C, M, IE, DE) are irrelevant.

    This is the **forward kernel** characterization: sufficient conditions
    for two profiles to have the same image under `profileToDegree`. -/
theorem profileToDegree_depends_only_on_patient (p q : EntailmentProfile)
    (hcos : p.changeOfState = q.changeOfState)
    (hit : p.incrementalTheme = q.incrementalTheme)
    (hca : p.causallyAffected = q.causallyAffected)
    (hst : p.stationary = q.stationary) :
    profileToDegree p = profileToDegree q := by
  simp only [profileToDegree, hcos, hit, hca, hst]

/-- What `quantized` guarantees: both CoS and IT hold. -/
theorem quantized_implies (p : EntailmentProfile)
    (h : profileToDegree p = .quantized) :
    p.changeOfState = true ∧ p.incrementalTheme = true := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-- What `nonquantized` guarantees: CoS without IT. -/
theorem nonquantized_implies (p : EntailmentProfile)
    (h : profileToDegree p = .nonquantized) :
    p.changeOfState = true ∧ p.incrementalTheme = false := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-- What `potential` guarantees: no CoS, but CA or St. -/
theorem potential_implies (p : EntailmentProfile)
    (h : profileToDegree p = .potential) :
    p.changeOfState = false ∧
    (p.causallyAffected = true ∨ p.stationary = true) := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-- What `unspecified` guarantees: no CoS, no CA, no St. -/
theorem unspecified_implies (p : EntailmentProfile)
    (h : profileToDegree p = .unspecified) :
    p.changeOfState = false ∧ p.causallyAffected = false ∧
    p.stationary = false := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  unfold profileToDegree at h
  cases it <;> cases cos <;> cases ca <;> cases st <;> simp_all

/-! ### Verification on Canonical Profiles -/

/-- Build object: incremental theme + CoS → quantized. -/
theorem build_object_quantized :
    profileToDegree buildObjectProfile = .quantized := rfl

/-- Eat object: incremental theme + CoS → quantized. -/
theorem eat_object_quantized :
    profileToDegree eatObjectProfile = .quantized := rfl

/-- Kick object: CoS but no IT → nonquantized. -/
theorem kick_object_nonquantized :
    profileToDegree kickObjectProfile = .nonquantized := rfl

/-- See subject has no P-Patient features → unspecified. -/
theorem see_unspecified :
    profileToDegree seeSubjectProfile = .unspecified := rfl

/-- Die subject: CoS but no IT → nonquantized (the dying entity
    undergoes change but not incrementally). -/
theorem die_nonquantized :
    profileToDegree dieSubjectProfile = .nonquantized := rfl

/-! ### Bridge: EntailmentProfile ↔ Typeclass Hierarchy -/

/-! The Bool-side `profileToDegree p = .quantized` and the typeclass-side
    `IsQuantizedAffected θ` say the same thing about Beavers level —
    *modulo* the missing primitive that connects a verb's Dowty profile
    to its substrate-level θ relation.

    **Substrate gap (acknowledged):** linglib has no `HasObjectTheme V α β`
    typeclass providing the canonical θ for a fragment verb. EntailmentProfile
    is per-(verb, argument) Bool data; θ is the abstract semantic relation. A
    structural bridge between them requires per-verb instances binding the
    two — fragment-level work that is not yet built.

    **Available now:** an explicit-witness smart constructor for the
    `(profile, θ, scalar witnesses)` triple. The user provides BOTH the Bool
    declaration (the profile projects to .quantized) AND the scalar witness
    (`Quantized θ g_φ`); the smart constructor packages them into a
    typeclass instance, ensuring the two declarations are jointly consistent.

    Mathlib pattern: when a structural bridge requires content the substrate
    doesn't carry, expose an explicit-witness smart constructor (cf. mathlib's
    `MetricSpace.ofDistTopology` and similar). -/

open ArgumentStructure.Affectedness.Hierarchy
open ArgumentStructure.Affectedness

/-- Joint consistency smart constructor: given a profile that projects to
    `.quantized` AND a scalar witness for some θ on a dimension δ,
    produce an `IsQuantizedAffected θ` instance.

    The two arguments encode parallel commitments — the Bool side
    (`p.profileToDegree = .quantized`) and the scalar side
    (`Quantized θ g_φ`). The smart constructor makes joint consistency
    structural: a consumer cannot construct an instance with a profile
    that projects to `.nonquantized` while declaring `Quantized` on the
    scalar side. -/
@[reducible]
def IsQuantizedAffected.ofProfileAndWitness {α β δ : Type*}
    [HasScalarResult α δ β] [HasLatentScale α β]
    (θ : α → β → Prop) (p : EntailmentProfile)
    (_h_profile : profileToDegree p = .quantized)
    (forget : ∀ (x : α) (e : β),
              (∃ g : δ, HasScalarResult.resultAt x g e) →
              HasLatentScale.latentScale x e)
    (g_φ : δ) (h_quantized : Quantized θ g_φ) :
    IsQuantizedAffected (δ := δ) θ :=
  IsQuantizedAffected.mk' forget g_φ h_quantized

end ArgumentStructure.Affectedness.Profile
