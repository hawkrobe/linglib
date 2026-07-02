import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Affectedness

[beavers-2011]'s scalar-theoretic affectedness hierarchy: two independent
typeclass primitives (result states, force recipients), the Beavers (60a–c)
predicates and eq. (62) implication chain over them, a mathlib-style
typeclass chain, and the projection of [dowty-1991]'s P-Patient entailments
onto the four-level degree scale ([beavers-2010]).

## Main definitions

- `HasScalarResult α δ β` — patient `x : α` ends event `e : β` holding
  degree `g : δ`; drives Beavers (60a) Quantized and (60b) Non-quantized.
- `HasLatentScale α β` — patient `x` is a force-recipient at event `e`
  ([rappaport-hovav-levin-2001]); drives Beavers (60c) Potential.
- `Quantized`, `NonQuantized`, `Potential` — Beavers (60a–c) on a thematic
  relation `θ : α → β → Prop`.
- `ScalarToLatent` — the forgetful link from result-bearing to
  force-receiving; hypothesis of the eq. (62) middle arrow.
- `nonQuantized_of_quantized`, `potential_of_nonQuantized` — the eq. (62)
  implication chain `quantized → non-quantized → potential`.
- `AffectednessDegree` — the four-level scale, linearly ordered by
  truth-conditional strength via `strength`.
- `IsQuantizedAffected → IsNonQuantizedAffected → IsPotentialAffected` —
  the typeclass `extends` chain, with smart constructors `mk'` deriving
  the inherited fields.
- `profileToDegree` — projection of [dowty-1991]'s `EntailmentProfile`
  onto `AffectednessDegree`, with kernel characterization.

## Implementation notes

`HasScalarResult` and `HasLatentScale` are kept formally independent: a verb
may have a latent scale without entailing a final degree, entail a final
degree without an explicit force-recipient relation, or both. The
Non-quantized → Potential step of eq. (62) therefore takes the forgetful
link `ScalarToLatent` as an explicit hypothesis rather than an instance — it
always holds in the canonical model (a result-bearing event is, a fortiori,
force-receiving) but is not forced by the types. `IsQuantizedAffected` is
Type-valued (cf. `MetricSpace` vs `T2Space`) so the lexically-named final
degree `g_φ` survives as data rather than being lost to existential closure.

Beavers' (60d) `Unspecified` (`φ → ∃e∃θ'[θ'(x, e)]`, mere participation) is
not formalised: for any binary `θ`, taking `θ' = θ` makes it vacuous, so a
definition would carry no content. The typeclass chain bottoms at Potential;
the `AffectednessDegree` enum keeps `unspecified` as a level tag for "no
class declared."

`profileToDegree` is one of three canonical projections of
`EntailmentProfile`, each preserving different information:

| Projection            | Preserves              | Used for                |
|-----------------------|------------------------|-------------------------|
| AgentivityNode        | 4 P-Agent features     | Subject selection, case |
| AffectednessDegree    | P-Patient strength     | MAP, direct/oblique     |
| PersistenceLevel      | Persistence pattern    | Case regions, DOM       |

The hierarchy predicts the Morphosyntactic Alignment Principle: a direct
realization has truth conditions at least as strong as its oblique
alternant — verified empirically in `Studies/Beavers2010.lean`.

`AffectednessDegree` interfaces with three distinct change-of-state notions
in the codebase: `EntailmentProfile.changeOfState` (the proto-patient
entailment, this projection's input), `MeaningComponents.changeOfState`
(the surface diagnostic), and `LexKind.result` membership in a root's
`Root.Kinds` (root-level change). These are not the same concept:
[beavers-koontz-garboden-2020] show surface CoS can come from either the
root or the template; the projection here operates at the proto-role
level — the final composed meaning.
-/

namespace ArgumentStructure.Affectedness

variable {α β δ : Type*}

/-! ### Scalar-result and latent-scale primitives -/

/-- `HasScalarResult α δ β` provides `resultAt x g e`: patient `x : α` ends
event `e : β` holding degree `g : δ`. The primitive behind [beavers-2011]
eq. (60a–b); per-verb the dimension `δ` is fixed by lexical content (*cool*
on temperature, *widen* on width, *eat* on consumption). Beavers' state
token `s` is elided in the 3-place form; consumers needing it for result-XP
licensing or *halfway*-modification ([beavers-koontz-garboden-2020] §1.6.1)
reintroduce it downstream. -/
class HasScalarResult (α δ β : Type*) where
  /-- Patient x ends event e holding degree g on dimension δ. -/
  resultAt : α → δ → β → Prop

/-- `HasLatentScale α β` provides `latentScale x e`: patient `x : α` is a
force-recipient at event `e : β` — related to some latent scale, no
transition entailed. The primitive behind [beavers-2011] eq. (60c),
originating with [rappaport-hovav-levin-2001]'s "force recipient" (surface
contact / impact verbs: *wipe, scrub, rub, punch, hit, kick, slap*).
Independent of `HasScalarResult` by design — see the module docstring. -/
class HasLatentScale (α β : Type*) where
  /-- Patient x is a force-recipient at event e (latent scale relation). -/
  latentScale : α → β → Prop

/-! ### Beavers (60a–c) affectedness predicates -/

section
variable [HasScalarResult α δ β]

/-- [beavers-2011] eq. (60a) **Quantized**: `θ` entails patient `x` ends
event `e` holding the SPECIFIC degree `g_φ` the predicate names (`dead` for
*kill*, `broken` for *break*, `g₁₀₀°C` for *heat to 100°C*). Linguistic
exemplars: accomplishments / achievements (*break, shatter, destroy,
devour x*). -/
def Quantized (θ : α → β → Prop) (g_φ : δ) : Prop :=
  ∀ x e, θ x e → HasScalarResult.resultAt x g_φ e

/-- [beavers-2011] eq. (60b) **Non-quantized**: `θ` entails patient `x`
ends event `e` holding SOME degree, not necessarily a specific one.
Linguistic exemplars: degree achievements (*widen, cool, lengthen, cut,
slice x*). -/
def NonQuantized (θ : α → β → Prop) : Prop :=
  ∀ x e, θ x e → ∃ g : δ, HasScalarResult.resultAt x g e

end

/-- [beavers-2011] eq. (60c) **Potential**: `θ` entails patient `x` is a
force-recipient at event `e` — a latent scale exists, no transition
entailed. Defined via `HasLatentScale`, not by excluded middle over a
result state (that encoding would be vacuous, equivalent to `Nonempty δ`).
Linguistic exemplars: surface contact / impact verbs (*wipe, scrub, rub,
punch, hit, kick, slap x*). -/
def Potential [HasLatentScale α β] (θ : α → β → Prop) : Prop :=
  ∀ x e, θ x e → HasLatentScale.latentScale x e

/-- The forgetful link from result-bearing to force-receiving: a patient
that ends an event holding some degree is a force-recipient at that event.
Hypothesis of [beavers-2011] eq. (62)'s middle arrow
(`potential_of_nonQuantized`); it always holds in the canonical model but
is not forced by the types, keeping the two typeclasses independent. -/
def ScalarToLatent (α δ β : Type*) [HasScalarResult α δ β] [HasLatentScale α β] : Prop :=
  ∀ (x : α) (e : β),
    (∃ g : δ, HasScalarResult.resultAt x g e) → HasLatentScale.latentScale x e

/-! ### Implication chain (Beavers eq. 62) -/

section
variable [HasScalarResult α δ β] {θ : α → β → Prop}

/-- Quantized entails Non-quantized: the specific final degree witnesses
the existential. [beavers-2011] eq. (62) leftmost arrow. -/
theorem nonQuantized_of_quantized {g_φ : δ} (h : Quantized θ g_φ) :
    NonQuantized (δ := δ) θ :=
  fun x e hxe => ⟨g_φ, h x e hxe⟩

/-- Non-quantized entails Potential under the forgetful link.
[beavers-2011] eq. (62) middle arrow. -/
theorem potential_of_nonQuantized [HasLatentScale α β]
    (forget : ScalarToLatent α δ β) (h : NonQuantized (δ := δ) θ) : Potential θ :=
  fun x e hxe => forget x e (h x e hxe)

end

/-! ### The affectedness degree scale -/

/-- [beavers-2011] eq. (62) — the affectedness hierarchy: four degrees of
affectedness, defined by increasingly weaker truth conditions about what
change occurs in the patient. Constructor order matches strength (weakest
first): `unspecified < potential < nonquantized < quantized`. -/
inductive AffectednessDegree where
  /-- Mere participation: no scale commitment (e.g., perception verbs *see, smell*). -/
  | unspecified
  /-- Force recipient: latent scale exists (e.g., surface contact *hit, wipe*). -/
  | potential
  /-- Some result state entailed (e.g., degree achievements *cool, widen*). -/
  | nonquantized
  /-- Specific final degree entailed (e.g., accomplishments *break, destroy*). -/
  | quantized
  deriving DecidableEq, Fintype, Repr, Inhabited

namespace AffectednessDegree

/-- Numeric strength: higher index = stronger truth conditions. -/
def strength : AffectednessDegree → Nat
  | .unspecified => 0
  | .potential => 1
  | .nonquantized => 2
  | .quantized => 3

instance : LinearOrder AffectednessDegree :=
  .lift' strength fun a b => by cases a <;> cases b <;> simp [strength]

end AffectednessDegree

/-! ### Typeclass chain (Beavers eq. 62)

Each level extends the next-weaker; the chain bottoms at
`IsPotentialAffected` (see the module docstring for why Beavers' (60d)
`Unspecified` is not a typeclass). -/

/-- [beavers-2011] eq. (60c) **Potential affectedness**, the bottom of the
typeclass chain: patient is a force-recipient at every event of `θ`.
Linguistic exemplars: surface contact / impact verbs (*hit, wipe, scrub,
kick*) — [rappaport-hovav-levin-2001]'s "force recipients". -/
class IsPotentialAffected [HasLatentScale α β] (θ : α → β → Prop) : Prop where
  /-- Beavers (60c): every event of θ has a force-receiving patient. -/
  isPotential : Potential θ

section
variable [HasScalarResult α δ β] [HasLatentScale α β]

/-- [beavers-2011] eq. (60b) **Non-quantized affectedness**: extends
Potential with a result-state commitment (some final degree on the scale).
Linguistic exemplars: degree achievements (*widen, cool, lengthen*),
non-quantized cutting verbs (*cut, slice*). -/
class IsNonQuantizedAffected (θ : α → β → Prop) : Prop
    extends IsPotentialAffected θ where
  /-- Beavers (60b): every event of θ ends with some result degree. -/
  isNonQuantized : NonQuantized (δ := δ) θ

/-- [beavers-2011] eq. (60a) **Quantized affectedness**: extends
Non-quantized with the commitment to a SPECIFIC final degree `g_φ : δ`,
lexically named by the verb. Type-valued so `finalDegree` survives as data
(*break-into-shards* vs *break-into-dust* are distinguishable instances).
Linguistic exemplars: accomplishments / achievements (*break, shatter,
destroy, devour*); K98 SINC verbs are a strictly stronger class — see
`Semantics/Aspect/Incremental.lean` for the bridge smart constructor. -/
class IsQuantizedAffected (θ : α → β → Prop)
    extends IsNonQuantizedAffected (δ := δ) θ where
  /-- The lexically-named specific final degree `g_φ`. -/
  finalDegree : δ
  /-- Witness that θ entails patient ends event with this degree. -/
  isQuantized : Quantized θ finalDegree

end

/-! ### Smart constructors -/

/-- Smart constructor for `IsPotentialAffected` from the `Potential`
witness. -/
@[reducible]
def IsPotentialAffected.mk' [HasLatentScale α β] {θ : α → β → Prop}
    (h : Potential θ) : IsPotentialAffected θ where
  isPotential := h

section
variable [HasScalarResult α δ β] [HasLatentScale α β] {θ : α → β → Prop}
  (forget : ScalarToLatent α δ β)

/-- Smart constructor for `IsNonQuantizedAffected`: derives the inherited
Potential field via `potential_of_nonQuantized`. -/
@[reducible]
def IsNonQuantizedAffected.mk' (h : NonQuantized (δ := δ) θ) :
    IsNonQuantizedAffected (δ := δ) θ where
  toIsPotentialAffected := IsPotentialAffected.mk' (potential_of_nonQuantized forget h)
  isNonQuantized := h

/-- Smart constructor for `IsQuantizedAffected`: derives all weaker levels
via the eq. (62) chain, preserving `g_φ` as accessible data. -/
@[reducible]
def IsQuantizedAffected.mk' (g_φ : δ) (h : Quantized θ g_φ) :
    IsQuantizedAffected (δ := δ) θ where
  toIsNonQuantizedAffected :=
    IsNonQuantizedAffected.mk' forget (nonQuantized_of_quantized h)
  finalDegree := g_φ
  isQuantized := h

end

/-! ### Projection from EntailmentProfile -/

/-- Project an `EntailmentProfile` onto the affectedness hierarchy
([beavers-2010] Table 5): `changeOfState` and `incrementalTheme`
distinguish quantized/nonquantized; `causallyAffected` and `stationary`
distinguish potential/unspecified. All 5 P-Agent features and
`dependentExistence` are irrelevant
(`profileToDegree_depends_only_on_patient`). -/
def profileToDegree (p : EntailmentProfile) : AffectednessDegree :=
  if p.incrementalTheme && p.changeOfState then .quantized
  else if p.changeOfState then .nonquantized
  else if p.causallyAffected || p.stationary then .potential
  else .unspecified

/-- Forward kernel characterization: profiles agreeing on {CoS, IT, CA, St}
map to the same degree — the remaining six features are irrelevant. -/
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
  unfold profileToDegree at h
  split_ifs at h
  simp_all

/-- What `nonquantized` guarantees: CoS without IT. -/
theorem nonquantized_implies (p : EntailmentProfile)
    (h : profileToDegree p = .nonquantized) :
    p.changeOfState = true ∧ p.incrementalTheme = false := by
  unfold profileToDegree at h
  split_ifs at h
  simp_all

/-- What `potential` guarantees: no CoS, but CA or St. -/
theorem potential_implies (p : EntailmentProfile)
    (h : profileToDegree p = .potential) :
    p.changeOfState = false ∧
    (p.causallyAffected = true ∨ p.stationary = true) := by
  unfold profileToDegree at h
  split_ifs at h
  simp_all

/-- What `unspecified` guarantees: no CoS, no CA, no St. -/
theorem unspecified_implies (p : EntailmentProfile)
    (h : profileToDegree p = .unspecified) :
    p.changeOfState = false ∧ p.causallyAffected = false ∧
    p.stationary = false := by
  unfold profileToDegree at h
  split_ifs at h
  simp_all

/-! ### Bridge to the typeclass chain

The Bool-side `profileToDegree p = .quantized` and the typeclass-side
`IsQuantizedAffected θ` describe the same Beavers level, but connecting
them structurally needs substrate linglib does not yet have: a per-verb
typeclass binding a fragment verb's `EntailmentProfile` to its thematic
relation θ. Until that lands, consumers declare both sides and package the
scalar witnesses with `IsQuantizedAffected.mk'`. -/

end ArgumentStructure.Affectedness
