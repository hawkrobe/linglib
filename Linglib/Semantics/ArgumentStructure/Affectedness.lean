import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Affectedness

[beavers-2011]'s scalar-theoretic affectedness hierarchy: two independent
typeclass primitives (result states, force recipients), the Beavers (60a–c)
predicates and eq. (62) implication chain over them, stackable mixin
classes, and the projection of [dowty-1991]'s P-Patient entailments onto
the four-level degree scale ([beavers-2010]).

## Main definitions

- `HasScalarResult`, `HasLatentScale` — the two scalar primitives
- `Quantized`, `NonQuantized`, `Potential` — Beavers (60a–c) on a thematic
  relation, with the eq. (62) chain (`nonQuantized_of_quantized`,
  `potential_of_nonQuantized`) and its hypothesis `ScalarToLatent`
- `LawfulScalarLatent` — the forgetful link as a coherence mixin between
  the two primitives
- `AffectednessDegree` — the four-level scale, a `LinearOrder`
- `IsQuantizedAffected`, `IsNonQuantizedAffected`, `IsPotentialAffected` —
  eq. (62) as stackable mixin classes
- `profileToDegree` — projection of `EntailmentProfile` onto the scale

## Implementation notes

The two primitives are formally independent; the eq. (62) middle arrow
takes `ScalarToLatent` as an explicit hypothesis. The affectedness classes
are stackable mixins, not an `extends` chain: declare the strongest class
that holds and the weaker ones are derived (the ordered-algebra
`IsOrderedRing` precedent) — the leftmost arrow by instance, the middle
arrow by `IsNonQuantizedAffected.isPotential'`. The middle arrow is
deliberately *not* an instance: its `δ` would be a metavariable during
synthesis, and the forgetful link is a modeling assumption that should
stay visible at use sites. `IsQuantizedAffected` is
Type-valued so the verb's named final degree survives as data. Beavers'
(60d) `Unspecified` is vacuous for any binary `θ` and is a degree tag only,
not a typeclass. One of three `EntailmentProfile` projections
(`AgentivityNode` P-Agent, this file P-Patient strength → MAP
(`Studies/Beavers2010.lean`), `PersistenceLevel` → case regions); distinct
from the surface (`MeaningComponents.changeOfState`) and root
(`LexKind.result`) change-of-state notions ([beavers-koontz-garboden-2020]).
-/

namespace ArgumentStructure.Affectedness

variable {α β δ : Type*}

/-! ### Scalar-result and latent-scale primitives -/

/-- `resultAt x g e`: patient `x` ends event `e` holding degree `g` on the
verb's lexical dimension `δ` ([beavers-2011] eq. 60a–b). -/
class HasScalarResult (α δ β : Type*) where
  /-- Patient x ends event e holding degree g on dimension δ. -/
  resultAt : α → δ → β → Prop

/-- `latentScale x e`: patient `x` is a force-recipient at event `e` — a
latent scale, no transition entailed ([beavers-2011] eq. 60c;
[rappaport-hovav-levin-2001]). -/
class HasLatentScale (α β : Type*) where
  /-- Patient x is a force-recipient at event e (latent scale relation). -/
  latentScale : α → β → Prop

/-! ### Beavers (60a–c) affectedness predicates -/

section
variable [HasScalarResult α δ β] (θ : α → β → Prop)

/-- [beavers-2011] eq. (60a): `θ` entails the patient ends the event at the
specific degree `g_φ` the verb names (*break*, *destroy*). -/
def Quantized (g_φ : δ) : Prop :=
  ∀ x e, θ x e → HasScalarResult.resultAt x g_φ e

/-- [beavers-2011] eq. (60b): `θ` entails the patient ends the event at
some degree (*widen*, *cool*). -/
def NonQuantized : Prop :=
  ∀ x e, θ x e → ∃ g : δ, HasScalarResult.resultAt x g e

end

section
variable [HasLatentScale α β] (θ : α → β → Prop)

/-- [beavers-2011] eq. (60c): `θ` entails the patient is a force-recipient
(*hit*, *wipe*). -/
def Potential : Prop :=
  ∀ x e, θ x e → HasLatentScale.latentScale x e

end

/-- The forgetful link: a result-bearing patient is a force-recipient.
Hypothesis of eq. (62)'s middle arrow; holds in the canonical model but is
not forced by the types. -/
def ScalarToLatent (α δ β : Type*) [HasScalarResult α δ β] [HasLatentScale α β] : Prop :=
  ∀ (x : α) (e : β),
    (∃ g : δ, HasScalarResult.resultAt x g e) → HasLatentScale.latentScale x e

/-- The forgetful link as a coherence mixin between the two primitives:
holds in the canonical model; per-model instances declare it. -/
class LawfulScalarLatent (α δ β : Type*) [HasScalarResult α δ β]
    [HasLatentScale α β] : Prop where
  /-- The `ScalarToLatent` witness. -/
  toLatent : ScalarToLatent α δ β

/-! ### Implication chain (Beavers eq. 62) -/

section
variable [HasScalarResult α δ β] {θ : α → β → Prop}

/-- [beavers-2011] eq. (62), leftmost arrow. -/
theorem nonQuantized_of_quantized {g_φ : δ} (h : Quantized θ g_φ) :
    NonQuantized (δ := δ) θ :=
  fun x e hxe => ⟨g_φ, h x e hxe⟩

/-- [beavers-2011] eq. (62), middle arrow, under the forgetful link. -/
theorem potential_of_nonQuantized [HasLatentScale α β]
    (forget : ScalarToLatent α δ β) (h : NonQuantized (δ := δ) θ) : Potential θ :=
  fun x e hxe => forget x e (h x e hxe)

end

/-! ### The affectedness degree scale -/

/-- [beavers-2011] eq. (62): four affectedness degrees, ordered by
truth-conditional strength, weakest first. -/
inductive AffectednessDegree where
  /-- Mere participation: no scale commitment (*see*, *smell*). -/
  | unspecified
  /-- Force recipient: latent scale exists (*hit*, *wipe*). -/
  | potential
  /-- Some result state entailed (*cool*, *widen*). -/
  | nonquantized
  /-- Specific final degree entailed (*break*, *destroy*). -/
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

/-! ### Typeclass mixins (Beavers eq. 62) -/

section
variable [HasLatentScale α β] (θ : α → β → Prop)

/-- Eq. (60c) as the bottom of the mixin stack (*hit*, *wipe*). -/
class IsPotentialAffected : Prop where
  /-- Beavers (60c): every event of θ has a force-receiving patient. -/
  isPotential : Potential θ

end

section
variable [HasScalarResult α δ β] (θ : α → β → Prop)

/-- Eq. (60b): a result-state commitment (*widen*, *cool*). -/
class IsNonQuantizedAffected : Prop where
  /-- Beavers (60b): every event of θ ends with some result degree. -/
  isNonQuantized : NonQuantized (δ := δ) θ

/-- Eq. (60a): the verb's specific final degree, kept as data (*break*,
*destroy*; the SINC bridge is in `Semantics/Aspect/Incremental.lean`). -/
class IsQuantizedAffected where
  /-- The lexically-named specific final degree `g_φ`. -/
  finalDegree : δ
  /-- Witness that θ entails patient ends event with this degree. -/
  isQuantized : Quantized θ finalDegree

variable {θ}

/-- Eq. (62), leftmost arrow, free at the class level: quantized-affected
verbs are non-quantized-affected. -/
instance IsQuantizedAffected.toIsNonQuantizedAffected
    [inst : IsQuantizedAffected (δ := δ) θ] :
    IsNonQuantizedAffected (δ := δ) θ :=
  ⟨nonQuantized_of_quantized inst.isQuantized⟩

/-- Eq. (62), middle arrow at the class level, under the
`LawfulScalarLatent` mixin. Deliberately a theorem, not an instance (see
Implementation notes). -/
theorem IsNonQuantizedAffected.isPotential' [HasLatentScale α β]
    [LawfulScalarLatent α δ β] [inst : IsNonQuantizedAffected (δ := δ) θ] :
    IsPotentialAffected θ :=
  ⟨potential_of_nonQuantized LawfulScalarLatent.toLatent inst.isNonQuantized⟩

end

/-! ### Projection from EntailmentProfile -/

/-- Project a profile onto the hierarchy ([beavers-2010] Table 5): CoS/IT
split quantized/nonquantized; CA/St split potential/unspecified. -/
def profileToDegree (p : EntailmentProfile) : AffectednessDegree :=
  if p.incrementalTheme && p.changeOfState then .quantized
  else if p.changeOfState then .nonquantized
  else if p.causallyAffected || p.stationary then .potential
  else .unspecified

variable (p q : EntailmentProfile)

/-- Profiles agreeing on {CoS, IT, CA, St} map to the same degree — the
remaining six features are irrelevant. -/
theorem profileToDegree_depends_only_on_patient
    (hcos : p.changeOfState = q.changeOfState)
    (hit : p.incrementalTheme = q.incrementalTheme)
    (hca : p.causallyAffected = q.causallyAffected)
    (hst : p.stationary = q.stationary) :
    profileToDegree p = profileToDegree q := by
  simp only [profileToDegree, hcos, hit, hca, hst]

/-- The `quantized` fiber: exactly IT ∧ CoS. -/
@[simp]
theorem profileToDegree_eq_quantized_iff :
    profileToDegree p = .quantized ↔
      p.incrementalTheme = true ∧ p.changeOfState = true := by
  unfold profileToDegree; split_ifs <;> simp_all

/-- The `nonquantized` fiber: exactly CoS without IT. -/
@[simp]
theorem profileToDegree_eq_nonquantized_iff :
    profileToDegree p = .nonquantized ↔
      p.changeOfState = true ∧ p.incrementalTheme = false := by
  unfold profileToDegree; split_ifs <;> simp_all

/-- The `potential` fiber: exactly no CoS with CA or St. -/
@[simp]
theorem profileToDegree_eq_potential_iff :
    profileToDegree p = .potential ↔
      p.changeOfState = false ∧
        (p.causallyAffected = true ∨ p.stationary = true) := by
  unfold profileToDegree; split_ifs <;> simp_all

/-- The `unspecified` fiber: exactly no CoS, no CA, no St. -/
@[simp]
theorem profileToDegree_eq_unspecified_iff :
    profileToDegree p = .unspecified ↔
      p.changeOfState = false ∧ p.causallyAffected = false ∧
        p.stationary = false := by
  unfold profileToDegree
  split_ifs <;> simp_all [or_iff_not_imp_left]

/-! ### Bridge to the typeclass chain

Connecting `profileToDegree` to `IsQuantizedAffected` structurally needs
per-verb substrate binding a fragment verb's profile to its θ; until that
lands, consumers declare the strongest mixin the verb's scalar witnesses
support. -/

end ArgumentStructure.Affectedness
