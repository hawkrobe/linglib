import Mathlib.Data.Fintype.Basic
import Linglib.Core.Order.PullbackPreorder

/-!
# Feature bundles

The representation-polymorphic interface for feature bundles, and the
canonical extensional representation `Features.Bundle`.

A feature bundle assigns values to features. Theories disagree about
what a bundle *is* — a list of valued features, a finite set, a partial
assignment over a feature space, an attribute-value structure, a
hierarchical tree whose root label is the flat bundle. They agree about
what a bundle *says*: which features it specifies, with which values.
`BundleLike` captures that shared observation language — a single
valuation `val : B → (t : F) → Option (V t)` — so that specification,
subsumption, and the information order are stated once and inherited by
every representation.

Extensionality is deliberately not part of `BundleLike`: structured
representations (assembly trees, feature-geometric hierarchies) can
present the same valuation in distinct ways, and that multiplicity can
itself carry theoretical content. Representations whose valuation is
injective opt into `LawfulBundleLike` and get extensionality and the
subsumption partial order.

Both parameters are fully general. The feature space `F` is data, not a
built-in inventory, so per-language and per-theory feature sets are
choices of `F`. The value family `V` covers the standard ontologies:
`V t := Unit` is privative, `V t := Bool` is bivalent `[±F]`, any enum
gives multivalent features, a mode-tagged product recovers
valued/unvalued distinctions, and `V t := ℚ` recovers gradient feature
theories.

## Main declarations

* `BundleLike` — the valuation interface
* `LawfulBundleLike` — extensional representations; gives
  `BundleLike.ext` and `BundleLike.partialOrder`
* `BundleLike.Specifies`, `BundleLike.Subsumes` — the derived API;
  `Subsumes` is the subsumption order of the unification-grammar
  tradition ([shieber-1986])
* `Features.Bundle F V` — the canonical extensional carrier, a partial
  assignment `(t : F) → Option (V t)`, carrying the subsumption
  `PartialOrder` with `⊥` the everywhere-underspecified bundle
* `BundleLike.subsumptionPreorder` — any representation pulls the
  subsumption order back along `val`, as a `Core.Order.PullbackPreorder`

## Implementation notes

`Features.Bundle` is a `def`, not an `abbrev`, on the `WithBot`
precedent: it is the same underlying type as the dependent Pi
`(t : F) → Option (V t)` but carries the subsumption order as *the*
order, and a reducible synonym would leak that instance onto bare Pi
types. Pi-level instances that are wanted (`DecidableEq`) are
transferred explicitly. `Features.Bundle` is unrelated to mathlib's
fiber-bundle `Bundle` namespace; qualify when both are in scope.

Instances live with their carriers, not here: this file imports only
`Core` and mathlib, and e.g. the phonological partial-assignment carrier
instantiates `BundleLike` in its own file.

## Todo

* Instantiate at the existing carriers: `Phonology/Featural/Bundle.lean`
  (lawful; its `FeatureBundle F V` is definitionally
  `Features.Bundle F (λ _ => V)`), `Data/UD/Basic.lean`'s
  `MorphFeatures` (a flat attribute-value record; deriving its
  hand-rolled `Subsumes` from `BundleLike.Subsumes` collapses
  `Morphology/Unification.lean`'s parallel order proofs), and the
  Minimalist `FeatureBundle` (lawful only after the planned
  list-to-assignment retype).
* Unification: the partial meet/join `Bundle.unify : Bundle F V →
  Bundle F V → Option (Bundle F V)` (defined where valuations are
  compatible), characterized as the join in the subsumption order —
  the algebra the unification-grammar tradition is actually about.
* A hierarchical assembly-tree carrier with the flattening valuation —
  `BundleLike` but not `LawfulBundleLike`.
-/

universe u v

/-- `BundleLike B F V`: `B` presents feature bundles over the feature
space `F`, with values of feature `t` drawn from `V t`. The single
primitive is the valuation: which value, if any, a bundle assigns to
each feature. -/
class BundleLike (B : Type*) (F : outParam Type*) (V : outParam (F → Type*)) where
  /-- The value, if any, that the bundle assigns to feature `t`. -/
  val : B → (t : F) → Option (V t)

/-- An extensional bundle representation: bundles with the same valuation
are equal. Structured representations whose internal organization
outruns their valuation are deliberately not lawful. -/
class LawfulBundleLike (B : Type*) {F : Type*} {V : F → Type*}
    [BundleLike B F V] : Prop where
  val_injective : Function.Injective (BundleLike.val (B := B) (F := F) (V := V))

namespace BundleLike

variable {B F : Type*} {V : F → Type*} [BundleLike B F V]

/-- Extensionality for lawful representations. -/
@[ext]
theorem ext [LawfulBundleLike B] {b₁ b₂ : B}
    (h : ∀ t, val (V := V) b₁ t = val b₂ t) : b₁ = b₂ :=
  LawfulBundleLike.val_injective (funext h)

/-- `b` specifies feature `t` (assigns it some value). -/
def Specifies (b : B) (t : F) : Prop :=
  ∃ v, val b t = some v

instance (b : B) (t : F) : Decidable (Specifies b t) :=
  decidable_of_iff _ Option.isSome_iff_exists

/-- Subsumption: `b₁` subsumes into `b₂` when every feature `b₁`
specifies is specified by `b₂` with the same value. The information
order of the feature-structure literature ([shieber-1986]): `b₂` is at
least as specified as `b₁`. -/
def Subsumes (b₁ b₂ : B) : Prop :=
  ∀ t (v : V t), val b₁ t = some v → val b₂ t = some v

theorem subsumes_refl (b : B) : Subsumes b b :=
  λ _ _ h => h

theorem subsumes_trans {b₁ b₂ b₃ : B} (h₁₂ : Subsumes b₁ b₂)
    (h₂₃ : Subsumes b₂ b₃) : Subsumes b₁ b₃ :=
  λ t v hv => h₂₃ t v (h₁₂ t v hv)

/-- On a lawful representation, subsumption is antisymmetric. -/
theorem subsumes_antisymm [LawfulBundleLike B] {b₁ b₂ : B}
    (h₁ : Subsumes b₁ b₂) (h₂ : Subsumes b₂ b₁) : b₁ = b₂ :=
  ext λ t => by
    cases hv : val (V := V) b₁ t with
    | some v => exact (h₁ t v hv).symm
    | none =>
      cases hw : val (V := V) b₂ t with
      | some w => exact hv ▸ h₂ t w hw
      | none => rfl

/-- Disjunctive characterization of subsumption; the decidable form. -/
theorem subsumes_iff_forall_eq {b₁ b₂ : B} :
    Subsumes b₁ b₂ ↔
      ∀ t, val (V := V) b₁ t = none ∨ val b₁ t = val b₂ t := by
  constructor
  · intro h t
    cases hv : val (V := V) b₁ t with
    | none => exact .inl rfl
    | some v => exact .inr (h t v hv).symm
  · intro h t v hv
    rcases h t with h' | h'
    · rw [hv] at h'; exact absurd h' (Option.some_ne_none v)
    · rw [← h', hv]

instance [Fintype F] [∀ t, DecidableEq (V t)] (b₁ b₂ : B) :
    Decidable (Subsumes b₁ b₂) :=
  decidable_of_iff _ subsumes_iff_forall_eq.symm

/-- The subsumption partial order on a lawful representation. Not an
instance: a representation may carry its own canonical order. -/
@[reducible]
def partialOrder [LawfulBundleLike B] : PartialOrder B where
  le := Subsumes
  le_refl := subsumes_refl
  le_trans _ _ _ := subsumes_trans
  le_antisymm _ _ := subsumes_antisymm

end BundleLike

namespace Features

/-- The canonical extensional feature bundle: a partial assignment of
values to features. Underspecification is `none`; at most one value per
feature holds by construction. A `def` rather than an `abbrev` so that
the subsumption order below does not leak onto bare Pi types (see the
module docstring). -/
def Bundle (F : Type u) (V : F → Type v) : Type max u v :=
  (t : F) → Option (V t)

namespace Bundle

variable {F : Type u} {V : F → Type v}

instance : BundleLike (Bundle F V) F V :=
  ⟨λ b => b⟩

instance : LawfulBundleLike (Bundle F V) :=
  ⟨λ _ _ h => h⟩

instance [Fintype F] [∀ t, DecidableEq (V t)] : DecidableEq (Bundle F V) :=
  inferInstanceAs (DecidableEq ((t : F) → Option (V t)))

/-- The subsumption (information) partial order: `b₁ ≤ b₂` iff `b₂`
specifies everything `b₁` does, with the same values. -/
instance : PartialOrder (Bundle F V) :=
  BundleLike.partialOrder

instance [Fintype F] [∀ t, DecidableEq (V t)] (b₁ b₂ : Bundle F V) :
    Decidable (b₁ ≤ b₂) :=
  inferInstanceAs (Decidable (BundleLike.Subsumes b₁ b₂))

/-- The everywhere-underspecified bundle is the bottom of the
subsumption order. -/
instance : OrderBot (Bundle F V) where
  bot := λ _ => none
  bot_le _ _ _ h := absurd h (Option.some_ne_none _).symm

@[simp]
theorem val_bot (t : F) : BundleLike.val (⊥ : Bundle F V) t = none :=
  rfl

/-- The bundle specifying exactly one feature. -/
def single [DecidableEq F] (t : F) (v : V t) : Bundle F V :=
  Function.update (⊥ : Bundle F V) t (some v)

@[simp]
theorem val_single_self [DecidableEq F] (t : F) (v : V t) :
    BundleLike.val (single t v) t = some v := by
  simp [single, BundleLike.val]

@[simp]
theorem val_single_of_ne [DecidableEq F] {s t : F} (h : s ≠ t) (v : V t) :
    BundleLike.val (single t v) s = none := by
  simp only [single, BundleLike.val, Function.update_of_ne h]
  rfl

@[simp]
theorem not_specifies_bot (t : F) : ¬ BundleLike.Specifies (⊥ : Bundle F V) t :=
  λ ⟨_, hv⟩ => by simp at hv

@[simp]
theorem specifies_single [DecidableEq F] {s t : F} (v : V t) :
    BundleLike.Specifies (single t v) s ↔ s = t := by
  constructor
  · intro ⟨w, hw⟩
    by_contra h
    rw [val_single_of_ne h] at hw
    exact Option.some_ne_none w hw.symm
  · rintro rfl
    exact ⟨v, val_single_self s v⟩

end Bundle

end Features

namespace BundleLike

variable {B F : Type*} {V : F → Type*} [BundleLike B F V]

/-- Any bundle representation carries the subsumption order pulled back
along its valuation, packaged as a `Core.Order.PullbackPreorder` into the
canonical carrier. Coarsenings between representations (e.g. assembly
trees to flat bundles) then factor through
`Core.Order.PullbackPreorder.coarsen_via_monotone`. A `def`, not an
instance, matching `PullbackPreorder`'s own convention. -/
def subsumptionPreorder [Fintype F] [∀ t, DecidableEq (V t)] :
    Core.Order.PullbackPreorder B (Features.Bundle F V) :=
  .ofProj (λ b => (val b : Features.Bundle F V)) (λ _ _ => inferInstance)

end BundleLike
