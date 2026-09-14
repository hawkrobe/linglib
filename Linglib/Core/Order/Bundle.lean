import Mathlib.Data.Fintype.Basic
import Linglib.Core.Order.Flat
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
valuation `val : B → (t : F) → S t` — so that specification,
subsumption, and the information order are stated once and inherited by
every representation.

Extensionality is deliberately not part of `BundleLike`: structured
representations (assembly trees, feature-geometric hierarchies) can
present the same valuation in distinct ways, and that multiplicity can
itself carry theoretical content. Representations whose valuation is
injective opt into `LawfulBundleLike` and get extensionality and the
subsumption partial order.

All three parameters are fully general. The feature space `F` is data,
not a built-in inventory, so per-language and per-theory feature sets
are choices of `F`. The slot family `S : F → Type*` is the per-feature
information space — it carries its own order, so each slot may be (a)
`Flat (V t)` for a single atom from an enum `V t` (the determinate
case: privative if `V t := Unit`, bivalent if `V t := Bool`,
multivalent for an enum, mode-tagged products for valued/unvalued
distinctions, `ℚ` for gradient theories); or (b) `(Finset α)ᵒᵈ` for
indeterminate values in the sense of [dalrymple-kaplan-2000]; or (c)
some richer order for layered or hierarchical features. The lattice
theory is proved once at the Pi level and inherited by every choice of
`S`.

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

`Features.Bundle` is an `abbrev` over the Pi type of `Flat` slots
(`Core/Order/Flat.lean`): the reducibility barrier sits at `Flat`, so
the subsumption order does not leak onto bare `Option`-valued Pi types,
while mathlib's Pi instances supply the whole order stack — the
subsumption `PartialOrder`, `OrderBot` (`⊥` = everywhere
underspecified), `SemilatticeInf` (generalization/anti-unification),
and the partial join `PartialUnify` (unification). This is the bounded
complete partial order of the unification tradition ([carpenter-1992]
Definition 2.1; "a finite BCPO is nothing more nor less than a finite
meet semilattice", presented through its joins). `Features.Bundle` is
unrelated to mathlib's fiber-bundle `Bundle` namespace; qualify when
both are in scope.

Instances live with their carriers, not here: this file imports only
`Core` and mathlib, and e.g. `Morphology.UD.MorphFeatures` instantiates
`BundleLike` in its own file.

The phonological carrier uses `Bundle` directly: `Phonology.Segment`'s `spec`
field is `Features.Bundle Feature (fun _ => Bool)` (in unfolded `Feature →
Option Bool` form), with the shared `merge`/`set`/`delete` algebra below.

## Todo

* Instantiate `BundleLike` at the Minimalist `FeatureBundle`
  (lawful only after the planned list-to-assignment retype).
* Per-slot generality: `Bundle` fixes the flat slot order. UD-practice
  pressure (multivalued features as `Finset`-superset slots, layered
  features as a nested index) is accommodated by working with
  `(t : F) → S t` for other slot orders `S`; the `PartialUnify` Pi
  instance is already stated at that generality.
* A hierarchical assembly-tree carrier with the flattening valuation —
  `BundleLike` but not `LawfulBundleLike`.
-/

universe u v

/-- `BundleLike B F S`: `B` presents feature bundles over the feature
space `F`, with slot `t` taking values in the order space `S t`. The
single primitive is the valuation: a function reading off the slot
value at each feature.

The slot type `S t` carries its own order. The canonical flat-atomic
slot is `Flat (V t)` for an atom enum `V t`; richer slot orders
(`Finset α` for indeterminacy in the sense of [dalrymple-kaplan-2000],
nested attribute spaces for UD layered features) are obtained by
choosing different `S`. -/
class BundleLike (B : Type*) (F : outParam Type*) (S : outParam (F → Type*)) where
  /-- The value the bundle assigns to feature `t`. -/
  val : B → (t : F) → S t

/-- An extensional bundle representation: bundles with the same valuation
are equal. Structured representations whose internal organization
outruns their valuation are deliberately not lawful. -/
class LawfulBundleLike (B : Type*) {F : Type*} {S : F → Type*}
    [BundleLike B F S] : Prop where
  val_injective : Function.Injective (BundleLike.val (B := B) (F := F) (S := S))

namespace BundleLike

variable {B F : Type*} {S : F → Type*} [BundleLike B F S]

/-- Extensionality for lawful representations. -/
@[ext]
theorem ext [LawfulBundleLike B] {b₁ b₂ : B}
    (h : ∀ t, val (S := S) b₁ t = val b₂ t) : b₁ = b₂ :=
  LawfulBundleLike.val_injective (funext h)

/-- `b` specifies feature `t` (assigns it more than the slot's bottom
information). For flat slots this coincides with "the slot is `some`";
for richer slots (set-valued indeterminacy) it means "the slot has not
been left at `Finset.univ`" (in the order dual where superset = less
determinate). Only `Bot` is required; the order is not. -/
def Specifies [∀ t, Bot (S t)] (b : B) (t : F) : Prop :=
  val (S := S) b t ≠ ⊥

instance [∀ t, Bot (S t)] [∀ t, DecidableEq (S t)]
    (b : B) (t : F) : Decidable (Specifies (S := S) b t) :=
  inferInstanceAs (Decidable (val (S := S) b t ≠ ⊥))

section Order

variable [∀ t, PartialOrder (S t)]

/-- Subsumption: pointwise ≤ on slots — `b₂` is at least as specified as
`b₁` ([shieber-1986] §3.2.2; [carpenter-1992] Definition 2.1). For flat
slots this is `≤` on `Flat`; for set-valued slots it is the
indeterminacy order ([dalrymple-kaplan-2000]: superset = less
determinate). -/
def Subsumes (b₁ b₂ : B) : Prop :=
  ∀ t, val (S := S) b₁ t ≤ val b₂ t

theorem subsumes_refl (b : B) : Subsumes (S := S) b b :=
  λ _ => le_rfl

theorem subsumes_trans {b₁ b₂ b₃ : B}
    (h₁₂ : Subsumes (S := S) b₁ b₂) (h₂₃ : Subsumes b₂ b₃) :
    Subsumes (S := S) b₁ b₃ :=
  λ t => le_trans (h₁₂ t) (h₂₃ t)

/-- On a lawful representation with partial slot orders, subsumption is
antisymmetric. -/
theorem subsumes_antisymm [LawfulBundleLike B] {b₁ b₂ : B}
    (h₁ : Subsumes (S := S) b₁ b₂) (h₂ : Subsumes b₂ b₁) : b₁ = b₂ :=
  ext λ t => le_antisymm (h₁ t) (h₂ t)

instance [Fintype F] [∀ t, DecidableLE (S t)] (b₁ b₂ : B) :
    Decidable (Subsumes (S := S) b₁ b₂) :=
  inferInstanceAs (Decidable (∀ t, val b₁ t ≤ val b₂ t))

/-- The subsumption partial order on a lawful representation. Not an
instance: a representation may carry its own canonical order. -/
@[reducible]
def partialOrder [LawfulBundleLike B] : PartialOrder B where
  le := Subsumes
  le_refl := subsumes_refl
  le_trans _ _ _ := subsumes_trans
  le_antisymm _ _ := subsumes_antisymm

end Order

end BundleLike

namespace Features

/-- The canonical extensional feature bundle: a partial assignment of
values to features, as a Pi type of `Flat` slots. Underspecification is
`none`; at most one value per feature holds by construction. The order
stack — subsumption `PartialOrder`, `OrderBot`, `SemilatticeInf`,
`PartialUnify` — is inherited from the slots through mathlib's Pi
instances (the reducibility barrier lives at `Flat`, see the module
docstring). -/
abbrev Bundle (F : Type u) (V : F → Type v) : Type max u v :=
  (t : F) → Flat (V t)

namespace Bundle

variable {F : Type u} {V : F → Type v}

instance : BundleLike (Bundle F V) F (λ t => Flat (V t)) :=
  ⟨λ b => b⟩

instance : LawfulBundleLike (Bundle F V) :=
  ⟨λ _ _ h => h⟩

/-- The Pi subsumption order agrees with the interface-level
`BundleLike.Subsumes`. -/
theorem le_iff_subsumes {b₁ b₂ : Bundle F V} :
    b₁ ≤ b₂ ↔ BundleLike.Subsumes b₁ b₂ :=
  Iff.rfl

instance [Fintype F] [∀ t, DecidableEq (V t)] (b₁ b₂ : Bundle F V) :
    Decidable (b₁ ≤ b₂) :=
  inferInstanceAs (Decidable (∀ t, b₁ t ≤ b₂ t))

@[simp]
theorem val_bot (t : F) :
    BundleLike.val (⊥ : Bundle F V) t = (none : Flat (V t)) :=
  rfl

/-- The bundle specifying exactly one feature. -/
def single [DecidableEq F] (t : F) (v : V t) : Bundle F V :=
  Function.update (⊥ : Bundle F V) t (some v)

@[simp]
theorem val_single_self [DecidableEq F] (t : F) (v : V t) :
    BundleLike.val (single t v) t = (some v : Flat (V t)) := by
  simp [single, BundleLike.val]

@[simp]
theorem val_single_of_ne [DecidableEq F] {s t : F} (h : s ≠ t) (v : V t) :
    BundleLike.val (single t v) s = (none : Flat (V s)) := by
  simp only [single, BundleLike.val, Function.update_of_ne h]
  rfl

@[simp]
theorem not_specifies_bot (t : F) : ¬ BundleLike.Specifies (⊥ : Bundle F V) t :=
  λ hv => hv rfl

@[simp]
theorem specifies_single [DecidableEq F] {s t : F} (v : V t) :
    BundleLike.Specifies (single t v) s ↔ s = t := by
  constructor
  · intro h
    by_contra hne
    exact h (val_single_of_ne hne v)
  · rintro rfl
    intro h
    exact Option.some_ne_none v (val_single_self s v ▸ h)

/-! ### Mutation algebra

`Function.update`/`orElse`-based operations for building and combining
bundles, dual to the order/lattice stack above. General over any
`Bundle F V`; the phonological `Segment` and tonal `TRN` specialize them
at `V := fun _ => Bool`. -/

/-- **Override merge**: take `b₁`'s value where specified, else `b₂`'s. -/
def merge (b₁ b₂ : Bundle F V) : Bundle F V :=
  fun t => match b₁ t with
    | some v => some v
    | none => b₂ t

@[simp] theorem merge_self (b : Bundle F V) : merge b b = b := by
  funext t; simp only [merge]; cases b t <;> rfl

/-- **Override**: set feature `t` to `some v`, regardless of current value. -/
def set [DecidableEq F] (t : F) (v : V t) (b : Bundle F V) : Bundle F V :=
  Function.update b t (some v)

/-- **Deletion**: return feature `t` to underspecified (`none`). -/
def delete [DecidableEq F] (t : F) (b : Bundle F V) : Bundle F V :=
  Function.update b t none

/-- **Single-feature assimilation**: `tgt` adopts `src`'s value at `t`,
leaving every other feature untouched. -/
def assimilate [DecidableEq F] (t : F) (src tgt : Bundle F V) : Bundle F V :=
  Function.update tgt t (src t)

end Bundle

end Features

namespace BundleLike

variable {B F : Type*} {S : F → Type*} [BundleLike B F S]

/-- Any bundle representation with a finite signature carries the
subsumption order pulled back along its valuation into the Pi
`(t : F) → S t`, packaged as a `Core.Order.PullbackPreorder`.
Coarsenings between representations factor through
`Core.Order.PullbackPreorder.coarsen_via_monotone`. A `def`, not an
instance, matching `PullbackPreorder`'s own convention. -/
def subsumptionPreorder [Fintype F] [∀ t, PartialOrder (S t)]
    [∀ t, DecidableLE (S t)] :
    Core.Order.PullbackPreorder B ((t : F) → S t) :=
  .ofProj (λ b => (val (S := S) b : (t : F) → S t)) fun a a' =>
    inferInstanceAs (Decidable (∀ t, val a t ≤ val a' t))

end BundleLike
