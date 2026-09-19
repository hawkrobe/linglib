import Mathlib.Data.Fintype.Basic
import Linglib.Core.Order.Flat

/-!
# Feature bundles

This file defines an interface for feature bundles that is polymorphic in their
representation, and the canonical extensional representation `Bundle`.

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
indeterminate values in the sense of Dalrymple and Kaplan; or (c)
some richer order for layered or hierarchical features. The lattice
theory is proved once at the Pi level and inherited by every choice of
`S`.

## Main declarations

* `BundleLike` — the valuation interface
* `LawfulBundleLike` — extensional representations; gives
  `BundleLike.ext` and `BundleLike.partialOrder`
* `BundleLike.Specifies`, `BundleLike.Subsumes` — the derived API;
  `Subsumes` is the subsumption order of the unification-grammar
  tradition, as in Shieber
* `Bundle F V` — the canonical extensional representation, a partial
  assignment `(t : F) → Option (V t)`, carrying the subsumption
  `PartialOrder` with `⊥` the everywhere-underspecified bundle
* `Bundle.single`, `Bundle.ofList` — the bundle specifying one feature,
  and the bundle read off an association list; `single_le_iff` and
  `ofList_le_iff` characterize lying below a bundle by the values it
  carries

## Implementation notes

`Bundle` is an `abbrev` over the Pi type of `Flat` slots
(`Core/Order/Flat.lean`): the reducibility barrier sits at `Flat`, so
the subsumption order does not leak onto bare `Option`-valued Pi types,
while mathlib's Pi instances supply the whole order stack — the
subsumption `PartialOrder`, `OrderBot` (`⊥` = everywhere
underspecified), `SemilatticeInf` (generalization/anti-unification),
and the partial join `PartialUnify` (unification). This is the bounded
complete partial order of the unification tradition after Carpenter, a finite
meet semilattice presented through its joins. `Bundle` is
unrelated to mathlib's fiber-bundle `Bundle` namespace; qualify when
both are in scope.

Instances live with their representations, not here: this file imports only
`Core` and mathlib, and e.g. `Morphology.UD.MorphFeatures` instantiates
`BundleLike` in its own file.

The phonological representation uses `Bundle` directly: `Phonology.Segment`'s `spec`
field is `Bundle Feature (fun _ ↦ Bool)` (in unfolded `Feature →
Option Bool` form), with the shared `merge`/`set`/`delete` algebra below.

## Todo

* Instantiate `BundleLike` at the Minimalist `FeatureBundle`
  (lawful only after the planned list-to-assignment retype).
* Per-slot generality: `Bundle` fixes the flat slot order. UD-practice
  pressure (multivalued features as `Finset`-superset slots, layered
  features as a nested index) is accommodated by working with
  `(t : F) → S t` for other slot orders `S`; the `PartialUnify` Pi
  instance is already stated at that generality.
* A hierarchical assembly-tree representation with the flattening valuation, which is
  `BundleLike` but not `LawfulBundleLike`.

## References

* [S. M. Shieber, *An Introduction to Unification-Based Approaches to Grammar*
  (1986)][shieber-1986]
* [B. Carpenter, *The Logic of Typed Feature Structures: With Applications to Unification
  Grammars, Logic Programs and Constraint Resolution* (1992)][carpenter-1992]
* [M. Dalrymple and R. M. Kaplan, *Feature Indeterminacy and Feature Resolution*
  (2000)][dalrymple-kaplan-2000]
-/

universe u v

/-- `BundleLike B F S` says that `B` presents feature bundles over the feature space `F`, with slot
`t` taking values in the order space `S t`. The single primitive is the valuation, a function
reading off the slot value at each feature. The slot type `S t` carries its own order. The canonical
flat-atomic slot is `Flat (V t)` for an atom enumeration `V t`, and richer slot orders, such as
`Finset α` for indeterminacy or nested attribute spaces for layered features, are obtained by
choosing a different `S`. -/
class BundleLike (B : Type*) (F : outParam Type*) (S : outParam (F → Type*)) where
  /-- The value the bundle assigns to feature `t`. -/
  val : B → (t : F) → S t

/-- A bundle representation is extensional when bundles with the same valuation are equal.
Structured representations whose internal organization outruns their valuation are deliberately not
lawful. -/
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

/-- Subsumption is pointwise ≤ on slots, so that `b₂` is at least as specified as `b₁`. For flat
slots this is `≤` on `Flat`, and for set-valued slots it is the indeterminacy order, where a
superset is less determinate. -/
def Subsumes (b₁ b₂ : B) : Prop :=
  ∀ t, val (S := S) b₁ t ≤ val b₂ t

theorem subsumes_refl (b : B) : Subsumes (S := S) b b :=
  fun _ ↦ le_rfl

theorem subsumes_trans {b₁ b₂ b₃ : B}
    (h₁₂ : Subsumes (S := S) b₁ b₂) (h₂₃ : Subsumes b₂ b₃) :
    Subsumes (S := S) b₁ b₃ :=
  fun t ↦ le_trans (h₁₂ t) (h₂₃ t)

/-- On a lawful representation with partial slot orders, subsumption is
antisymmetric. -/
theorem subsumes_antisymm [LawfulBundleLike B] {b₁ b₂ : B}
    (h₁ : Subsumes (S := S) b₁ b₂) (h₂ : Subsumes b₂ b₁) : b₁ = b₂ :=
  ext fun t ↦ le_antisymm (h₁ t) (h₂ t)

instance [Fintype F] [∀ t, DecidableLE (S t)] (b₁ b₂ : B) :
    Decidable (Subsumes (S := S) b₁ b₂) :=
  inferInstanceAs (Decidable (∀ t, val b₁ t ≤ val b₂ t))

/-- The subsumption partial order on a lawful representation. It is not an instance, since a
representation may carry its own canonical order. -/
@[reducible]
def partialOrder [LawfulBundleLike B] : PartialOrder B where
  le := Subsumes
  le_refl := subsumes_refl
  le_trans _ _ _ := subsumes_trans
  le_antisymm _ _ := subsumes_antisymm

end Order

end BundleLike


/-- The canonical extensional feature bundle is a partial assignment of values to features, as a Pi
type of `Flat` slots. Underspecification is `none`, and at most one value per feature holds by
construction. The order structure (the subsumption `PartialOrder`, `OrderBot`, `SemilatticeInf` and
`PartialUnify`) is inherited from the slots through mathlib's Pi instances, the reducibility barrier
living at `Flat` as the module docstring explains. -/
abbrev Bundle (F : Type u) (V : F → Type v) : Type max u v :=
  (t : F) → Flat (V t)

namespace Bundle

variable {F : Type u} {V : F → Type v}

instance : BundleLike (Bundle F V) F (fun t ↦ Flat (V t)) :=
  ⟨fun b ↦ b⟩

instance : LawfulBundleLike (Bundle F V) :=
  ⟨fun _ _ h ↦ h⟩

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
  fun hv ↦ hv rfl

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
at `V := fun _ ↦ Bool`. -/

/-- Override merge takes the value of `b₁` where it is specified, and otherwise that of `b₂`. -/
def merge (b₁ b₂ : Bundle F V) : Bundle F V :=
  fun t ↦ match b₁ t with
    | some v => some v
    | none => b₂ t

@[simp] theorem merge_self (b : Bundle F V) : merge b b = b := by
  funext t; simp only [merge]; cases b t <;> rfl

/-- Override sets the feature `t` to `some v`, whatever its current value. -/
def set [DecidableEq F] (t : F) (v : V t) (b : Bundle F V) : Bundle F V :=
  Function.update b t (some v)

/-- Deletion returns the feature `t` to underspecified (`none`). -/
def delete [DecidableEq F] (t : F) (b : Bundle F V) : Bundle F V :=
  Function.update b t none

/-- In single-feature assimilation `tgt` adopts the value of `src` at `t`, and every other feature
is left untouched. -/
def assimilate [DecidableEq F] (t : F) (src tgt : Bundle F V) : Bundle F V :=
  Function.update tgt t (src t)

/-! ### Association lists and the single-feature bundles -/

section OfList

variable [DecidableEq F] {β : Type*}

/-- The bundle over a constant slot family read off an association list gives a feature its first
entry as value, and leaves an unlisted feature unspecified. -/
def ofList (l : List (F × β)) : Bundle F fun _ ↦ β := fun t ↦ l.lookup t

@[simp] theorem ofList_apply (l : List (F × β)) (t : F) : ofList l t = l.lookup t := rfl

/-- A single-feature bundle lies below a bundle exactly when that bundle carries the value. -/
theorem single_le_iff {t : F} {v : V t} {b : Bundle F V} : single t v ≤ b ↔ b t = ↑v := by
  refine ⟨fun h ↦ ?_, fun h u ↦ ?_⟩
  · have := h t
    rw [single, Function.update_self] at this
    exact Flat.coe_le_iff.1 this
  · by_cases hu : u = t
    · subst hu
      rw [single, Function.update_self]
      exact Flat.coe_le_iff.2 h
    · rw [single, Function.update_of_ne hu]
      exact bot_le

/-- An association list lies below a bundle exactly when the bundle carries every value the
list looks up. -/
theorem ofList_le_iff {l : List (F × β)} {b : Bundle F fun _ ↦ β} :
    ofList l ≤ b ↔ ∀ t v, l.lookup t = some v → b t = ↑v := by
  refine ⟨fun h t v hv ↦ ?_, fun h t ↦ ?_⟩
  · have := h t
    rw [ofList_apply, hv] at this
    exact Flat.coe_le_iff.1 this
  · rw [ofList_apply]
    cases hf : l.lookup t with
    | none => exact bot_le
    | some v => exact Flat.coe_le_iff.2 (h t v hf)

/-- With distinct features, an association list lies below a bundle exactly when the bundle
carries each listed value. -/
theorem ofList_le_iff_forall_mem {l : List (F × β)} (h : (l.map Prod.fst).Nodup)
    {b : Bundle F fun _ ↦ β} : ofList l ≤ b ↔ ∀ p ∈ l, b p.1 = ↑p.2 := by
  rw [ofList_le_iff]
  refine ⟨fun H p hp ↦ H p.1 p.2 ?_, fun H t v hv ↦ ?_⟩
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
    refine List.lookup_eq_some_iff.2 ⟨l₁, l₂, rfl, fun q hq ↦ bne_iff_ne.2 fun hpq ↦ ?_⟩
    rw [List.map_append, List.map_cons] at h
    exact (List.nodup_append'.1 h).2.2 (List.mem_map.2 ⟨q, hq, rfl⟩)
      (by rw [← hpq]; exact List.mem_cons_self)
  · obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hv
    exact H (t, v) (List.mem_append_right _ List.mem_cons_self)

end OfList

end Bundle

