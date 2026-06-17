import Mathlib.Order.OmegaCompletePartialOrder
import Linglib.Core.Order.PartialUnify

/-!
# The flat domain

`Flat α` is `Option α` carrying the *flat* order: `⊥` (`none`, no information)
below everything, distinct values incomparable. An order-carrying alias in the
`WithBot` mold, but the underlying order is *discrete*, not lifted — committed
values are an antichain.

This is the **free (Scott) domain on a set**: the lift of the discrete order,
`Flat = lift ∘ discrete`, equivalently `1 + α` as an object. Two facts make it
the canonical small domain rather than an ad-hoc gadget:

* it is **bounded-complete but not a lattice** — meets are total
  (`SemilatticeInf`, agreement or `⊥`) while joins are *partial*
  (`PartialUnify`: `⊥` is identity, equal commitments merge, distinct
  commitments have no upper bound). Bounded-completeness *is* the join being
  partial-yet-unique-when-defined;
* it is **ω-complete** (`OmegaCompletePartialOrder`) — chains are eventually
  constant, so they have suprema. `Flat` is the generator of domain theory and
  the order side of the lifting/partiality monad (`Option`), whose Kleisli
  arrows `α → Flat β` are partial functions — `PartialUnify.unify` among them.

Linguistically it is one atomic feature slot: the order is [shieber-1986]'s and
[carpenter-1992]'s subsumption order (an *information* order — `⊥` = unmarked,
a wildcard for agreement), and `Flat Bool` is the knowledge order of Kleene
three-valued logic. Feature bundles are built from it by the `Pi` `PartialUnify`
instance; `Compat` is consistency.

The order skeleton (`Option.FlatLE`, `Flat`, the `PartialOrder`/`OrderBot`/
`SemilatticeInf`/`OmegaCompletePartialOrder` instances) is an `[UPSTREAM]`
candidate for `Mathlib/Order/Flat.lean` — root-level `Flat` as with `WithBot`,
coexisting with the existing namespaced `Module.Flat` and `ConvexCone.Flat`
(write `_root_.Flat` under `open Module`). The `PartialUnify` instance and
`compat_iff` stay here: `PartialUnify` is linglib's, not mathlib's.

## Main declarations

* `Option.FlatLE` — the flat order as a relation on `Option α`
* `Flat` — the order-carrying alias, with `PartialOrder`, `OrderBot`,
  `SemilatticeInf`, `OmegaCompletePartialOrder`, and `PartialUnify` instances
* `Flat.coe_le_coe`, `Flat.not_coe_le_bot` — the order, characterized
* `Flat.ωSup` — the supremum of a chain (the eventual value, or `⊥`)
* `Flat.compat_iff` — slot compatibility (`Compat`), characterized
* `Flat.unify_distinct_eq_none` — distinct atoms do not unify (the
  non-distributivity witness)

## TODO

The order skeleton is here; the domain-theoretic content that makes it the
*free domain* rather than an ad-hoc poset is not yet formalized:

* **Universal property.** `Flat` is the free pointed ω-CPO on a set: strict
  continuous maps `Flat α →𝒄 D` into a pointed domain `D` correspond to bare
  functions `α → D`. State the free–forgetful adjunction `Flat ⊣ U`.
* **Lifting monad.** Give `Flat` (= `Option`) its ω-CPO monad structure — the
  partiality/lifting monad — whose Kleisli arrows `α → Flat β` are partial
  continuous functions; `PartialUnify.unify` is one such arrow, which is why it
  composes through `Option.bind` (`unify_assoc`).
* **Scott continuity.** Every monotone map out of `Flat α` is continuous
  (chains are eventually constant), so a map `Flat α →𝒄 D` is fixed by its
  values on atoms. Record the `ωScottContinuous` lemmas.
* **Algebraicity / bounded-completeness.** Every element of `Flat α` is compact,
  making it an algebraic (finite-height) bounded-complete domain — the
  Scott-domain packaging of the partial join `PartialUnify` provides.
* **Three-valued logic.** `Flat Bool` is the knowledge order of Kleene
  three-valued logic; the strong-Kleene connectives are exactly its continuous
  maps. Connects this substrate to the trivalence/presupposition layer.

Ergonomics, separately: add a coercion `↑ : α → Flat α` (as `WithBot.some`) so
`coe_le_coe`/`not_coe_le_bot` need no explicit `@LE.le`, and move the order
relation out of the `Option` namespace (`Option.FlatLE → Flat.LE`).
-/

/-- The flat information order on an atomic feature slot: every
committed value persists upward, so `none` is below everything and
distinct atoms are incomparable. -/
def Option.FlatLE {α : Type*} (a b : Option α) : Prop :=
  ∀ x : α, a = some x → b = some x

namespace Option.FlatLE

variable {α : Type*} {a b c : Option α}

protected theorem refl (a : Option α) : a.FlatLE a := λ _ h => h

protected theorem trans (h1 : a.FlatLE b) (h2 : b.FlatLE c) : a.FlatLE c :=
  λ x hx => h2 x (h1 x hx)

protected theorem antisymm (h1 : a.FlatLE b) (h2 : b.FlatLE a) : a = b := by
  cases a with
  | some x => exact (h1 x rfl).symm
  | none =>
    cases b with
    | none => rfl
    | some y => exact absurd (h2 y rfl) (by simp)

theorem none_le (b : Option α) : Option.FlatLE none b := λ _ h => nomatch h

instance [DecidableEq α] : Decidable (a.FlatLE b) :=
  match a, b with
  | none, _ => .isTrue (λ _ h => nomatch h)
  | some x, some y =>
    if h : x = y then .isTrue (λ _ hx => by simpa [h] using hx)
    else .isFalse (λ hle => h (Option.some.inj (hle x rfl)).symm)
  | some x, none => .isFalse (λ hle => nomatch hle x rfl)

end Option.FlatLE

/-- An atomic feature slot: `Option α` carrying the flat information
order as its `≤`. A `def`, not an `abbrev`, so the order instances do
not leak onto bare `Option`. -/
def Flat (α : Type*) := Option α

namespace Flat

variable {α : Type*}

instance [DecidableEq α] : DecidableEq (Flat α) :=
  inferInstanceAs (DecidableEq (Option α))

instance [Repr α] : Repr (Flat α) :=
  inferInstanceAs (Repr (Option α))

instance : Inhabited (Flat α) :=
  ⟨(none : Option α)⟩

instance : PartialOrder (Flat α) where
  le a b := Option.FlatLE a b
  le_refl := Option.FlatLE.refl
  le_trans _ _ _ := Option.FlatLE.trans
  le_antisymm _ _ := Option.FlatLE.antisymm

instance : OrderBot (Flat α) where
  bot := (none : Option α)
  bot_le := Option.FlatLE.none_le

instance [DecidableEq α] (a b : Flat α) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (Option.FlatLE a b))

theorem le_def {a b : Flat α} : a ≤ b ↔ Option.FlatLE a b := Iff.rfl

theorem none_eq_bot : (none : Flat α) = (⊥ : Flat α) := rfl

@[simp] theorem coe_le_coe {a b : α} :
    @LE.le (Flat α) _ (some a) (some b) ↔ a = b := by
  rw [le_def]
  refine ⟨λ h => (Option.some.inj (h a rfl)).symm, ?_⟩
  rintro rfl x hx
  exact hx

@[simp] theorem not_coe_le_bot (a : α) : ¬ @LE.le (Flat α) _ (some a) ⊥ := by
  rw [le_def]
  exact λ h => (Option.some_ne_none a).symm (h a rfl)

/-- The meet of two slots: their agreement, or nothing. -/
protected def inf [DecidableEq α] (a b : Flat α) : Flat α :=
  if (a : Option α) = (b : Option α) then a else (none : Option α)

instance [DecidableEq α] : SemilatticeInf (Flat α) where
  inf := Flat.inf
  inf_le_left a b := by
    unfold Flat.inf
    split
    · exact Option.FlatLE.refl a
    · exact Option.FlatLE.none_le a
  inf_le_right a b := by
    unfold Flat.inf
    split
    · next h => exact h ▸ Option.FlatLE.refl a
    · exact Option.FlatLE.none_le b
  le_inf c a b hca hcb := by
    intro x hx
    have ha := hca x hx
    have hb := hcb x hx
    unfold Flat.inf
    rw [ha, hb]
    exact if_pos rfl

/-! ### The flat domain is ω-complete

A monotone chain in the flat order is eventually constant — `⊥` until it
(optionally) commits to a single value, then constant — so it has a
supremum. This is the *flat domain*, the canonical nontrivial example of an
`OmegaCompletePartialOrder`. -/

section OmegaCPO
open OmegaCompletePartialOrder (Chain)

open Classical in
/-- The supremum of a chain in the flat order: the committed value if the
chain ever leaves `⊥`, and `⊥` otherwise. -/
noncomputable def ωSup (c : Chain (Flat α)) : Flat α :=
  if h : ∃ i, (c i).isSome then c (Nat.find h) else none

private theorem ωSup_isLUB (c : Chain (Flat α)) :
    IsLUB (Set.range c) (ωSup c) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    unfold ωSup
    split
    · next h =>
      intro a ha
      have hj : (c j).isSome := by rw [ha]; rfl
      have hmono : c (Nat.find h) ≤ c j := (OrderHomClass.mono c) (Nat.find_min' h hj)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Nat.find_spec h)
      have hjb : c j = some b := hmono b hb
      rw [hb, Option.some.inj (ha.symm.trans hjb)]
    · next h =>
      intro a ha
      exact absurd ⟨j, by rw [ha]; rfl⟩ h
  · intro u hu
    unfold ωSup
    split
    · next h => exact hu (Set.mem_range_self (Nat.find h))
    · exact Option.FlatLE.none_le u

/-- The flat domain is an `OmegaCompletePartialOrder`: chains are eventually
constant, so their suprema are the eventual value (or `⊥`). -/
noncomputable instance : OmegaCompletePartialOrder (Flat α) where
  ωSup := ωSup
  le_ωSup c i := (ωSup_isLUB c).1 (Set.mem_range_self i)
  ωSup_le c x hub := (ωSup_isLUB c).2 (by rintro _ ⟨i, rfl⟩; exact hub i)

end OmegaCPO

/-- Unify two slots: `none` is identity, equal commitments merge,
distinct commitments clash. -/
protected def unify [DecidableEq α] (a b : Flat α) : Option (Flat α) :=
  match (a : Option α), (b : Option α) with
  | none, b => some b
  | some x, none => some (some x)
  | some x, some y => if x = y then some (some x) else none

private theorem unify_some_some [DecidableEq α] (x y : α) :
    Flat.unify (some x : Flat α) (some y) = if x = y then some (some x) else none :=
  rfl

instance [DecidableEq α] : PartialUnify (Flat α) where
  unify := Flat.unify
  isLUB_of_unify_eq_some := by
    intro a b c h
    match a, b with
    | none, b =>
      obtain rfl : b = c := Option.some.inj h
      exact ⟨PartialUnify.mem_upperBounds_pair.mpr
          ⟨Option.FlatLE.none_le _, le_rfl⟩,
        λ u hu => (PartialUnify.mem_upperBounds_pair.mp hu).2⟩
    | some x, none =>
      obtain rfl : (some x : Flat α) = c := Option.some.inj h
      exact ⟨PartialUnify.mem_upperBounds_pair.mpr
          ⟨le_rfl, Option.FlatLE.none_le _⟩,
        λ u hu => (PartialUnify.mem_upperBounds_pair.mp hu).1⟩
    | some x, some y =>
      rw [unify_some_some] at h
      split at h
      · next hxy =>
        subst hxy
        obtain rfl : (some x : Flat α) = c := Option.some.inj h
        rw [Set.pair_eq_singleton]
        exact isLUB_singleton
      · exact absurd h.symm (Option.some_ne_none c)
  isSome_unify_of_bddAbove := by
    intro a b hbdd
    obtain ⟨u, hu⟩ := hbdd
    obtain ⟨hau, hbu⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    match a, b with
    | none, b => exact rfl
    | some x, none => exact rfl
    | some x, some y =>
      have hx : (u : Option α) = some x := hau x rfl
      have hy : (u : Option α) = some y := hbu y rfl
      have hxy : x = y := Option.some.inj (hx.symm.trans hy)
      show (Flat.unify (some x : Option α) (some y : Option α)).isSome
      rw [unify_some_some, if_pos hxy]
      rfl

/-- Slot compatibility, characterized: committed values must coincide;
    an uncommitted slot is a wildcard. -/
theorem compat_iff [DecidableEq α] {a b : Flat α} :
    Compat a b ↔ ∀ x : α, a = some x → ∀ y : α, b = some y → x = y := by
  rw [compat_iff_isSome_unify]
  show (Flat.unify a b).isSome = true ↔ _
  match a, b with
  | none, b =>
    exact iff_of_true rfl (λ x hx => nomatch hx)
  | some x, none =>
    exact iff_of_true rfl (λ x' _ y hy => nomatch hy)
  | some x, some y =>
    rw [unify_some_some]
    by_cases hxy : x = y
    · subst hxy
      exact iff_of_true (by rw [if_pos rfl]; rfl)
        (λ x' hx' y' hy' =>
          (Option.some.inj hx').symm.trans (Option.some.inj hy'))
    · rw [if_neg hxy]
      exact iff_of_false nofun (λ h => hxy (h x rfl y rfl))

/-! ### Non-distributivity

The flat order is not distributive: three distinct atoms (with a top
adjoined) form the diamond M₃ — [carpenter-1992] takes subsumption orders
to be neither distributive nor modular in general. `Flat` carries only the
partial join (`PartialUnify`), so the distributive law cannot even be
*stated* on it directly; `unify_distinct_eq_none` is the witness — distinct
atoms have no upper bound, so the join the law would require is undefined. -/

theorem unify_distinct_eq_none [DecidableEq α] {a b : α} (h : a ≠ b) :
    Flat.unify (some a : Flat α) (some b) = none := by
  show (if a = b then some (some a : Flat α) else none) = none
  exact if_neg h

end Flat
