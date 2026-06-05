import Linglib.Core.Order.PartialUnify

/-!
# The flat information order on an atomic slot

`Flat α` is `Option α` carrying the flat information order: `none` (no
information) below everything, distinct values incomparable. An
order-carrying alias in the `WithBot` mold — the slot type out of which
partial feature assignments are built, and the atomic case of
[shieber-1986]'s subsumption order (a committed atomic value neither
subsumes nor is subsumed by a different one).

The slot is a bounded complete partial order in miniature: meets are
total (`SemilatticeInf` — agreement or nothing), joins are partial
(`PartialUnify` — `none` is identity, equal commitments merge, distinct
commitments clash).

## Main declarations

* `Option.FlatLE` — the flat order as a relation on `Option α`
* `Flat` — the order-carrying alias, with `PartialOrder`, `OrderBot`,
  `SemilatticeInf`, and `PartialUnify` instances
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

theorem bot_eq_none : (⊥ : Flat α) = (none : Option α) := rfl

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
    simp

/-- Unify two slots: `none` is identity, equal commitments merge,
distinct commitments clash. -/
protected def unify [DecidableEq α] (a b : Flat α) : Option (Flat α) :=
  match (a : Option α), (b : Option α) with
  | none, b => some b
  | some x, none => some (some x)
  | some x, some y => if x = y then some (some x) else none

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
      rw [show Flat.unify (some x : Option α) (some y : Option α) =
          if x = y then some (some x) else none from rfl] at h
      split at h
      · next hxy =>
        subst hxy
        obtain rfl : (some x : Flat α) = c := Option.some.inj h
        rw [Set.pair_eq_singleton]
        exact isLUB_singleton
      · exact absurd h (by simp)
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
      rw [show Flat.unify (some x : Option α) (some y : Option α) =
          if x = y then some (some x) else none from rfl, if_pos hxy]
      rfl

/-! ### The flat lattice is non-distributive

A flat slot with three distinct atoms, lifted with a top, is the
diamond M₃ — modular but *not* distributive ([carpenter-1992] p. 15,
eq. (4): "our partial orders are *not* required to be distributive
(and in fact, are not even required to be modular)").

`Flat` itself has only the partial join (`PartialUnify`), so the
distributive law cannot even be *stated* on `Flat` directly. The
witness here is the meet-side identity that holds in *any* distributive
lattice and *fails* on our slot: for three distinct atoms,
`(a ⊓ b) ⊔ (a ⊓ c) = ⊥` but `a ⊓ (b ⊔ c)` is undefined (no upper bound
for `{b, c}`). The `PartialUnify` failure (`unify_eq_none_iff`) is the
constructive witness. -/

theorem unify_distinct_eq_none [DecidableEq α] {a b : α} (h : a ≠ b) :
    Flat.unify (some a : Flat α) (some b) = none := by
  show (if a = b then some (some a : Flat α) else none) = none
  exact if_neg h

end Flat
