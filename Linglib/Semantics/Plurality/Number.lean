module

public import Linglib.Syntax.Number.Basic
public import Linglib.Semantics.Mereology

/-!
# Number values as lattice regions

This file interprets the number values of `Number` over a join-semilattice of
individuals, following Harbour's decomposition of number into the binary
features atomicity, minimality and additivity: `Number.interp P n` is the
region of `P` picked out by the value `n`.

## Main definitions

* `Number.additiveIn`: `x` is additive in a region `Q` if `Q` is closed under
  joining with `x`, Harbour's `[+additive]`.
* `Number.atomsOf`, `Number.nonAtomsOf`, `Number.dualOf`, `Number.pluralOf`:
  the singular, non-atomic, dual and plural regions of `P`.
* `Number.nonMinimalOf`: the non-minimal elements of `P`, Harbour's `[−minimal]`.
* `Number.interp`: the region a number value denotes over `P`.

## Main results

* `Number.additive_subregion_is_cum`: the additive elements of a region form
  a cumulative predicate.
* `Number.not_nonMinimalOf_atomize`: `[−minimal]` applied after `[+minimal]` is empty.
* `Number.singular_subset_minimal`, `Number.atomize_eq_of_atoms`: atoms are
  minimal in any region excluding the null individual, so `[+atomic]` entails
  `[+minimal]`.
* `Number.interp_isSome_iff`: `interp` is defined exactly on the
  non-approximative values.

## Implementation notes

Minimality in a region is mathlib's `Minimal`, exposed as `Mereology.atomize`;
atomicity is `Mereology.Atom`. The approximative values (paucal, greater
paucal, greater plural, global plural) are additive relative to a
conventionally fixed cut that the lexicon does not supply, so `interp` returns
`none` for them. Since the carrier is any `SemilatticeSup`, `interp` at an
event lattice interprets verbal number. The inclusive reading of the plural is
pragmatic and not encoded.

## References

* [harbour-2014], (10), (20), (21), §4.2, §4.4
* [link-1983]
* [corbett-2000], ch. 7–8
-/

@[expose] public section

namespace Number

open Mereology (Atom CUM atomize)

variable {D : Type*} [SemilatticeSup D]

/-- `x` is additive in the region `Q` if `Q x` and `Q (x ⊔ y)` for every `y`
with `Q y`: Harbour's `[+additive]`. -/
def additiveIn (Q : D → Prop) (x : D) : Prop :=
  Q x ∧ ∀ y, Q y → Q (x ⊔ y)

theorem additiveIn_sup {Q : D → Prop} {x y : D} (hx : additiveIn Q x) (hy : additiveIn Q y) :
    additiveIn Q (x ⊔ y) := by
  refine ⟨hx.2 y hy.1, fun z hz => ?_⟩
  rw [sup_assoc]
  exact hx.2 (y ⊔ z) (hy.2 z hz)

/-- The additive elements of a region form a cumulative predicate. -/
theorem additive_subregion_is_cum (Q : D → Prop) : CUM (additiveIn Q) :=
  fun _ hx _ hy => additiveIn_sup hx hy

instance {Q : D → Prop} [Fintype D] [DecidablePred Q] (x : D) : Decidable (additiveIn Q x) :=
  decidable_of_iff (Q x ∧ ∀ y, Q y → Q (x ⊔ y)) Iff.rfl


/-- The atoms of `P` form Harbour's `[+atomic]` region, the singular. -/
abbrev atomsOf (P : D → Prop) (x : D) : Prop := P x ∧ Atom x

/-- The non-atoms of `P` form Harbour's `[−atomic]` region. -/
abbrev nonAtomsOf (P : D → Prop) (x : D) : Prop := P x ∧ ¬ Atom x

/-- The non-minimal elements of `P` form Harbour's `[−minimal]` region, the complement in `P` of
`atomize P`. -/
abbrev nonMinimalOf (P : D → Prop) (x : D) : Prop := P x ∧ ¬ atomize P x

/-- The minimal elements of a region of minimal elements are all of them, so
`(−minimal(+minimal(P)))` is empty. -/
theorem not_nonMinimalOf_atomize (P : D → Prop) (x : D) : ¬ nonMinimalOf (atomize P) x :=
  fun h ↦ h.2 ⟨h.1, fun _ hy hyx ↦ h.1.2 hy.1 hyx⟩

/-- The minimal non-atoms of `P` form the `[−atomic, +minimal]` region, the dual. -/
abbrev dualOf (P : D → Prop) : D → Prop := atomize (nonAtomsOf P)

/-- The non-minimal non-atoms of `P` form the `[−atomic, −minimal]` region, the plural. -/
abbrev pluralOf (P : D → Prop) : D → Prop := nonMinimalOf (nonAtomsOf P)

/-- An atom of a region excluding the null individual is minimal in it, so
`[+atomic]` entails `[+minimal]`. -/
theorem singular_subset_minimal {P : D → Prop} (hP : ∀ y, P y → ¬ IsBot y) {x : D}
    (hx : atomsOf P x) : atomize P x :=
  ⟨hx.1, fun _ hy hle => hx.2.2 (hP _ hy) hle⟩

/-- Over a region of atoms, minimality selects everything, which is why
`[±atomic]` cannot undergo feature recursion. -/
theorem atomize_eq_of_atoms {P : D → Prop} (hAll : ∀ x, P x → Atom x) : atomize P = P :=
  funext fun x => propext ⟨fun h => h.1, fun hPx =>
    singular_subset_minimal (fun y hy => (hAll y hy).not_isBot) ⟨hPx, hAll x hPx⟩⟩

/-- `interp P n` is the region of `P` the value `n` denotes, and `none` for the
approximative values. -/
def interp (P : D → Prop) : Number → Option (D → Prop)
  | .general => some P
  | .singular => some (atomsOf P)
  | .dual => some (dualOf P)
  | .plural => some (pluralOf P)
  | .trial => some (atomize (pluralOf P))
  | .minimal => some (atomize P)
  | .augmented => some (nonMinimalOf P)
  | .unitAugmented => some (atomize (nonMinimalOf P))
  | _ => none

theorem interp_isSome_iff (P : D → Prop) (n : Number) :
    (interp P n).isSome ↔
      n ∉ ([.paucal, .greaterPaucal, .greaterPlural, .globalPlural] : List Number) := by
  cases n <;> simp [interp]

end Number
