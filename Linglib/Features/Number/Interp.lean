import Linglib.Features.Number.Basic
import Linglib.Semantics.Mereology

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
* `Number.interp`: the region a number value denotes over `P`.

## Main results

* `Number.additive_subregion_is_cum`: the additive elements of a region form
  a cumulative predicate.
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

namespace Number

open Mereology (Atom CUM Null atomize null)

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

variable [Null D]

/-- The atoms of `P`: Harbour's `[+atomic]`, the singular region. -/
abbrev atomsOf (P : D → Prop) (x : D) : Prop := P x ∧ Atom x

/-- The non-atoms of `P`: Harbour's `[−atomic]`. -/
abbrev nonAtomsOf (P : D → Prop) (x : D) : Prop := P x ∧ ¬ Atom x

/-- The minimal non-atoms of `P`: `[−atomic, +minimal]`, the dual region. -/
abbrev dualOf (P : D → Prop) : D → Prop := atomize (nonAtomsOf P)

/-- The non-minimal non-atoms of `P`: `[−atomic, −minimal]`, the plural region. -/
abbrev pluralOf (P : D → Prop) (x : D) : Prop := nonAtomsOf P x ∧ ¬ dualOf P x

/-- An atom of a region excluding the null individual is minimal in it:
`[+atomic]` entails `[+minimal]`. -/
theorem singular_subset_minimal {P : D → Prop} (hP : ∀ y, P y → ¬ null y) {x : D}
    (hx : atomsOf P x) : atomize P x :=
  ⟨hx.1, fun _ hy hle => hx.2.2 (hP _ hy) hle⟩

/-- Over a region of atoms, minimality selects everything, which is why
`[±atomic]` cannot undergo feature recursion. -/
theorem atomize_eq_of_atoms {P : D → Prop} (hAll : ∀ x, P x → Atom x) : atomize P = P :=
  funext fun x => propext ⟨fun h => h.1, fun hPx =>
    singular_subset_minimal (fun y hy => (hAll y hy).not_null) ⟨hPx, hAll x hPx⟩⟩

/-- The region a number value denotes over `P`; the approximative values
return `none`. -/
def interp (P : D → Prop) : Number → Option (D → Prop)
  | .general => some P
  | .singular => some (atomsOf P)
  | .dual => some (dualOf P)
  | .plural => some (pluralOf P)
  | .trial => some (atomize (pluralOf P))
  | .minimal => some (atomize P)
  | .augmented => some fun x => P x ∧ ¬ atomize P x
  | .unitAugmented => some (atomize fun x => P x ∧ ¬ atomize P x)
  | _ => none

theorem interp_isSome_iff (P : D → Prop) (n : Number) :
    (interp P n).isSome ↔
      n ∉ ([.paucal, .greaterPaucal, .greaterPlural, .globalPlural] : List Number) := by
  cases n <;> simp [interp]

end Number
