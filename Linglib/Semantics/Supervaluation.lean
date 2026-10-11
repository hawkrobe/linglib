module

public import Linglib.Logic.Trivalent.Flat

/-!
# Supervaluation over specification spaces

Fine's super-truth theory of vagueness takes a vague sentence to be true when it is true on every
admissible way of making the language precise, false when it is false on every one, and indefinite
otherwise. A specification space is a nonempty set of admissible complete specifications
(`SpecSpace`), ordered by extension: `S ≤ T` when `T` admits only specifications that `S` admits,
so that going up the order makes the language more precise. Super-truth is van Fraassen's
supervaluation `Trivalent.supervaluation` over the admissible set. The space contributes the
nonemptiness that keeps truth and falsity apart (`SpecSpace.supervaluation_eq_false_iff`) and
makes negation classical (`SpecSpace.supervaluation_not`).

## Main results

* `SpecSpace.toFlat_supervaluation_mono`: Stability, super-truth is monotone from the extension
  order into the knowledge order of `Trivalent`, so extension preserves definite values and can
  only resolve the indefinite.

## Implementation notes

Specification spaces are `Finset`-based so that studies close their examples by `decide`; the
order is the reverse inclusion of the admissible sets, as mathlib orders `Filter`. Fine's partial
specification points, his `D` operator and the logic of the theory are the paper's own and live in
`Studies/Fine1975`.

## References

* [fine-1975]
* [van-fraassen-1966]
-/

@[expose] public section

namespace Semantics.Supervaluation

open Trivalent

variable {Spec : Type*}

/-- A specification space in the reduced sense is a nonempty finite set of admissible complete
specifications, each one way of making every vague predicate precise at once. -/
@[ext]
structure SpecSpace (Spec : Type*) where
  /-- The admissible complete specifications. -/
  admissible : Finset Spec
  nonempty : admissible.Nonempty

namespace SpecSpace

attribute [coe] admissible

instance : CoeOut (SpecSpace Spec) (Finset Spec) := ⟨admissible⟩

/-- Extension orders the spaces, with `S ≤ T` when every specification `T` admits is admitted by
`S`, so that `T` is the more precise space. -/
instance : PartialOrder (SpecSpace Spec) where
  le S T := T.admissible ⊆ S.admissible
  le_refl _ := subset_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁
  le_antisymm _ _ h₁ h₂ := SpecSpace.ext (h₂.antisymm h₁)

theorem le_def {S T : SpecSpace Spec} : S ≤ T ↔ T.admissible ⊆ S.admissible := Iff.rfl

/-- A single admissible specification, a classical model as a degenerate space. -/
def singleton (s : Spec) : SpecSpace Spec := ⟨{s}, Finset.singleton_nonempty s⟩

@[simp] theorem admissible_singleton (s : Spec) : (singleton s).admissible = {s} := rfl

variable (eval : Spec → Prop) [DecidablePred eval] (S : SpecSpace Spec)

/-- Over a specification space, super-falsity is falsity at every admissible specification. -/
theorem supervaluation_eq_false_iff :
    supervaluation S eval = .false ↔ ∀ s ∈ S.admissible, ¬ eval s :=
  (Trivalent.supervaluation_eq_false_iff ..).trans (and_iff_right S.nonempty)

/-- Negation is classical, super-falsity of `eval` being super-truth of its negation. -/
theorem supervaluation_not :
    supervaluation S (fun s ↦ ¬ eval s) = (supervaluation S eval).neg :=
  Trivalent.supervaluation_not _ S.nonempty

/-- Super-truth is monotone from the extension order into the knowledge order (Stability). -/
theorem toFlat_supervaluation_mono :
    Monotone fun S : SpecSpace Spec ↦ toFlat (supervaluation S eval) :=
  fun _ T hST ↦ Trivalent.toFlat_supervaluation_mono eval hST T.nonempty

end SpecSpace

end Semantics.Supervaluation
