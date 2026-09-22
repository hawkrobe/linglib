import Linglib.Logic.Duality
import Linglib.Core.Order.Bilattice.Kleene

/-!
# Supervaluation over specification spaces

[fine-1975]'s super-truth theory of vagueness: a vague sentence is true when it is true on
every admissible way of making the language precise, false when false on every one, and
indefinite otherwise. A specification space is a nonempty set of admissible complete
specifications (`SpecSpace`), ordered by extension: `S ≤ T` when `T` admits only
specifications `S` admits, so that going up the order makes the language more precise. Fine's
partial specification points reduce to these sets, each point standing for the set of its
complete extensions, and extension of points becomes inclusion of the sets; the partial-order
form with the reduction map is `Studies/Fine1975`.

Super-truth (`superTrue`) is the trivalent classifier `Trivalent.dist` on the admissible set,
the construction of [van-fraassen-1966]. The specification space contributes the nonemptiness
that keeps truth and falsity apart, so that the three truth values are exactly the cases of
`superTrue_true_iff`, `superTrue_false_iff` and `superTrue_indet_iff`, and negation is
classical (`superTrue_not`). `definitely` is the `Prop` face of super-truth, Fine's `D`
operator, and `indefinite` his `I`.

## Main results

* `superTrue_singleton`: Fidelity, super-truth over a single specification is classical
  truth.
* `definitely_mono`, `toFlat_superTrue_mono`: Stability, super-truth and super-falsity are
  preserved by extension; equivalently, super-truth is monotone from the extension order into
  the knowledge order of `Trivalent`.

## Implementation notes

Specification spaces are `Finset`-based so that studies close their examples by `decide`; the
order is the reverse inclusion of the admissible sets, as mathlib orders `Filter`, with
`SpecSpace.le_def` its unfolding. The logic of the theory, that validity and consequence are
classical, that `D` is an S5 modality, and that the Deduction Theorem fails, is the paper's own
§4 and §5 and lives in `Studies/Fine1975`.

## References

* [fine-1975]
* [van-fraassen-1966]
-/

namespace Semantics.Supervaluation

open Trivalent

variable {Spec : Type*}

/-- A specification space in the reduced sense: a nonempty finite set of admissible complete
specifications, each one way of making every vague predicate precise at once. -/
@[ext]
structure SpecSpace (Spec : Type*) where
  /-- The admissible complete specifications. -/
  admissible : Finset Spec
  nonempty : admissible.Nonempty

namespace SpecSpace

/-- Extension: `S ≤ T` when every specification `T` admits is admitted by `S`, so that `T` is
the more precise space. -/
instance : PartialOrder (SpecSpace Spec) where
  le S T := T.admissible ⊆ S.admissible
  le_refl _ := subset_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁
  le_antisymm _ _ h₁ h₂ := SpecSpace.ext (h₂.antisymm h₁)

theorem le_def {S T : SpecSpace Spec} : S ≤ T ↔ T.admissible ⊆ S.admissible := Iff.rfl

/-- A single admissible specification: a classical model as a degenerate space. -/
def singleton (s : Spec) : SpecSpace Spec := ⟨{s}, Finset.singleton_nonempty s⟩

@[simp] theorem admissible_singleton (s : Spec) : (singleton s).admissible = {s} := rfl

end SpecSpace

section SuperTrue

variable (eval : Spec → Prop) [DecidablePred eval] (S : SpecSpace Spec)

/-- Super-truth: `.true` when `eval` holds at every admissible specification, `.false` when it
fails at every one, `.indet` otherwise. -/
def superTrue : Trivalent := dist S.admissible eval

/-- Fine's `D`: `eval` holds at every admissible specification. -/
def definitely : Prop := ∀ s ∈ S.admissible, eval s

instance : Decidable (definitely eval S) := inferInstanceAs (Decidable (∀ s ∈ _, _))

/-- Fine's `I`: neither definitely true nor definitely false. -/
def indefinite : Prop := ¬ definitely eval S ∧ ¬ definitely (fun s ↦ ¬ eval s) S

instance : Decidable (indefinite eval S) := inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

theorem superTrue_true_iff : superTrue eval S = .true ↔ ∀ s ∈ S.admissible, eval s :=
  dist_eq_true_iff _ _

theorem superTrue_false_iff : superTrue eval S = .false ↔ ∀ s ∈ S.admissible, ¬ eval s :=
  (dist_eq_false_iff _ _).trans (and_iff_right S.nonempty)

theorem superTrue_indet_iff :
    superTrue eval S = .indet ↔
      (∃ s ∈ S.admissible, eval s) ∧ ∃ s ∈ S.admissible, ¬ eval s :=
  dist_eq_indet_iff _ _

theorem definitely_iff : definitely eval S ↔ superTrue eval S = .true :=
  (superTrue_true_iff eval S).symm

theorem indefinite_iff : indefinite eval S ↔ superTrue eval S = .indet := by
  simp only [indefinite, definitely, superTrue_indet_iff, not_forall, not_not, exists_prop]
  exact and_comm

/-- Negation is classical: super-falsity of `eval` is super-truth of its negation. -/
theorem superTrue_not : superTrue (fun s ↦ ¬ eval s) S = (superTrue eval S).neg :=
  dist_not_of_nonempty _ _ S.nonempty

/-- Fidelity: over a single specification super-truth is classical truth. -/
@[simp] theorem superTrue_singleton (s : Spec) :
    superTrue eval (.singleton s) = if eval s then .true else .false :=
  dist_singleton s eval

omit [DecidablePred eval] in
/-- Stability: definite truth is preserved by extension. -/
theorem definitely_mono : Monotone (definitely eval) :=
  fun _ _ hST h s hs ↦ h s (hST hs)

/-- Stability: super-truth is monotone from the extension order into the knowledge order, so
extension preserves definite values and can only resolve the indefinite. -/
theorem toFlat_superTrue_mono : Monotone fun S ↦ toFlat (superTrue eval S) := by
  intro S T hST
  show toFlat (superTrue eval S) ≤ toFlat (superTrue eval T)
  rcases h : superTrue eval S with _ | _ | _
  · rw [(superTrue_true_iff ..).2 (definitely_mono eval hST ((superTrue_true_iff ..).1 h))]
  · rw [(superTrue_false_iff ..).2 (definitely_mono _ hST ((superTrue_false_iff ..).1 h))]
  · exact bot_le

end SuperTrue

end Semantics.Supervaluation
