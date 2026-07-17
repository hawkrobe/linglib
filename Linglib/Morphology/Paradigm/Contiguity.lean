import Linglib.Morphology.Paradigm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Image

/-!
# Paradigm contiguity: the *ABA generalization
[bobaljik-2012] [caha-2009] [graf-2019]

Across graded paradigms — degree (positive < comparative < superlative,
[bobaljik-2012]), case (NOM < ACC < GEN < DAT, [caha-2009]), path roles
([pantcheva-2011]) — the cross-linguistic *ABA generalization says a
form never recurs across a distinct intervening form: each form's fiber
is order-convex (`IsContiguous`). [graf-2019] reconstructs *ABA across
these domains as *feasible monotonicity*: the form assignment is
monotone with respect to *some* linear order on the output forms (his
def. (6); the cell order is what is fixed). Over linearly ordered
cells, that is equivalent to the assignment being the kernel of a
monotone score (`FeasiblyMonotone`) —
`isContiguous_iff_feasiblyMonotone`, stated here as the general theorem
behind Graf's instance-by-instance verification, independently of any
insertion mechanism.

Theory-laden derivations of contiguity (vocabulary insertion under the
Elsewhere Condition over containment hierarchies) live in
`Morphology/Containment/Vocabulary.lean`; the n = 3 degree and n = 4
case specializations in `Morphology/DegreeContainment.lean` and
`Morphology/Case/Allomorphy.lean`.

## Main declarations

* `IsContiguous` — no ABA configuration: fibers are convex
* `FeasiblyMonotone`, `isContiguous_iff_feasiblyMonotone` —
  [graf-2019]'s monotonicity reconstruction of *ABA
* `IsContiguous.comp_monotone`, `isContiguous_comp_left` — composition API
-/

namespace Morphology

variable {n : ℕ} {F : Type*}

/-- A paradigm is **contiguous** when no form recurs across a distinct
intervening form: if the cells at `i ≤ k` agree, every cell between
them agrees too, so each form's fiber is an interval of cells. ABA
(`![a, b, a]`) violates this; AAA, ABB, ABC — and AAB — satisfy it.
(*AAB is excluded by vocabulary-level conditions, not by contiguity;
see `Morphology/Containment/Vocabulary.lean`.) -/
def IsContiguous (p : Paradigm n F) : Prop :=
  ∀ ⦃i j k : Fin n⦄, i ≤ j → j ≤ k → p i = p k → p i = p j

instance [DecidableEq F] (p : Paradigm n F) : Decidable (IsContiguous p) :=
  inferInstanceAs
    (Decidable (∀ i j k : Fin n, i ≤ j → j ≤ k → p i = p k → p i = p j))

/-- Precomposition with a monotone regrading preserves contiguity. -/
theorem IsContiguous.comp_monotone {m : ℕ} {p : Paradigm n F}
    (hp : IsContiguous p) {f : Fin m → Fin n} (hf : Monotone f) :
    IsContiguous (p ∘ f) :=
  λ _ _ _ hij hjk heq => hp (hf hij) (hf hjk) heq

/-- A paradigm that factors as a monotone score followed by a map
injective on the score's range is contiguous. -/
theorem isContiguous_comp_left {β : Type*} [PartialOrder β] {g : Fin n → β}
    (hg : Monotone g) {h : β → F} (hh : Set.InjOn h (Set.range g)) :
    IsContiguous (h ∘ g) := by
  intro i j k hij hjk heq
  have hgik : g i = g k := hh (Set.mem_range_self i) (Set.mem_range_self k) heq
  exact congrArg h (le_antisymm (hg hij) (hgik.symm ▸ hg hjk))

/-! ### Graf's monotonicity reconstruction

[graf-2019] recasts the *ABA generalization — across adjectival
gradation, person-pronoun syncretism, case syncretism, and noun stem
allomorphy — as feasible monotonicity of the form assignment from a
fixed cell order ([bobaljik-sauerland-2018] is the feature-combinatoric
counterpart, deriving which cell arrangements exclude ABA without
stipulating containment). The kernel formulation below is this file's
gloss: forms are bins, so feasible monotonicity over linearly ordered
cells is the existence of a monotone score with the paradigm's kernel.
The prefix-image score `i ↦ #{forms among cells 0..i}` is monotone and
has the same kernel as a contiguous paradigm, and conversely any
paradigm sharing its kernel with a monotone score has convex fibers.
(Graf's case hierarchies are partial orders going beyond this linear
setting, and his PCC/GCC treatment is a different object — monotone
maps into the fixed two-element truth-value algebra, i.e. upper sets;
see `Studies/Graf2019.lean`.) -/

section Graf

variable [DecidableEq F]

/-- The prefix-image score of a paradigm: how many distinct forms appear
among the cells up to and including `i`. -/
private def score (p : Paradigm n F) (i : Fin n) : ℕ :=
  ((Finset.Iic i).image p).card

private theorem score_mono {p : Paradigm n F} : Monotone (score p) :=
  λ _ _ hij =>
    Finset.card_le_card (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij))

private theorem score_eq_of_eq {p : Paradigm n F} (hp : IsContiguous p)
    {i j : Fin n} (hij : i ≤ j) (hpij : p i = p j) : score p i = score p j := by
  unfold score
  congr 1
  refine Finset.Subset.antisymm
    (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)) (λ x hx => ?_)
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Iic] at hl
  rcases le_total l i with hli | hil
  · exact Finset.mem_image_of_mem p (Finset.mem_Iic.mpr hli)
  · rw [← hp hil hl hpij]
    exact Finset.mem_image_of_mem p (Finset.mem_Iic.mpr le_rfl)

private theorem eq_of_score_eq {p : Paradigm n F} (hp : IsContiguous p)
    {i j : Fin n} (hij : i ≤ j) (hs : score p i = score p j) : p i = p j := by
  have heq : (Finset.Iic i).image p = (Finset.Iic j).image p :=
    Finset.eq_of_subset_of_card_le
      (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)) (le_of_eq hs.symm)
  have hj : p j ∈ (Finset.Iic i).image p :=
    heq ▸ Finset.mem_image_of_mem p (Finset.mem_Iic.mpr le_rfl)
  obtain ⟨l, hl, hpl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_Iic] at hl
  exact (hp hl hij hpl).symm.trans hpl

end Graf

/-- **Feasible monotonicity** ([graf-2019] def. (6)), in monotone-score
form: some monotone score identifies exactly the cells the paradigm
identifies. Equivalent to Graf's literal statement — monotone with
respect to *some* linear order on the output forms — over finitely many
cells, since forms are bins and only the kernel matters. -/
def FeasiblyMonotone (p : Paradigm n F) : Prop :=
  ∃ g : Fin n → ℕ, Monotone g ∧ ∀ i j, p i = p j ↔ g i = g j

/-- **[graf-2019]'s monotonicity reconstruction of *ABA**: a paradigm is
contiguous iff it is feasibly monotonic. Forward direction via the
prefix-image score; backward direction is the sandwich argument that
makes monotone kernels convex. -/
theorem isContiguous_iff_feasiblyMonotone (p : Paradigm n F) :
    IsContiguous p ↔ FeasiblyMonotone p := by
  classical
  constructor
  · intro hp
    refine ⟨score p, score_mono, λ i j => ⟨λ hpij => ?_, λ hs => ?_⟩⟩
    · rcases le_total i j with h | h
      · exact score_eq_of_eq hp h hpij
      · exact (score_eq_of_eq hp h hpij.symm).symm
    · rcases le_total i j with h | h
      · exact eq_of_score_eq hp h hs
      · exact (eq_of_score_eq hp h hs.symm).symm
  · rintro ⟨g, hmono, hker⟩ i j k hij hjk heq
    have hik : g i = g k := (hker i k).mp heq
    exact (hker i j).mpr (le_antisymm (hmono hij) (hik.symm ▸ hmono hjk))

end Morphology
