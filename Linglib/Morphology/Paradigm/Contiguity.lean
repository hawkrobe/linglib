module

public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Data.Finset.Image

/-!
# Paradigm contiguity: the *ABA generalization

A form assignment on preordered cells is contiguous when no form recurs across a distinct
intervening form, so that the cells sharing a form are order-connected. The *ABA generalization
says graded paradigms are contiguous, for degree (positive < comparative < superlative, after
Bobaljik), case (after Caha), and path roles (after Pantcheva). Graf recasts *ABA as feasible
monotonicity, monotonicity of the assignment with respect to some linear order on the forms,
which over linearly ordered cells is contiguity. Of the five syncretism patterns of three cells,
named as Bobaljik names the degree patterns, contiguity excludes exactly ABA.

## Main definitions

* `IsContiguous`: no form recurs across a distinct intervening form.
* `FeasiblyMonotone`: some monotone score identifies the cells the assignment identifies.
* `Paradigm.aaa`, `Paradigm.abb`, `Paradigm.abc`, `Paradigm.aba`, `Paradigm.aab`: the
  three-cell patterns.

## Main results

* `isContiguous_iff_ordConnected_preimage`: contiguity is order-connectedness of every fiber.
* `isContiguous_comp_iff`: postcomposition with an injective map preserves and reflects
  contiguity.
* `isContiguous_iff_ker_ne_ker_aba`: over three cells contiguity excludes exactly ABA.
* `ker_eq_ker_aba_iff`, `ker_eq_ker_aab_iff`, `ker_eq_ker_abc_iff`, `ker_eq_ker_iff_fin_three`:
  the three-cell patterns by equalities of their cells.
* `isContiguous_iff_feasiblyMonotone`: over linearly ordered cells contiguity is feasible
  monotonicity.

## References

* [bobaljik-2012]
* [caha-2009]
* [pantcheva-2011]
* [graf-2019]
* [bobaljik-sauerland-2018]
-/

@[expose] public section

namespace Morphology

variable {F : Type*}

section Preorder

variable {ι κ : Type*} [Preorder ι] [Preorder κ]

/-- A form assignment on preordered cells is **contiguous** when no form
recurs across a distinct intervening form. If the cells at `i ≤ k` agree,
every cell between them agrees too, so each form's fiber is order-connected.
ABA (`![a, b, a]`) violates this; AAA, ABB, ABC — and AAB — satisfy it.
(*AAB is excluded by vocabulary-level conditions, not by contiguity;
see `Morphology/Exponence/Containment/Contiguity.lean`.) -/
def IsContiguous (p : ι → F) : Prop :=
  ∀ ⦃i j k : ι⦄, i ≤ j → j ≤ k → p i = p k → p i = p j

instance [Fintype ι] [DecidableLE ι] [DecidableEq F] (p : ι → F) :
    Decidable (IsContiguous p) :=
  inferInstanceAs (Decidable (∀ i j k : ι, i ≤ j → j ≤ k → p i = p k → p i = p j))

/-- Contiguity is order-connectedness of every fiber. -/
theorem isContiguous_iff_ordConnected_preimage (p : ι → F) :
    IsContiguous p ↔ ∀ y, (p ⁻¹' {y}).OrdConnected := by
  refine ⟨fun hp y ↦ ⟨fun i hi k hk j hj ↦ ?_⟩, fun h i j k hij hjk hik ↦ ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi hk ⊢
    exact (hp hj.1 hj.2 (hi.trans hk.symm)).symm.trans hi
  · exact ((h (p i)).out (Set.mem_singleton _) hik.symm ⟨hij, hjk⟩).symm

/-- Postcomposition with an injective map preserves and reflects contiguity. -/
theorem isContiguous_comp_iff {G : Type*} {h : F → G} (hh : Function.Injective h) {p : ι → F} :
    IsContiguous (h ∘ p) ↔ IsContiguous p :=
  ⟨fun hp _ _ _ hij hjk he ↦ hh (hp hij hjk (congrArg h he)),
    fun hp _ _ _ hij hjk he ↦ congrArg h (hp hij hjk (hh he))⟩

/-- Precomposition with a monotone regrading preserves contiguity. -/
theorem IsContiguous.comp_monotone {p : ι → F} (hp : IsContiguous p) {f : κ → ι}
    (hf : Monotone f) : IsContiguous (p ∘ f) :=
  fun _ _ _ hij hjk heq ↦ hp (hf hij) (hf hjk) heq

/-- A form assignment that factors as a monotone score followed by a map
injective on the score's range is contiguous. -/
theorem isContiguous_comp_left {β : Type*} [PartialOrder β] {g : ι → β}
    (hg : Monotone g) {h : β → F} (hh : Set.InjOn h (Set.range g)) :
    IsContiguous (h ∘ g) := by
  intro i j k hij hjk heq
  have hgik : g i = g k := hh (Set.mem_range_self i) (Set.mem_range_self k) heq
  exact congrArg h (le_antisymm (hg hij) (hgik.symm ▸ hg hjk))

/-- A form assignment is **feasibly monotone** ([graf-2019] def. (6)) when some monotone score
identifies exactly the cells the assignment identifies. Over finitely many cells this is Graf's
literal statement, monotonicity with respect to *some* linear order on the output forms, since
forms are bins and only the kernel matters. -/
def FeasiblyMonotone (p : ι → F) : Prop :=
  ∃ g : ι → ℕ, Monotone g ∧ ∀ i j, p i = p j ↔ g i = g j

end Preorder

/-! ### The three-cell patterns

The five syncretism patterns of a three-cell chain, as form-class indices,
named as [bobaljik-2012] names the degree patterns over positive <
comparative < superlative. A concrete paradigm has a pattern when its
syncretism, the kernel `Setoid.ker`, is the pattern's. ABA is the pattern contiguity excludes; AAB
is contiguous, and its exclusion for degree is a vocabulary-level matter
(`Morphology/Exponence/Containment/Contiguity.lean`). -/

namespace Paradigm

/-- The AAA pattern has one form throughout (*tall – taller – tallest*). -/
def aaa : Paradigm 3 ℕ := ![0, 0, 0]

/-- In the ABB pattern the two upper cells share a form the lowest lacks
(*good – better – best*). -/
def abb : Paradigm 3 ℕ := ![0, 1, 1]

/-- The ABC pattern has three forms (*bonus – melior – optimus*). -/
def abc : Paradigm 3 ℕ := ![0, 1, 2]

/-- In the ABA pattern the outer cells share a form the middle one lacks. -/
def aba : Paradigm 3 ℕ := ![0, 1, 0]

/-- In the AAB pattern the two lower cells share a form the highest lacks. -/
def aab : Paradigm 3 ℕ := ![0, 0, 1]

end Paradigm

/-- Over three cells contiguity is the one condition on the outer pair. -/
theorem isContiguous_fin_three_iff (p : Paradigm 3 F) :
    IsContiguous p ↔ (p 0 = p 2 → p 0 = p 1) := by
  refine ⟨fun h ↦ h (i := 0) (j := 1) (k := 2) (by decide) (by decide),
    fun h i j k hij hjk heq ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | rfl
    | exact heq
    | exact h heq
    | exact absurd hij (by decide)
    | exact absurd hjk (by decide)

/-- A three-cell paradigm has the ABA pattern iff its outer cells agree and
its middle cell differs. -/
theorem ker_eq_ker_aba_iff (p : Paradigm 3 F) :
    Setoid.ker p = Setoid.ker Paradigm.aba ↔ p 0 = p 2 ∧ p 0 ≠ p 1 := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨(h 0 2).mpr rfl, fun h01 ↦ absurd ((h 0 1).mp h01) (by decide)⟩, ?_⟩
  rintro ⟨h02, h01⟩ a b
  have h12 : p 1 ≠ p 2 := fun h ↦ h01 (h02.trans h.symm)
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact iff_of_true h02 rfl
    | exact iff_of_true h02.symm rfl
    | exact iff_of_false h01 (by decide)
    | exact iff_of_false h01.symm (by decide)
    | exact iff_of_false h12 (by decide)
    | exact iff_of_false h12.symm (by decide)

/-- A three-cell paradigm has the AAB pattern iff its lower cells agree and its highest cell
differs. -/
theorem ker_eq_ker_aab_iff (p : Paradigm 3 F) :
    Setoid.ker p = Setoid.ker Paradigm.aab ↔ p 0 = p 1 ∧ p 1 ≠ p 2 := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨(h 0 1).mpr rfl, fun h12 ↦ absurd ((h 1 2).mp h12) (by decide)⟩, ?_⟩
  rintro ⟨h01, h12⟩ a b
  have h02 : p 0 ≠ p 2 := fun h ↦ h12 (h01.symm.trans h)
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact iff_of_true h01 rfl
    | exact iff_of_true h01.symm rfl
    | exact iff_of_false h12 (by decide)
    | exact iff_of_false h12.symm (by decide)
    | exact iff_of_false h02 (by decide)
    | exact iff_of_false h02.symm (by decide)

/-- A three-cell paradigm has the ABC pattern iff its cells differ pairwise. -/
theorem ker_eq_ker_abc_iff (p : Paradigm 3 F) :
    Setoid.ker p = Setoid.ker Paradigm.abc ↔ p 0 ≠ p 1 ∧ p 1 ≠ p 2 ∧ p 0 ≠ p 2 := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨fun e ↦ absurd ((h 0 1).mp e) (by decide),
    fun e ↦ absurd ((h 1 2).mp e) (by decide), fun e ↦ absurd ((h 0 2).mp e) (by decide)⟩, ?_⟩
  rintro ⟨h01, h12, h02⟩ a b
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact iff_of_false h01 (by decide)
    | exact iff_of_false h01.symm (by decide)
    | exact iff_of_false h12 (by decide)
    | exact iff_of_false h12.symm (by decide)
    | exact iff_of_false h02 (by decide)
    | exact iff_of_false h02.symm (by decide)

/-- Two three-cell paradigms have the same pattern iff the same pairs of cells agree. -/
theorem ker_eq_ker_iff_fin_three {G : Type*} (p : Paradigm 3 F) (q : Paradigm 3 G) :
    Setoid.ker p = Setoid.ker q ↔
      (p 0 = p 1 ↔ q 0 = q 1) ∧ (p 1 = p 2 ↔ q 1 = q 2) ∧ (p 0 = p 2 ↔ q 0 = q 2) := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨h 0 1, h 1 2, h 0 2⟩, fun ⟨h01, h12, h02⟩ a b ↦ ?_⟩
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact h01
    | exact h12
    | exact h02
    | exact (eq_comm.trans h01).trans eq_comm
    | exact (eq_comm.trans h12).trans eq_comm
    | exact (eq_comm.trans h02).trans eq_comm

/-- ABA is the only three-cell pattern contiguity excludes. -/
theorem isContiguous_iff_ker_ne_ker_aba (p : Paradigm 3 F) :
    IsContiguous p ↔ Setoid.ker p ≠ Setoid.ker Paradigm.aba := by
  rw [isContiguous_fin_three_iff, ne_eq, ker_eq_ker_aba_iff, not_and, not_not]

/-! ### Graf's monotonicity reconstruction

[graf-2019] recasts the *ABA generalization — across adjectival
gradation, person-pronoun syncretism, case syncretism, and noun stem
allomorphy — as feasible monotonicity of the form assignment from a
fixed cell order ([bobaljik-sauerland-2018] is the feature-combinatoric
counterpart, deriving which cell arrangements exclude ABA without
stipulating containment). The kernel formulation below is this file's
gloss: forms are bins, so feasible monotonicity over linearly ordered
cells is the existence of a monotone score with the paradigm's kernel.
The prefix-image score `i ↦ #{forms among cells ≤ i}` is monotone and
has the same kernel as a contiguous paradigm, and conversely any
paradigm sharing its kernel with a monotone score has convex fibers.
(Graf's case hierarchies are partial orders going beyond this linear
setting, and his PCC/GCC treatment is a different object — monotone
maps into the fixed two-element truth-value algebra, i.e. upper sets;
see `Studies/Graf2019.lean`.) -/

section Graf

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

section

variable [DecidableEq F]

/-- The prefix-image score of a paradigm counts the distinct forms among the cells up to and
including `i`. -/
private def score (p : ι → F) (i : ι) : ℕ :=
  ((Finset.Iic i).image p).card

private theorem score_mono {p : ι → F} : Monotone (score p) :=
  fun _ _ hij ↦
    Finset.card_le_card (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij))

private theorem score_eq_of_eq {p : ι → F} (hp : IsContiguous p)
    {i j : ι} (hij : i ≤ j) (hpij : p i = p j) : score p i = score p j := by
  unfold score
  congr 1
  refine Finset.Subset.antisymm
    (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)) (fun x hx ↦ ?_)
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Iic] at hl
  rcases le_total l i with hli | hil
  · exact Finset.mem_image_of_mem p (Finset.mem_Iic.mpr hli)
  · rw [← hp hil hl hpij]
    exact Finset.mem_image_of_mem p (Finset.mem_Iic.mpr le_rfl)

private theorem eq_of_score_eq {p : ι → F} (hp : IsContiguous p)
    {i j : ι} (hij : i ≤ j) (hs : score p i = score p j) : p i = p j := by
  have heq : (Finset.Iic i).image p = (Finset.Iic j).image p :=
    Finset.eq_of_subset_of_card_le
      (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)) (le_of_eq hs.symm)
  have hj : p j ∈ (Finset.Iic i).image p :=
    heq ▸ Finset.mem_image_of_mem p (Finset.mem_Iic.mpr le_rfl)
  obtain ⟨l, hl, hpl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_Iic] at hl
  exact (hp hl hij hpl).symm.trans hpl

end

/-- Over linearly ordered cells a paradigm is contiguous iff it is feasibly monotonic,
[graf-2019]'s monotonicity reconstruction of *ABA. The forward direction uses the prefix-image
score, and the backward direction is the sandwich argument that makes monotone kernels
convex. -/
theorem isContiguous_iff_feasiblyMonotone (p : ι → F) :
    IsContiguous p ↔ FeasiblyMonotone p := by
  classical
  constructor
  · intro hp
    refine ⟨score p, score_mono, fun i j ↦ ⟨fun hpij ↦ ?_, fun hs ↦ ?_⟩⟩
    · rcases le_total i j with h | h
      · exact score_eq_of_eq hp h hpij
      · exact (score_eq_of_eq hp h hpij.symm).symm
    · rcases le_total i j with h | h
      · exact eq_of_score_eq hp h hs
      · exact (eq_of_score_eq hp h hs.symm).symm
  · rintro ⟨g, hmono, hker⟩ i j k hij hjk heq
    have hik : g i = g k := (hker i k).mp heq
    exact (hker i j).mpr (le_antisymm (hmono hij) (hik.symm ▸ hmono hjk))

end Graf

end Morphology
