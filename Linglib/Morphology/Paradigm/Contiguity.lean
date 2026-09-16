import Linglib.Morphology.Paradigm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Image

/-!
# Paradigm contiguity: the *ABA generalization

Across graded paradigms — degree (positive < comparative < superlative,
[bobaljik-2012]), case (NOM < ACC < GEN < DAT, [caha-2009]), path roles
([pantcheva-2011]) — the cross-linguistic *ABA generalization says a
form never recurs across a distinct intervening form: each form's fiber
is order-connected (`IsContiguous`). The predicate is stated over any
preordered cell type, so it applies alike to a `Paradigm n F` over
`Fin n` and, under `open scoped Case.Caha`, to a form assignment
`Case → F` over the containment order of `Syntax/Case/Order.lean`.
[graf-2019] reconstructs *ABA across these domains as *feasible
monotonicity*: the form assignment is monotone with respect to *some*
linear order on the output forms (his def. (6); the cell order is what
is fixed). Over linearly ordered cells, that is equivalent to the
assignment being the kernel of a monotone score (`FeasiblyMonotone`) —
`isContiguous_iff_feasiblyMonotone`, stated here as the general theorem
behind Graf's instance-by-instance verification, independently of any
insertion mechanism.

Over three cells the five syncretism patterns are named as
[bobaljik-2012] names the degree patterns (`Paradigm.aaa`, `Paradigm.abb`,
`Paradigm.abc`, `Paradigm.aba`, `Paradigm.aab`); ABA is the one contiguity
excludes (`isContiguous_iff_syncretism_ne_aba`). Theory-laden derivations
of contiguity (vocabulary insertion under the Elsewhere Condition over
containment hierarchies) live in
`Morphology/Exponence/Containment/Contiguity.lean`.

## Main declarations

* `IsContiguous`, `isContiguous_iff_ordConnected_preimage` — no ABA
  configuration: every fiber is `Set.OrdConnected`
* `FeasiblyMonotone`, `isContiguous_iff_feasiblyMonotone` —
  [graf-2019]'s monotonicity reconstruction of *ABA
* `IsContiguous.comp_monotone`, `isContiguous_comp_left` — composition API
* `Paradigm.aaa` … `Paradigm.aab`, `isContiguous_iff_syncretism_ne_aba` —
  the three-cell patterns and the one contiguity excludes

## References

* [bobaljik-2012]
* [caha-2009]
* [pantcheva-2011]
* [graf-2019]
* [bobaljik-sauerland-2018]
-/

namespace Morphology

variable {F : Type*}

section Preorder

variable {ι κ : Type*} [Preorder ι] [Preorder κ]

/-- A form assignment on preordered cells is **contiguous** when no form
recurs across a distinct intervening form: if the cells at `i ≤ k` agree,
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

/-- **Feasible monotonicity** ([graf-2019] def. (6)), in monotone-score
form: some monotone score identifies exactly the cells the assignment
identifies. Equivalent to Graf's literal statement — monotone with
respect to *some* linear order on the output forms — over finitely many
cells, since forms are bins and only the kernel matters. -/
def FeasiblyMonotone (p : ι → F) : Prop :=
  ∃ g : ι → ℕ, Monotone g ∧ ∀ i j, p i = p j ↔ g i = g j

end Preorder

/-! ### The three-cell patterns

The five syncretism patterns of a three-cell chain, as form-class indices,
named as [bobaljik-2012] names the degree patterns over positive <
comparative < superlative. A concrete paradigm has a pattern when its
`syncretism` is the pattern's. ABA is the pattern contiguity excludes; AAB
is contiguous, and its exclusion for degree is a vocabulary-level matter
(`Morphology/Exponence/Containment/Contiguity.lean`). -/

namespace Paradigm

/-- AAA: one form throughout (*tall – taller – tallest*). -/
def aaa : Paradigm 3 ℕ := ![0, 0, 0]

/-- ABB: the two upper cells share a form the lowest lacks (*good – better – best*). -/
def abb : Paradigm 3 ℕ := ![0, 1, 1]

/-- ABC: three forms (*bonus – melior – optimus*). -/
def abc : Paradigm 3 ℕ := ![0, 1, 2]

/-- ABA: the outer cells share a form the middle one lacks. -/
def aba : Paradigm 3 ℕ := ![0, 1, 0]

/-- AAB: the two lower cells share a form the highest lacks. -/
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
theorem syncretism_eq_aba_iff (p : Paradigm 3 F) :
    syncretism p = syncretism Paradigm.aba ↔ p 0 = p 2 ∧ p 0 ≠ p 1 := by
  rw [syncretism_eq_iff]
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

/-- ABA is the only three-cell pattern contiguity excludes. -/
theorem isContiguous_iff_syncretism_ne_aba (p : Paradigm 3 F) :
    IsContiguous p ↔ syncretism p ≠ syncretism Paradigm.aba := by
  rw [isContiguous_fin_three_iff, ne_eq, syncretism_eq_aba_iff, not_and, not_not]

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

/-- The prefix-image score of a paradigm: how many distinct forms appear
among the cells up to and including `i`. -/
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

/-- **[graf-2019]'s monotonicity reconstruction of *ABA**: over linearly
ordered cells, a paradigm is contiguous iff it is feasibly monotonic.
Forward direction via the prefix-image score; backward direction is the
sandwich argument that makes monotone kernels convex. -/
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
