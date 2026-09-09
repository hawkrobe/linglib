import Linglib.Semantics.Questions.Exhaustivity
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.CompleteLattice.Finset

/-!
# Hamblin sets closed under conjunction or disjunction

A wh-question over atomic answers `a i` denotes, under [dayal-1996]'s sum-closed restrictor,
the family of conjunctions `conjFamily a S` over non-empty groups `S`; under [spector-2008]'s
higher-order quantification (pruned to disjunctions of atoms, as in [fox-2018]) it denotes the
family of disjunctions `disj a S`. Both families are read off a world's `profile`, the atoms
true there, and both induce the same strong answers.

## References

* [dayal-1996]
* [spector-2008]
* [fox-2007]
* [fox-2018]
-/

namespace Question

variable {W ι : Type*} (a : ι → Set W)

/-- The atoms true at a world. -/
def profile (w : W) : Set ι := {i | w ∈ a i}

/-- The conjunction of the atoms in a group. -/
def conjFamily (S : Finset ι) : Set W := ⋂ i ∈ S, a i

/-- The disjunction of the atoms in a group. -/
def disj (S : Finset ι) : Set W := ⋃ i ∈ S, a i

/-- The Hamblin set closed under conjunction: one member per non-empty group. -/
def conjClosure : Set (Set W) := conjFamily a '' {S | S.Nonempty}

/-- The Hamblin set closed under disjunction: one member per non-empty group. -/
def disjClosure : Set (Set W) := disj a '' {S | S.Nonempty}

variable {a}

@[simp] theorem mem_profile {w : W} {i : ι} : i ∈ profile a w ↔ w ∈ a i := Iff.rfl

theorem mem_conjFamily {S : Finset ι} {w : W} : w ∈ conjFamily a S ↔ ∀ i ∈ S, w ∈ a i :=
  Set.mem_iInter₂

theorem mem_disj {S : Finset ι} {w : W} : w ∈ disj a S ↔ ∃ i ∈ S, w ∈ a i := by simp [disj]

theorem mem_conjFamily_iff_subset {S : Finset ι} {w : W} : w ∈ conjFamily a S ↔ ↑S ⊆ profile a w :=
  mem_conjFamily.trans ⟨λ h _ hi => h _ hi, λ h _ hi => h hi⟩

theorem conjFamily_singleton (i : ι) : conjFamily a {i} = a i := Finset.set_biInter_singleton i a

theorem disj_singleton (i : ι) : disj a {i} = a i := Finset.set_biUnion_singleton i a

theorem conjFamily_mem_conjClosure {S : Finset ι} (hS : S.Nonempty) :
    conjFamily a S ∈ conjClosure a :=
  ⟨S, hS, rfl⟩

theorem disj_mem_disjClosure {S : Finset ι} (hS : S.Nonempty) : disj a S ∈ disjClosure a :=
  ⟨S, hS, rfl⟩

theorem conjClosure_finite [Fintype ι] : (conjClosure a).Finite :=
  (Set.toFinite {S : Finset ι | S.Nonempty}).image _

theorem disjClosure_finite [Fintype ι] : (disjClosure a).Finite :=
  (Set.toFinite {S : Finset ι | S.Nonempty}).image _

/-- Under either closure, two worlds give the same strong answer iff they have the same
profile. -/
theorem mem_strongAnswer_conjClosure_iff {w v : W} :
    v ∈ strongAnswer (conjClosure a) w ↔ profile a v = profile a w := by
  rw [mem_strongAnswer]
  constructor
  · intro h
    ext i
    have := h _ (conjFamily_mem_conjClosure ⟨i, Finset.mem_singleton_self i⟩)
    rw [conjFamily_singleton] at this
    exact this.symm
  · rintro h _ ⟨S, -, rfl⟩
    rw [mem_conjFamily_iff_subset, mem_conjFamily_iff_subset, h]

theorem mem_strongAnswer_disjClosure_iff {w v : W} :
    v ∈ strongAnswer (disjClosure a) w ↔ profile a v = profile a w := by
  rw [mem_strongAnswer]
  constructor
  · intro h
    ext i
    have := h _ (disj_mem_disjClosure ⟨i, Finset.mem_singleton_self i⟩)
    rw [disj_singleton] at this
    exact this.symm
  · rintro h _ ⟨S, -, rfl⟩
    have hi : ∀ i, w ∈ a i ↔ v ∈ a i := λ i => by
      change i ∈ profile a w ↔ i ∈ profile a v
      rw [h]
    simp only [mem_disj, hi]

/-- Both closures induce the same logical partition. -/
theorem strongAnswer_conjClosure_eq_disjClosure (w : W) :
    strongAnswer (conjClosure a) w = strongAnswer (disjClosure a) w :=
  Set.ext λ _ => mem_strongAnswer_conjClosure_iff.trans mem_strongAnswer_disjClosure_iff.symm

end Question
