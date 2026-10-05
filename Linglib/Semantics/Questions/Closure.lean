module

public import Linglib.Semantics.Questions.Exhaustivity
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Hamblin sets closed under conjunction or disjunction

A wh-question over atomic answers `a i` denotes, under [dayal-1996]'s sum-closed restrictor,
the family of conjunctions `conjFamily a S` over non-empty groups `S`; under [spector-2008]'s
higher-order quantification (pruned to disjunctions of atoms, as in [fox-2018]) it denotes the
family of disjunctions `disj a S`. Both families are read off a world's `profile`, the atoms
true there, and both induce the same partition, the kernel of `profile`.

## References

* [dayal-1996]
* [spector-2008]
* [fox-2007]
* [fox-2018]
-/

@[expose] public section

namespace Question

variable {W ι : Type*} (a : ι → Set W)

/-- The atoms true at a world. -/
def profile (w : W) : Set ι := {i | w ∈ a i}

/-- The conjunction of the atoms in a group. -/
def conjFamily (S : Finset ι) : Set W := ⋂ i ∈ S, a i

/-- The disjunction of the atoms in a group. -/
def disj (S : Finset ι) : Set W := ⋃ i ∈ S, a i

/-- The Hamblin set closed under conjunction has one member per non-empty group. -/
def conjClosure : Set (Set W) := conjFamily a '' {S | S.Nonempty}

/-- The Hamblin set closed under disjunction has one member per non-empty group. -/
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

/-- Under conjunctive closure, two worlds are in the same cell iff they have the same
profile. -/
theorem partition_conjClosure : partition (conjClosure a) = Setoid.ker (profile a) := by
  ext v w
  rw [partition_iff, Setoid.ker_def]
  constructor
  · intro h
    ext i
    simpa only [conjFamily_singleton, mem_profile] using
      h _ (conjFamily_mem_conjClosure (Finset.singleton_nonempty i))
  · rintro h _ ⟨S, -, rfl⟩
    rw [mem_conjFamily_iff_subset, mem_conjFamily_iff_subset, h]

/-- Under disjunctive closure, two worlds are in the same cell iff they have the same profile. -/
theorem partition_disjClosure : partition (disjClosure a) = Setoid.ker (profile a) := by
  ext v w
  rw [partition_iff, Setoid.ker_def]
  constructor
  · intro h
    ext i
    simpa only [disj_singleton, mem_profile] using
      h _ (disj_mem_disjClosure (Finset.singleton_nonempty i))
  · rintro h _ ⟨S, -, rfl⟩
    simp only [Set.ext_iff, mem_profile] at h
    simp only [mem_disj, h]

/-- Both closures induce the same partition. -/
theorem partition_conjClosure_eq_disjClosure :
    partition (conjClosure a) = partition (disjClosure a) :=
  partition_conjClosure.trans partition_disjClosure.symm

end Question
