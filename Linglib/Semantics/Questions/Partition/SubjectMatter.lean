import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Fintype.Basic

/-!
# Subject matters and the propositions they settle

This file defines, for a partition of the worlds given as a `Setoid W`, the cell of a world,
the propositions the partition settles, and the partition determined by a finite family of
propositions. A partition question in the sense of [groenendijk-stokhof-1984] is a `Setoid W`;
a subject matter in the sense of [lewis-1988] is the same object, and a proposition is entirely
about it when it is settled by it, that is, constant on its cells. Settledness is the lattice
order `s ≤ Setoid.ker (· ∈ p)`, so the facts that a finer partition settles more, that the
finest partition settles everything, and that the partition determined by a family settles
each member are `le_trans`, `bot_le`, and `iInf₂_le`.

## Main definitions

* `Setoid.cell s w` — the cell of `w`, an element of `s.classes`.
* `Setoid.Settles s p` — `s` settles `p`: `p` is a union of cells.
* `Setoid.subjectMatter ps` — the coarsest partition settling each proposition in `ps`.

## References

* [groenendijk-stokhof-1984]
* [lewis-1988]
* [von-fintel-gillies-2010]
-/

namespace Setoid

variable {W : Type*} (s : Setoid W) (p q : Set W)

/-! ### Cells -/

/-- The cell of `w`: the worlds equivalent to it. -/
def cell (w : W) : Set W := {v | s v w}

variable {s p q} {w v : W}

@[simp] theorem mem_cell : v ∈ s.cell w ↔ s v w := Iff.rfl

theorem cell_mem_classes (w : W) : s.cell w ∈ s.classes := s.mem_classes w

theorem mem_cell_self (w : W) : w ∈ s.cell w := s.refl' w

theorem cell_eq_of_rel (h : s w v) : s.cell w = s.cell v :=
  Set.ext λ _ => ⟨λ h' => s.trans' h' h, λ h' => s.trans' h' (s.symm' h)⟩

@[simp] theorem cell_bot (w : W) : (⊥ : Setoid W).cell w = {w} := by
  ext; simp [cell]

instance [DecidableEq W] : DecidableRel (⊥ : Setoid W) :=
  λ v w => decidable_of_iff (v = w) (by rw [Setoid.bot_def])

instance {β : Type*} [DecidableEq β] (f : W → β) : DecidableRel (Setoid.ker f) :=
  λ _ _ => inferInstanceAs (Decidable (_ = _))

instance [DecidableRel s] : Decidable (v ∈ s.cell w) := inferInstanceAs (Decidable (s v w))

instance [Fintype W] [DecidableRel s] [DecidablePred (· ∈ p)] : Decidable (s.cell w ⊆ p) :=
  inferInstanceAs (Decidable (∀ v, s v w → v ∈ p))

/-! ### Settled propositions -/

variable (s p) in
/-- `s` settles `p`: `p` is constant on the cells of `s`, so it is a union of cells. The
partition question `s` entails the polar question whether `p`. -/
def Settles : Prop := s ≤ Setoid.ker (· ∈ p)

theorem settles_iff : s.Settles p ↔ ∀ w v, s w v → (w ∈ p ↔ v ∈ p) :=
  ⟨λ h _ _ hwv => Iff.of_eq (h hwv), λ h _ _ hwv => propext (h _ _ hwv)⟩

/-- `s` settles `p` iff each cell entails `p` or entails its negation. -/
theorem settles_iff_forall_cell :
    s.Settles p ↔ ∀ w, s.cell w ⊆ p ∨ ∀ v ∈ s.cell w, v ∉ p := by
  rw [settles_iff]
  refine ⟨λ h w => ?_, λ h w v hwv => ?_⟩
  · by_cases hw : w ∈ p
    · exact Or.inl λ v hv => (h v w hv).2 hw
    · exact Or.inr λ v hv hv' => hw ((h v w hv).1 hv')
  · rcases h v with hall | hnone
    · exact iff_of_true (hall hwv) (hall (s.refl' v))
    · exact iff_of_false (hnone w hwv) (hnone v (s.refl' v))

instance [Fintype W] [DecidableRel s] [DecidablePred (· ∈ p)] : Decidable (s.Settles p) :=
  decidable_of_iff _ settles_iff.symm

/-- A finer partition settles whatever a coarser one does. -/
theorem Settles.mono {s' : Setoid W} (hs : s' ≤ s) (h : s.Settles p) : s'.Settles p :=
  hs.trans h

/-- The finest partition settles every proposition. -/
theorem bot_settles : (⊥ : Setoid W).Settles p := bot_le

theorem settles_compl_iff : s.Settles pᶜ ↔ s.Settles p := by
  simp only [settles_iff, Set.mem_compl_iff, not_iff_not]

theorem Settles.compl (h : s.Settles p) : s.Settles pᶜ := settles_compl_iff.2 h

theorem Settles.inter (hp : s.Settles p) (hq : s.Settles q) : s.Settles (p ∩ q) :=
  settles_iff.2 λ _ _ h => and_congr (settles_iff.1 hp _ _ h) (settles_iff.1 hq _ _ h)

theorem Settles.union (hp : s.Settles p) (hq : s.Settles q) : s.Settles (p ∪ q) :=
  settles_iff.2 λ _ _ h => or_congr (settles_iff.1 hp _ _ h) (settles_iff.1 hq _ _ h)

/-- A cell of a partition settling `p` that meets `p` entails it. -/
theorem Settles.cell_subset (h : s.Settles p) (hw : w ∈ p) : s.cell w ⊆ p :=
  λ _ hv => (settles_iff.1 h _ _ hv).2 hw

/-! ### The subject matter of a family of propositions -/

variable (ps : Finset (Finset W))

/-- The subject matter of a family of propositions: the coarsest partition settling each of
them, the kernel of the map recording which of them hold. -/
def subjectMatter : Setoid W := ⨅ p ∈ ps, Setoid.ker (· ∈ p)

theorem subjectMatter_iff : subjectMatter ps w v ↔ ∀ p ∈ ps, (w ∈ p ↔ v ∈ p) := by
  simp only [iInf, Setoid.sInf_iff, Set.forall_mem_range, Setoid.ker_def, eq_iff_iff]

instance [DecidableEq W] : DecidableRel (subjectMatter ps) :=
  λ _ _ => decidable_of_iff _ (subjectMatter_iff ps).symm

/-- The subject matter of a family settles each of its members. -/
theorem subjectMatter_settles {p : Finset W} (hp : p ∈ ps) : (subjectMatter ps).Settles ↑p :=
  iInf₂_le p hp

/-- The subject matter of a family is the finest partition settling all of its members. -/
theorem le_subjectMatter_iff : s ≤ subjectMatter ps ↔ ∀ p ∈ ps, s.Settles ↑p :=
  le_iInf₂_iff

end Setoid
