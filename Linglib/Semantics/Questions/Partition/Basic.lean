import Linglib.Core.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Partition.Finpartition
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Partition questions

This file defines the basic vocabulary of partition questions. A question in the sense of
[groenendijk-stokhof-1984] is a `Setoid W`, its answers the cells; the same object is a subject
matter in the sense of [lewis-1988], and a proposition is entirely about it when the partition
settles it, that is, when it is constant on the cells. The polar question whether `p` is the
kernel of the indicator of `p`, settledness is the refinement order `s ≤ polar p`, and the
question raised by a family of propositions is the meet of their polar questions, so a finer
question settles more (`le_trans`), the finest question settles everything (`bot_le`), and a
family's question settles each member (`iInf₂_le`). Over a finite type the cells are the parts
of mathlib's `Finpartition.ofSetoid`, refinement is monotone into the `Finpartition` order, and
the number of cells is `Nat.card (Quotient s)`.

## Main definitions

* `Setoid.cell s w` — the cell of `w`, an element of `s.classes`.
* `Setoid.polar p` — the polar question whether `p`.
* `Setoid.Settles s p` — `s` settles `p`: `p` is a union of cells.
* `Setoid.ofProps ps` — the question raised by a finite family of propositions.

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

instance : DecidableRel (⊤ : Setoid W) := λ _ _ => isTrue trivial

instance [DecidableRel s] : Decidable (v ∈ s.cell w) := inferInstanceAs (Decidable (s v w))

instance [Fintype W] [DecidableRel s] [DecidablePred (· ∈ p)] : Decidable (s.cell w ⊆ p) :=
  inferInstanceAs (Decidable (∀ v, s v w → v ∈ p))

/-! ### Polar questions and settled propositions -/

variable (p) in
/-- The polar question whether `p`: the kernel of its indicator. -/
def polar : Setoid W := Setoid.ker (· ∈ p)

theorem polar_iff : polar p w v ↔ (w ∈ p ↔ v ∈ p) := eq_iff_iff

@[simp] theorem polar_compl : polar pᶜ = polar p :=
  Setoid.ext λ _ _ => by simp only [polar_iff, Set.mem_compl_iff, not_iff_not]

instance [DecidablePred (· ∈ p)] : DecidableRel (polar p) :=
  λ _ _ => decidable_of_iff _ polar_iff.symm

variable (s p) in
/-- `s` settles `p`: `p` is constant on the cells of `s`, so it is a union of cells. The
question `s` refines the polar question whether `p`. -/
def Settles : Prop := s ≤ polar p

theorem settles_iff : s.Settles p ↔ ∀ w v, s w v → (w ∈ p ↔ v ∈ p) :=
  ⟨λ h _ _ hwv => polar_iff.1 (h hwv), λ h _ _ hwv => polar_iff.2 (h _ _ hwv)⟩

/-- Equivalent worlds agree on a settled proposition. -/
theorem Settles.iff (h : s.Settles p) (hwv : s w v) : w ∈ p ↔ v ∈ p :=
  settles_iff.1 h w v hwv

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

/-- A finer question settles whatever a coarser one does. -/
theorem Settles.mono {s' : Setoid W} (hs : s' ≤ s) (h : s.Settles p) : s'.Settles p :=
  hs.trans h

/-- The finest question settles every proposition. -/
theorem bot_settles : (⊥ : Setoid W).Settles p := bot_le

/-- The polar question whether `p` settles `p`. -/
theorem polar_settles : (polar p).Settles p := le_rfl

/-- The coarsest question settles only the trivial propositions. -/
theorem top_settles_iff : (⊤ : Setoid W).Settles p ↔ ∀ w v, (w ∈ p ↔ v ∈ p) := by
  simp [settles_iff, Setoid.top_def]

theorem settles_compl_iff : s.Settles pᶜ ↔ s.Settles p := by
  simp only [Settles, polar_compl]

theorem Settles.compl (h : s.Settles p) : s.Settles pᶜ := settles_compl_iff.2 h

theorem Settles.inter (hp : s.Settles p) (hq : s.Settles q) : s.Settles (p ∩ q) :=
  settles_iff.2 λ _ _ h => and_congr (settles_iff.1 hp _ _ h) (settles_iff.1 hq _ _ h)

theorem Settles.union (hp : s.Settles p) (hq : s.Settles q) : s.Settles (p ∪ q) :=
  settles_iff.2 λ _ _ h => or_congr (settles_iff.1 hp _ _ h) (settles_iff.1 hq _ _ h)

/-- A cell of a question settling `p` that meets `p` entails it. -/
theorem Settles.cell_subset (h : s.Settles p) (hw : w ∈ p) : s.cell w ⊆ p :=
  λ _ hv => (settles_iff.1 h _ _ hv).2 hw

/-! ### The question raised by a family of propositions -/

variable (ps : Finset (Finset W))

/-- The question raised by a family of propositions: the coarsest question settling each of
them, the meet of their polar questions. -/
def ofProps : Setoid W := ⨅ p ∈ ps, polar (↑p : Set W)

theorem ofProps_iff : ofProps ps w v ↔ ∀ p ∈ ps, (w ∈ p ↔ v ∈ p) := by
  simp only [iInf, Setoid.sInf_iff, Set.forall_mem_range, polar_iff, Finset.mem_coe]

instance [DecidableEq W] : DecidableRel (ofProps ps) :=
  λ _ _ => decidable_of_iff _ (ofProps_iff ps).symm

/-- The question raised by a family settles each of its members. -/
theorem ofProps_settles {p : Finset W} (hp : p ∈ ps) : (ofProps ps).Settles ↑p :=
  iInf₂_le p hp

/-- The question raised by a family is the coarsest question settling all of its members. -/
theorem le_ofProps_iff : s ≤ ofProps ps ↔ ∀ p ∈ ps, s.Settles ↑p :=
  le_iInf₂_iff

/-! ### Finite questions -/

/-- A coarser question has no more cells. -/
theorem natCard_quotient_anti [Finite W] {s t : Setoid W} (h : s ≤ t) :
    Nat.card (Quotient t) ≤ Nat.card (Quotient s) :=
  Nat.card_le_card_of_surjective (Quotient.map' id λ _ _ hab => h hab)
    (Quotient.ind λ a => ⟨⟦a⟧, rfl⟩)

/-- The parts of the finpartition of a question are its cells. [UPSTREAM] -/
theorem mem_parts_ofSetoid_iff [Fintype W] [DecidableEq W] [DecidableRel s] {c : Finset W} :
    c ∈ (Finpartition.ofSetoid s).parts ↔ ∃ w, c = Finset.univ.filter (s w ·) := by
  simp [Finpartition.ofSetoid, Finpartition.ofSetSetoid_parts, eq_comm]

/-- Refinement of questions is refinement of their finpartitions. [UPSTREAM] -/
theorem _root_.Finpartition.ofSetoid_mono [Fintype W] [DecidableEq W] {s t : Setoid W}
    [DecidableRel s] [DecidableRel t] (h : s ≤ t) :
    Finpartition.ofSetoid s ≤ Finpartition.ofSetoid t := by
  intro c hc
  obtain ⟨w, rfl⟩ := mem_parts_ofSetoid_iff.1 hc
  refine ⟨_, mem_parts_ofSetoid_iff.2 ⟨w, rfl⟩, λ x hx => ?_⟩
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, Setoid.le_def.1 h hx.2⟩

end Setoid
