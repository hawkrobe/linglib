module

public import Linglib.Core.Data.Setoid.Basic
public import Mathlib.Data.Setoid.Partition

/-!
# Partition questions

This file defines the basic vocabulary of partition questions. A question in the sense of
[groenendijk-stokhof-1984] is a `Setoid W`, its answers the cells; the same object is a subject
matter in the sense of [lewis-1988], and a proposition is entirely about it when the question
decides it, that is, when it is constant on the cells. The polar question whether `p` is the
kernel of the indicator of `p`, a question decides `p` exactly when it refines the polar
question, `Q ≤ polar p`, and the question raised by a family of propositions is the meet of
their polar questions, so a finer question decides more (`le_trans`), the finest question
decides everything (`bot_le`), and a family's question decides each member (`iInf₂_le`). A
proposition a question decides is [cariani-2013]'s visible, [phillips-brown-2025]'s
considered, and an issue in a subject matter for [von-fintel-gillies-2010]; the converse
relation, a proposition settling a question, is `Question.Resolves`.

## Main definitions

* `Setoid.cell Q w` — the cell of `w`, an element of `Q.classes`.
* `Setoid.polar p` — the polar question whether `p`.
* `Setoid.Decides Q p` — `Q` decides `p`: `p` is a union of cells.
* `Setoid.ofProps ps` — the question raised by a finite family of propositions.

## References

* [groenendijk-stokhof-1984]
* [lewis-1988]
* [von-fintel-gillies-2010]
* [cariani-2013]
* [phillips-brown-2025]
-/

@[expose] public section

namespace Setoid

variable {W : Type*} (Q : Setoid W) (p q : Set W)

/-! ### Cells -/

/-- The cell of `w`: the worlds equivalent to it. -/
def cell (w : W) : Set W := {v | Q v w}

variable {Q p q} {w v : W}

@[simp] theorem mem_cell : v ∈ Q.cell w ↔ Q v w := Iff.rfl

theorem cell_mem_classes (w : W) : Q.cell w ∈ Q.classes := Q.mem_classes w

theorem mem_cell_self (w : W) : w ∈ Q.cell w := Q.refl' w

theorem cell_eq_of_rel (h : Q w v) : Q.cell w = Q.cell v :=
  Set.ext λ _ => ⟨λ h' => Q.trans' h' h, λ h' => Q.trans' h' (Q.symm' h)⟩

@[simp] theorem cell_bot (w : W) : (⊥ : Setoid W).cell w = {w} := by
  ext; simp [cell]

instance [DecidableEq W] : DecidableRel (⊥ : Setoid W) :=
  λ v w => decidable_of_iff (v = w) (by rw [Setoid.bot_def])

instance : DecidableRel (⊤ : Setoid W) := λ _ _ => isTrue trivial

instance [DecidableRel Q] : Decidable (v ∈ Q.cell w) := inferInstanceAs (Decidable (Q v w))

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ p)] : Decidable (Q.cell w ⊆ p) :=
  inferInstanceAs (Decidable (∀ v, Q v w → v ∈ p))

/-! ### Polar questions and decided propositions -/

variable (p) in
/-- The polar question whether `p`: the kernel of its indicator. -/
def polar : Setoid W := Setoid.ker (· ∈ p)

theorem polar_iff : polar p w v ↔ (w ∈ p ↔ v ∈ p) := eq_iff_iff

@[simp] theorem polar_compl : polar pᶜ = polar p :=
  Setoid.ext λ _ _ => by simp only [polar_iff, Set.mem_compl_iff, not_iff_not]

instance [DecidablePred (· ∈ p)] : DecidableRel (polar p) :=
  λ _ _ => decidable_of_iff _ polar_iff.symm

variable (Q p) in
/-- `Q` decides `p`: `p` is constant on the cells of `Q`, so it is a union of cells. The
question `Q` refines the polar question whether `p`. -/
def Decides : Prop := Q ≤ polar p

theorem decides_iff : Q.Decides p ↔ ∀ w v, Q w v → (w ∈ p ↔ v ∈ p) :=
  ⟨λ h _ _ hwv => polar_iff.1 (h hwv), λ h _ _ hwv => polar_iff.2 (h _ _ hwv)⟩

/-- Equivalent worlds agree on a decided proposition. -/
theorem Decides.iff (h : Q.Decides p) (hwv : Q w v) : w ∈ p ↔ v ∈ p :=
  decides_iff.1 h w v hwv

/-- `Q` decides `p` iff each cell entails `p` or entails its negation. -/
theorem decides_iff_forall_cell :
    Q.Decides p ↔ ∀ w, Q.cell w ⊆ p ∨ ∀ v ∈ Q.cell w, v ∉ p := by
  rw [decides_iff]
  refine ⟨λ h w => ?_, λ h w v hwv => ?_⟩
  · by_cases hw : w ∈ p
    · exact Or.inl λ v hv => (h v w hv).2 hw
    · exact Or.inr λ v hv hv' => hw ((h v w hv).1 hv')
  · rcases h v with hall | hnone
    · exact iff_of_true (hall hwv) (hall (Q.refl' v))
    · exact iff_of_false (hnone w hwv) (hnone v (Q.refl' v))

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ p)] : Decidable (Q.Decides p) :=
  decidable_of_iff _ decides_iff.symm

/-- A finer question decides whatever a coarser one does. -/
theorem Decides.mono {Q' : Setoid W} (hQ : Q' ≤ Q) (h : Q.Decides p) : Q'.Decides p :=
  hQ.trans h

/-- The finest question decides every proposition. -/
theorem bot_decides : (⊥ : Setoid W).Decides p := bot_le

/-- The polar question whether `p` decides `p`. -/
theorem polar_decides : (polar p).Decides p := le_rfl

/-- The coarsest question decides only the trivial propositions. -/
theorem top_decides_iff : (⊤ : Setoid W).Decides p ↔ ∀ w v, (w ∈ p ↔ v ∈ p) := by
  simp [decides_iff, Setoid.top_def]

theorem decides_compl_iff : Q.Decides pᶜ ↔ Q.Decides p := by
  simp only [Decides, polar_compl]

theorem Decides.compl (h : Q.Decides p) : Q.Decides pᶜ := decides_compl_iff.2 h

theorem Decides.inter (hp : Q.Decides p) (hq : Q.Decides q) : Q.Decides (p ∩ q) :=
  decides_iff.2 λ _ _ h => and_congr (decides_iff.1 hp _ _ h) (decides_iff.1 hq _ _ h)

theorem Decides.union (hp : Q.Decides p) (hq : Q.Decides q) : Q.Decides (p ∪ q) :=
  decides_iff.2 λ _ _ h => or_congr (decides_iff.1 hp _ _ h) (decides_iff.1 hq _ _ h)

/-- A question decides each of its cells. -/
theorem decides_cell (w : W) : Q.Decides (Q.cell w) :=
  decides_iff.2 λ _ _ hab => ⟨λ h => Q.trans (Q.symm hab) h, λ h => Q.trans hab h⟩

/-- A cell of a question deciding `p` that meets `p` entails it. -/
theorem Decides.cell_subset (h : Q.Decides p) (hw : w ∈ p) : Q.cell w ⊆ p :=
  λ _ hv => (decides_iff.1 h _ _ hv).2 hw

/-! ### The question raised by a family of propositions -/

variable (ps : Finset (Finset W))

/-- The question raised by a family of propositions: the coarsest question deciding each of
them, the meet of their polar questions. -/
def ofProps : Setoid W := ⨅ p ∈ ps, polar (↑p : Set W)

theorem ofProps_iff : ofProps ps w v ↔ ∀ p ∈ ps, (w ∈ p ↔ v ∈ p) := by
  simp only [iInf, Setoid.sInf_iff, Set.forall_mem_range, polar_iff, Finset.mem_coe]

instance [DecidableEq W] : DecidableRel (ofProps ps) :=
  λ _ _ => decidable_of_iff _ (ofProps_iff ps).symm

/-- The question raised by a family decides each of its members. -/
theorem ofProps_decides {p : Finset W} (hp : p ∈ ps) : (ofProps ps).Decides ↑p :=
  iInf₂_le p hp

/-- The question raised by a family is the coarsest question deciding all of its members. -/
theorem le_ofProps_iff : Q ≤ ofProps ps ↔ ∀ p ∈ ps, Q.Decides ↑p :=
  le_iInf₂_iff

end Setoid
