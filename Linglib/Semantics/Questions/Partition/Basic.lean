import Mathlib.Data.Setoid.Partition
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Partition.QUD

/-!
# Partition questions

The correspondence between partition-style inquiry
([groenendijk-stokhof-1984]'s question semantics, a `Setoid W`) and
the more general inquisitive content `Question W`
([ciardelli-groenendijk-roelofsen-2018]). The embedding is one-way:
every partition is an issue whose alternatives are its cells, but
mention-some, intermediate-exhaustive, and conditional-question
alternative sets are non-disjoint or non-exhaustive and are not the
classes of any equivalence relation.

## Main definitions

- `fromSetoid r` — the issue whose alternatives are the cells of `r`.
- `IsPartition P` — `Setoid.IsPartition (alt P)`.
- `toSetoid h` — the equivalence relation of a partition issue.
- `toQUD h` — bridge to the legacy Bool-based `QUD W`.

## Main theorems

- `fromSetoid_le_iff` — the embedding is an order embedding: partition
  refinement is issue entailment.
- `info_fromSetoid`, `info_eq_univ` — partition issues are
  non-informative.
- `isPartition_polar`, `isPartition_ofList` — the basic Hamblin
  constructions yield partition issues under nontriviality /
  disjointness / cover hypotheses.
- `toSetoid_fromSetoid` — `Setoid → Question → Setoid` is the
  identity.
-/


namespace Question

variable {W : Type*}

/-! ### The `Setoid → Question` embedding -/

/-- The issue raised by a setoid `r`: a state `q` resolves it iff `q`
is empty or contained in an `r`-equivalence class. -/
def fromSetoid (r : Setoid W) : Question W :=
  ofLowerSet {q | q = ∅ ∨ ∃ c ∈ r.classes, q ⊆ c} (Or.inl rfl) <| by
    rintro a b hba (rfl | ⟨c, hc, hac⟩)
    · exact Or.inl (Set.subset_empty_iff.mp hba)
    · exact Or.inr ⟨c, hc, hba.trans hac⟩

/-- Partition-derived issues are non-informative: they raise an issue
but supply no information. -/
theorem info_fromSetoid (r : Setoid W) : (fromSetoid r).info = Set.univ := by
  ext w
  simp only [info, fromSetoid, props_ofLowerSet, Set.mem_sUnion, Set.mem_setOf_eq,
             Set.mem_univ, iff_true]
  refine ⟨{x | r x w}, ?_, ?_⟩
  · exact Or.inr ⟨{x | r x w}, Setoid.mem_classes r w, subset_rfl⟩
  · exact Setoid.refl' r w

/-- A setoid with two distinct cells yields an inquisitive content; the
trivial partition yields a declarative. -/
theorem isInquisitive_fromSetoid_of_two_classes
    (r : Setoid W) (w₁ w₂ : W) (hne : ¬ r w₁ w₂) :
    (fromSetoid r).isInquisitive := by
  show (fromSetoid r).info ∉ (fromSetoid r).props
  rw [info_fromSetoid]
  rintro (huniv | ⟨c, hc, hsub⟩)
  · exact (huniv ▸ Set.mem_univ w₁ : w₁ ∈ (∅ : Set W)).elim
  · obtain ⟨v, hv, rfl⟩ := hc
    have h1 : r w₁ v := hsub (Set.mem_univ w₁)
    have h2 : r w₂ v := hsub (Set.mem_univ w₂)
    exact hne (Setoid.trans' r h1 (Setoid.symm' r h2))

/-- The embedding reflects the order: a setoid is finer than another
iff its issue entails the other's — Groenendijk–Stokhof's "partition
refinement is question entailment". -/
theorem fromSetoid_le_iff (r₁ r₂ : Setoid W) :
    fromSetoid r₁ ≤ fromSetoid r₂ ↔ r₁ ≤ r₂ := by
  refine ⟨?_, ?_⟩
  · -- the doubleton {x, y} resolves fromSetoid r₁, hence fromSetoid r₂
    intro hle x y hxy
    have hpair : ({x, y} : Set W) ∈ fromSetoid r₁ := by
      refine Or.inr ⟨{z | r₁ z x}, Setoid.mem_classes r₁ x, ?_⟩
      rintro z (rfl | hz)
      · exact Setoid.refl' r₁ z
      · rw [Set.mem_singleton_iff] at hz; subst hz
        exact Setoid.symm' r₁ hxy
    have hpair' : ({x, y} : Set W) ∈ fromSetoid r₂ := hle hpair
    rcases hpair' with hempty | ⟨c, hc, hsub⟩
    · have : x ∈ ({x, y} : Set W) := Set.mem_insert x _
      rw [hempty] at this; exact this.elim
    · obtain ⟨v, _hv, rfl⟩ := hc
      have hxv : r₂ x v := hsub (Set.mem_insert x _)
      have hyv : r₂ y v := hsub (Set.mem_insert_of_mem x rfl)
      exact Setoid.trans' r₂ hxv (Setoid.symm' r₂ hyv)
  · -- a state in an r₁-cell is in the surrounding r₂-cell
    intro hle q hq
    rcases hq with hempty | ⟨c, hc, hqc⟩
    · subst hempty; exact (fromSetoid r₂).contains_empty
    · obtain ⟨v, _hv, rfl⟩ := hc
      refine Or.inr ⟨{z | r₂ z v}, Setoid.mem_classes r₂ v, ?_⟩
      intro z hz
      exact hle (hqc hz)

/-- Monotonicity of the embedding. -/
theorem fromSetoid_mono {r₁ r₂ : Setoid W} (h : r₁ ≤ r₂) :
    fromSetoid r₁ ≤ fromSetoid r₂ :=
  (fromSetoid_le_iff r₁ r₂).mpr h

/-- Every alternative of `fromSetoid r` is the empty state or a cell of
`r` (the empty case only when `W` is empty). -/
theorem alt_fromSetoid_subset_classes (r : Setoid W) {p : Set W}
    (hp : p ∈ alt (fromSetoid r)) : p = ∅ ∨ p ∈ r.classes := by
  obtain ⟨hp_props, hmax⟩ := hp
  rcases hp_props with hempty | ⟨c, hc, hpc⟩
  · exact Or.inl hempty
  · have hc_props : c ∈ (fromSetoid r).props :=
      Or.inr ⟨c, hc, subset_rfl⟩
    have heq : p = c := hmax c hc_props hpc
    exact Or.inr (heq ▸ hc)

/-- Each cell of `r` is an alternative of `fromSetoid r`. -/
theorem class_mem_alt_fromSetoid (r : Setoid W) {c : Set W}
    (hc : c ∈ r.classes) : c ∈ alt (fromSetoid r) := by
  refine ⟨Or.inr ⟨c, hc, subset_rfl⟩, ?_⟩
  obtain ⟨v, _hv, rfl⟩ := hc
  intro q hq hcq
  rcases hq with hempty | ⟨c', hc', hqc'⟩
  · have hv : v ∈ ({x | r x v} : Set W) := Setoid.refl' r v
    rw [hempty] at hcq
    exact (hcq hv).elim
  · obtain ⟨v', _hv', rfl⟩ := hc'
    have hvv' : r v v' := hqc' (hcq (Setoid.refl' r v))
    apply Set.Subset.antisymm hcq
    intro x hxq
    have hxv' : r x v' := hqc' hxq
    exact Setoid.trans' r hxv' (Setoid.symm' r hvv')

/-! ### `IsPartition` predicate -/

/-- An issue is a **partition** iff its alternative set is a partition
    of `W` in mathlib's `Setoid.IsPartition` sense: no empty
    alternative, and every world lies in a unique alternative. The
    Groenendijk–Stokhof partition shape. -/
def IsPartition (P : Question W) : Prop :=
  Setoid.IsPartition (alt P)

namespace IsPartition

/-- Partition issues are **non-informative**: every world is covered by
    some alternative, hence by some resolving proposition, so
    `info P = Set.univ`. -/
@[simp] theorem info_eq_univ {P : Question W} (h : P.IsPartition) :
    info P = Set.univ := by
  refine Set.eq_univ_of_forall fun w => ?_
  obtain ⟨p, ⟨hpAlt, hwp⟩, _⟩ := h.2 w
  exact ⟨p, alt_subset_props P hpAlt, hwp⟩

/-- Alternatives of a partition issue are pairwise disjoint. Direct
    inheritance from mathlib's `Setoid.IsPartition.pairwiseDisjoint`. -/
theorem pairwiseDisjoint {P : Question W} (h : P.IsPartition) :
    (alt P).PairwiseDisjoint id :=
  Setoid.IsPartition.pairwiseDisjoint h

/-- Alternatives of a partition issue are nonempty. Mathlib's
    `Setoid.nonempty_of_mem_partition` specialized to `Question`. -/
theorem nonempty_of_mem_alt {P : Question W} (h : P.IsPartition)
    {p : Set W} (hp : p ∈ alt P) : p.Nonempty :=
  Setoid.nonempty_of_mem_partition h hp

/-- The union of a partition issue's alternatives is the whole universe. -/
theorem sUnion_alt_eq_univ {P : Question W} (h : P.IsPartition) :
    ⋃₀ alt P = Set.univ :=
  Setoid.IsPartition.sUnion_eq_univ h

end IsPartition

/-! ### `toSetoid` — equivalence relation from a partition issue -/

/-- The setoid derived from a partition issue: two worlds are
    equivalent iff they lie in the same alternative cell. Built from
    mathlib's `Setoid.mkClasses` on the alternative set. -/
def toSetoid {P : Question W} (h : P.IsPartition) : Setoid W :=
  Setoid.mkClasses (alt P) h.2

/-- The equivalence classes of `toSetoid h` are exactly the
    alternatives of `P`. The defining roundtrip property of
    `Setoid.mkClasses`. -/
@[simp] theorem classes_toSetoid {P : Question W} (h : P.IsPartition) :
    (toSetoid h).classes = alt P :=
  Setoid.classes_mkClasses (alt P) h

/-- Two worlds are related under `toSetoid h` iff they share an
    alternative cell — the linguistic reading of the underlying
    equivalence relation. -/
theorem toSetoid_rel_iff {P : Question W} (h : P.IsPartition) (w v : W) :
    (toSetoid h) w v ↔ ∃ p ∈ alt P, w ∈ p ∧ v ∈ p := by
  rw [Setoid.rel_iff_exists_classes, classes_toSetoid h]

/-! ### `toQUD` — bridge to the legacy Bool-based QUD -/

/-- Bridge to legacy Bool-based `QUD W`: two worlds get the same
    answer iff they share an alternative cell. `noncomputable` —
    decidability of the underlying equivalence is supplied
    classically. -/
noncomputable def toQUD {P : Question W} (h : P.IsPartition) : QUD W := by
  classical
  exact { toSetoid := toSetoid h, decR := fun w v => Classical.dec _ }

/-- `toQUD`'s relation holds iff the two worlds share an alternative cell. -/
theorem toQUD_r_iff {P : Question W} (h : P.IsPartition) (w v : W) :
    (toQUD h).r w v ↔ ∃ p ∈ alt P, w ∈ p ∧ v ∈ p :=
  toSetoid_rel_iff h w v

/-- `toQUD`'s `sameAnswer` is true iff the two worlds share a cell. -/
theorem toQUD_sameAnswer_iff {P : Question W} (h : P.IsPartition) (w v : W) :
    (toQUD h).sameAnswer w v = true ↔ ∃ p ∈ alt P, w ∈ p ∧ v ∈ p := by
  rw [QUD.sameAnswer_eq_true_iff]
  exact toQUD_r_iff h w v

/-- The cell of a world under `toQUD h` is in `alt P`. -/
theorem cell_toQUD_mem_alt {P : Question W} (h : P.IsPartition) (w : W) :
    (toQUD h).cell w ∈ alt P := by
  obtain ⟨p, ⟨hpAlt, hwp⟩, huniq⟩ := h.2 w
  rw [show (toQUD h).cell w = p from ?_]
  · exact hpAlt
  ext v
  rw [QUD.mem_cell_iff_r, toQUD_r_iff]
  refine ⟨?_, fun hvp => ⟨p, hpAlt, hwp, hvp⟩⟩
  rintro ⟨q, hqAlt, hwq, hvq⟩
  exact ((huniq q ⟨hqAlt, hwq⟩).trans (huniq p ⟨hpAlt, hwp⟩).symm) ▸ hvq

/-- A world lies in its own `toQUD` cell. -/
theorem mem_cell_toQUD {P : Question W} (h : P.IsPartition) (w : W) :
    w ∈ (toQUD h).cell w :=
  QUD.cell_self _ w

/-- The `toQUD` cell of any world in an alternative `p` is exactly `p`. -/
theorem cell_toQUD_eq {P : Question W} (h : P.IsPartition) {p : Set W}
    (hpAlt : p ∈ alt P) {w : W} (hwp : w ∈ p) :
    (toQUD h).cell w = p := by
  obtain ⟨q, ⟨hqAlt, hwq⟩, huniq⟩ := h.2 w
  have hpq : p = q := huniq p ⟨hpAlt, hwp⟩
  ext v
  rw [QUD.mem_cell_iff_r, toQUD_r_iff]
  refine ⟨?_, fun hvp => ⟨p, hpAlt, hwp, hvp⟩⟩
  rintro ⟨r, hrAlt, hwr, hvr⟩
  exact ((huniq r ⟨hrAlt, hwr⟩).trans hpq.symm) ▸ hvr

/-! ### Round-trip with `fromSetoid`

The `Setoid → Question` embedding (`fromSetoid`, in
`Semantics/Questions/Partition/Basic.lean`) and `Question → Setoid` projection
(`toSetoid`) compose to the identity on partition-shaped issues. -/

/-- Under `Nonempty W`, `fromSetoid r` is a partition issue. The
    nonemptiness assumption rules out the degenerate `∅`-alternative
    that would otherwise appear when `W` is empty. -/
theorem isPartition_fromSetoid [Nonempty W] (r : Setoid W) :
    (fromSetoid r).IsPartition := by
  refine ⟨?_, ?_⟩
  · intro hempty
    obtain ⟨w⟩ := ‹Nonempty W›
    have heq : (∅ : Set W) = {x | r x w} :=
      hempty.2 _ (Or.inr ⟨_, Setoid.mem_classes r w, subset_rfl⟩)
        (Set.empty_subset _)
    exact Set.notMem_empty w (heq ▸ Setoid.refl' r w)
  · intro w
    refine ⟨{x | r x w},
      ⟨class_mem_alt_fromSetoid r (Setoid.mem_classes r w), Setoid.refl' r w⟩,
      ?_⟩
    rintro c' ⟨hc'alt, hwc'⟩
    rcases alt_fromSetoid_subset_classes r hc'alt with hempty | hclass
    · exact absurd (hempty ▸ hwc') (Set.notMem_empty w)
    · obtain ⟨v, _, rfl⟩ := hclass
      ext x
      exact ⟨fun hx => Setoid.trans' r hx (Setoid.symm' r hwc'),
             fun hx => Setoid.trans' r hx hwc'⟩

/-- **Round-trip**: the setoid derived from a partition issue built
    from a setoid recovers the original setoid. The `Setoid → Question →
    Setoid` direction of the partition–setoid correspondence. -/
theorem toSetoid_fromSetoid [Nonempty W] (r : Setoid W) :
    toSetoid (isPartition_fromSetoid r) = r := by
  apply Setoid.classes_inj.mpr
  rw [classes_toSetoid]
  ext c
  refine ⟨?_, class_mem_alt_fromSetoid r⟩
  intro hc
  rcases alt_fromSetoid_subset_classes r hc with hempty | hclass
  · exact (((isPartition_fromSetoid r).1) (hempty ▸ hc)).elim
  · exact hclass

/-! ### `IsPartition` for the basic Hamblin constructions -/

/-- `Question.polar p` is a partition issue when `p` is non-trivial: the
    two alternatives `p` and `pᶜ` partition `W` by LEM. -/
theorem isPartition_polar {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    (polar p).IsPartition := by
  rw [IsPartition, alt_polar_of_nontrivial hne hnu]
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact hne h.symm
    · rw [Set.mem_singleton_iff] at h
      exact hnu (Set.compl_empty_iff.mp h.symm)
  · classical
    intro w
    by_cases hwp : w ∈ p
    · refine ⟨p, ⟨Set.mem_insert _ _, hwp⟩, ?_⟩
      rintro q ⟨hq, hwq⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · rfl
      · exact (hwq hwp).elim
    · refine ⟨pᶜ, ⟨Set.mem_insert_of_mem _ rfl, hwp⟩, ?_⟩
      rintro q ⟨hq, hwq⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact (hwp hwq).elim
      · rfl

/-- `Question.ofList L` is a partition issue when `L` is a nonempty list of
    pairwise-disjoint nonempty cells that exhaust `W`. -/
theorem isPartition_ofList {L : List (Set W)} (hL : L ≠ [])
    (hdisj : ∀ p₁ ∈ L, ∀ p₂ ∈ L, p₁ ≠ p₂ → Disjoint p₁ p₂)
    (hne : ∀ p ∈ L, p ≠ ∅)
    (hcover : ∀ w : W, ∃ p ∈ L, w ∈ p) :
    (ofList L).IsPartition := by
  rw [IsPartition, alt_ofList_of_pairwise_disjoint_nonempty L hL hdisj hne]
  refine ⟨?_, ?_⟩
  · intro h
    rw [Set.mem_setOf_eq] at h
    exact hne ∅ h rfl
  · intro w
    obtain ⟨p, hpL, hwp⟩ := hcover w
    refine ⟨p, ⟨hpL, hwp⟩, ?_⟩
    rintro q ⟨hqL, hwq⟩
    rw [Set.mem_setOf_eq] at hqL
    by_contra hne_qp
    exact Set.disjoint_left.mp (hdisj q hqL p hpL hne_qp) hwq hwp

end Question

