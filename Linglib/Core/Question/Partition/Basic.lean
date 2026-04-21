import Mathlib.Data.Setoid.Partition
import Linglib.Core.Question.Hamblin
import Linglib.Core.Mood.PartitionAsInquiry
import Linglib.Core.Question.Partition.QUD

/-!
# Question — partition predicate, Setoid bridge, QUD bridge
@cite{groenendijk-stokhof-1984} @cite{roberts-2012}
@cite{ciardelli-groenendijk-roelofsen-2018}

Bridge from `Question W` (downward-closed nonempty families of information
states) to **partition-style inquiry** in mathlib's `Setoid.IsPartition`
sense, plus a legacy bridge to the Bool-based `QUD W`.

## Main definitions

- `IsPartition P` — `Setoid.IsPartition (alt P)`. Mention-some,
  intermediate-exhaustive, and conditional-question alternative sets are
  not partitions and so fail this predicate.
- `toSetoid h` — the equivalence relation derived from a partition issue
  (two worlds equivalent iff they share an alternative cell).
- `toQUD h` — bridge to legacy Bool-based `QUD W`. `noncomputable`,
  uses classical decidability of the underlying equivalence.

## Main theorems

- `info_eq_univ`, `pairwiseDisjoint`, `nonempty_of_mem_alt`,
  `sUnion_alt_eq_univ` — partition issues are non-informative and their
  alternative sets are partitions in the standard sense.
- `isPartition_polar`, `isPartition_ofList` — the basic Hamblin
  constructions yield partition issues under nontriviality / disjointness
  / cover hypotheses.
- `toSetoid_fromSetoid` — `Setoid → Question → Setoid` is the identity
  (round-trip with `fromSetoid` from `Core/Mood/PartitionAsInquiry.lean`).
-/

namespace Core

namespace Question

variable {W : Type*}

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
`Core/Mood/PartitionAsInquiry.lean`) and `Question → Setoid` projection
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

end Core
