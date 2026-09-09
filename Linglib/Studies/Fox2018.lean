import Linglib.Semantics.Questions.Closure
import Linglib.Semantics.Exhaustification.InnocentInclusion
import Linglib.Studies.Fox2007
import Linglib.Data.Examples.Fox2018

/-!
# Fox (2018): Partition by Exhaustification

This file formalizes [fox-2018]'s reconstruction of [dayal-1996]'s maximality presupposition as a
matching condition between a question's Hamblin set and the partition it induces. Each member is
exhaustified pointwise into a cell of the contextual partition; Cell Identification demands that
every cell be so reached and Non-Vacuity that every member reach a cell, and
`qpm_iff_partitionsBy` shows that together they say that pointwise exhaustification partitions
the context set. With exhaustification as the strongest true member, Cell Identification is
Dayal's presupposition (`cellIdentification_exhCell_iff`) and Non-Vacuity fails whenever the set
contains the disjunction of two incomparable members, the negative island of higher-order
questions (`not_nonVacuity_exhCell_of_union`), unless a necessity modal intervenes
(`nonVacuity_box`). With exhaustification as [bar-lev-fox-2020]'s cell operator, a question closed
under conjunction and its disjunctive counterpart identify the same cells by different members
(`cell_conj`, `cell_disj`), and the answer set of the paper's revised answer operator is a
singleton for the former but not for the latter: mention-all against mention-some.

## Implementation notes

Questions are Hamblin sets `Set (Set W)` rather than `Question` lower sets, since the paper's sets
are not antichains. The three-location model is a family of atoms `a : ι → Set W` with every
profile realized (`Rich`); `Questions.conjClosure` and `Questions.disjClosure` are the paper's two
denotations; their innocently excludable sets are characterized and the cells read off. Sections 5–7
on the distribution of mention-some enter only through the rows on singular wh-phrases.

## References

* [fox-2018]
* [dayal-1996]
* [spector-2008]
* [bar-lev-fox-2020]
* [fox-hackl-2006]
* [heim-1994]
-/

namespace Fox2018

open Questions Exhaustification Set Data.Examples

variable {W : Type*}

/-! ### Question Partition Matching -/

section Matching

variable (Exh : Set W → Set W) (H : Set (Set W)) (A : Set W)

/-- The contextual partition: the strong answers restricted to the context set. -/
def contextualPartition : Set (Set W) := {C | ∃ w ∈ A, C = strongAnswer H w ∩ A}

/-- Cell Identification: every cell of the contextual partition is the exhaustification of some
member. -/
def CellIdentification : Prop := ∀ C ∈ contextualPartition H A, ∃ p ∈ H, Exh p ∩ A = C

/-- Non-Vacuity: every member exhaustifies to a cell of the contextual partition. -/
def NonVacuity : Prop := ∀ p ∈ H, ∃ C ∈ contextualPartition H A, Exh p ∩ A = C

/-- Question Partition Matching. -/
def QPM : Prop := CellIdentification Exh H A ∧ NonVacuity Exh H A

/-- The pointwise exhaustifications partition the context set. -/
def PartitionsBy : Prop :=
  (∀ p ∈ H, (Exh p ∩ A).Nonempty) ∧
    (∀ p ∈ H, ∀ q ∈ H, Exh p ∩ A = Exh q ∩ A ∨ Disjoint (Exh p ∩ A) (Exh q ∩ A)) ∧
    ∀ w ∈ A, ∃ p ∈ H, w ∈ Exh p

/-- An exhaustifier identifies cells when each of its non-empty values is a strong answer. -/
def IsCellValued : Prop := ∀ p ∈ H, ∀ w ∈ Exh p, Exh p = strongAnswer H w

variable {Exh H A}

theorem mem_contextualPartition {C : Set W} :
    C ∈ contextualPartition H A ↔ ∃ w ∈ A, C = strongAnswer H w ∩ A := Iff.rfl

/-- For a cell-identifying exhaustifier, matching is partitioning. -/
theorem qpm_iff_partitionsBy (h : IsCellValued Exh H) : QPM Exh H A ↔ PartitionsBy Exh H A := by
  constructor
  · rintro ⟨hCI, hNV⟩
    refine ⟨λ p hp => ?_, λ p hp q hq => ?_, λ w hw => ?_⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩, hpw⟩ := hNV p hp
      exact ⟨w, by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩, hpw⟩ := hNV p hp
      obtain ⟨_, ⟨v, hv, rfl⟩, hqv⟩ := hNV q hq
      rw [hpw, hqv]
      rcases strongAnswer_eq_or_disjoint H w v with heq | hdisj
      · exact Or.inl (by rw [heq])
      · exact Or.inr (Disjoint.mono inter_subset_left inter_subset_left hdisj)
    · obtain ⟨p, hp, hpw⟩ := hCI _ ⟨w, hw, rfl⟩
      have : w ∈ Exh p ∩ A := by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩
      exact ⟨p, hp, this.1⟩
  · rintro ⟨hne, -, hcov⟩
    refine ⟨?_, λ p hp => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨p, hp, hwp⟩ := hcov w hw
      exact ⟨p, hp, by rw [h p hp w hwp]⟩
    · obtain ⟨w, hwp, hwA⟩ := hne p hp
      exact ⟨_, ⟨w, hwA, rfl⟩, by rw [h p hp w hwp]⟩

end Matching

/-! ### Dayal's presupposition -/

section Dayal

variable {H : Set (Set W)} {A : Set W}

theorem isCellValued_exhCell : IsCellValued (exhCell H) H :=
  λ _ _ w hw => exhCell_eq_strongAnswer H w hw

/-- With exhaustification as the strongest true member, Cell Identification is Dayal's
presupposition on the context set. -/
theorem cellIdentification_exhCell_iff :
    CellIdentification (exhCell H) H A ↔ ∀ w ∈ A, IsExhaustivelyResolvable H w := by
  constructor
  · intro h w hw
    obtain ⟨p, -, hpw⟩ := h _ ⟨w, hw, rfl⟩
    have : w ∈ exhCell H p ∩ A := by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩
    exact ⟨p, this.1⟩
  · rintro h _ ⟨w, hw, rfl⟩
    obtain ⟨p, hp⟩ := h w hw
    exact ⟨p, hp.1.1, by rw [exhCell_eq_strongAnswer H w hp]⟩

/-- Non-Vacuity: every member is the strongest true member at some context world. -/
theorem nonVacuity_exhCell_iff :
    NonVacuity (exhCell H) H A ↔ ∀ p ∈ H, ∃ w ∈ A, IsStrongestTrueAnswer H w p := by
  constructor
  · intro h p hp
    obtain ⟨_, ⟨w, hw, rfl⟩, hpw⟩ := h p hp
    have : w ∈ exhCell H p ∩ A := by rw [hpw]; exact ⟨self_mem_strongAnswer H w, hw⟩
    exact ⟨w, hw, this.1⟩
  · intro h p hp
    obtain ⟨w, hw, hwp⟩ := h p hp
    exact ⟨_, ⟨w, hw, rfl⟩, by rw [exhCell_eq_strongAnswer H w hwp]⟩

/-- A singular which-question: over pairwise incomparable atoms, Dayal's presupposition is that
exactly one is true. -/
theorem isExhaustivelyResolvable_range_iff {ι : Type*} {a : ι → Set W}
    (ha : ∀ i j, a i ⊆ a j → i = j) (w : W) :
    IsExhaustivelyResolvable (range a) w ↔ ∃! i, w ∈ a i := by
  constructor
  · rintro ⟨_, ⟨⟨i, rfl⟩, hwi⟩, hmin⟩
    exact ⟨i, hwi, λ j hwj => (ha _ _ (hmin ⟨⟨j, rfl⟩, hwj⟩)).symm⟩
  · rintro ⟨i, hwi, huniq⟩
    refine ⟨a i, ⟨⟨i, rfl⟩, hwi⟩, ?_⟩
    rintro _ ⟨⟨j, rfl⟩, hwj⟩
    rw [huniq j hwj]

/-- A plural which-question: closed under conjunction, the set is resolvable wherever some
member is true. -/
theorem isExhaustivelyResolvable_conjClosure {ι : Type*} [Fintype ι] {a : ι → Set W} {w : W}
    (hw : ∃ i, w ∈ a i) : IsExhaustivelyResolvable (conjClosure a) w := by
  classical
  obtain ⟨i, hi⟩ := hw
  let T : Finset ι := Finset.univ.filter (λ i => w ∈ a i)
  have hT : ∀ i, i ∈ T ↔ w ∈ a i := λ i => by simp [T]
  refine ⟨conj a T, ⟨conj_mem_conjClosure ⟨i, (hT i).2 hi⟩, mem_conj.2 λ i hi => (hT i).1 hi⟩, ?_⟩
  rintro _ ⟨⟨S, -, rfl⟩, hwS⟩ v hv
  exact mem_conj.2 λ j hj => mem_conj.1 hv j ((hT j).2 (mem_conj.1 hwS j hj))

/-! ### Negative islands -/

/-- The disjunction of two incomparable members is never the strongest true member. -/
theorem not_isStrongestTrueAnswer_union {q₁ q₂ : Set W} (h₁ : q₁ ∈ H) (h₂ : q₂ ∈ H)
    (h₁₂ : ¬ q₁ ⊆ q₂) (h₂₁ : ¬ q₂ ⊆ q₁) (w : W) : ¬ IsStrongestTrueAnswer H w (q₁ ∪ q₂) := by
  rintro ⟨⟨-, hw⟩, hmin⟩
  rcases hw with hw | hw
  · exact h₂₁ (subset_union_right.trans (hmin ⟨h₁, hw⟩))
  · exact h₁₂ (subset_union_left.trans (hmin ⟨h₂, hw⟩))

/-- A higher-order question under negation contains the negated conjunction of two readings
together with each negated reading, so Non-Vacuity fails: the negative island. -/
theorem not_nonVacuity_exhCell_of_union {q₁ q₂ : Set W} (h₁ : q₁ ∈ H) (h₂ : q₂ ∈ H)
    (hu : q₁ ∪ q₂ ∈ H) (h₁₂ : ¬ q₁ ⊆ q₂) (h₂₁ : ¬ q₂ ⊆ q₁) : ¬ NonVacuity (exhCell H) H A := by
  rw [nonVacuity_exhCell_iff]
  intro h
  obtain ⟨w, -, hw⟩ := h _ hu
  exact not_isStrongestTrueAnswer_union h₁ h₂ h₁₂ h₂₁ w hw

/-- Under a necessity modal, a member that is exactly the modal base of a context world is the
strongest true member there: the island is obviated. -/
theorem isStrongestTrueAnswer_box {W' : Type*} {R : W' → W → Prop} {p : Set W} (hp : p ∈ H)
    {x : W'} (hx : ∀ v, R x v ↔ v ∈ p) :
    IsStrongestTrueAnswer (box H R) x {y | ∀ v, R y v → v ∈ p} := by
  refine ⟨⟨⟨p, hp, rfl⟩, λ v hv => (hx v).1 hv⟩, ?_⟩
  rintro _ ⟨⟨q, -, rfl⟩, hxq⟩ y hy v hyv
  exact hxq v ((hx v).2 (hy v hyv))

/-- Non-Vacuity holds for the necessitated question whenever every member is exactly the modal
base of some context world. -/
theorem nonVacuity_box {W' : Type*} {R : W' → W → Prop} {A : Set W'}
    (h : ∀ p ∈ H, ∃ x ∈ A, ∀ v, R x v ↔ v ∈ p) :
    NonVacuity (exhCell (box H R)) (box H R) A := by
  rw [nonVacuity_exhCell_iff]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, hx, hxp⟩ := h p hp
  exact ⟨x, hx, isStrongestTrueAnswer_box hp hxp⟩

end Dayal

/-! ### Exhaustivity as cell identification -/

section Cell

variable {H : Set (Set W)}

/-- The cell operator identifies cells: each of its non-empty values is a strong answer. -/
theorem cell_eq_strongAnswer {p : Set W} (hp : p ∈ H) {w : W} (hw : w ∈ cell H p) :
    cell H p = strongAnswer H w := by
  ext v
  rw [mem_strongAnswer]
  constructor
  · intro hv q hq
    by_cases hIE : IsInnocentlyExcludable H p q
    · exact ⟨λ hwq => (hw.2.1 q hIE hwq).elim, λ hvq => (hv.2.1 q hIE hvq).elim⟩
    · exact ⟨λ _ => hv.2.2 q ⟨hq, hIE⟩, λ _ => hw.2.2 q ⟨hq, hIE⟩⟩
  · intro hv
    exact ⟨(hv p hp).1 hw.1, λ q hIE hvq => hw.2.1 q hIE ((hv q hIE.1).2 hvq),
      λ r hr => (hv r hr.1).1 (hw.2.2 r hr)⟩

theorem isCellValued_cell : IsCellValued (cell H) H := λ _ hp _ hw => cell_eq_strongAnswer hp hw

/-- With the cell operator, matching is partitioning. -/
theorem qpm_cell_iff_partitionsBy {A : Set W} : QPM (cell H) H A ↔ PartitionsBy (cell H) H A :=
  qpm_iff_partitionsBy isCellValued_cell

/-- Free choice in one step: on [fox-2007]'s diamond the cell operator asserts both independent
alternatives and denies the strongest. -/
theorem cell_diamond {w s n e : Set W} (h : Fox2007.IsDiamond w s n e) :
    cell {w, s, n, e} w = (s ∩ n) \ e := by
  rw [cell_eq_of_iff _ _ λ q hq => h.isInnocentlyExcludable_iff hq]
  have hne : ∀ q ∈ ({w, s, n} : Set (Set W)), q ≠ e := by
    obtain ⟨rfl, hs, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    rintro q (rfl | rfl | rfl) hqe
    · exact ha.2 (hn (hqe ▸ Or.inl ha.1))
    · exact ha.2 (hn (hqe ▸ ha.1))
    · exact hb.2 (hs (hqe ▸ hb.1))
  ext x
  constructor
  · rintro ⟨-, hx⟩
    exact ⟨⟨(hx s (by simp)).2 (hne s (by simp)), (hx n (by simp)).2 (hne n (by simp))⟩,
      λ hxe => (hx e (by simp)).1 hxe rfl⟩
  · rintro ⟨⟨hxs, hxn⟩, hxe⟩
    refine ⟨h.union ▸ Or.inl hxs, λ q hq => ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    obtain h1 | h1 | h1 | h1 := hq <;> subst q
    · exact iff_of_true (h.union ▸ Or.inl hxs) (hne _ (by simp))
    · exact iff_of_true hxs (hne _ (by simp))
    · exact iff_of_true hxn (hne _ (by simp))
    · exact iff_of_false hxe λ h' => h' rfl

/-- The cell operator agrees with [fox-2007]'s recursive exhaustification wherever free choice
is consistent. -/
theorem cell_eq_exh₂ {w s n e : Set W} (h : Fox2007.IsDiamond w s n e)
    (hne : ((s ∩ n) \ e).Nonempty) : cell {w, s, n, e} w = Fox2007.exh₂ {w, s, n, e} w := by
  rw [cell_diamond h, h.exh₂_eq hne]

end Cell

/-! ### Mention-some and mention-all -/

section Closures

variable {ι : Type*} {a : ι → Set W}

/-- Every profile is realized by some world. -/
def Rich (a : ι → Set W) : Prop := ∀ T : Finset ι, ∃ w, profile a w = ↑T

/-- The worlds with a given profile: a cell of the logical partition of either closure. -/
def profileCell (a : ι → Set W) (T : Finset ι) : Set W := {v | profile a v = ↑T}

theorem mem_profileCell {T : Finset ι} {v : W} : v ∈ profileCell a T ↔ profile a v = ↑T := Iff.rfl

/-- Both closures induce the profile cells. -/
theorem strongAnswer_conjClosure_eq {T : Finset ι} {w : W} (hw : profile a w = ↑T) :
    strongAnswer (conjClosure a) w = profileCell a T := by
  ext v
  rw [mem_strongAnswer_conjClosure_iff, hw, mem_profileCell]

theorem strongAnswer_disjClosure_eq {T : Finset ι} {w : W} (hw : profile a w = ↑T) :
    strongAnswer (disjClosure a) w = profileCell a T := by
  ext v
  rw [mem_strongAnswer_disjClosure_iff, hw, mem_profileCell]

/-- Under either closure, a world lies below another iff its profile is included. -/
theorem leALT_conjClosure_iff {u v : W} :
    (u ≤[conjClosure a] v) ↔ profile a u ⊆ profile a v := by
  constructor
  · intro h i hi
    exact h _ (conj_singleton (a := a) i ▸ conj_mem_conjClosure ⟨i, Finset.mem_singleton_self i⟩) hi
  · rintro h _ ⟨S, -, rfl⟩ hu
    exact mem_conj_iff_subset.2 ((mem_conj_iff_subset.1 hu).trans h)

theorem leALT_disjClosure_iff {u v : W} :
    (u ≤[disjClosure a] v) ↔ profile a u ⊆ profile a v := by
  constructor
  · intro h i hi
    exact h _ (disj_singleton (a := a) i ▸ disj_mem_disjClosure ⟨i, Finset.mem_singleton_self i⟩) hi
  · rintro h _ ⟨S, -, rfl⟩ hu
    obtain ⟨i, hi, hui⟩ := mem_disj.1 hu
    exact mem_disj.2 ⟨i, hi, h hui⟩

variable (hrich : Rich a)
include hrich

theorem conj_subset_conj_iff {S T : Finset ι} : conj a T ⊆ conj a S ↔ S ⊆ T := by
  constructor
  · intro h i hi
    obtain ⟨w, hw⟩ := hrich T
    have := mem_conj_iff_subset.1 (h (mem_conj_iff_subset.2 (by rw [hw]))) (Finset.mem_coe.2 hi)
    rw [hw] at this
    exact Finset.mem_coe.1 this
  · exact λ h _ hv => mem_conj.2 λ i hi => mem_conj.1 hv i (h hi)

theorem disj_subset_disj_iff {S T : Finset ι} : disj a S ⊆ disj a T ↔ S ⊆ T := by
  constructor
  · intro h i hi
    obtain ⟨w, hw⟩ := hrich ({i} : Finset ι)
    have hwi : w ∈ a i := by
      change i ∈ profile a w
      rw [hw]
      exact Finset.mem_coe.2 (Finset.mem_singleton_self i)
    obtain ⟨j, hj, hwj⟩ := mem_disj.1 (h (mem_disj.2 ⟨i, hi, hwi⟩))
    have : j ∈ profile a w := hwj
    rw [hw, Finset.coe_singleton, mem_singleton_iff] at this
    exact this ▸ hj
  · rintro h _ hv
    obtain ⟨i, hi, hvi⟩ := mem_disj.1 hv
    exact mem_disj.2 ⟨i, h hi, hvi⟩

/-- Given the conjunction over a group, a member is innocently excludable iff its group is not
included: the paper's computation for the low-type question. -/
theorem isInnocentlyExcludable_conj_iff [Fintype ι] {S T : Finset ι} (hS : S.Nonempty) :
    IsInnocentlyExcludable (conjClosure a) (conj a T) (conj a S) ↔ ¬ S ⊆ T := by
  obtain ⟨w₀, hw₀⟩ := hrich T
  have hw₀T : w₀ ∈ conj a T := mem_conj_iff_subset.2 (by rw [hw₀])
  constructor
  · exact λ hIE hST => not_isInnocentlyExcludable_of_phi_subset conjClosure_finite ⟨w₀, hw₀T⟩
      ((conj_subset_conj_iff hrich).2 hST) hIE
  · intro hST
    refine .of_forall_subset_or_notMem (conj_mem_conjClosure hS) hw₀T ?_ ?_
    · rw [mem_conj_iff_subset, hw₀]
      exact λ h => hST (Finset.coe_subset.1 h)
    · rintro _ ⟨U, -, rfl⟩
      by_cases hUT : U ⊆ T
      · exact Or.inl ((conj_subset_conj_iff hrich).2 hUT)
      · right
        rw [mem_conj_iff_subset, hw₀]
        exact λ h => hUT (Finset.coe_subset.1 h)

/-- The minimal worlds given the disjunction over a group: the sole witnesses of its members. -/
theorem mem_exhMW_disjClosure_iff {T : Finset ι} {u : W} :
    u ∈ exhMW (disjClosure a) (disj a T) ↔ ∃ i ∈ T, profile a u = ↑({i} : Finset ι) := by
  have hsing : ∀ {i : ι} {v : W}, profile a v = ↑({i} : Finset ι) → v ∈ a i := λ {i v} hv => by
    change i ∈ profile a v
    rw [hv]
    exact Finset.mem_coe.2 (Finset.mem_singleton_self i)
  constructor
  · rintro ⟨hu, hmin⟩
    obtain ⟨i, hi, hui⟩ := mem_disj.1 hu
    obtain ⟨v, hv⟩ := hrich ({i} : Finset ι)
    have hvu : v ≤[disjClosure a] u := leALT_disjClosure_iff.2 (by
      rw [hv, Finset.coe_singleton]
      exact singleton_subset_iff.2 hui)
    have huv : u ≤[disjClosure a] v :=
      by_contra λ h => hmin ⟨v, mem_disj.2 ⟨i, hi, hsing hv⟩, hvu, h⟩
    refine ⟨i, hi, subset_antisymm ?_ ?_⟩
    · rw [← hv]
      exact leALT_disjClosure_iff.1 huv
    · rw [Finset.coe_singleton]
      exact singleton_subset_iff.2 hui
  · rintro ⟨i, hi, hu⟩
    refine ⟨mem_disj.2 ⟨i, hi, hsing hu⟩, ?_⟩
    rintro ⟨v, hv, hvu, hnuv⟩
    obtain ⟨j, -, hvj⟩ := mem_disj.1 hv
    have hj : j ∈ profile a v := hvj
    have hji : j ∈ profile a u := leALT_disjClosure_iff.1 hvu hj
    rw [hu, Finset.coe_singleton, mem_singleton_iff] at hji
    subst hji
    refine hnuv (leALT_disjClosure_iff.2 ?_)
    rw [hu, Finset.coe_singleton]
    exact singleton_subset_iff.2 hj

/-- Given the disjunction over a group, a member is innocently excludable iff its group is
disjoint from it: the paper's computation for the high-type question. -/
theorem isInnocentlyExcludable_disj_iff {S T : Finset ι} (hS : S.Nonempty) :
    IsInnocentlyExcludable (disjClosure a) (disj a T) (disj a S) ↔ Disjoint S T := by
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (disj_mem_disjClosure hS),
    Finset.disjoint_left]
  constructor
  · intro h i hiS hiT
    obtain ⟨v, hv⟩ := hrich ({i} : Finset ι)
    refine h ((mem_exhMW_disjClosure_iff hrich).2 ⟨i, hiT, hv⟩) (mem_disj.2 ⟨i, hiS, ?_⟩)
    change i ∈ profile a v
    rw [hv]
    exact Finset.mem_coe.2 (Finset.mem_singleton_self i)
  · intro h u hu huS
    obtain ⟨i, hiT, hui⟩ := (mem_exhMW_disjClosure_iff hrich).1 hu
    obtain ⟨j, hjS, huj⟩ := mem_disj.1 huS
    have : j ∈ profile a u := huj
    rw [hui, Finset.coe_singleton, mem_singleton_iff] at this
    exact h hjS (this ▸ hiT)

/-- For the conjunctive question, the member for a group identifies the cell of that profile. -/
theorem cell_conj [Fintype ι] (T : Finset ι) :
    cell (conjClosure a) (conj a T) = profileCell a T := by
  rw [conjClosure, cell_image_eq _ λ S hS => isInnocentlyExcludable_conj_iff hrich hS]
  ext x
  simp only [mem_ofPred_eq, mem_conj_iff_subset, not_not, mem_profileCell]
  constructor
  · rintro ⟨-, h⟩
    ext i
    have := h {i} ⟨i, Finset.mem_singleton_self i⟩
    rw [Finset.coe_singleton, singleton_subset_iff, Finset.singleton_subset_iff] at this
    exact this.trans Finset.mem_coe.symm
  · intro hx
    exact ⟨by rw [hx], λ S _ => by rw [hx, Finset.coe_subset]⟩

/-- For the disjunctive question, the member for a group identifies the same cell. -/
theorem cell_disj {T : Finset ι} (hT : T.Nonempty) :
    cell (disjClosure a) (disj a T) = profileCell a T := by
  rw [disjClosure, cell_image_eq _ λ S hS => isInnocentlyExcludable_disj_iff hrich hS]
  ext x
  simp only [mem_ofPred_eq, mem_disj, Finset.not_disjoint_iff, mem_profileCell]
  constructor
  · rintro ⟨-, h⟩
    ext i
    have := h {i} ⟨i, Finset.mem_singleton_self i⟩
    simp only [Finset.mem_singleton, exists_eq_left] at this
    exact this.trans Finset.mem_coe.symm
  · intro hx
    obtain ⟨i, hi⟩ := hT
    have hmem : ∀ j, x ∈ a j ↔ j ∈ T := λ j => by
      change j ∈ profile a x ↔ j ∈ T
      rw [hx, Finset.mem_coe]
    refine ⟨⟨i, hi, (hmem i).2 hi⟩, λ S _ => ?_⟩
    simp only [hmem]

/-- The revised answer operator: the true members entailing the cell identifier. -/
def ans (Exh : Set W → Set W) (H : Set (Set W)) (w : W) : Set (Set W) :=
  {q ∈ H | w ∈ q ∧ ∀ p ∈ H, w ∈ Exh p → q ⊆ p}

/-- Mention-all: the conjunctive question's answer set is the conjunction over the profile. -/
theorem ans_conjClosure [Fintype ι] {T : Finset ι} (hT : T.Nonempty) {w : W} (hw : profile a w = ↑T) :
    ans (cell (conjClosure a)) (conjClosure a) w = {conj a T} := by
  ext q
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨⟨S, -, rfl⟩, hwS, h⟩
    have h1 : S ⊆ T := by
      have := mem_conj_iff_subset.1 hwS
      rw [hw] at this
      exact Finset.coe_subset.1 this
    have h2 : T ⊆ S := (conj_subset_conj_iff hrich).1
      (h _ (conj_mem_conjClosure hT) (by rw [cell_conj hrich T]; exact hw))
    rw [Finset.Subset.antisymm h1 h2]
  · rintro rfl
    refine ⟨conj_mem_conjClosure hT, mem_conj_iff_subset.2 (by rw [hw]), ?_⟩
    rintro _ ⟨U, hU, rfl⟩ hwU
    rw [cell_conj hrich U] at hwU
    have hwU' : profile a w = ↑U := hwU
    rw [hw, Finset.coe_inj] at hwU'
    subst hwU'
    exact subset_rfl

/-- Mention-some: the disjunctive question's answer set is every disjunction over a sub-group of
the profile. -/
theorem ans_disjClosure {T : Finset ι} (hT : T.Nonempty) {w : W} (hw : profile a w = ↑T) :
    ans (cell (disjClosure a)) (disjClosure a) w = disj a '' {S | S.Nonempty ∧ S ⊆ T} := by
  ext q
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, -, h⟩
    exact ⟨S, ⟨hS, (disj_subset_disj_iff hrich).1
      (h _ (disj_mem_disjClosure hT) (by rw [cell_disj hrich hT]; exact hw))⟩, rfl⟩
  · rintro ⟨S, ⟨⟨i, hi⟩, hST⟩, rfl⟩
    refine ⟨disj_mem_disjClosure ⟨i, hi⟩, mem_disj.2 ⟨i, hi, ?_⟩, ?_⟩
    · change i ∈ profile a w
      rw [hw]
      exact Finset.mem_coe.2 (hST hi)
    · rintro _ ⟨U, hU, rfl⟩ hwU
      rw [cell_disj hrich hU] at hwU
      have hwU' : profile a w = ↑U := hwU
      rw [hw, Finset.coe_inj] at hwU'
      subst hwU'
      exact (disj_subset_disj_iff hrich).2 hST

/-- With two or more true atoms, the disjunctive question's answer set has more than one
member: the mention-some reading. -/
theorem not_subsingleton_ans_disjClosure {T : Finset ι} (hT : 1 < T.card) {w : W}
    (hw : profile a w = ↑T) : ¬ (ans (cell (disjClosure a)) (disjClosure a) w).Subsingleton := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hT
  rw [ans_disjClosure hrich ⟨i, hi⟩ hw]
  intro h
  have := h ⟨{i}, ⟨⟨i, Finset.mem_singleton_self i⟩, Finset.singleton_subset_iff.2 hi⟩, rfl⟩
    ⟨T, ⟨⟨i, hi⟩, subset_rfl⟩, rfl⟩
  have := (disj_subset_disj_iff hrich).1 this.ge
  exact hij (Finset.mem_singleton.1 (this hj)).symm

end Closures

/-! ### The data -/

/-- A question of the data: whether it is a degree question, whether negation and a modal
intervene, whether the wh-phrase is singular, and whether the island reading is blocked. -/
structure Row where
  negation : Bool
  modal : Bool
  singular : Bool
  blocked : Bool
  deriving DecidableEq

def yesNoTable : List (String × Bool) := [("yes", true), ("no", false)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let n ← ex.parse? "negation" yesNoTable
  let m ← ex.parse? "modal" yesNoTable
  let s ← ex.parse? "number"
    [("singular", true), ("plural", false), ("neutral", false), ("na", false)]
  let b ← ex.parse? "blocked" yesNoTable
  pure ⟨n, m, s, b⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The islands of the data: a reading is blocked under negation without an intervening modal,
or for a singular wh-phrase. -/
theorem rows_predicted :
    ∀ r ∈ rows, (r.blocked = true ↔ (r.negation = true ∧ r.modal = false) ∨ r.singular = true) := by
  decide

end Fox2018
