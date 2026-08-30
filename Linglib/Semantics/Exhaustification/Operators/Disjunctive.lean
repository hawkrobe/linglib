import Linglib.Semantics.Exhaustification.Operators.InnocentInclusion
import Mathlib.Data.Finset.Card

/-!
# Exhaustifying a disjunction whose alternatives are its sub-disjunctions

A disjunction `⋃ i ∈ I, p i` whose alternatives are disjunctions over subsets of `I` — sub-
disjunctions but no conjunctions — strengthens under `exhIEII` to their conjunction, provided
some world verifies each disjunct alone and some world verifies all of them: nothing is
innocently excludable, since a single-disjunct world is minimal, and everything is innocently
includable, since the cell is consistent. With all sub-disjunctions present the result is the
conjunction of the disjuncts; with only the disjunctions over subsets of size `m` it is that
at least `|I| + 1 - m` disjuncts hold. This is the generalization behind free choice without
a conjunctive alternative and behind the implicature account of homogeneity, where the
disjuncts are the atoms of a plurality and pruning to the size-`m` alternatives gives the
non-maximal readings.

## References

* [bar-lev-2021]
* [bar-lev-fox-2020]
-/

namespace Exhaustification

variable {World ι : Type*} (I : Finset ι) (p : ι → Set World)

/-- The disjunction over a subset. -/
def subDisj (S : Finset ι) : Set World := ⋃ i ∈ S, p i

/-- The disjunction of the family over `I`. -/
abbrev disj : Set World := subDisj p I

/-- The disjunctions over the nonempty subsets of `I`. -/
def subDisjs : Set (Set World) := {q | ∃ S ⊆ I, S.Nonempty ∧ q = subDisj p S}

/-- The disjunction over `I` together with the disjunctions over its subsets of size `m`. -/
def subDisjsOfCard (m : ℕ) : Set (Set World) :=
  insert (disj I p) {q | ∃ S ⊆ I, S.card = m ∧ q = subDisj p S}

variable {I p}

@[simp] theorem mem_subDisj {S : Finset ι} {w : World} :
    w ∈ subDisj p S ↔ ∃ i ∈ S, w ∈ p i := by
  simp [subDisj]

theorem subDisjsOfCard_subset_subDisjs (hI : I.Nonempty) {m : ℕ} (hm : 0 < m) :
    subDisjsOfCard I p m ⊆ subDisjs I p := by
  rintro q (rfl | ⟨S, hS, hcard, rfl⟩)
  · exact ⟨I, le_rfl, hI, rfl⟩
  · exact ⟨S, hS, Finset.card_pos.1 (hcard ▸ hm), rfl⟩

section Family

variable {A : Set (Set World)}

/-- A world verifying exactly the disjunct `i` is minimal among the disjunction's worlds,
relative to a family whose alternatives true at that world are sub-disjunctions and which
separates every other index from `i`. -/
theorem isMinimal_of_single {i : ι} (hi : i ∈ I) {w : World}
    (hA : ∀ q ∈ A, w ∈ q → ∃ S ⊆ I, q = subDisj p S)
    (hsplit : ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, subDisj p S ∈ A ∧ j ∈ S ∧ i ∉ S)
    (hw : ∀ j ∈ I, w ∈ p j ↔ j = i) : IsMinimal A (disj I p) w := by
  refine ⟨mem_subDisj.2 ⟨i, hi, (hw i hi).2 rfl⟩, ?_⟩
  rintro ⟨v, hv, hle, hnle⟩
  obtain ⟨j, hj, hvj⟩ := mem_subDisj.1 hv
  by_cases hji : j = i
  · subst hji
    refine hnle λ q hq hwq => ?_
    obtain ⟨S, hS, rfl⟩ := hA q hq hwq
    obtain ⟨k, hk, hwk⟩ := mem_subDisj.1 hwq
    exact mem_subDisj.2 ⟨k, hk, ((hw k (hS hk)).1 hwk) ▸ hvj⟩
  · obtain ⟨S, hS, hSA, hjS, hiS⟩ := hsplit j hj hji
    obtain ⟨k, hk, hwk⟩ := mem_subDisj.1 (hle _ hSA (mem_subDisj.2 ⟨j, hjS, hvj⟩))
    exact hiS (((hw k (hS hk)).1 hwk) ▸ hk)

variable (hA : A ⊆ subDisjs I p)
  (hsplit : ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, subDisj p S ∈ A ∧ j ∈ S ∧ i ∉ S)
  (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
include hA hsplit hsep

/-- Nothing is innocently excludable: each sub-disjunction holds at the minimal world of one
of its disjuncts. -/
theorem not_isInnocentlyExcludable_of_subDisjs (q : Set World) :
    ¬ IsInnocentlyExcludable A (disj I p) q := by
  intro hq
  obtain ⟨S, hS, ⟨i, hi⟩, rfl⟩ := hA hq.1
  obtain ⟨w, hw⟩ := hsep i (hS hi)
  exact (isInnocentlyExcludable_iff_exhMW_entails_neg A _ _ hq.1).1 hq
    (isMinimal_of_single (hS hi) (λ q hq _ => let ⟨S, hS, _, h⟩ := hA hq; ⟨S, hS, h⟩)
      (hsplit i (hS hi)) hw)
    (mem_subDisj.2 ⟨i, hi, (hw i (hS hi)).2 rfl⟩)

/-- With a world verifying every disjunct, the cell is consistent. -/
theorem cell_nonempty_of_subDisjs (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    (cell A (disj I p)).Nonempty := by
  obtain ⟨w, hw⟩ := hall
  obtain ⟨i, hi⟩ := hI
  refine ⟨w, mem_subDisj.2 ⟨i, hi, hw i hi⟩,
    λ q hq => absurd hq (not_isInnocentlyExcludable_of_subDisjs hA hsplit hsep q),
    λ r ⟨hr, _⟩ => ?_⟩
  obtain ⟨S, hS, ⟨j, hj⟩, rfl⟩ := hA hr
  exact mem_subDisj.2 ⟨j, hj, hw j (hS hj)⟩

/-- Exhaustification asserts the disjunction and every alternative. -/
theorem exhIEII_eq_sInter_of_subDisjs (hI : I.Nonempty) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) :
    exhIEII A (disj I p) = disj I p ∩ ⋂₀ A := by
  rw [exhIEII_eq_cell_of_cell_nonempty _ _ (cell_nonempty_of_subDisjs hA hsplit hsep hI hall)]
  ext w
  constructor
  · rintro ⟨hφ, _, hne⟩
    exact ⟨hφ, Set.mem_sInter.2 λ r hr =>
      hne r ⟨hr, not_isInnocentlyExcludable_of_subDisjs hA hsplit hsep r⟩⟩
  · rintro ⟨hφ, hall'⟩
    exact ⟨hφ, λ q hq => absurd hq (not_isInnocentlyExcludable_of_subDisjs hA hsplit hsep q),
      λ r ⟨hr, _⟩ => Set.mem_sInter.1 hall' r hr⟩

end Family

theorem hsplit_subDisjs :
    ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, subDisj p S ∈ subDisjs I p ∧ j ∈ S ∧ i ∉ S :=
  λ _ _ j hj hji => ⟨{j}, by simpa, ⟨{j}, by simpa, by simp, rfl⟩, by simp, by simpa using hji.symm⟩

/-- All the sub-disjunctions strengthen the disjunction to the conjunction. -/
theorem exhIEII_subDisjs (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) (hI : I.Nonempty)
    (hall : ∃ w, ∀ i ∈ I, w ∈ p i) : exhIEII (subDisjs I p) (disj I p) = ⋂ i ∈ I, p i := by
  rw [exhIEII_eq_sInter_of_subDisjs le_rfl hsplit_subDisjs hsep hI hall]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_sInter, Set.mem_iInter]
  constructor
  · rintro ⟨_, h⟩ i hi
    simpa using h _ ⟨{i}, by simpa, by simp, rfl⟩
  · intro h
    obtain ⟨i, hi⟩ := hI
    refine ⟨mem_subDisj.2 ⟨i, hi, h i hi⟩, ?_⟩
    rintro r ⟨S, hS, ⟨j, hj⟩, rfl⟩
    exact mem_subDisj.2 ⟨j, hj, h j (hS hj)⟩

theorem hsplit_subDisjsOfCard [DecidableEq ι] {m : ℕ} (hm : 0 < m) (hmI : m < I.card) :
    ∀ i ∈ I, ∀ j ∈ I, j ≠ i → ∃ S ⊆ I, subDisj p S ∈ subDisjsOfCard I p m ∧ j ∈ S ∧ i ∉ S := by
  intro i hi j hj hji
  obtain ⟨S', hS', hcard⟩ := Finset.exists_subset_card_eq (s := (I.erase i).erase j) (n := m - 1)
    (by rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hji, hj⟩), Finset.card_erase_of_mem hi]
        omega)
  refine ⟨insert j S', ?_, Or.inr ⟨insert j S', ?_, ?_, rfl⟩, Finset.mem_insert_self _ _, ?_⟩
  · exact Finset.insert_subset hj
      ((hS'.trans (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _))
  · exact Finset.insert_subset hj
      ((hS'.trans (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _))
  · rw [Finset.card_insert_of_notMem (λ h => (Finset.mem_erase.1 (hS' h)).1 rfl), hcard]; omega
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact hji rfl
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 (hS' h)).2).1 rfl

/-- Every size-`m` subset of `I` meets `T ⊆ I` iff fewer than `m` elements of `I` lie outside
`T`. -/
theorem forall_card_eq_exists_mem_iff [DecidableEq ι] {T : Finset ι} (hT : T ⊆ I) {m : ℕ} :
    (∀ S ⊆ I, S.card = m → ∃ i ∈ S, i ∈ T) ↔ I.card < m + T.card := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (s := I \ T) (n := m)
      (by rw [Finset.card_sdiff_of_subset hT]; omega)
    obtain ⟨i, hi, hiT⟩ := h S (hS.trans Finset.sdiff_subset) hcard
    exact (Finset.mem_sdiff.1 (hS hi)).2 hiT
  · intro h S hS hcard
    by_contra hnone
    push Not at hnone
    have : S ⊆ I \ T := λ i hi => Finset.mem_sdiff.2 ⟨hS hi, hnone i hi⟩
    have h₁ := Finset.card_le_card this
    have h₂ := Finset.card_le_card hT
    rw [Finset.card_sdiff_of_subset hT, hcard] at h₁
    omega

/-- The size-`|I|` alternatives are the disjunction itself. -/
theorem subDisjsOfCard_card : subDisjsOfCard I p I.card = {disj I p} := by
  ext q
  simp only [subDisjsOfCard, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    or_iff_left_iff_imp]
  rintro ⟨S, hS, hcard, rfl⟩
  rw [Finset.eq_of_subset_of_card_le hS hcard.ge]

/-- Keeping only the size-`m` alternatives strengthens the disjunction to "at least
`|I| + 1 - m` disjuncts hold". -/
theorem exhIEII_subDisjsOfCard [DecidableEq ι] [∀ w i, Decidable (w ∈ p i)]
    (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i) (hall : ∃ w, ∀ i ∈ I, w ∈ p i) {m : ℕ}
    (hm : 0 < m) (hmI : m ≤ I.card) :
    exhIEII (subDisjsOfCard I p m) (disj I p) =
      {w | I.card < m + (I.filter λ i => w ∈ p i).card} := by
  have hI : I.Nonempty := Finset.card_pos.1 (by omega)
  rcases hmI.lt_or_eq with hmI | rfl
  swap
  · have hsat : ∃ w, disj I p w :=
      hall.imp λ w hw => mem_subDisj.2 (hI.imp λ i hi => ⟨hi, hw i hi⟩)
    rw [subDisjsOfCard_card, exhIEII_singleton (disj I p) hsat]
    ext w
    constructor
    · intro h
      obtain ⟨i, hi, hw⟩ := mem_subDisj.1 h
      have := Finset.card_pos.2
        (⟨i, Finset.mem_filter.2 ⟨hi, hw⟩⟩ : (I.filter λ i => w ∈ p i).Nonempty)
      show I.card < I.card + _
      omega
    · intro h
      have h' : I.card < I.card + (I.filter λ i => w ∈ p i).card := h
      have hpos : 0 < (I.filter λ i => w ∈ p i).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
      exact mem_subDisj.2 ⟨i, (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩
  rw [exhIEII_eq_sInter_of_subDisjs (subDisjsOfCard_subset_subDisjs hI hm)
    (hsplit_subDisjsOfCard hm hmI) hsep hI hall]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_sInter, Set.mem_ofPred_eq]
  rw [← forall_card_eq_exists_mem_iff (Finset.filter_subset _ _)]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩ S hS hcard
    obtain ⟨i, hi, hwi⟩ := mem_subDisj.1 (h _ (Or.inr ⟨S, hS, hcard, rfl⟩))
    exact ⟨i, hi, hS hi, hwi⟩
  · intro h
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (s := I) (n := m) hmI.le
    obtain ⟨i, hi, hiI, hwi⟩ := h S hS hcard
    refine ⟨mem_subDisj.2 ⟨i, hiI, hwi⟩, ?_⟩
    rintro r (rfl | ⟨S', hS', hcard', rfl⟩)
    · exact mem_subDisj.2 ⟨i, hiI, hwi⟩
    · obtain ⟨j, hj, _, hwj⟩ := h S' hS' hcard'
      exact mem_subDisj.2 ⟨j, hj, hwj⟩

/-- With the conjunction of the disjuncts among the alternatives, it is innocently excludable
whenever there are two disjuncts: exhaustification then denies it. -/
theorem isInnocentlyExcludable_iInter_of_insert (hsep : ∀ i ∈ I, ∃ w, ∀ j ∈ I, w ∈ p j ↔ j = i)
    (h2 : 2 ≤ I.card) :
    IsInnocentlyExcludable (insert (⋂ i ∈ I, p i) (subDisjs I p)) (disj I p) (⋂ i ∈ I, p i) := by
  refine (isInnocentlyExcludable_iff_exhMW_entails_neg _ _ _ (Set.mem_insert _ _)).2 ?_
  intro w ⟨hw, hmin⟩
  obtain ⟨i, hi, hwi⟩ := mem_subDisj.1 hw
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) i
  intro hall
  simp only [Set.mem_iInter] at hall
  obtain ⟨v, hv⟩ := hsep i hi
  refine hmin ⟨v, mem_subDisj.2 ⟨i, hi, (hv i hi).2 rfl⟩, ?_, ?_⟩
  · rintro q (rfl | ⟨S, hS, _, rfl⟩) hvq
    · exact absurd (Set.mem_iInter₂.1 hvq j hj) (by rw [hv j hj]; exact hji)
    · obtain ⟨k, hk, hvk⟩ := mem_subDisj.1 hvq
      exact mem_subDisj.2 ⟨k, hk, ((hv k (hS hk)).1 hvk) ▸ hwi⟩
  · intro hle
    obtain ⟨k, hk, hvk⟩ := mem_subDisj.1
      (hle _ (Or.inr ⟨{j}, by simpa, by simp, rfl⟩) (mem_subDisj.2 ⟨j, by simp, hall j hj⟩))
    rw [Finset.mem_singleton] at hk
    subst hk
    exact hji ((hv k hj).1 hvk)

end Exhaustification
