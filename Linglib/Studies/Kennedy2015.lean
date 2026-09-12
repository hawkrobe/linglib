import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Pragmatics.NeoGricean.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Kennedy (2015): A "de-Fregean" Semantics (and Neo-Gricean Pragmatics) for Modified and Unmodified Numerals

This file formalizes the de-Fregean semantics of [kennedy-2015]: a numeral, bare or modified,
is a quantifier over degree properties, true of a property when its greatest degree stands in
the numeral's relation to the number, `max{n | D(n)} = m` for the bare numeral ((29)), `> m` and
`< m` for the Class A modifiers *more than* and *fewer than* ((41)), `≥ m` and `≤ m` for the
Class B modifiers *at least* and *at most* ((42)). Applied to the degrees a count reaches this is
the substrate's `Degree.Comparison.over`, so bare numerals are two-sided without a Horn scale
(`deFregean_Iic`), and the one-sided readings of numerals under root modals ((31)–(34)) are
matters of scope: a bare numeral scoping over a necessity modal states the least count the modal
requires and over a possibility modal the greatest it allows (`necessity_wide_iff`,
`possibility_wide_iff`).

The ignorance inferences of the Class B modifiers are Sauerland's primary implicatures ((43))
over Kennedy's single alternative set, the five forms of one numeral ((46)): *at least m* is
asymmetrically entailed by the bare numeral and by *more than m* and by no other alternative,
*at most m* by the bare numeral and *fewer than m* ((47)), while the bare numeral and the
Class A forms are entailed by no alternative at all (`primaryAlternatives_ge`,
`primaryAlternatives_gt`, and the rest); and neither primary implicature of a Class B form
strengthens to a secondary one ((44)), each contradicting the assertion together with the other
(`not_isSecondaryImplicature_ge`, `not_isSecondaryImplicature_le`).

## Implementation notes

The worlds of the pragmatics are counts, so a form's content is the set `c.over id m` of counts,
the alternatives are the images of the substrate's `Numerals.kennedyAlternatives`, and the
neo-Gricean operators are `NeoGricean.commitment` and `NeoGricean.IsSecondaryImplicature`. The
interactions of Class B modifiers with root modals (Section 4.2) are not formalized.

## References

* [kennedy-2015]
* [sauerland-2004]
* [nouwen-2010]
-/

namespace Kennedy2015

open Degree Numerals NeoGricean Set

/-! ### The de-Fregean semantics (Section 3) -/

/-- (29), (41), (42): the numeral form `c m` is true of a degree property `D` when `D` has a
greatest degree standing in the relation `c` to `m`. -/
def deFregean (c : Comparison) (m : ℕ) (D : Set ℕ) : Prop := ∃ k, IsGreatest D k ∧ c.rel k m

/-- A count reaching a degree is a member of the comparison's interval. -/
theorem mem_over (c : Comparison) (m n : ℕ) : n ∈ c.over id m ↔ c.rel n m :=
  Comparison.mem_interval c n m

/-- On the degrees a count reaches, the de-Fregean form is the comparison of the count itself,
the substrate's meaning of the numeral: two-sided bare content with no Horn scale. -/
theorem deFregean_Iic (c : Comparison) (m n : ℕ) : deFregean c m (Iic n) ↔ n ∈ c.over id m := by
  constructor
  · rintro ⟨k, hk, hrel⟩
    rw [← isGreatest_Iic.unique hk] at hrel
    exact (mem_over c m n).mpr hrel
  · exact λ h => ⟨n, isGreatest_Iic, (mem_over c m n).mp h⟩

section Modals

variable {W : Type*}

/-- The degrees reached in every accessible world: the property a numeral measures when it
scopes over a necessity modal. -/
def necessityDegrees (R : Set W) (count : W → ℕ) : Set ℕ := {n | ∀ w ∈ R, n ≤ count w}

/-- The degrees reached in some accessible world: the property a numeral measures when it
scopes over a possibility modal. -/
def possibilityDegrees (R : Set W) (count : W → ℕ) : Set ℕ := {n | ∃ w ∈ R, n ≤ count w}

/-- (33a), (34a): under a modal the bare numeral keeps its two-sided content in each accessible
world. -/
theorem narrow_scope_two_sided (R : Set W) (count : W → ℕ) (m : ℕ) :
    (∀ w ∈ R, deFregean .eq m (Iic (count w))) ↔ ∀ w ∈ R, count w = m := by
  simp only [deFregean_Iic]
  exact Iff.rfl

/-- (33b): over a necessity modal the bare numeral is lower-bounded: every accessible world
reaches `m` and one reaches exactly `m`, so `m` is the least count the modal requires. -/
theorem necessity_wide_iff (R : Set W) (count : W → ℕ) (m : ℕ) :
    deFregean .eq m (necessityDegrees R count) ↔
      (∀ w ∈ R, m ≤ count w) ∧ ∃ w ∈ R, count w = m := by
  constructor
  · rintro ⟨k, ⟨hmem, hub⟩, hkm⟩
    have hkm' : k = m := hkm
    subst hkm'
    refine ⟨hmem, ?_⟩
    by_contra h
    push Not at h
    have : k + 1 ∈ necessityDegrees R count :=
      λ w hw => Nat.lt_of_le_of_ne (hmem w hw) (h w hw).symm
    exact absurd (hub this) (by omega)
  · rintro ⟨hall, w, hw, hwm⟩
    exact ⟨m, ⟨hall, λ n hn => hwm ▸ hn w hw⟩, rfl⟩

/-- (34b): over a possibility modal the bare numeral is upper-bounded: some accessible world
reaches exactly `m` and none exceeds it, so `m` is the greatest count the modal allows. -/
theorem possibility_wide_iff (R : Set W) (count : W → ℕ) (m : ℕ) :
    deFregean .eq m (possibilityDegrees R count) ↔
      (∃ w ∈ R, count w = m) ∧ ∀ w ∈ R, count w ≤ m := by
  constructor
  · rintro ⟨k, ⟨⟨w, hw, hwk⟩, hub⟩, hkm⟩
    have hkm' : k = m := hkm
    subst hkm'
    exact ⟨⟨w, hw, le_antisymm (hub ⟨w, hw, le_rfl⟩) hwk⟩, λ w' hw' => hub ⟨w', hw', le_rfl⟩⟩
  · rintro ⟨⟨w, hw, hwm⟩, hall⟩
    exact ⟨m, ⟨⟨w, hw, hwm.ge⟩, λ _ ⟨w', hw', hn⟩ => hn.trans (hall w' hw')⟩, rfl⟩

end Modals

/-! ### Ignorance implicatures (Section 4.1) -/

/-- (46): the alternatives of a numeral form are the five forms of the same numeral, the
substrate's `kennedyAlternatives`, as sets of counts. -/
def alternatives (m : ℕ) : Set (Set ℕ) := {ψ | ∃ c ∈ kennedyAlternatives, ψ = c.over id m}

/-- (43): the alternatives that asymmetrically entail a form, whose content is a proper subset of
its content; their negated knowledge is the form's primary implicatures. -/
def primaryAlternatives (c : Comparison) (m : ℕ) : Set (Set ℕ) :=
  {ψ ∈ alternatives m | ψ ⊂ c.over id m}

/-- Inclusion between two forms of a positive numeral is decided at three counts, one below,
at, and above the number. -/
private theorem over_subset_iff (c c' : Comparison) {m : ℕ} (hm : 0 < m) :
    c.over id m ⊆ c'.over id m ↔
      (c.rel 0 m → c'.rel 0 m) ∧ (c.rel m m → c'.rel m m) ∧
        (c.rel (m + 1) m → c'.rel (m + 1) m) := by
  simp only [Set.subset_def, mem_over]
  refine ⟨λ h => ⟨h 0, h m, h (m + 1)⟩, λ ⟨h0, hm', h1⟩ x hx => ?_⟩
  cases c <;> cases c' <;>
    simp only [Comparison.rel, imp_iff_not_or, not_true_eq_false, false_or] at h0 hm' h1 hx ⊢ <;>
    omega

private theorem over_ssubset_iff (c c' : Comparison) {m : ℕ} (hm : 0 < m) :
    c.over id m ⊂ c'.over id m ↔
      ((c.rel 0 m → c'.rel 0 m) ∧ (c.rel m m → c'.rel m m) ∧
          (c.rel (m + 1) m → c'.rel (m + 1) m)) ∧
        ¬ ((c'.rel 0 m → c.rel 0 m) ∧ (c'.rel m m → c.rel m m) ∧
          (c'.rel (m + 1) m → c.rel (m + 1) m)) := by
  rw [Set.ssubset_def, over_subset_iff c c' hm, over_subset_iff c' c hm]

private theorem mem_alternatives_iff (m : ℕ) (ψ : Set ℕ) :
    ψ ∈ alternatives m ↔ ψ = Comparison.eq.over id m ∨ ψ = Comparison.gt.over id m ∨
      ψ = Comparison.lt.over id m ∨ ψ = Comparison.ge.over id m ∨ ψ = Comparison.le.over id m := by
  simp [alternatives, kennedyAlternatives]

/-- (47a): *at least m* is asymmetrically entailed by the bare numeral and by *more than m*, so
its primary implicatures are ignorance of both, and by no other alternative. -/
theorem primaryAlternatives_ge {m : ℕ} (hm : 0 < m) :
    primaryAlternatives .ge m = {Comparison.eq.over id m, Comparison.gt.over id m} := by
  ext ψ
  simp only [primaryAlternatives, mem_ofPred_eq, mem_alternatives_iff, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl | rfl, h⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    all_goals
      rw [over_ssubset_iff _ _ hm] at h
      simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not] at h
      omega
  · rintro (rfl | rfl) <;> refine ⟨by simp, ?_⟩ <;> rw [over_ssubset_iff _ _ hm] <;>
      simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not,
        not_true_eq_false, false_or] <;> omega

/-- (47b): *at most m* is asymmetrically entailed by the bare numeral and by *fewer than m*. -/
theorem primaryAlternatives_le {m : ℕ} (hm : 0 < m) :
    primaryAlternatives .le m = {Comparison.eq.over id m, Comparison.lt.over id m} := by
  ext ψ
  simp only [primaryAlternatives, mem_ofPred_eq, mem_alternatives_iff, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl | rfl, h⟩
    · exact Or.inl rfl
    · exfalso
      rw [over_ssubset_iff _ _ hm] at h
      simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not] at h
      omega
    · exact Or.inr rfl
    all_goals
      rw [over_ssubset_iff _ _ hm] at h
      simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not] at h
      omega
  · rintro (rfl | rfl) <;> refine ⟨by simp, ?_⟩ <;> rw [over_ssubset_iff _ _ hm] <;>
      simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not,
        not_true_eq_false, false_or] <;> omega

/-- The bare numeral is entailed by none of its alternatives: no primary implicatures, and none
of the upper-bounding secondary ones a Horn scale would give. -/
theorem primaryAlternatives_eq {m : ℕ} (hm : 0 < m) : primaryAlternatives .eq m = ∅ := by
  ext ψ
  simp only [primaryAlternatives, mem_ofPred_eq, mem_alternatives_iff, mem_empty_iff_false,
    iff_false, not_and]
  rintro (rfl | rfl | rfl | rfl | rfl) h <;> rw [over_ssubset_iff _ _ hm] at h <;>
    simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not,
        not_true_eq_false, false_or, true_and] at h <;> omega

/-- Class A: *more than m* is entailed by no alternative, so it carries no ignorance
implicature. -/
theorem primaryAlternatives_gt {m : ℕ} (hm : 0 < m) : primaryAlternatives .gt m = ∅ := by
  ext ψ
  simp only [primaryAlternatives, mem_ofPred_eq, mem_alternatives_iff, mem_empty_iff_false,
    iff_false, not_and]
  rintro (rfl | rfl | rfl | rfl | rfl) h <;> rw [over_ssubset_iff _ _ hm] at h <;>
    simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not,
        not_true_eq_false, false_or] at h <;> omega

/-- Class A: *fewer than m* is entailed by no alternative. -/
theorem primaryAlternatives_lt {m : ℕ} (hm : 0 < m) : primaryAlternatives .lt m = ∅ := by
  ext ψ
  simp only [primaryAlternatives, mem_ofPred_eq, mem_alternatives_iff, mem_empty_iff_false,
    iff_false, not_and]
  rintro (rfl | rfl | rfl | rfl | rfl) h <;> rw [over_ssubset_iff _ _ hm] at h <;>
    simp only [Comparison.rel, imp_iff_not_or, not_and_or, not_or, not_not,
        not_true_eq_false, false_or] at h <;> omega

/-- (44) fails for *at least m*: knowing the bare numeral false with the assertion is knowing
*more than m*, and knowing *more than m* false with the assertion is knowing the bare numeral,
each contradicting the other primary implicature; the ignorance is not strengthened. -/
theorem not_isSecondaryImplicature_ge (m : ℕ) :
    ¬ IsSecondaryImplicature (Comparison.ge.over id m) (alternatives m)
        (Comparison.eq.over id m) ∧
      ¬ IsSecondaryImplicature (Comparison.ge.over id m) (alternatives m)
        (Comparison.gt.over id m) := by
  refine ⟨λ h => ?_, λ h => ?_⟩
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.gt.over id m)
      ((mem_alternatives_iff m _).mpr (by simp)) λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.eq.over id m)
      ((mem_alternatives_iff m _).mpr (by simp)) λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega

/-- (44) fails for *at most m* the same way, with *fewer than m* in place of *more than m*. -/
theorem not_isSecondaryImplicature_le (m : ℕ) :
    ¬ IsSecondaryImplicature (Comparison.le.over id m) (alternatives m)
        (Comparison.eq.over id m) ∧
      ¬ IsSecondaryImplicature (Comparison.le.over id m) (alternatives m)
        (Comparison.lt.over id m) := by
  refine ⟨λ h => ?_, λ h => ?_⟩
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.lt.over id m)
      ((mem_alternatives_iff m _).mpr (by simp)) λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.eq.over id m)
      ((mem_alternatives_iff m _).mpr (by simp)) λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega

end Kennedy2015
