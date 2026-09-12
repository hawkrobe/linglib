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
Class A forms are entailed by no alternative at all (`over_ssubset_iff`, `stronger_ge`,
`stronger_gt`, and the rest); and neither primary implicature of a Class B form
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
def alternatives (m : ℕ) : Set (Set ℕ) := (·.over id m) '' {c | c ∈ kennedyAlternatives}

/-- (43): the alternatives that asymmetrically entail a form, as comparisons; their negated
knowledge is the form's primary implicatures. -/
def stronger (m : ℕ) (c : Comparison) : Set Comparison :=
  {c' | c' ∈ kennedyAlternatives ∧ c'.over id m ⊂ c.over id m}

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

/-- Asymmetric entailment among the forms of a positive numeral: the bare numeral entails both
Class B forms and each Class A form entails the Class B form on its side, and nothing else. -/
theorem over_ssubset_iff {m : ℕ} (hm : 0 < m) (c c' : Comparison) :
    c.over id m ⊂ c'.over id m ↔
      (c, c') ∈ [(Comparison.eq, Comparison.ge), (.eq, .le), (.gt, .ge), (.lt, .le)] := by
  rw [Set.ssubset_def, over_subset_iff c c' hm, over_subset_iff c' c hm]
  cases c <;> cases c' <;> simp [Comparison.rel, imp_iff_not_or] <;> omega

/-- (47a): *at least m* is asymmetrically entailed by the bare numeral and by *more than m*, so
its primary implicatures are ignorance of both. -/
theorem stronger_ge {m : ℕ} (hm : 0 < m) : stronger m .ge = {.eq, .gt} := by
  ext c
  cases c <;> simp [stronger, kennedyAlternatives, over_ssubset_iff hm]

/-- (47b): *at most m* is asymmetrically entailed by the bare numeral and by *fewer than m*. -/
theorem stronger_le {m : ℕ} (hm : 0 < m) : stronger m .le = {.eq, .lt} := by
  ext c
  cases c <;> simp [stronger, kennedyAlternatives, over_ssubset_iff hm]

/-- The bare numeral is entailed by none of its alternatives: no primary implicatures, and none
of the upper-bounding secondary ones a Horn scale would give. -/
theorem stronger_eq {m : ℕ} (hm : 0 < m) : stronger m .eq = ∅ := by
  ext c
  cases c <;> simp [stronger, kennedyAlternatives, over_ssubset_iff hm]

/-- Class A: *more than m* is entailed by no alternative, so it carries no ignorance
implicature. -/
theorem stronger_gt {m : ℕ} (hm : 0 < m) : stronger m .gt = ∅ := by
  ext c
  cases c <;> simp [stronger, kennedyAlternatives, over_ssubset_iff hm]

/-- Class A: *fewer than m* is entailed by no alternative. -/
theorem stronger_lt {m : ℕ} (hm : 0 < m) : stronger m .lt = ∅ := by
  ext c
  cases c <;> simp [stronger, kennedyAlternatives, over_ssubset_iff hm]

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
      ⟨_, by simp [kennedyAlternatives], rfl⟩ λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.eq.over id m)
      ⟨_, by simp [kennedyAlternatives], rfl⟩ λ n ⟨h1, h2⟩ => ?_
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
      ⟨_, by simp [kennedyAlternatives], rfl⟩ λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.eq.over id m)
      ⟨_, by simp [kennedyAlternatives], rfl⟩ λ n ⟨h1, h2⟩ => ?_
    simp only [mem_over, Comparison.rel] at *
    omega

end Kennedy2015
