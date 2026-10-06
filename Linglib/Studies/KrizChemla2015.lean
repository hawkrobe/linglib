module

public import Linglib.Data.Examples.KrizChemla2015
public import Linglib.Data.Generalizations.HomogeneityGap
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Semantics.Quantification.NumberTree
public import Linglib.Studies.Magri2014
public import Mathlib.Data.List.Sections

/-!
# Križ and Chemla (2015): Two Methods to Find Truth-Value Gaps and Their Application to the Projection Problem of Homogeneity

Križ and Chemla introduce two experimental methods for detecting truth-value gaps, separate
completely-true and completely-false tasks (Experiments A0 to A3) and one-shot ternary judgments
(Experiments B1 to B3 and C2 to C4), and use them to test whether the homogeneity gap of a plural
definite projects from the scope of sentential negation, *every*, *no* and *exactly 2*. It
projects in every tested environment except the gap? configuration, where the variants of the
sentence with *some* and with *all* in place of the definite are both false, and under *no* it
emerges only in Experiment C2.

A display gives each boy the trivalent value of *he found his presents*, the bare plural over his
nine presents. Resolving every partial cell to truth gives the existential variant and resolving
every one to falsity the universal variant, and the embedding quantifier, a number tree, is
evaluated on the resolution. The approaches the paper assesses are Spector's supervaluation over
the two variants, Magri's double strengthening, which compares the literal meaning with the
globally exhaustified one, and the universal projection of a homogeneity presupposition after
Schwarzschild, Löbner and Gajewski.

## Main results

* `supervaluation_matches_data`: the supervaluation reproduces every judgment on the displays of
  Table 13.
* `globalExh_iff_mem_strengthened`: global exhaustification is Magri's double strengthening.
* `globalConstrual_eq_supervaluation_of_scopeMonotone`,
  `globalConstrual_ne_indet_of_scopeAntitone`: the global construals agree with the
  supervaluation under monotone quantifiers and never gap under antitone ones.
* `globalConstrual_divergence`: they fail on exactly the C2 *no* gap and the C4 gap?? gap.
* `universalPresupposition_divergence`: universal projection fails on exactly the bivalently
  judged conditions whose displays contain partial cells.
* `toFlat_pointwise_le`, `pointwise_divergence`: supervaluating over resolutions that treat the
  partial cells one by one only adds gaps, exactly the gap? condition's.

## Implementation notes

A display records, for each of four arrays of nine objects, how many are target-colored or found.
A resolution is a list of booleans, one per boy, and a number tree holds of it according to how
many boys it puts out of and into the scope (`holds`). The uniform resolutions read each cell at
one designation standard of `Trivalent.designated`, LP (non-false) for the existential variant and
K3 (true) for the universal one; the per-boy resolutions choose the standard boy by boy
(`resolutions`), so the uniform ones are their least and greatest elements.

The (si2)/(si4) construals of §6.1.2 are identified with the supervaluation by Table 12's
lit ≠ loc column: the implicature (31b) is a different formula, but for *exactly* Table 12
compares the literal meaning with the locally exhaustified one, as (39) does. The observed value
of a gap-family row is read by `Generalizations.HomogeneityGap.gapTruth`, `.indet` when the gap
was detected and the recorded bivalent value otherwise. `bareLiteralNegative` and
`wideScopeParse` reconstruct the diagnosis in §6.1.3 of the downward-entailing problem for the
implicature approach: the bare existential literal meaning predicts no gap under negation, and
parsing the definite above negation restores the fit for plain negation but not for *no*, whose
definite contains a variable bound by the quantifier, as Steedman observes.

## TODO

* The trivalent projection theory after George that §6.3 credits with matching the
  supervaluation predictions is not implemented.

## References

* [kriz-chemla-2015]
* [spector-2013b]
* [magri-2009]
* [magri-2014]
* [chierchia-fox-spector-2012]
* [schwarzschild-1994]
* [lobner-2000]
* [gajewski-2005]
* [george-2008]
* [steedman-2012]
* [beaver-krahmer-2001]
* [van-benthem-1984]
-/

@[expose] public section

namespace KrizChemla2015

open Generalizations Quantifier
open Trivalent (Designation designated)

/-! ### Displays and their resolutions -/

/-- A display lists, for each boy, the trivalent value of *he found his presents*. -/
abbrev Display := List Trivalent

/-- A cell in which `n` of the nine objects are found or target-colored has the value of the
bare plural over the nine, true when all are, false when none are, and a gap otherwise. -/
def cell (n : ℕ) : Trivalent :=
  Homogeneity.barePlural (fun j m ↦ j < m) (Finset.range 9) n

/-- A cell is true, designated at K3, when all nine objects are found. -/
theorem designated_k3_cell (n : ℕ) : designated .k3 (cell n) ↔ 9 ≤ n := by
  rw [Trivalent.designated_k3_iff, cell, Homogeneity.barePlural,
    Trivalent.supervaluation_eq_true_iff]
  exact ⟨fun h ↦ h 8 (by simp), fun h j hj ↦ by simp at hj; omega⟩

/-- A cell is non-false, designated at LP, when at least one object is found. -/
theorem designated_lp_cell (n : ℕ) : designated .lp (cell n) ↔ 1 ≤ n := by
  rw [Trivalent.designated_lp_iff, Ne, cell, Homogeneity.barePlural,
    Trivalent.supervaluation_eq_false_iff]
  simp only [Finset.mem_range, not_and, not_forall, not_not, exists_prop]
  exact ⟨fun h ↦ by obtain ⟨j, -, hj⟩ := h ⟨0, by simp⟩; omega,
    fun h _ ↦ ⟨0, by omega, h⟩⟩

/-- The display recorded on a row, read cell by cell from its digits. -/
def displayOf? (e : Datum) : Option Display :=
  (e.feature? "display").bind fun s ↦
    s.toList.mapM fun ch ↦ if ch.isDigit then some (cell (ch.toNat - '0'.toNat)) else none

/-- A number tree holds of a resolution according to how many boys it resolves out of and into
the scope. -/
def holds (q : NumberTree) (c : List Bool) : Prop := q (c.count false) (c.count true)

instance (q : NumberTree) [DecidableRel q] (c : List Bool) : Decidable (holds q c) :=
  inferInstanceAs (Decidable (q _ _))

/-- The uniform resolution of a display at a designation standard puts each boy in the scope
when his value is designated. -/
def resolve (δ : Designation) (d : Display) : List Bool := d.map fun v ↦ decide (designated δ v)

/-- The resolutions of a display that choose a designation standard boy by boy. -/
def resolutions (d : Display) : List (List Bool) :=
  (d.map fun v ↦ [decide (designated .lp v), decide (designated .k3 v)]).sections

theorem resolve_mem_resolutions (δ : Designation) (d : Display) :
    resolve δ d ∈ resolutions d := by
  refine List.mem_sections.2 <| List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
    List.forall₂_same.2 fun v _ ↦ ?_
  cases δ <;> simp

/-- The K3 resolution is least and the LP resolution greatest among the resolutions. -/
theorem resolve_le_of_mem_resolutions {d : Display} {c : List Bool} (hc : c ∈ resolutions d) :
    List.Forall₂ (· ≤ ·) (resolve .k3 d) c ∧ List.Forall₂ (· ≤ ·) c (resolve .lp d) := by
  have h := List.forall₂_map_right_iff.1 (List.mem_sections.1 hc)
  refine ⟨List.forall₂_map_left_iff.2 (h.flip.imp fun v b hb ↦ ?_),
    List.forall₂_map_right_iff.2 (h.imp fun b v hb ↦ ?_)⟩ <;>
  cases v <;> cases b <;> simp_all

/-- A display without partial cells has a single resolution. -/
theorem resolve_lp_eq_resolve_k3 {d : Display} (h : ∀ v ∈ d, v.isDefined) :
    resolve .lp d = resolve .k3 d :=
  List.map_congr_left fun v hv ↦ by cases v <;> first | rfl | exact absurd (h _ hv) id

/-- Moving boys into the scope preserves a scope-monotone quantifier. -/
theorem holds_of_forall₂_le {q : NumberTree} (hq : q.ScopeMonotone) {c c' : List Bool}
    (h : List.Forall₂ (· ≤ ·) c c') (hc : holds q c) : holds q c' := by
  obtain ⟨j, h₁, h₂⟩ : ∃ j, c'.count true = c.count true + j ∧
      c.count false = c'.count false + j := by
    clear hc
    induction h with
    | nil => exact ⟨0, rfl, rfl⟩
    | @cons b b' _ _ hb _ ih =>
      obtain ⟨j, h₁, h₂⟩ := ih
      cases b <;> cases b'
      · exact ⟨j, by simp [h₁], by simp [h₂]; omega⟩
      · exact ⟨j + 1, by simp [h₁]; omega, by simp [h₂]; omega⟩
      · exact absurd hb (by decide)
      · exact ⟨j, by simp [h₁]; omega, by simp [h₂]⟩
  unfold holds at hc ⊢
  rw [h₂] at hc
  rw [h₁]
  exact hq.shift j hc

/-! ### The some- and all-substituted readings

§3's guiding principle: a sentence with a definite plural has a gap in a situation where the
variant with an existential in place of the definite is true while the variant with a universal is
false. -/

section Readings

variable (q : NumberTree) (d : Display)

/-- A reading evaluates the quantifier over the uniform resolution at `δ`, which at LP
(non-false) is the existential resolution of the definite and at K3 (true) the universal one. -/
def reading (δ : Designation) : Prop := holds q (resolve δ d)

/-- The some-substituted reading puts *some (of his) presents* in place of the definite. It is
the literal meaning on [magri-2014]'s analysis and the existential resolution on
[spector-2013b]'s. -/
abbrev someReading : Prop := reading q d .lp

/-- The all-substituted reading puts *all of his presents* in place of the definite. It is the
locally exhaustified parse on [magri-2014]'s analysis and the universal resolution on
[spector-2013b]'s. -/
abbrev allReading : Prop := reading q d .k3

instance [DecidableRel q] (δ : Designation) : Decidable (reading q d δ) :=
  inferInstanceAs (Decidable (holds q _))

variable {q d}

/-- The universal quantifier holds of a resolution when every boy is in the scope. -/
theorem reading_all (δ : Designation) : reading NumberTree.all d δ ↔ ∀ v ∈ d, designated δ v := by
  simp [reading, holds, resolve, NumberTree.all, List.count_eq_zero]

/-- The negative quantifier holds of a resolution when no boy is in the scope. -/
theorem reading_no (δ : Designation) : reading NumberTree.no d δ ↔ ∀ v ∈ d, ¬ designated δ v := by
  simp [reading, holds, resolve, NumberTree.no, List.count_eq_zero]

/-- On a display without partial cells the two resolutions coincide. -/
theorem someReading_iff_allReading (h : ∀ v ∈ d, v.isDefined) :
    someReading q d ↔ allReading q d := by
  rw [someReading, allReading, reading, reading, resolve_lp_eq_resolve_k3 h]

/-- Under a scope-monotone quantifier the universal variant entails the existential one. -/
theorem allReading_imp_someReading (hq : q.ScopeMonotone) : allReading q d → someReading q d :=
  holds_of_forall₂_le hq (resolve_le_of_mem_resolutions (resolve_mem_resolutions .lp d)).1

/-- Under a scope-antitone quantifier the existential variant entails the universal one. -/
theorem someReading_imp_allReading (hq : q.ScopeAntitone) : someReading q d → allReading q d :=
  fun hs ↦ not_not.1 fun ha ↦ allReading_imp_someReading (q := qᶜ) hq.compl ha hs

end Readings

/-! ### Two-component verdicts -/

/-- The verdict from two meaning components is the supervaluation over the pair, clearly true
when both hold, clearly false when neither does, and a truth-value gap when they conflict. -/
def gapValue (p q : Prop) [Decidable p] [Decidable q] : Trivalent :=
  Trivalent.supervaluation Finset.univ fun b : Bool ↦ if b then p else q

section GapValue

variable {p q : Prop} [Decidable p] [Decidable q]

@[simp] theorem gapValue_eq_true_iff : gapValue p q = .true ↔ p ∧ q := by
  simp [gapValue, Trivalent.supervaluation_eq_true_iff, Bool.forall_bool, and_comm]

@[simp] theorem gapValue_eq_false_iff : gapValue p q = .false ↔ ¬ p ∧ ¬ q := by
  simp [gapValue, Trivalent.supervaluation_eq_false_iff, Bool.forall_bool, and_comm]

@[simp] theorem gapValue_eq_indet_iff : gapValue p q = .indet ↔ ¬ (p ↔ q) := by
  simp only [gapValue, Trivalent.supervaluation_eq_indet_iff, Finset.mem_univ, true_and,
    Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true]
  tauto

/-- Two components that agree yield their common classical value. -/
theorem gapValue_of_iff (h : p ↔ q) : gapValue p q = .ofProp p := by
  by_cases hp : p
  · rw [gapValue_eq_true_iff.2 ⟨hp, h.1 hp⟩, Trivalent.ofProp_eq_true_iff.2 hp]
  · rw [gapValue_eq_false_iff.2 ⟨hp, fun hq ↦ hp (h.2 hq)⟩, Trivalent.ofProp_eq_false_iff.2 hp]

/-- Two components that agree yield a bivalent verdict. -/
theorem gapValue_ne_indet (h : p ↔ q) : gapValue p q ≠ .indet := by simp [h]

/-- Negating both components negates the verdict. -/
theorem gapValue_not : gapValue (¬ p) (¬ q) = (gapValue p q).neg := by
  cases h : gapValue p q <;> simp_all [not_iff_not]

end GapValue

/-! ### The approaches of §6 -/

section Approaches

variable (q : NumberTree) [DecidableRel q] (d : Display)

/-- The two-candidate supervaluation of [spector-2013b] (§6.2) supervaluates over the existential
and universal resolutions of the definite. Extensionally this is also the (si2)/(si4) implicature
construal of §6.1.2, a gap iff the literal and locally exhaustified meanings conflict, which is
how §6.2 argues the two approaches make the same projection predictions. -/
def supervaluation : Trivalent := gapValue (someReading q d) (allReading q d)

/-- The globally double-exhaustified meaning, (30) and (39), is the conjunction of the some- and
all-substituted readings, [magri-2014]'s double strengthening
(`globalExh_iff_mem_strengthened`). In a downward-entailing scope exhaustification is vacuous,
and the conjunction is then the literal meaning (`globalExh_iff_of_scopeAntitone`). -/
def globalExh : Prop := someReading q d ∧ allReading q d

instance : Decidable (globalExh q d) := inferInstanceAs (Decidable (_ ∧ _))

/-- The implicature construals (si1) and (si3) of §6.1.2, after [magri-2009]'s oddness condition,
put a gap where the literal and the globally exhaustified meaning conflict. -/
def globalConstrual : Trivalent := gapValue (someReading q d) (globalExh q d)

/-- Homogeneity as a presupposition projecting universally from the quantifier's scope, after
[schwarzschild-1994], [lobner-2000] and [gajewski-2005] as assessed in §6.3, is the presupposition
that every cell is homogeneous weakly conjoined with the universal-force assertion, in the
∂-operator notation of [beaver-krahmer-2001]. -/
def universalPresupposition : Trivalent :=
  (Trivalent.ofProp (∀ v ∈ d, v.isDefined)).presuppose.meetWeak (.ofProp (allReading q d))

/-- Supervaluation over the resolutions that treat the partial cells one by one, a richer
candidate set than the existential and universal readings, of the kind §6.2 says predicts a gap
in the gap? condition; footnote 19 notes that quantified trivalent logics make the same
prediction. -/
def pointwise : Trivalent := Trivalent.supervaluation (resolutions d).toFinset (holds q)

variable {q d}

/-- A display without partial cells gets a bivalent verdict, whatever the quantifier. -/
theorem supervaluation_ne_indet (h : ∀ v ∈ d, v.isDefined) : supervaluation q d ≠ .indet :=
  gapValue_ne_indet (someReading_iff_allReading h)

omit [DecidableRel q] in
/-- Under a downward-entailing quantifier global exhaustification is vacuous. -/
theorem globalExh_iff_of_scopeAntitone (hq : q.ScopeAntitone) :
    globalExh q d ↔ someReading q d :=
  ⟨And.left, fun h ↦ ⟨h, someReading_imp_allReading hq h⟩⟩

/-- The global construals depart from supervaluation exactly where the literal meaning is false
and the locally exhaustified meaning true. -/
theorem globalConstrual_ne_supervaluation_iff :
    globalConstrual q d ≠ supervaluation q d ↔ ¬ someReading q d ∧ allReading q d := by
  unfold globalConstrual supervaluation globalExh
  by_cases hs : someReading q d <;> by_cases ha : allReading q d <;> simp [hs, ha]
  decide

/-- In the scope of a scope-monotone quantifier such as *every* the implicature construals all
align: comparing the literal meaning with global exhaustification and with local exhaustification
comes to the same thing (§6.1.3). -/
theorem globalConstrual_eq_supervaluation_of_scopeMonotone (hq : q.ScopeMonotone) :
    globalConstrual q d = supervaluation q d :=
  not_not.1 fun h ↦ (globalConstrual_ne_supervaluation_iff.1 h).elim fun hs ha ↦
    hs (allReading_imp_someReading hq ha)

/-- Without local exhaustification, no gap can arise in the scope of a downward-entailing
quantifier such as *no*: exhaustification is vacuous there, so the literal and globally
exhaustified meanings never conflict. The observed C2 gap therefore forces either local
exhaustification or the supervaluation and presupposition alternatives. -/
theorem globalConstrual_ne_indet_of_scopeAntitone (hq : q.ScopeAntitone) :
    globalConstrual q d ≠ .indet :=
  gapValue_ne_indet (globalExh_iff_of_scopeAntitone hq).symm

end Approaches

/-! ### Global exhaustification is double strengthening -/

section Strengthening

open Magri2014 (strengthened primalMates primal)

variable (q : NumberTree) [DecidableRel q] (n : ℕ)

/-- The displays of `n` boys on which the some-substituted reading holds, the weak pole. -/
def weakPole : Finset (Fin n → Trivalent) :=
  Finset.univ.filter fun w ↦ someReading q (List.ofFn w)

/-- The displays of `n` boys on which the all-substituted reading holds, the strong pole. -/
def strongPole : Finset (Fin n → Trivalent) :=
  Finset.univ.filter fun w ↦ allReading q (List.ofFn w)

variable {q n}

/-- Exhaustifying the sentence twice over its some- and all-substituted alternatives, by
[magri-2014]'s double strengthening, yields `globalExh`, (30) and (39), provided either the strong
pole is weaker, as in a downward-entailing scope, or the two poles are compatible. -/
theorem globalExh_iff_mem_strengthened
    (h : weakPole q n ⊆ strongPole q n ∨ (weakPole q n ∩ strongPole q n).Nonempty)
    (w : Fin n → Trivalent) :
    globalExh q (List.ofFn w) ↔
      w ∈ strengthened primalMates (primal (weakPole q n) (strongPole q n)) .mystery := by
  rcases (weakPole q n \ strongPole q n).eq_empty_or_nonempty with h₀ | h₀
  · have hsub := Finset.sdiff_eq_empty_iff_subset.1 h₀
    rw [Magri2014.strengthened_primal_mystery_of_subset hsub]
    have hw : w ∈ weakPole q n ↔ someReading q (List.ofFn w) := by simp [weakPole]
    have hw' : w ∈ strongPole q n ↔ allReading q (List.ofFn w) := by simp [strongPole]
    exact ⟨fun h ↦ hw.2 h.1, fun h ↦ ⟨hw.1 h, hw'.1 (hsub h)⟩⟩
  · have h₂ := h.resolve_left fun hsub ↦ by simp [Finset.sdiff_eq_empty_iff_subset.2 hsub] at h₀
    rw [Magri2014.strengthened_primal_mystery h₀ h₂]
    simp [weakPole, strongPole, globalExh]

end Strengthening

/-! ### Per-boy resolutions -/

section Pointwise

variable {q : NumberTree} [DecidableRel q] {d : Display}

/-- The two-candidate supervaluation ranges over the uniform resolutions. -/
theorem supervaluation_eq_image :
    supervaluation q d =
      Trivalent.supervaluation (Finset.univ.image fun δ ↦ resolve δ d) (holds q) := by
  have hall : (∀ c ∈ Finset.univ.image fun δ ↦ resolve δ d, holds q c) ↔
      someReading q d ∧ allReading q d := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]
    exact ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ δ ↦ by cases δ <;> assumption⟩
  have hex : (∃ c ∈ Finset.univ.image fun δ ↦ resolve δ d, holds q c) ↔
      someReading q d ∨ allReading q d := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and]
    exact ⟨fun ⟨δ, h⟩ ↦ by cases δ <;> simp [reading, h], fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩
  have hne : (Finset.univ.image fun δ ↦ resolve δ d).Nonempty := Finset.univ_nonempty.image _
  cases h : supervaluation q d
  · exact ((Trivalent.supervaluation_eq_true_iff ..).2 (hall.2 (gapValue_eq_true_iff.1 h))).symm
  · refine ((Trivalent.supervaluation_eq_false_iff ..).2 ⟨hne, fun c hc hq' ↦ ?_⟩).symm
    exact (gapValue_eq_false_iff.1 h).elim fun h₁ h₂ ↦ (hex.1 ⟨c, hc, hq'⟩).elim h₁ h₂
  · have hni := gapValue_eq_indet_iff.1 h
    refine ((Trivalent.supervaluation_eq_indet_iff ..).2 ⟨hex.2 (by tauto), ?_⟩).symm
    by_contra hn
    push Not at hn
    exact hni (iff_of_true (hall.1 hn).1 (hall.1 hn).2)

/-- Richer candidates can only add gaps: whatever the quantifier, the per-boy supervaluation is
at most as informative as the two-candidate one. -/
theorem toFlat_pointwise_le :
    Trivalent.toFlat (pointwise q d) ≤ Trivalent.toFlat (supervaluation q d) := by
  rw [supervaluation_eq_image]
  refine Trivalent.toFlat_supervaluation_mono _ (fun c hc ↦ ?_) (Finset.univ_nonempty.image _)
  obtain ⟨δ, -, rfl⟩ := Finset.mem_image.1 hc
  exact List.mem_toFinset.2 (resolve_mem_resolutions δ d)

/-- Under a scope-monotone quantifier the per-boy resolutions add no gap: the uniform ones are
their extremes. -/
theorem pointwise_eq_supervaluation_of_scopeMonotone (hq : q.ScopeMonotone) :
    pointwise q d = supervaluation q d := by
  have hk3 := List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)
  have hlp := List.mem_toFinset.2 (resolve_mem_resolutions .lp d)
  have hall : (∀ c ∈ (resolutions d).toFinset, holds q c) ↔ allReading q d :=
    ⟨fun h ↦ h _ hk3, fun h c hc ↦ holds_of_forall₂_le hq
      (resolve_le_of_mem_resolutions (List.mem_toFinset.1 hc)).1 h⟩
  have hex : (∃ c ∈ (resolutions d).toFinset, holds q c) ↔ someReading q d :=
    ⟨fun ⟨c, hc, h⟩ ↦ holds_of_forall₂_le hq
      (resolve_le_of_mem_resolutions (List.mem_toFinset.1 hc)).2 h, fun h ↦ ⟨_, hlp, h⟩⟩
  have hle := allReading_imp_someReading (d := d) hq
  cases h : supervaluation q d
  · exact (Trivalent.supervaluation_eq_true_iff ..).2 (hall.2 (gapValue_eq_true_iff.1 h).2)
  · exact (Trivalent.supervaluation_eq_false_iff ..).2 ⟨⟨_, hk3⟩,
      fun c hc hq' ↦ (gapValue_eq_false_iff.1 h).1 (hex.1 ⟨c, hc, hq'⟩)⟩
  · have ⟨hs, ha⟩ : someReading q d ∧ ¬ allReading q d := by
      have := gapValue_eq_indet_iff.1 h
      tauto
    exact (Trivalent.supervaluation_eq_indet_iff ..).2 ⟨hex.2 hs, _, hk3, ha⟩

theorem supervaluation_compl : supervaluation qᶜ d = (supervaluation q d).neg :=
  gapValue_not

theorem pointwise_compl : pointwise qᶜ d = (pointwise q d).neg :=
  Trivalent.supervaluation_not _ ⟨_, List.mem_toFinset.2 (resolve_mem_resolutions .k3 d)⟩

/-- Under a scope-antitone quantifier, likewise. -/
theorem pointwise_eq_supervaluation_of_scopeAntitone (hq : q.ScopeAntitone) :
    pointwise q d = supervaluation q d := by
  have := pointwise_eq_supervaluation_of_scopeMonotone (d := d) hq.compl
  rwa [pointwise_compl, supervaluation_compl, Trivalent.neg_involutive.injective.eq_iff] at this

end Pointwise

/-! ### The tested grid -/

/-- The embedding quantifiers of the C-series conditions of Table 2 are *every*, *no* and
*exactly two*. -/
inductive Operator where
  | every
  | no
  | exactlyTwo
  deriving DecidableEq, Repr

/-- The number tree each embedding quantifier denotes. -/
def Operator.tree : Operator → NumberTree
  | .every => NumberTree.all
  | .no => NumberTree.no
  | .exactlyTwo => NumberTree.cardinal {2}

instance : (op : Operator) → DecidableRel op.tree
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .exactlyTwo => inferInstanceAs (DecidableRel (NumberTree.cardinal {2}))

/-- The conditions of Table 2 are the clearly true and clearly false situations and three gap
candidates, the gap?? condition being the one Experiment C4 adds under *exactly*. -/
inductive Condition where
  | clearlyTrue
  | clearlyFalse
  | gap
  | gapQ
  | gapQQ
  deriving DecidableEq, Repr

/-- A row records a tested condition with its quantifier, its Table 13 display, and the judgment
the results commit to. -/
structure Row where
  operator : Operator
  condition : Condition
  display : Display
  observed : Trivalent
  deriving Repr

/-- A datum reads as a row with its display, a clear condition taking its clear value and a
gap-family condition its recorded one (`HomogeneityGap.gapTruth`). -/
def Row.ofDatum (e : Datum) : Option Row := do
  let op ← e.parse? "operator" [("every", .every), ("no", .no), ("exactlyTwo", .exactlyTwo)]
  let c ← e.parse? "condition" [("TRUE", .clearlyTrue), ("FALSE", .clearlyFalse),
    ("GAP", .gap), ("GAP?", .gapQ), ("GAP??", .gapQQ)]
  let d ← displayOf? e
  let observed ← match c with
    | .clearlyTrue => some .true
    | .clearlyFalse => some .false
    | _ => HomogeneityGap.gapTruth e.paperFeatures
  some ⟨op, c, d, observed⟩

/-- The embedded conditions of Experiments C2 to C4. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

/-- Each condition is realized by a display with the intended pattern of variants: both true in
the clearly true condition, differing in the gap and gap?? conditions, and both false otherwise. -/
theorem condition_pattern :
    ∀ t ∈ data, (t.condition = .clearlyTrue ↔
        someReading t.operator.tree t.display ∧ allReading t.operator.tree t.display) ∧
      (t.condition ∈ [.gap, .gapQQ] ↔
        ¬ (someReading t.operator.tree t.display ↔ allReading t.operator.tree t.display)) := by
  decide

/-! ### Predictions against the data -/

/-- The supervaluation (equivalently, local-exhaustification) prediction reproduces every
embedded judgment, the bottom line of §6.4. The fit is bought either by allowing local
exhaustification in downward-entailing contexts, contra [chierchia-fox-spector-2012], or by
restricting the supervaluation candidates to the existential and universal resolutions. -/
theorem supervaluation_matches_data :
    ∀ t ∈ data, supervaluation t.operator.tree t.display = t.observed := by
  decide

/-- Construals locating the gap in a literal-vs-global-exhaustification conflict fail on
exactly two cells: the small-but-robust *no* gap of Experiment C2, where no implicature
arises in a downward-entailing context (§6.1.3), and the gap?? gap of Experiment C4, where
the literal meaning and the implicature are false and true respectively, so their
conjunction is simply false. Both cells are predicted clearly false but observed gappy. -/
theorem globalConstrual_divergence :
    ∀ t ∈ data, (globalConstrual t.operator.tree t.display ≠ t.observed ↔
      (t.operator, t.condition) ∈ [(.no, .gap), (.exactlyTwo, .gapQQ)]) := by
  decide

/-- Universal projection of the homogeneity presupposition fails on exactly the bivalently
judged conditions whose displays contain partial cells, the argument from (42) of §6.3: the
clearly false conditions of Experiments C2 and C3 and the gap? condition, where a presupposition
failure is predicted but falsity observed. -/
theorem universalPresupposition_divergence :
    ∀ t ∈ data, (universalPresupposition t.operator.tree t.display ≠ t.observed ↔
      t.observed ≠ .indet ∧ .indet ∈ t.display) := by
  decide

/-- Resolving the partial cells boy by boy predicts a gap in the gap? condition, where two boys
found some but not all of their presents and resolving one each way makes exactly two finders;
falsity was observed. Every other condition is predicted as by the two-candidate
supervaluation. -/
theorem pointwise_divergence :
    ∀ t ∈ data, (pointwise t.operator.tree t.display ≠ t.observed ↔
      (t.operator, t.condition) = (.exactlyTwo, .gapQ)) := by
  decide

/-! ### The unembedded grid

The polarity × scenario cells of Exps. A0/A1/B1 are pooled in [[Generalizations.HomogeneityGap]].
An unembedded display is a single cell, nine shapes of which all, some, or none are
target-colored; the positive sentence is the scope-monotone and its negation the scope-antitone
corner of the square over it. -/

/-- The paper's unembedded rows, read by the pool's adapter. -/
def gapData : List HomogeneityGap.GapDatum := Examples.all.filterMap HomogeneityGap.fromDatum

/-- The value of the single cell realizing each unembedded scenario. -/
def scenarioValue : HomogeneityGap.GapScenario → Trivalent
  | .all => .true
  | .none => .false
  | .gap => .indet

/-- The quantifier an unembedded sentence of each polarity applies to its one cell. -/
def unembedded : Polarity → NumberTree
  | .positive => NumberTree.all
  | .negative => NumberTree.no

instance : (pol : Polarity) → DecidableRel (unembedded pol)
  | .positive => inferInstanceAs (DecidableRel NumberTree.all)
  | .negative => inferInstanceAs (DecidableRel NumberTree.no)

/-- The supervaluation over the unembedded grid resolves the definite existentially and
universally, under negation at the negative polarity. -/
def supervaluationGap (pol : Polarity) (sc : HomogeneityGap.GapScenario) : Trivalent :=
  supervaluation (unembedded pol) [scenarioValue sc]

/-- The unembedded positive prediction is the cell's own value. -/
theorem supervaluationGap_positive (sc : HomogeneityGap.GapScenario) :
    supervaluationGap .positive sc = scenarioValue sc := by
  cases sc <;> decide

/-- The unembedded negative prediction is the negation of the cell's value. -/
theorem supervaluationGap_negative (sc : HomogeneityGap.GapScenario) :
    supervaluationGap .negative sc = (scenarioValue sc).neg := by
  cases sc <;> decide

/-- The supervaluation account reproduces the paper's unembedded and negated judgments: truth on
uniform displays, the gap on mixed ones, projected through negation (Exps. A1/B1). -/
theorem supervaluationGap_matches_data :
    ∀ d ∈ gapData, supervaluationGap d.polarity d.scenario = d.observed := by
  decide

/-- The bare implicature construal assigns a negated sentence its existential literal meaning
outright: negation is downward-entailing, so no implicature arises and no gap is predicted
(§6.1.3). -/
def bareLiteralNegative (sc : HomogeneityGap.GapScenario) : Trivalent :=
  .ofProp (someReading NumberTree.no [scenarioValue sc])

/-- The E-neg gap of Exps. A1/B1 refutes the bare implicature construal: the negated mixed-display
cell is observed gappy but predicted clearly false. This is §6.1.3's downward-entailing problem,
which for plain negation the wide-scope parse solves (`wideScopeParse_matches_data`) but for
`no`, whose definite contains a variable bound by the quantifier ([steedman-2012]), nothing
does. -/
theorem bareLiteral_misses_negation_gap :
    ∃ d ∈ gapData, d.polarity = .negative ∧ d.scenario = .gap ∧
      bareLiteralNegative d.scenario ≠ d.observed := by
  decide

/-- The wide-scope parse of the negated sentence (§6.1.3) puts the definite above negation, with
the literal meaning *some of the shapes are not green* and the strengthening *all of the shapes
are not green*. -/
def wideScopeParse (sc : HomogeneityGap.GapScenario) : Trivalent :=
  gapValue (¬ designated .k3 (scenarioValue sc)) (¬ designated .lp (scenarioValue sc))

/-- With the wide-scope parse, the implicature construal again reproduces the negated judgments,
the paper's rescue for plain negation. -/
theorem wideScopeParse_matches_data :
    ∀ d ∈ gapData, d.polarity = .negative → wideScopeParse d.scenario = d.observed := by
  decide

end KrizChemla2015
