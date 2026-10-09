module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Linglib.Data.Examples.Haslinger2025

/-!
# Haslinger (2025): Pragmatic constraints on imprecision and homogeneity

Haslinger argues that the availability of imprecise construals is regulated not in the lexicon
but by alternatives, through two constraints. No Needless Manner Violations combines two Manner
preferences, for lower structural complexity and for less potential for imprecision, as Pareto
dominance, and blocks a sentence that a potentially p-equivalent alternative dominates. Inference
Preservation blocks an imprecise construal of a subexpression that loses an inference, entailment
or incompatibility, that its precise construal licenses about an alternative.

## Main results

* `lt_complexity_of_lt_potential`: an unblocked expression more imprecise than a competitor is
  strictly simpler, the form–meaning correlation behind *the doors* and *all the doors*.
* `ninetyNine_blocked`, `hundred_preserved`: with the numerals at least as round as
  alternatives, (79a), *99* is blocked at any deviation while *100* survives deviations under
  fifty.
* `conjunction_violates`: a conjunction read non-maximally loses the entailment of its conjuncts.

## Implementation notes

The Manner orderings are read off two natural-number measures on an abstract sentence type, with
potential p-equivalence a relation parameter, since the dissertation's (68) quantifies over
contexts that differ only in the issue parameter. Degree expressions are construals over `ℚ`, the
precise interpretation the exact value and the imprecise one the halo of a contextual deviation
`m`, (69)–(70); the roundness score of `Numerals.Roundness` stands in for the
conventionalized scales, and `score_ge_six_lt_two_hundred` is the finite computation behind the
asymmetry. The dissertation's examples are the rows of `Data/Examples/Haslinger2025.json`; its
Ch. 5 extensions to presupposition and redundancy and the collective exceptions of Ch. 7 are not
modelled.

## References

* [haslinger-2025-diss]
* [haslinger-2024]
* [kriz-spector-2021]
* [woodin-etal-2024]
-/

@[expose] public section

namespace Haslinger2025

/-! ### No Needless Manner Violations -/

section Manner

variable {S : Type*} (complexity potential : S → ℕ) (PotEquiv : S → S → Prop)

/-- The Manner profile of a sentence pairs its structural complexity with its potential for
imprecision, the two orderings of (58), combined by the product order as in (57). -/
def manner (φ : S) : ℕ × ℕ := (complexity φ, potential φ)

/-- A cooperative speaker will not use `ψ` when a potentially p-equivalent `φ` is at least as good
on both orderings and better on one, (59). -/
def Blocked (ψ : S) : Prop :=
  ∃ φ, PotEquiv φ ψ ∧ manner complexity potential φ < manner complexity potential ψ

/-- By the form–meaning correlation, an unblocked sentence with more potential for imprecision than
a potentially p-equivalent competitor is strictly simpler than it. -/
theorem lt_complexity_of_lt_potential {φ ψ : S} (h : PotEquiv φ ψ)
    (hp : potential φ < potential ψ) (hb : ¬ Blocked complexity potential PotEquiv ψ) :
    complexity ψ < complexity φ := by
  by_contra hc
  exact hb ⟨φ, h, Prod.lt_iff.mpr (Or.inr ⟨not_lt.mp hc, hp⟩)⟩

end Manner

/-- The sentences of (6) and (8) are the definite plural, the universal quantifier that contains it,
and the hypothetical definite that would contain the quantifier. -/
inductive Plural where
  | the
  | all
  | defAll
  deriving DecidableEq, Repr

/-- In structural complexity *all the doors* contains *the doors*, and the hypothetical (8a)
contains *all doors*. -/
def Plural.complexity : Plural → ℕ
  | .the => 1
  | .all => 2
  | .defAll => 3

/-- The definites have potential for imprecision and the universal quantifier does not. -/
def Plural.potential : Plural → ℕ
  | .the => 1
  | .all => 0
  | .defAll => 1

/-- *The doors* and *all the doors* are incomparable, each better on one ordering, so neither blocks
the other, (60). -/
theorem the_all_incomparable :
    ¬ manner Plural.complexity Plural.potential .the <
        manner Plural.complexity Plural.potential .all ∧
      ¬ manner Plural.complexity Plural.potential .all <
        manner Plural.complexity Plural.potential .the := by
  simp [manner, Prod.lt_iff, Plural.complexity, Plural.potential]

/-- A definite built on the quantifier is dominated by the quantifier, so it is blocked wherever the
two are potentially p-equivalent, (8). -/
theorem defAll_blocked (PotEquiv : Plural → Plural → Prop) (h : PotEquiv .all .defAll) :
    Blocked Plural.complexity Plural.potential PotEquiv .defAll :=
  ⟨.all, h, by simp [manner, Prod.lt_iff, Plural.complexity, Plural.potential]⟩

/-! ### Inference Preservation -/

/-- A subexpression's precise and imprecise interpretations in a context, as predicates over a
domain of degrees or worlds. -/
structure Construal (D : Type*) where
  precise : D → Prop
  imprecise : D → Prop

/-- `[X]^p` is the truth set of a predicate for `p = true` and its falsity set for `p = false`. -/
def valued {D : Type*} (P : D → Prop) : Bool → D → Prop
  | true => P
  | false => fun d ↦ ¬ P d

instance {D : Type*} (P : D → Prop) [DecidablePred P] (p : Bool) (d : D) :
    Decidable (valued P p d) := by
  cases p <;> simp only [valued] <;> infer_instance

/-- Inference Preservation (18), for one alternative `ψ` of the subexpression `φ`, blocks the use
when, for some truth value, the precise truth of `φ` entails that status of `ψ`, the precise falsity
of `φ` does not, but the imprecise truth of `φ` fails to entail the imprecise status of `ψ`. -/
def Violates {D : Type*} (φ ψ : Construal D) : Prop :=
  ∃ p : Bool, (∀ d, φ.precise d → valued ψ.precise p d) ∧
    ¬ (∀ d, ¬ φ.precise d → valued ψ.precise p d) ∧
    ¬ (∀ d, φ.imprecise d → valued ψ.imprecise p d)

/-! #### Degree expressions (Ch. 6) -/

open Numerals.Roundness

/-- A bare numeral is read with deviation at most `m`, (69a) and (70a). -/
def numeral (n : ℕ) (m : ℚ) : Construal ℚ := ⟨fun d ↦ d = n, fun d ↦ |d - n| ≤ m⟩

/-- *More than n* is read with deviation at most `m`, (69b) and (70b). -/
def moreThan (n : ℕ) (m : ℚ) : Construal ℚ := ⟨fun d ↦ n < d, fun d ↦ (n : ℚ) - m < d⟩

/-- The scalar alternatives of a numeral for Inference Preservation, (79a), are the other numerals
at least as round. -/
def IsAlternative (n n' : ℕ) : Prop := n' ≠ n ∧ roundnessScore n ≤ roundnessScore n'

instance (n n' : ℕ) : Decidable (IsAlternative n n') := inferInstanceAs (Decidable (_ ∧ _))

/-- Two distinct bare numerals whose halos meet violate Inference Preservation: incompatible
precisely, compatible imprecisely. -/
theorem numeral_violates_of_le {n n' : ℕ} (h : n ≠ n') {m : ℚ}
    (hd : |(n : ℚ) - n'| ≤ 2 * m) : Violates (numeral n m) (numeral n' m) := by
  refine ⟨false, fun d hd' hn' ↦ ?_, fun hall ↦ ?_, fun hall ↦ ?_⟩
  · exact h (Nat.cast_injective (hd'.symm.trans hn'))
  · exact (hall (n' : ℚ) (by simp only [numeral]; exact_mod_cast h.symm)) rfl
  · refine hall (((n : ℚ) + n') / 2) ?_ ?_
    · simp only [numeral]
      rw [show ((n : ℚ) + n') / 2 - n = (n' - n) / 2 by ring, abs_div,
        abs_of_pos (by norm_num : (0 : ℚ) < 2), abs_sub_comm]
      linarith
    · show |((n : ℚ) + n') / 2 - n'| ≤ m
      rw [show ((n : ℚ) + n') / 2 - n' = (n - n') / 2 by ring, abs_div,
        abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      linarith

/-- Distinct bare numerals whose halos are apart preserve every inference. -/
theorem not_numeral_violates_of_lt {n n' : ℕ} (h : n ≠ n') {m : ℚ}
    (hd : 2 * m < |(n : ℚ) - n'|) : ¬ Violates (numeral n m) (numeral n' m) := by
  rintro ⟨p, ha, -, hc⟩
  cases p with
  | true =>
    have := ha n rfl
    simp only [numeral, valued] at this
    exact h (by exact_mod_cast this)
  | false =>
    refine hc fun d hdn hdn' ↦ ?_
    have hdn : |d - n| ≤ m := hdn
    have hdn' : |d - n'| ≤ m := hdn'
    have := abs_sub_le (n : ℚ) d n'
    rw [abs_sub_comm (n : ℚ) d] at this
    linarith

/-- *100* is an alternative of *99*, which has no roundness. -/
theorem isAlternative_ninetyNine_hundred : IsAlternative 99 100 := by decide

/-- *99* is blocked by its alternative *100* as soon as it admits half a unit of deviation:
non-round numerals must be exact. -/
theorem ninetyNine_blocked {m : ℚ} (hm : 1 / 2 ≤ m) : Violates (numeral 99 m) (numeral 100 m) :=
  numeral_violates_of_le (by decide) (by norm_num; linarith)

/-- Below two hundred, only *100* itself carries the full roundness score. -/
theorem score_ge_six_lt_two_hundred : ∀ n < 200, 6 ≤ roundnessScore n → n = 100 := by
  intro n hn h6
  rw [roundnessScore_eq] at h6
  split_ifs at h6 with h5 h10 hk10 h20 h25 h50 <;> try omega
  have h50d := h50.dvd
  have h20d := h20.dvd
  have hpos : 0 < n := by
    obtain ⟨b, m, hm1, -, rfl⟩ := h50
    exact Nat.mul_pos (Nat.mul_pos hm1 (by norm_num)) (Nat.pow_pos (by norm_num))
  omega

/-- *100* keeps every alternative at bay under deviations below fifty: its nearest alternative at
least as round, *200*, lies a hundred away. -/
theorem hundred_preserved {m : ℚ} (hm : m < 50) {n' : ℕ} (h : IsAlternative 100 n') :
    ¬ Violates (numeral 100 m) (numeral n' m) := by
  refine not_numeral_violates_of_lt (Ne.symm h.1) ?_
  by_contra hle
  have hlt : n' < 200 := by
    by_contra hge
    have : (200 : ℚ) ≤ n' := by exact_mod_cast not_lt.mp hge
    rw [not_lt, abs_le] at hle
    simp only [Nat.cast_ofNat] at hle
    linarith [hle.1]
  exact h.1 (score_ge_six_lt_two_hundred n' hlt (le_trans (by decide) h.2))

/-- *more than n* is blocked by its alternative bare *n* at any positive deviation, their
(69)–(70): the imprecise comparative overlaps the exact value it is precisely incompatible
with. -/
theorem moreThan_blocked (n : ℕ) {m : ℚ} (hm : 0 < m) :
    Violates (moreThan n m) (numeral n m) := by
  refine ⟨false, fun d hd ↦ ?_, fun hall ↦ ?_, fun hall ↦ ?_⟩
  · simp only [moreThan, numeral, valued] at hd ⊢
    exact ne_of_gt hd
  · exact (hall (n : ℚ) (lt_irrefl _)) rfl
  · exact hall (n : ℚ) (by show (n : ℚ) - m < n; linarith)
      (by show |(n : ℚ) - n| ≤ m; simp; linarith)

/-! #### Conjunctions (Ch. 7) -/

/-- *Bert, Claire and Dora were there*, (19)–(20), is precisely maximal and imprecisely non-maximal
over the worlds recording who was there. -/
def conjunction : Construal (Fin 3 → Bool) :=
  ⟨fun w ↦ ∀ i, w i = true, fun w ↦ ∃ i, w i = true⟩

/-- A conjunct alternative, *Bert was there*, with no potential for imprecision. -/
def conjunct (i : Fin 3) : Construal (Fin 3 → Bool) :=
  ⟨fun w ↦ w i = true, fun w ↦ w i = true⟩

/-- The non-maximal construal of the conjunction loses the entailment of each conjunct that the
precise construal licenses, so only the maximal construal survives Inference Preservation. -/
theorem conjunction_violates (i : Fin 3) : Violates conjunction (conjunct i) := by
  refine ⟨true, fun w hw ↦ hw i, fun hall ↦ ?_, fun hall ↦ ?_⟩
  · exact Bool.false_ne_true (hall (fun _ ↦ false) (by simp [conjunction]))
  · have hw : conjunction.imprecise (fun j ↦ decide (j ≠ i)) :=
      ⟨if i = 0 then 1 else 0, by fin_cases i <;> decide⟩
    have := hall _ hw
    simp [conjunct, valued] at this

end Haslinger2025
