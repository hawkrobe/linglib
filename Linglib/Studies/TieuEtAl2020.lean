module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Core.Data.Trivalent
public import Linglib.Data.Examples.TieuEtAl2020

/-!
# Tieu, Bill, Romoli and Crain (2020): Testing Theories of Plural Meanings

This file formalizes the three theories of the multiplicity inference of the English plural
that [tieu-etal-2020] test experimentally, and the predictions on which they diverge. *Emily
fed giraffes* conveys that she fed more than one, (1), while *Emily didn't feed giraffes*
conveys that she fed none, (2), and the inference likewise disappears in conditional
antecedents and questions, (3)–(4). The ambiguity approach of [farkas-de-swart-2010] gives the
plural a weak reading, one or more, and a strong reading, more than one, and selects the
stronger by the Strongest Meaning Hypothesis, (5)–(7). The implicature approach of
[spector-2007] and [zweig-2009] gives the plural the weak meaning and derives the multiplicity
inference by exhaustification against the singular alternative, (13)–(15), which is entailed
rather than excludable under negation, (16)–(17). The homogeneity approach of [kriz-2015],
extended to bare plurals, makes the plural predicate undefined of a single giraffe, so the
sentence is true of more than one, false of none and undefined otherwise, (20)–(24). All
three predict the monotonicity pattern, `readings_positive` and `readings_negative`. They
diverge in a context where Emily fed exactly one giraffe, (27): the implicature approach makes
the positive sentence literally true with a false implicature and the negative one false,
while the ambiguity approach makes both false and the homogeneity approach both undefined,
`singular_context`. The implicature approach alone derives the multiplicity inference by the
mechanism of the *not all* inference of *some*, (29), the same exhaustifier against a stronger
alternative, `exhIE_some`, whence its uniformity prediction, (28), that children compute fewer
of both.

## Implementation notes

The worlds are the number of giraffes fed, so the readings are sets of natural numbers and
negation is complementation. The implicature approach is the innocent-exclusion exhaustifier
of `Semantics.Exhaustification.InnocentExclusion` with the singular alternative; the paper's
versions differ in how they derive that alternative, footnote 4, and agree on the result. The
Strongest Meaning Hypothesis is the entailment-least reading, which is unique. Homogeneity is
a trivalent predicate whose negation is `Trivalent.neg`. The experiments are not formalized:
in Experiment 1, a truth-value judgment task, adults rejected positive plural sentences after a
story with one animal fed far more often than four- and five-year-olds did, and accepted the
negative ones only moderately; in Experiment 2 children computed fewer multiplicity inferences
and fewer *not all* implicatures than adults, and the two rates were correlated within
children; in Experiment 3, a ternary judgment task, adults gave the positive plural in a
singular context an intermediate reward and the negative plural the minimal one. The examples
are the rows of `Data.Examples.TieuEtAl2020`.

## References

* [tieu-etal-2020]
* [farkas-de-swart-2010]
* [spector-2007]
* [zweig-2009]
* [kriz-2015]
* [fox-2007]
-/

@[expose] public section

namespace TieuEtAl2020

open Exhaustification

/-! ### Plural meanings over the number of giraffes fed -/

/-- (5a): the weak reading, one or more. -/
def weak : Set ℕ := {n | 1 ≤ n}

/-- (5b): the strong reading, more than one, the multiplicity inference. -/
def strong : Set ℕ := {n | 2 ≤ n}

/-- (14): the singular alternative, exactly one. -/
def singular : Set ℕ := {1}

/-! ### The implicature approach (section 1.2.2) -/

/-- (13)–(15): exhaustifying the weak plural against its singular alternative yields the
multiplicity inference. -/
theorem exhIE_weak : exhIE {weak, singular} weak = strong := by
  rw [exhIE_pair_sdiff (φ := weak) (d := singular) ⟨2, by simp [weak, singular]⟩]
  ext n
  simp only [weak, singular, strong, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  omega

/-- (16)–(17): under negation the singular alternative is entailed by the negated plural, so
nothing is excluded and the sentence conveys that no giraffe was fed. -/
theorem exhIE_compl_weak : exhIE {weakᶜ, singularᶜ} weakᶜ = weakᶜ := by
  ext n
  rw [mem_exhIE_iff _ _ (Set.toFinite _)]
  refine ⟨And.left, λ h => ⟨h, λ a ha => ?_⟩⟩
  have hsub : weakᶜ ⊆ a := by
    rcases Set.mem_insert_iff.1 ha.1 with rfl | h
    · exact subset_rfl
    · rw [Set.mem_singleton_iff] at h
      subst h
      intro m hm
      simp only [weak, singular, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
        Set.mem_singleton_iff] at hm ⊢
      omega
  exact absurd ha (not_isInnocentlyExcludable_of_phi_subset (Set.toFinite _)
    ⟨0, by show (0 : ℕ) ∈ weakᶜ; simp [weak]⟩ hsub)

/-- (29): the *not all* implicature of *some of the k giraffes* is the same exhaustifier
against the stronger alternative *all*, the mechanism the uniformity prediction (28)
rests on. -/
theorem exhIE_some {k : ℕ} (hk : 2 ≤ k) :
    exhIE {{n | 1 ≤ n}, {k}} {n | 1 ≤ n} = {n | 1 ≤ n ∧ n ≠ k} := by
  rw [exhIE_pair_sdiff (φ := {n | 1 ≤ n}) (d := {k}) ⟨1, by simp; omega⟩]
  ext n
  simp

/-! ### The ambiguity approach (section 1.2.1) -/

/-- The Strongest Meaning Hypothesis, (7): among the readings of a plural sentence, prefer the
one entailing all the others. -/
def IsPreferred (R : Set (Set ℕ)) (r : Set ℕ) : Prop := r ∈ R ∧ ∀ r' ∈ R, r ⊆ r'

theorem IsPreferred.unique {R : Set (Set ℕ)} {r r' : Set ℕ} (h : IsPreferred R r)
    (h' : IsPreferred R r') : r = r' :=
  (h.2 r' h'.1).antisymm (h'.2 r h.1)

/-- In a positive sentence the strong reading is preferred, (5). -/
theorem isPreferred_strong : IsPreferred {weak, strong} strong :=
  ⟨by simp, by
    rintro r (rfl | rfl)
    · intro n hn
      simp only [weak, strong, Set.mem_ofPred_eq] at hn ⊢
      omega
    · exact subset_rfl⟩

/-- Under negation the negated weak reading is preferred, (6). -/
theorem isPreferred_compl_weak : IsPreferred {weakᶜ, strongᶜ} weakᶜ :=
  ⟨by simp, by
    rintro r (rfl | rfl)
    · exact subset_rfl
    · intro n hn
      simp only [weak, strong, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hn ⊢
      omega⟩

/-! ### The homogeneity approach (section 1.2.3) -/

/-- (20)–(22): the plural sentence is true of a plurality of giraffes, false of none and
undefined otherwise. -/
def homogeneous (n : ℕ) : Trivalent :=
  if 2 ≤ n then .true else if n = 0 then .false else .indet

theorem homogeneous_eq_true_iff {n : ℕ} : homogeneous n = .true ↔ 2 ≤ n := by
  rcases n with _ | _ | n <;> simp [homogeneous]

/-- (23)–(24): negation leaves undefinedness untouched, so the negated sentence is true of no
giraffe fed. -/
theorem neg_homogeneous_eq_true_iff {n : ℕ} : (homogeneous n).neg = .true ↔ n = 0 := by
  rcases n with _ | _ | n <;> simp [homogeneous]

/-! ### Predictions (section 1.3) -/

/-- All three approaches derive the multiplicity inference of a positive plural sentence. -/
theorem readings_positive :
    exhIE {weak, singular} weak = strong ∧ IsPreferred {weak, strong} strong ∧
      {n | homogeneous n = .true} = strong :=
  ⟨exhIE_weak, isPreferred_strong, Set.ext λ _ => homogeneous_eq_true_iff⟩

/-- All three approaches make a negated plural sentence convey that none was fed. -/
theorem readings_negative :
    exhIE {weakᶜ, singularᶜ} weakᶜ = weakᶜ ∧ IsPreferred {weakᶜ, strongᶜ} weakᶜ ∧
      {n | (homogeneous n).neg = .true} = weakᶜ := by
  refine ⟨exhIE_compl_weak, isPreferred_compl_weak, Set.ext λ n => ?_⟩
  rw [Set.mem_ofPred_eq, neg_homogeneous_eq_true_iff]
  simp [weak]

/-- (27), the singular context: the implicature approach makes the positive sentence literally
true but its enriched meaning false and the negative sentence false, an asymmetry; the
ambiguity approach makes both false and the homogeneity approach both undefined. -/
theorem singular_context :
    (1 ∈ weak ∧ 1 ∉ exhIE {weak, singular} weak ∧
        1 ∉ exhIE {weakᶜ, singularᶜ} weakᶜ) ∧
      (1 ∉ strong ∧ 1 ∉ weakᶜ) ∧
      (homogeneous 1 = .indet ∧ (homogeneous 1).neg = .indet) := by
  rw [exhIE_weak, exhIE_compl_weak]
  simp [weak, strong, homogeneous]

end TieuEtAl2020
