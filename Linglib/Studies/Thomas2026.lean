import Linglib.Semantics.Questions.Probabilistic
import Linglib.Data.Examples.Thomas2026
import Mathlib.Algebra.BigOperators.Fin

/-!
# Thomas (2026): A probabilistic, question-based approach to additivity
[thomas-2026] [ciardelli-groenendijk-roelofsen-2018] [frank-goodman-2012]

Formalisation of [thomas-2026], which unifies the canonical additive use of
*too* with a previously unstudied "argument-building" use by stating felicity
in terms of Bayesian inquisitive answerhood. The substrate primitives
(`Answers`, `IsResolutionEvidencedBy`, `evidencesResolutionMore`,
`IsRelevantTo`) live in `Semantics/Questions/Probabilistic.lean`; this file
encodes the felicity conditions of [thomas-2026] Def 64 and their abstract
consequences.

## Main definitions

* `IsTooFelicitous` — conditions (a)-(c) of [thomas-2026] Def 64: the antecedent
  and the conjunction each answer a relevant question, the conjunction answers
  it more strongly, and the prejacent is neither redundant nor replaceable by a
  weaker proposition.
* `IsTooLicensedByDQ` — the full Def 64: `IsTooFelicitous` plus the requirement
  that the relevant question be relevant to a discourse question.
* `IsTooInfelicitous` — *too* is predicted infelicitous when no relevant
  question licenses it.

## Main statements

* `IsTooFelicitous.antecedent_probOfSet_pos`,
  `IsTooFelicitous.conjunction_probOfSet_pos` — felicity forces positive prior
  mass on the antecedent and on the conjunction.
* `IsTooFelicitous.exists_strict_improvement` — the conjunction is strictly
  better Bayesian evidence for its resolution than the antecedent alone.
* `Witness.answers_discriminates` — a concrete Fin-3 model in which `Answers`
  holds of informative evidence and fails of the trivial `univ`, exercising the
  `raises_prob` and `dominates` fields of the answerhood structure.
* `too_acceptable_iff_def64_satisfied` — over the paper's examples
  (`Data/Examples/Thomas2026.json`), a *too* row is acceptable iff the paper's
  Def 64 diagnosis is "satisfied"; the equation is uniform across the standard
  and argument-building uses, which is the paper's unification thesis.

## Implementation notes

The relevant question RQ need not be a Current Question; [thomas-2026] §5.4.3
requires only that it be relevant to some discourse question, which
`IsTooLicensedByDQ` captures via `IsRelevantTo`. The two prejacent conditions
rule out the [beaver-clark-2008] ecstatic case (the prejacent already entails
the answer) and the "some-instrument vs cello" case (a weaker prejacent would
do); see the per-field docstrings of `IsTooFelicitous`.
-/

namespace Thomas2026

open Question Semantics.Questions.Probabilistic

variable {W : Type*} {μ : PMF W}
  {prejacent antecedent : Set W} {rq : Question W}

/-! ### TOO felicity -/

/-- Conditions (a)-(c) of [thomas-2026] Def 64. The full Def 64 additionally
    requires the relevant question to be relevant to a discourse question; that
    is `IsTooLicensedByDQ`. -/
structure IsTooFelicitous (prejacent antecedent : Set W) (rq : Question W)
    (μ : PMF W) : Prop where
  /-- Def 64a: the antecedent answers the relevant question. -/
  antecedent_answers : Answers antecedent rq μ
  /-- Def 64b (first half): the conjunction answers the relevant question. -/
  conjunction_answers : Answers (antecedent ∩ prejacent) rq μ
  /-- Def 64b (second half): the conjunction evidences its resolution more
      strongly than the antecedent alone does. -/
  conjunction_stronger : ∃ 𝒜,
    IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ ∧
    evidencesResolutionMore μ 𝒜 (antecedent ∩ prejacent) antecedent
  /-- Def 64c.i: the prejacent does not by itself entail the resolution the
      conjunction evidences (rules out the [beaver-clark-2008] ecstatic case
      "Sam is happy. #He's ecstatic, too"). -/
  prejacent_not_entails : ∀ 𝒜,
    IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ →
    ¬ prejacent ⊆ ⋂₀ 𝒜
  /-- Def 64c.ii: no proper weakening `S ⊋ prejacent` licenses the same
      resolution as well as the prejacent does (rules out the
      "some-instrument vs cello" case). -/
  prejacent_minimal : ∀ S : Set W, prejacent ⊆ S → S ≠ prejacent →
    ∀ 𝒜, IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ →
      evidencesResolutionMore μ 𝒜 (antecedent ∩ prejacent) (antecedent ∩ S)

/-! ### Abstract consequences -/

/-- TOO felicity entails that the antecedent puts positive prior mass: a direct
    corollary of `Answers.probOfSet_pos` applied to the antecedent condition. -/
theorem IsTooFelicitous.antecedent_probOfSet_pos
    (h : IsTooFelicitous prejacent antecedent rq μ) :
    μ.probOfSet antecedent > 0 :=
  h.antecedent_answers.probOfSet_pos

/-- TOO felicity entails that the conjunction puts positive prior mass — same
    corollary applied to the conjunction condition. -/
theorem IsTooFelicitous.conjunction_probOfSet_pos
    (h : IsTooFelicitous prejacent antecedent rq μ) :
    μ.probOfSet (antecedent ∩ prejacent) > 0 :=
  h.conjunction_answers.probOfSet_pos

/-- TOO felicity entails that the conjunction is genuinely stronger evidence
    than the antecedent alone (the [thomas-2026] §4.4 intuition that *too* marks
    a strict improvement). The witness `𝒜` from `conjunction_stronger` exhibits
    this; the inequality is `evidencesResolutionMore` unfolded. -/
theorem IsTooFelicitous.exists_strict_improvement
    (h : IsTooFelicitous prejacent antecedent rq μ) :
    ∃ 𝒜, IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ ∧
      μ.condProbSet (antecedent ∩ prejacent) (⋂₀ 𝒜) >
      μ.condProbSet antecedent (⋂₀ 𝒜) :=
  h.conjunction_stronger

/-! ### RQ relevance to a discourse question -/

/-- The full [thomas-2026] Def 64: `IsTooFelicitous` together with the
    requirement that `rq` be relevant to some discourse question `dq`. The RQ
    need not be a Current Question — §5.4.3 requires only relevance to a DQ. -/
def IsTooLicensedByDQ (prejacent antecedent : Set W)
    (rq dq : Question W) (μ : PMF W) : Prop :=
  IsTooFelicitous prejacent antecedent rq μ ∧ IsRelevantTo rq dq μ

/-! ### Predicted infelicity -/

/-- *Too* is predicted infelicitous for a given (prejacent, antecedent) when no
    relevant question satisfies the felicity conditions ([thomas-2026] §5.5). -/
def IsTooInfelicitous (prejacent antecedent : Set W) (μ : PMF W) : Prop :=
  ∀ rq : Question W, ¬ IsTooFelicitous prejacent antecedent rq μ

/-! ### Data conformance

Each row of `Data/Examples/Thomas2026.json` records the paper's Def 64
diagnosis as a `def64_status` feature: `satisfied`, or the condition the paper
identifies as failing (`antecedent_violation` for (3), `conjunction_violation`
for (72)/(19c), `prejacent_violation_i` for (11), `prejacent_violation_ii` for
(30)). The *either* row carries no diagnosis — fn. 9 leaves *either* to future
work — so the transfer equation is stated for *too* rows only. -/

/-- **Transfer equation**: a *too* row is acceptable iff the paper exhibits an
    (ANT, RQ) pair satisfying all of Def 64. Uniform across the standard and
    argument-building rows — [thomas-2026]'s unification thesis. -/
theorem too_acceptable_iff_def64_satisfied :
    ∀ row ∈ Examples.all, row.feature? "particle" = some "too" →
      (row.judgment = .acceptable ↔
        row.feature? "def64_status" = some "satisfied") := by
  decide

end Thomas2026

/-! ### Worked witness

A concrete model showing the answerhood structure underlying TOO felicity is
satisfiable and discriminating. Over `W = Fin 3` with the uniform prior, the
evidence `R = {1}` answers the two-alternative question `Q` (alternatives
`A = {0,1}` and `B = {2}`) via the singleton resolution `{A}`, while the trivial
evidence `Set.univ` answers nothing. This instantiates the `raises_prob` and
`dominates` fields that the abstract `IsTooFelicitous` structure never forces a
caller to exhibit. -/

namespace Thomas2026.Witness

open Question Semantics.Questions.Probabilistic
open scoped ENNReal

abbrev W := Fin 3
abbrev A : Set W := {0, 1}
abbrev B : Set W := {2}
abbrev R : Set W := {1}

/-- The uniform prior on `Fin 3`. -/
noncomputable def μ : PMF W := PMF.ofFintype (fun _ => (3 : ℝ≥0∞)⁻¹) (by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- The relevant question: `Avery invited Bailey?` against `Avery invited
    Cameron?` — two incomparable alternatives `A` and `B`. -/
def Q : Question W := Question.declarative A ⊔ Question.declarative B

theorem hAnotB : ¬ A ⊆ B := by
  intro h; have : (0 : W) ∈ B := h (by simp); simp at this

theorem hBnotA : ¬ B ⊆ A := by
  intro h; have : (2 : W) ∈ A := h (by simp); simp at this

theorem hRA : R ⊆ A := by intro x hx; fin_cases x <;> simp_all

theorem hRcapB : R ∩ B = ∅ := by ext x; fin_cases x <;> simp_all

theorem A_mem_altQ : A ∈ alt Q := by
  apply Question.mem_alt_sup_of_alt_left
  · rw [Question.alt_declarative]; exact Set.mem_singleton_iff.mpr rfl
  · intro r hr hAr; exact absurd (hAr.trans hr) hAnotB

theorem B_mem_altQ : B ∈ alt Q := by
  apply Question.mem_alt_sup_of_alt_right
  · rw [Question.alt_declarative]; exact Set.mem_singleton_iff.mpr rfl
  · intro r hr hBr; exact absurd (hBr.trans hr) hBnotA

theorem altQ_subset : alt Q ⊆ {A, B} := by
  intro q hq
  have h := Question.alt_sup_subset_union (Question.declarative A)
    (Question.declarative B) hq
  rw [Question.alt_declarative, Question.alt_declarative, Set.singleton_union] at h
  exact h

theorem altQ_eq : alt Q = {A, B} := by
  apply Set.Subset.antisymm altQ_subset
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · exact A_mem_altQ
  · exact B_mem_altQ

theorem mu_apply (i : W) : μ i = (3 : ℝ≥0∞)⁻¹ := by simp [μ, PMF.ofFintype_apply]

theorem probOfSet_R_pos : μ.probOfSet R > 0 := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_three, mu_apply, mu_apply, mu_apply]
  have h0 : ¬ (0 : W) ∈ R := by simp [R]
  have h1 : (1 : W) ∈ R := by simp [R]
  have h2 : ¬ (2 : W) ∈ R := by simp [R]
  rw [if_neg h0, if_pos h1, if_neg h2]
  simp only [zero_add, add_zero]
  exact ENNReal.inv_pos.mpr (by simp)

theorem probOfSet_A_lt_one : μ.probOfSet A < 1 := by
  have hsum := PMF.probOfSet_compl_add μ A
  have hAc_pos : μ.probOfSet Aᶜ > 0 := by
    rw [PMF.probOfSet_apply, Fin.sum_univ_three, mu_apply, mu_apply, mu_apply]
    have h0 : ¬ (0 : W) ∈ Aᶜ := by simp [A]
    have h1 : ¬ (1 : W) ∈ Aᶜ := by simp [A]
    have h2 : (2 : W) ∈ Aᶜ := by simp [A]
    rw [if_neg h0, if_neg h1, if_pos h2]
    simp only [zero_add, add_zero]
    exact ENNReal.inv_pos.mpr (by simp)
  calc μ.probOfSet A < μ.probOfSet A + μ.probOfSet Aᶜ :=
        ENNReal.lt_add_right (PMF.probOfSet_ne_top μ A) hAc_pos.ne'
    _ = 1 := hsum

theorem hsel : ∀ A' ∈ alt Q, A' ≠ A → R ∩ A' = ∅ := by
  intro A' hA' hne
  rw [altQ_eq] at hA'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA'
  rcases hA' with rfl | rfl
  · exact absurd rfl hne
  · exact hRcapB

/-- **Positive witness**: `R` answers `Q`, via the singleton resolution `{A}`. -/
theorem answers_R : Answers R Q μ :=
  ⟨{A}, isResolutionEvidencedBy_singleton A_mem_altQ hsel hRA probOfSet_R_pos
    probOfSet_A_lt_one⟩

/-- **Discriminating contrast**: `Answers` distinguishes the informative
    evidence `R` from the uninformative `Set.univ`. -/
theorem answers_discriminates :
    Answers R Q μ ∧ ¬ Answers (Set.univ : Set W) Q μ :=
  ⟨answers_R, not_answers_univ⟩

end Thomas2026.Witness
