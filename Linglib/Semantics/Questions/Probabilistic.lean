import Linglib.Semantics.Questions.Basic
import Linglib.Core.Probability.Finite
import Linglib.Semantics.Questions.Resolution

/-!
# Probabilistic Question Semantics
[thomas-2026] [westera-brasoveanu-2014] [onea-2019]

Bayesian inquisitive answerhood. The probabilistic refinement of the
set-theoretic resolution relation in `Resolution.lean`: a state σ
"answers" a question Q under a prior μ to the extent that
conditioning μ on σ shifts mass toward some *resolution* of Q (a
conjunction of alternatives, in the inquisitive sense of
[ciardelli-groenendijk-roelofsen-2018]).

## Key API

- `evidencesMore μ A R R'` — Bayesian comparator: `R` provides more
  evidence for `A` than `R'` does. [thomas-2026] Def 63
  (operator-level).

- `IsResolutionEvidencedBy Q 𝒜 R μ` — structure with four named
  fields capturing [thomas-2026] Def 62: `𝒜 ⊆ alt Q` is
  nonempty, `R` raises `P(⋂𝒜)`, and the impact ratio of `⋂𝒜`
  strictly dominates that of any competing intersection.

- `Answers R Q μ` — `R` answers `Q`: an evidenced resolution exists.
  [thomas-2026] Def 62.

- `resolutionEvidencedBy Q R μ : Option (Set (Set W))` — the evidenced
  resolution as a `Classical.choose`-extracted witness, `none` when
  `Answers` fails.

- `evidencesResolutionMore μ 𝒜 R R'` — resolution-level analogue of
  `evidencesMore`. [thomas-2026] Def 63.

## Note on relocated apparatus

The doxastic `Supports` / `Agree` / `Disagree` predicates previously
lived here; they have been moved to
`Studies/IppolitoKissWilliams2022.lean` (the paper
that introduced them) since their only consumer is the IKW 2025
discourse-*only* study file.
-/

namespace Semantics.Questions.Probabilistic

open Question PMF

variable {W : Type*} {μ : PMF W} {A R R' R'' : Set W}
  {Q : Question W} {𝒜 𝒜' : Set (Set W)}

/-! ### Bayesian evidence comparator -/

/-- `R` evidences `A` more strongly than `R'` does:
    `P(A | R) > P(A | R')`. [thomas-2026] Def 63. -/
def evidencesMore (μ : PMF W) (A R R' : Set W) : Prop :=
  μ.condProbSet R A > μ.condProbSet R' A

theorem evidencesMore_irrefl (μ : PMF W) (A R : Set W) :
    ¬ evidencesMore μ A R R :=
  lt_irrefl _

theorem evidencesMore_asymm (h : evidencesMore μ A R R') :
    ¬ evidencesMore μ A R' R :=
  lt_asymm h

theorem evidencesMore_trans (h : evidencesMore μ A R R')
    (h' : evidencesMore μ A R' R'') : evidencesMore μ A R R'' :=
  lt_trans h' h

instance : Std.Irrefl (evidencesMore μ A) :=
  ⟨evidencesMore_irrefl μ A⟩

instance : Trans (evidencesMore μ A) (evidencesMore μ A) (evidencesMore μ A) :=
  ⟨fun {_ _ _} => evidencesMore_trans⟩

/-! ### Pointwise positive evidence

The atomic Bayesian-evidence relation: conditioning on `R` raises the
probability of `A`. The pointwise version of `IsResolutionEvidencedBy`'s
`raises_prob` field, factored out so consumers
([thomas-2026] §1.2, the IKW 2022 `Supports` predicate in
`Studies/IppolitoKissWilliams2022.lean`) can refer to
it directly. -/

/-- `R` provides **positive evidence** for `A`: conditioning on `R`
    raises the probability of `A`. -/
def IsPositiveEvidence (R A : Set W) (μ : PMF W) : Prop :=
  μ.condProbSet R A > μ.probOfSet A

theorem IsPositiveEvidence.probOfSet_pos
    (h : IsPositiveEvidence R A μ) : μ.probOfSet R > 0 :=
  PMF.probOfSet_pos_of_condProbSet_gt μ R A h

/-! ### Resolution evidenced by `R` ([thomas-2026] Def 62) -/

/-- `𝒜 ⊆ alt Q` is the resolution of `Q` evidenced by `R` under prior
    `μ`. [thomas-2026] Def 62.

    The four fields:
    * `subset_alt`  — `𝒜 ⊆ alt Q`;
    * `nonempty`    — `𝒜` is nonempty;
    * `raises_prob` — `R` raises the probability of `⋂₀ 𝒜`;
    * `dominates`   — for any other nonempty `𝒜' ⊆ alt Q` whose
      intersection does not contain `⋂₀ 𝒜`, the impact ratio of
      `⋂₀ 𝒜` strictly dominates the impact ratio of `⋂₀ 𝒜'`.

    The `⋂₀ 𝒜 ⊆ ⋂₀ 𝒜'` exclusion in `dominates` is what makes
    *weaker* resolutions (= larger intersections) not interfere with
    a stronger candidate: a weaker competitor's intersection contains
    the candidate's, so the comparison is vacuously waived. The
    intersection `⋂₀ 𝒜` is what [thomas-2026] calls "the
    resolution of `Q` evidenced by `R`" (notation `Q|_R`). -/
structure IsResolutionEvidencedBy (Q : Question W) (𝒜 : Set (Set W))
    (R : Set W) (μ : PMF W) : Prop where
  subset_alt  : 𝒜 ⊆ alt Q
  nonempty    : 𝒜.Nonempty
  raises_prob : μ.condProbSet R (⋂₀ 𝒜) > μ.probOfSet (⋂₀ 𝒜)
  dominates   : ∀ 𝒜' : Set (Set W),
    𝒜' ⊆ alt Q → 𝒜'.Nonempty → ¬ ⋂₀ 𝒜 ⊆ ⋂₀ 𝒜' →
    μ.impactRatio R (⋂₀ 𝒜) > μ.impactRatio R (⋂₀ 𝒜')

/-- Evidenced resolutions are **nested**: two resolutions of `Q` for the same
    evidence `R` have `⊆`-comparable intersections. This is the robust content
    of [thomas-2026] Def 62's "if such a set `𝒜` exists, it is unique" — the
    `dominates` field forces a chain, so the *strongest* (`⊆`-minimal)
    resolution is the canonical `Q|_R`. Full set-uniqueness does **not** hold:
    `dominates` deliberately waives competitors whose intersection contains
    `⋂₀ 𝒜`, so weaker resolutions can coexist higher in the chain. -/
theorem IsResolutionEvidencedBy.sInter_subset_or_subset
    (h₁ : IsResolutionEvidencedBy Q 𝒜 R μ)
    (h₂ : IsResolutionEvidencedBy Q 𝒜' R μ) :
    ⋂₀ 𝒜 ⊆ ⋂₀ 𝒜' ∨ ⋂₀ 𝒜' ⊆ ⋂₀ 𝒜 := by
  by_contra hcon
  rw [not_or] at hcon
  exact lt_asymm (h₁.dominates 𝒜' h₂.subset_alt h₂.nonempty hcon.1)
                 (h₂.dominates 𝒜 h₁.subset_alt h₁.nonempty hcon.2)

/-! ### Probabilistic answerhood -/

/-- `R` **answers** `Q` (under prior `μ`): an evidenced resolution
    exists. [thomas-2026] Def 62. -/
def Answers (R : Set W) (Q : Question W) (μ : PMF W) : Prop :=
  ∃ 𝒜, IsResolutionEvidencedBy Q 𝒜 R μ

theorem Answers.intro (h : IsResolutionEvidencedBy Q 𝒜 R μ) :
    Answers R Q μ :=
  ⟨𝒜, h⟩

/-- `Answers` requires the prior to put positive mass on the evidence:
    if `R` answers `Q` then `μ.probOfSet R > 0`. -/
theorem Answers.probOfSet_pos (h : Answers R Q μ) : μ.probOfSet R > 0 := by
  obtain ⟨_, hRes⟩ := h
  exact PMF.probOfSet_pos_of_condProbSet_gt μ R _ hRes.raises_prob

/-! ### Witnessing the structure (finite worlds)

A constructor and a negative test showing the answerhood structure is both
satisfiable and genuinely discriminating. Both require `[Fintype W]`, via the
finite-PMF mass bounds of `Core/Probability/Finite.lean`. -/

section Finite
variable [Fintype W]

/-- **Constructor for a singleton evidenced resolution.** If `A` is an
    alternative of `Q`, the evidence `R` lies inside `A` and misses every *other*
    alternative (`R ∩ A' = ∅` for `A' ∈ alt Q`, `A' ≠ A`), the prior puts
    positive mass on `R`, and `A` is not full-measure, then `{A}` is a resolution
    of `Q` evidenced by `R`. The `dominates` field holds because any competitor
    not containing `A` must contain some other alternative `A'`, whose
    intersection `R` misses — giving it impact ratio `0 < μ.impactRatio R A`. -/
theorem isResolutionEvidencedBy_singleton
    (hA : A ∈ alt Q)
    (hsel : ∀ A' ∈ alt Q, A' ≠ A → R ∩ A' = ∅)
    (hRA : R ⊆ A) (hRpos : μ.probOfSet R > 0) (hAlt1 : μ.probOfSet A < 1) :
    IsResolutionEvidencedBy Q {A} R μ := by
  have hcond : μ.condProbSet R A = 1 := by
    rw [PMF.condProbSet_eq_div, Set.inter_eq_left.mpr hRA]
    exact ENNReal.div_self hRpos.ne' (PMF.probOfSet_ne_top μ R)
  have hImpA_pos : μ.impactRatio R A > 0 := by
    unfold PMF.impactRatio
    rw [hcond]
    exact ENNReal.div_pos one_ne_zero (PMF.probOfSet_ne_top μ A)
  refine ⟨?_, ⟨A, Set.mem_singleton_iff.mpr rfl⟩, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hA
  · rw [Set.sInter_singleton, hcond]
    exact hAlt1
  · intro 𝒜' hsub hne hnotA
    rw [Set.sInter_singleton]
    obtain ⟨a, ha⟩ := hne
    have hadiff : ∃ A' ∈ 𝒜', A' ≠ A := by
      by_contra hcon
      push Not at hcon
      have hAmem : A ∈ 𝒜' := (hcon a ha) ▸ ha
      have hEq : 𝒜' = {A} := by
        apply Set.Subset.antisymm
        · intro x hx; rw [Set.mem_singleton_iff]; exact hcon x hx
        · intro x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ hAmem
      rw [hEq, Set.sInter_singleton] at hnotA
      exact hnotA (Set.Subset.refl A)
    obtain ⟨A', hA'mem, hA'ne⟩ := hadiff
    have hIA' : ⋂₀ 𝒜' ⊆ A' := Set.sInter_subset_of_mem hA'mem
    have hRcap : R ∩ ⋂₀ 𝒜' = ∅ := by
      have hsub' : R ∩ ⋂₀ 𝒜' ⊆ R ∩ A' :=
        Set.inter_subset_inter_right R hIA'
      rw [hsel A' (hsub hA'mem) hA'ne] at hsub'
      exact Set.subset_empty_iff.mp hsub'
    have hImpZero : μ.impactRatio R (⋂₀ 𝒜') = 0 := by
      unfold PMF.impactRatio
      rw [PMF.condProbSet_eq_div, hRcap, PMF.probOfSet_empty,
          ENNReal.zero_div, ENNReal.zero_div]
    rw [hImpZero]
    exact hImpA_pos

/-- Trivial (universal) evidence answers no question: conditioning on `univ`
    changes nothing, so no resolution is strictly raised. -/
theorem not_answers_univ : ¬ Answers (Set.univ : Set W) Q μ := by
  rintro ⟨𝒜, hRes⟩
  have h := hRes.raises_prob
  rw [PMF.condProbSet_univ] at h
  exact lt_irrefl _ h

end Finite

/-! ### Resolution-as-projection -/

/-- The evidenced resolution as `Option (Set (Set W))`: `some 𝒜` for
    some witness when `Answers R Q μ` holds, `none` otherwise.
    Witness extraction uses `Classical.choose`, hence `noncomputable`.
    Evidenced resolutions are nested
    (`IsResolutionEvidencedBy.sInter_subset_or_subset`), so the strongest is
    the canonical `Q|_R` of [thomas-2026] Def 62; `Classical.choose` need not
    return it, since full set-uniqueness fails (weaker resolutions coexist). -/
noncomputable def resolutionEvidencedBy (Q : Question W) (R : Set W)
    (μ : PMF W) : Option (Set (Set W)) :=
  open Classical in
  if h : Answers R Q μ then some (Classical.choose h) else none

@[simp] theorem resolutionEvidencedBy_isSome_iff (Q : Question W)
    (R : Set W) (μ : PMF W) :
    (resolutionEvidencedBy Q R μ).isSome ↔ Answers R Q μ := by
  unfold resolutionEvidencedBy
  split <;> simp_all

theorem resolutionEvidencedBy_spec (Q : Question W) (R : Set W)
    (μ : PMF W) (h : resolutionEvidencedBy Q R μ = some 𝒜) :
    IsResolutionEvidencedBy Q 𝒜 R μ := by
  unfold resolutionEvidencedBy at h
  split at h
  · case _ hAns =>
    rw [← Option.some.inj h]
    exact Classical.choose_spec hAns
  · case _ => contradiction

/-! ### Resolution-level evidence comparison -/

/-- `R` evidences resolution `⋂₀ 𝒜` more strongly than `R'` does;
    `evidencesMore` with the `A` argument fixed to `⋂₀ 𝒜`.
    [thomas-2026] Def 63. -/
def evidencesResolutionMore (μ : PMF W) (𝒜 : Set (Set W))
    (R R' : Set W) : Prop :=
  evidencesMore μ (⋂₀ 𝒜) R R'

@[simp] theorem evidencesResolutionMore_iff (μ : PMF W) (𝒜 : Set (Set W))
    (R R' : Set W) :
    evidencesResolutionMore μ 𝒜 R R' ↔
      μ.condProbSet R (⋂₀ 𝒜) > μ.condProbSet R' (⋂₀ 𝒜) :=
  Iff.rfl

theorem evidencesResolutionMore_asymm
    (h : evidencesResolutionMore μ 𝒜 R R') :
    ¬ evidencesResolutionMore μ 𝒜 R' R :=
  evidencesMore_asymm h

theorem evidencesResolutionMore_trans
    (h : evidencesResolutionMore μ 𝒜 R R')
    (h' : evidencesResolutionMore μ 𝒜 R' R'') :
    evidencesResolutionMore μ 𝒜 R R'' :=
  evidencesMore_trans h h'

/-! ### Probabilistic relevance ([thomas-2026] Def 61)

The weaker companion of `Answers`: `R` is *relevant* to `Q` if some
alternative of `Q` has its prior shifted by conditioning on some
alternative of `R`. Used in [thomas-2026] §5.4.3 to license
*too*'s prejacent against an implicit "Relevant Question" rather than
a Current Question — an RQ need not be a CQ, only relevant to one. -/

/-- `R` is **relevant** to `Q` (under prior `μ`): some alternative of
    `R` shifts the probability of some alternative of `Q`.
    [thomas-2026] Def 61. The relation is also lifted to
    declarative-as-singleton-issue contexts via `IsRelevantOf`. -/
def IsRelevantTo (R Q : Question W) (μ : PMF W) : Prop :=
  ∃ A ∈ alt R, ∃ A' ∈ alt Q, μ.condProbSet A A' ≠ μ.probOfSet A'

/-- A *proposition* `R` is relevant to a question `Q` if conditioning
    on `R` shifts the probability of some alternative of `Q`.
    The "assertion-to-question" instance of [thomas-2026] Def 61. -/
def IsRelevantPropOf (R : Set W) (Q : Question W) (μ : PMF W) : Prop :=
  ∃ A' ∈ alt Q, μ.condProbSet R A' ≠ μ.probOfSet A'

/-- The defining unfolding of `IsRelevantPropOf`. -/
@[simp] theorem isRelevantPropOf_iff (R : Set W) (Q : Question W) (μ : PMF W) :
    IsRelevantPropOf R Q μ ↔
      ∃ A' ∈ alt Q, μ.condProbSet R A' ≠ μ.probOfSet A' :=
  Iff.rfl

/-! ### Bridge: `Answers` ⇒ `IsRelevantPropOf`

[thomas-2026] §5.1.3 asserts "all Answers are Relevant, but not all Relevant
assertions are Answers." The forward direction does not hold mechanically: a
strict inequality on `condProbSet R (⋂₀ 𝒜)` need not imply that some single
`A ∈ alt Q` has `condProbSet R A ≠ probOfSet A`, because the conditional
probability of an intersection does not decompose into those of its components
without an independence assumption. Positivity of the prior on each alternative
is **not** sufficient — `R` can correlate with the conjunction while leaving
every marginal fixed. It does hold unconditionally for **singleton**
(mention-some/one) resolutions, and in general once the prior propagates
marginal irrelevance to the resolution. -/

/-- For a **singleton** resolution `{A}`, answerhood evidence is directly
    relevance to `Q`: `R` raises `P(A)` and `A ∈ alt Q`. The mention-some/one
    instance of [thomas-2026] §5.1.3. -/
theorem IsResolutionEvidencedBy.isRelevantPropOf_singleton
    (h : IsResolutionEvidencedBy Q {A} R μ) : IsRelevantPropOf R Q μ := by
  refine ⟨A, h.subset_alt (Set.mem_singleton_iff.mpr rfl), ?_⟩
  have hr := h.raises_prob
  rw [Set.sInter_singleton] at hr
  exact ne_of_gt hr

/-- General forward bridge under an explicit independence hypothesis: if the
    prior carries marginal irrelevance (`R` shifts no alternative of `Q`) to
    the resolution `⋂₀ 𝒜`, then any evidenced resolution makes `R` relevant to
    `Q`. The hypothesis is exactly the non-degeneracy [thomas-2026] §5.1.3
    leaves implicit. -/
theorem IsResolutionEvidencedBy.isRelevantPropOf
    (hRes : IsResolutionEvidencedBy Q 𝒜 R μ)
    (hindep : (∀ A' ∈ alt Q, μ.condProbSet R A' = μ.probOfSet A') →
      μ.condProbSet R (⋂₀ 𝒜) = μ.probOfSet (⋂₀ 𝒜)) :
    IsRelevantPropOf R Q μ := by
  by_contra hcon
  unfold IsRelevantPropOf at hcon
  push Not at hcon
  exact absurd (hindep hcon) (ne_of_gt hRes.raises_prob)

end Semantics.Questions.Probabilistic
