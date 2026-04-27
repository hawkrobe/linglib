import Linglib.Core.Question.Basic
import Linglib.Core.Probability.PMFFin
import Linglib.Theories.Semantics.Questions.Resolution

/-!
# Probabilistic Question Semantics
@cite{thomas-2026} @cite{ippolito-kiss-williams-2025} @cite{westera-brasoveanu-2014} @cite{onea-2019}

Bayesian inquisitive answerhood. The probabilistic refinement of the
set-theoretic resolution relation in `Resolution.lean`: a state σ
"answers" a question Q under a prior μ to the extent that
conditioning μ on σ shifts mass toward some *resolution* of Q (a
conjunction of alternatives, in the inquisitive sense of
@cite{ciardelli-groenendijk-roelofsen-2018}).

## Key API

- `evidencesMore μ A R R'` — Bayesian comparator: `R` provides more
  evidence for `A` than `R'` does. @cite{thomas-2026} Def 63
  (operator-level).

- `IsResolutionEvidencedBy Q 𝒜 R μ` — structure with four named
  fields capturing @cite{thomas-2026} Def 62: `𝒜 ⊆ alt Q` is
  nonempty, `R` raises `P(⋂𝒜)`, and the impact ratio of `⋂𝒜`
  strictly dominates that of any competing intersection.

- `Answers R Q μ` — `R` answers `Q`: an evidenced resolution exists.
  @cite{thomas-2026} Def 62.

- `resolutionEvidencedBy Q R μ : Option (Set (Set W))` — the evidenced
  resolution as a `Classical.choose`-extracted witness, `none` when
  `Answers` fails.

- `evidencesResolutionMore μ 𝒜 R R'` — resolution-level analogue of
  `evidencesMore`. @cite{thomas-2026} Def 63.
-/

namespace Semantics.Questions.Probabilistic

open Core Core.Question PMF

variable {W : Type*} {μ : PMF W} {A R R' R'' : Set W}
  {Q : Question W} {𝒜 𝒜' : Set (Set W)}

/-! ### Bayesian evidence comparator -/

/-- `R` evidences `A` more strongly than `R'` does:
    `P(A | R) > P(A | R')`. @cite{thomas-2026} Def 63. -/
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
(@cite{thomas-2026} §1.2, @cite{ippolito-kiss-williams-2025} Def. 13)
can refer to it directly. -/

/-- `R` provides **positive evidence** for `A`: conditioning on `R`
    raises the probability of `A`. -/
def IsPositiveEvidence (R A : Set W) (μ : PMF W) : Prop :=
  μ.condProbSet R A > μ.probOfSet A

theorem IsPositiveEvidence.probOfSet_pos
    (h : IsPositiveEvidence R A μ) : μ.probOfSet R > 0 :=
  PMF.probOfSet_pos_of_condProbSet_gt μ R A h

/-! ### Resolution evidenced by `R` (@cite{thomas-2026} Def 62) -/

/-- `𝒜 ⊆ alt Q` is the resolution of `Q` evidenced by `R` under prior
    `μ`. @cite{thomas-2026} Def 62.

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
    intersection `⋂₀ 𝒜` is what @cite{thomas-2026} calls "the
    resolution of `Q` evidenced by `R`" (notation `Q|_R`). -/
structure IsResolutionEvidencedBy (Q : Question W) (𝒜 : Set (Set W))
    (R : Set W) (μ : PMF W) : Prop where
  subset_alt  : 𝒜 ⊆ alt Q
  nonempty    : 𝒜.Nonempty
  raises_prob : μ.condProbSet R (⋂₀ 𝒜) > μ.probOfSet (⋂₀ 𝒜)
  dominates   : ∀ 𝒜' : Set (Set W),
    𝒜' ⊆ alt Q → 𝒜'.Nonempty → ¬ ⋂₀ 𝒜 ⊆ ⋂₀ 𝒜' →
    μ.impactRatio R (⋂₀ 𝒜) > μ.impactRatio R (⋂₀ 𝒜')

/-! ### Probabilistic answerhood -/

/-- `R` **answers** `Q` (under prior `μ`): an evidenced resolution
    exists. @cite{thomas-2026} Def 62. -/
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

/-! ### Resolution-as-projection -/

/-- The evidenced resolution as `Option (Set (Set W))`: `some 𝒜` for
    some witness when `Answers R Q μ` holds, `none` otherwise.
    Witness extraction uses `Classical.choose`, hence `noncomputable`.
    Uniqueness of `⋂₀ 𝒜` (the "resolution of `Q` evidenced by `R`" in
    @cite{thomas-2026} Def 62 prose) is a consumer-side claim that
    follows from the `dominates` field under appropriate side
    conditions. -/
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
    @cite{thomas-2026} Def 63. -/
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

/-! ### Probabilistic relevance (@cite{thomas-2026} Def 61)

The weaker companion of `Answers`: `R` is *relevant* to `Q` if some
alternative of `Q` has its prior shifted by conditioning on some
alternative of `R`. Used in @cite{thomas-2026} §5.4.3 to license
*too*'s prejacent against an implicit "Relevant Question" rather than
a Current Question — an RQ need not be a CQ, only relevant to one. -/

/-- `R` is **relevant** to `Q` (under prior `μ`): some alternative of
    `R` shifts the probability of some alternative of `Q`.
    @cite{thomas-2026} Def 61. The relation is also lifted to
    declarative-as-singleton-issue contexts via `IsRelevantOf`. -/
def IsRelevantTo (R Q : Question W) (μ : PMF W) : Prop :=
  ∃ A ∈ alt R, ∃ A' ∈ alt Q, μ.condProbSet A A' ≠ μ.probOfSet A'

/-- A *proposition* `R` is relevant to a question `Q` if conditioning
    on `R` shifts the probability of some alternative of `Q`.
    The "assertion-to-question" instance of @cite{thomas-2026} Def 61. -/
def IsRelevantPropOf (R : Set W) (Q : Question W) (μ : PMF W) : Prop :=
  ∃ A' ∈ alt Q, μ.condProbSet R A' ≠ μ.probOfSet A'

/-- The defining unfolding of `IsRelevantPropOf`. -/
@[simp] theorem isRelevantPropOf_iff (R : Set W) (Q : Question W) (μ : PMF W) :
    IsRelevantPropOf R Q μ ↔
      ∃ A' ∈ alt Q, μ.condProbSet R A' ≠ μ.probOfSet A' :=
  Iff.rfl

/-! ### Doxastic support (@cite{ippolito-kiss-williams-2025} Def. 13)

A sentence `S` "supports" a target proposition `r` from doxastic state
`dox` under prior `μ` if some alternative `q ∈ alt S` is *believed* by
the speaker (`dox ⊆ q`) and *positively evidences* `r`. The doxastic
anchor is what distinguishes `Supports` from raw Bayesian evidence: a
speaker who doesn't believe any alternative of `S` cannot use `S` to
support anything. This is what derives the
@cite{ippolito-kiss-williams-2025} §5.2 interrogative-left-argument
restriction from architecture rather than stipulation. -/

/-- `S` **supports** `r` from doxastic state `dox` under prior `μ`:
    some alternative `q ∈ alt S` is doxastically grounded (`dox ⊆ q`)
    and provides positive evidence for `r`.
    @cite{ippolito-kiss-williams-2025} Def. 13. -/
def Supports (dox : Set W) (S : Question W) (r : Set W) (μ : PMF W) : Prop :=
  ∃ q ∈ alt S, dox ⊆ q ∧ IsPositiveEvidence q r μ

/-- An info-seeking speaker — one who doesn't believe any alternative of
    `S` — cannot use `S` to support anything. The architectural
    derivation of @cite{ippolito-kiss-williams-2025} §5.2's
    interrogative-left-argument restriction: the failure isn't a
    clause-type filter but a doxastic consequence of `Supports`. -/
theorem Supports.of_no_belief_fails {dox : Set W} {S : Question W}
    {r : Set W} {μ : PMF W}
    (h : ∀ q ∈ alt S, ¬ (dox ⊆ q)) :
    ¬ Supports dox S r μ := by
  rintro ⟨q, hq, hdox, _⟩
  exact h q hq hdox

/-- `Supports dox S r μ` exposes a doxastically-grounded alternative
    of `S` containing `dox`. The bridge from probabilistic support to
    pure inquisitive `Resolves`-style witnesses. -/
theorem Supports.exists_dox_alt {dox : Set W} {S : Question W}
    {r : Set W} {μ : PMF W}
    (h : Supports dox S r μ) :
    ∃ p ∈ alt S, dox ⊆ p := by
  obtain ⟨p, hp, hdox, _⟩ := h
  exact ⟨p, hp, hdox⟩

/-! ### Agreement and disagreement (@cite{ippolito-kiss-williams-2025} Def. 14) -/

/-- Two sentences `S` and `S'` **agree** on QUD `Q` from doxastic state
    `dox` iff some alternative `α ∈ alt Q` is supported by both.
    @cite{ippolito-kiss-williams-2025} Def. 14a. -/
def Agree (dox : Set W) (S S' Q : Question W) (μ : PMF W) : Prop :=
  ∃ α ∈ alt Q, Supports dox S α μ ∧ Supports dox S' α μ

/-- Two sentences `S` and `S'` **disagree** on QUD `Q` from doxastic
    state `dox` iff each supports some answer but no shared alternative
    witnesses agreement.
    @cite{ippolito-kiss-williams-2025} Def. 14b. -/
def Disagree (dox : Set W) (S S' Q : Question W) (μ : PMF W) : Prop :=
  (∃ α ∈ alt Q, Supports dox S α μ) ∧
  (∃ α ∈ alt Q, Supports dox S' α μ) ∧
  ¬ Agree dox S S' Q μ

/-- `Agree` is symmetric in its `S`/`S'` arguments. -/
theorem Agree.symm {dox : Set W} {S S' Q : Question W} {μ : PMF W}
    (h : Agree dox S S' Q μ) : Agree dox S' S Q μ := by
  obtain ⟨α, hMem, hS, hS'⟩ := h
  exact ⟨α, hMem, hS', hS⟩

/-- `Disagree` is symmetric in its `S`/`S'` arguments. -/
theorem Disagree.symm {dox : Set W} {S S' Q : Question W} {μ : PMF W}
    (h : Disagree dox S S' Q μ) : Disagree dox S' S Q μ := by
  obtain ⟨hS, hS', hNotAgree⟩ := h
  exact ⟨hS', hS, fun hAgree => hNotAgree hAgree.symm⟩

/-! ### Bridge claim: `Answers` ⇒ `IsRelevantPropOf`

@cite{thomas-2026} §5.1.3 informally asserts "all Answers are
Relevant, but not all Relevant assertions are Answers." The forward
direction is non-trivial in the substrate: a strict inequality on
`condProbSet R (⋂₀ 𝒜)` does not mechanically imply that some
`A ∈ alt Q` has `condProbSet R A ≠ probOfSet A`, because conditional
probability of an intersection does not decompose into conditional
probabilities of its components without independence assumptions.

The bridge holds under standard non-degeneracy hypotheses (e.g., the
prior is positive on every alternative) and is proved consumer-side
in the relevant study files. -/

end Semantics.Questions.Probabilistic
