import Linglib.Core.Constraint.Decoder
import Linglib.Core.Constraint.Weighted
import Linglib.Core.Constraint.Profile
import Linglib.Core.Logic.OT

/-!
# Constraint Systems — The Unified Interface

A `ConstraintSystem` packages the three components of any
constraint-based grammar into a single record:

  1. a finite **candidate** set,
  2. a **score** function (whatever value type the framework needs), and
  3. a **decoder** that turns scored candidates into a probability
     distribution.

```
  Candidates  ──score──▶  Score   ──decoder──▶   P : Cand → ℝ
```

Different frameworks differ only in *what they pick for each component*.
Smart constructors below assemble the standard frameworks:

  - `otSystem`     — OT: `Score = LexProfile Nat n`, decoder = `argminDecoder`
  - `hgSystem`     — HG: `Score = ℝ`, decoder = `argmaxDecoder`
  - `maxEntSystem` — MaxEnt: `Score = ℝ`, decoder = `softmaxDecoder α`

Every system exposes a single `predict` operation, so downstream code
can compare frameworks (or replace one with another) without touching
the rest of the analysis.

Stochastic frameworks that put noise on weights or candidates
(NHG, Normal MaxEnt, Stochastic OT) are RUM specializations: the
noise kernel composes with the deterministic decoder. See
`NoiseKernel.lean` for the Dirac / Gumbel / Gaussian bridges.
-/

namespace Core.Constraint

-- ============================================================================
-- § 1: ConstraintSystem
-- ============================================================================

/-- A constraint-based grammar: candidate set + score function + decoder.

    `Cand` is the candidate type (often something like an output form,
    a syntactic structure, or an input/output pair). `Score` is whatever
    value the constraints aggregate to — `ℝ` for HG/MaxEnt, `LexProfile
    Nat n` for OT, etc. -/
structure ConstraintSystem (Cand : Type*) (Score : Type*) where
  /-- The finite set of candidates this system evaluates. -/
  candidates : Finset Cand
  /-- The aggregated score for each candidate. -/
  score : Cand → Score
  /-- The choice rule: scored candidates → probability distribution. -/
  decoder : Decoder Cand Score

namespace ConstraintSystem

variable {Cand : Type*} {Score : Type*}

/-- The predicted probability of each candidate. -/
def predict (s : ConstraintSystem Cand Score) : Cand → ℝ :=
  s.decoder.decode s.candidates s.score

/-- A system whose decoder is `IsProb` produces non-negative predictions. -/
theorem predict_nonneg (s : ConstraintSystem Cand Score)
    [Decoder.IsProb s.decoder] (c : Cand) :
    0 ≤ s.predict c :=
  Decoder.IsProb.nonneg s.candidates s.score c

/-- A system whose decoder is `IsProb` predicts a probability distribution
    over its candidate set. -/
theorem predict_sum_eq_one (s : ConstraintSystem Cand Score)
    [Decoder.IsProb s.decoder] (hne : s.candidates.Nonempty) :
    ∑ c ∈ s.candidates, s.predict c = 1 :=
  Decoder.IsProb.sum_eq_one hne s.score

end ConstraintSystem

-- ============================================================================
-- § 2: Smart Constructors
-- ============================================================================

/-- Build an Optimality Theory system: lexicographic minimum on a violation
    profile. The candidate set must be finite; `profile c` gives the
    `n`-tuple of constraint violations for candidate `c` ranked in
    order of dominance.

    Equivalent to choosing the OT winner(s) by `argmin` on the lex order. -/
noncomputable def otSystem {Cand : Type*} {n : Nat}
    (candidates : Finset Cand) (profile : Cand → LexProfile Nat n) :
    ConstraintSystem Cand (LexProfile Nat n) where
  candidates := candidates
  score := profile
  decoder := argminDecoder

/-- Build a (deterministic) Harmonic Grammar system: real-valued harmony
    score, choose the candidate(s) that maximise it.

    The harmony score is `harmonyScoreR constraints c = -Σⱼ wⱼ · Cⱼ(c)`.
    Higher harmony = lower (weighted) violation = more grammatical. -/
noncomputable def hgSystem {Cand : Type}
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand)) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := argmaxDecoder

/-- Build a MaxEnt Harmonic Grammar system: same harmony score as `hgSystem`,
    but soft-decode with temperature `α`. As `α → ∞`, this converges to
    `hgSystem` (see `softmax_argmax_limit` in `Core.Agent.RationalAction`).

    The default `α = 1` matches @cite{goldwater-johnson-2003}'s
    standard MaxEnt formulation. -/
noncomputable def maxEntSystem {Cand : Type}
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand))
    (α : ℝ := 1) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := softmaxDecoder α

-- ============================================================================
-- § 3: Tableau Bridge
-- ============================================================================

/-! `Core.ConstraintEvaluation.Tableau` is the established study-file API for
OT (used by `mkTableau ... .optimal = {winner}` patterns). The bridge below
shows that `Tableau` is a special case of `ConstraintSystem`: the OT score
`profile : C → ViolationProfile n` is exactly a `LexProfile Nat n`-valued
score (definitionally), and `Tableau.optimal` is exactly the support of the
`argminDecoder` distribution. So existing OT studies can keep their
`Tableau`/`optimal` formulation and additionally expose the unified
`ConstraintSystem.predict` view via `tableauSystem`. -/

open Core.ConstraintEvaluation

/-- An OT tableau viewed as a generic `ConstraintSystem`. The score type
    `LexProfile Nat n` is definitionally `ViolationProfile n`, so the
    `argminDecoder`'s `LinearOrder` requirement is satisfied by the
    standard `Pi.Lex` instance. -/
noncomputable def tableauSystem {C : Type} [DecidableEq C] {n : Nat}
    (t : Tableau C n) : ConstraintSystem C (LexProfile Nat n) where
  candidates := t.candidates
  score := t.profile
  decoder := argminDecoder

/-- The unifying identity: `tableauSystem`'s prediction is uniform over
    `Tableau.optimal`. Since `Tableau.optimal` IS the argmin filter set
    by definition, the `argminDecoder` reduces to the standard "uniform
    over winners" formula. All other bridge results follow. -/
theorem tableauSystem_predict_eq {C : Type} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    (tableauSystem t).predict c =
      (if c ∈ t.optimal then ((t.optimal.card : ℝ))⁻¹ else 0) := by
  have hfilter : t.optimal = (t.candidates.filter
      (fun c' => ∀ c'' ∈ t.candidates, t.profile c' ≤ t.profile c'')) := by
    ext x
    simp only [Finset.mem_filter, Tableau.optimal]
  show argminDecoder.decode t.candidates t.profile c = _
  unfold argminDecoder
  simp only
  rw [hfilter]
  congr

/-- A candidate is in the support of the `tableauSystem` distribution
    iff it is in the tableau's optimal set. -/
theorem tableauSystem_predict_pos_iff_optimal {C : Type} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (c : C) :
    0 < (tableauSystem t).predict c ↔ c ∈ t.optimal := by
  rw [tableauSystem_predict_eq]
  by_cases hc : c ∈ t.optimal
  · have hcard : 0 < (t.optimal.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c, hc⟩)
    simp [hc, inv_pos.mpr hcard]
  · simp [hc]

/-- When `Tableau.optimal = {winner}` (the typical deterministic-OT pattern
    used in study files via `by decide`), the unified `predict` view assigns
    probability 1 to the winner. -/
theorem tableauSystem_predict_unique_winner {C : Type} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (winner : C) (h : t.optimal = {winner}) :
    (tableauSystem t).predict winner = 1 := by
  rw [tableauSystem_predict_eq, h]; simp

/-- And losers in a unique-winner tableau receive probability 0. -/
theorem tableauSystem_predict_loser {C : Type} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (winner loser : C) (hne : loser ≠ winner)
    (h : t.optimal = {winner}) :
    (tableauSystem t).predict loser = 0 := by
  rw [tableauSystem_predict_eq, h]; simp [hne]

-- ============================================================================
-- § 4: MaxEnt Prediction Lemmas
-- ============================================================================

/-! Closed-form, monotonicity, and probability-distribution lemmas for
`ConstraintSystem`s decoded by `softmaxDecoder`. The hypothesis
`hd : s.decoder = softmaxDecoder α` is `rfl` for systems built via
`maxEntSystem` or via the explicit-record pattern study files use
(`{ candidates := …, score := …, decoder := softmaxDecoder 1 }`), so
study-file proofs collapse to one-line delegations. -/

namespace ConstraintSystem

variable {Cand : Type*} (s : ConstraintSystem Cand ℝ)

/-- For a system whose decoder is `softmaxDecoder α`, the predicted
    probability of an in-set candidate has the standard MaxEnt closed form
    `exp(α · score(c)) / Σ exp(α · score(c'))`. -/
theorem predict_softmax_of_mem {α : ℝ} (hd : s.decoder = softmaxDecoder α)
    {c : Cand} (hc : c ∈ s.candidates) :
    s.predict c =
      Real.exp (α * s.score c) / ∑ c' ∈ s.candidates, Real.exp (α * s.score c') := by
  classical
  show s.decoder.decode s.candidates s.score c = _
  rw [hd]
  simp only [softmaxDecoder, if_pos hc]

/-- Softmax monotonicity: for `α > 0` and both candidates in the candidate
    set, the candidate with strictly higher score gets strictly higher
    predicted probability. Lets MaxEnt study files derive ranking facts
    from raw harmony comparisons in one line. -/
theorem predict_softmax_lt_of_score_lt {α : ℝ} (hα : 0 < α)
    (hd : s.decoder = softmaxDecoder α)
    {c1 c2 : Cand} (h1 : c1 ∈ s.candidates) (h2 : c2 ∈ s.candidates)
    (hlt : s.score c1 < s.score c2) :
    s.predict c1 < s.predict c2 := by
  rw [predict_softmax_of_mem _ hd h1, predict_softmax_of_mem _ hd h2]
  have hZ : (0 : ℝ) < ∑ c' ∈ s.candidates, Real.exp (α * s.score c') :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨c1, h1⟩
  rw [div_lt_div_iff_of_pos_right hZ]
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hlt hα)

/-- Softmax equality: candidates with equal scores get equal predicted
    probability. Lets MaxEnt study files derive equiprobability from raw
    score equality in one line. -/
theorem predict_softmax_eq_of_score_eq {α : ℝ}
    (hd : s.decoder = softmaxDecoder α)
    {c1 c2 : Cand} (h1 : c1 ∈ s.candidates) (h2 : c2 ∈ s.candidates)
    (heq : s.score c1 = s.score c2) :
    s.predict c1 = s.predict c2 := by
  rw [predict_softmax_of_mem _ hd h1, predict_softmax_of_mem _ hd h2, heq]

/-- For a system whose decoder is `softmaxDecoder α`, predicted
    probabilities sum to 1 over the (non-empty) candidate set.
    Specialises `predict_sum_eq_one` so study files needn't supply
    the `IsProb` instance argument explicitly. -/
theorem predict_softmax_isProb {α : ℝ}
    (hd : s.decoder = softmaxDecoder α) (hne : s.candidates.Nonempty) :
    ∑ c ∈ s.candidates, s.predict c = 1 := by
  show ∑ c ∈ s.candidates, s.decoder.decode s.candidates s.score c = 1
  rw [hd]
  exact (softmaxDecoder_isProb α).sum_eq_one hne _

end ConstraintSystem

end Core.Constraint
