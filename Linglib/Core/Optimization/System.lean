import Linglib.Core.Optimization.Decoder

/-!
# Scored choice systems

A `ConstraintSystem Cand Score` packages the three components of a
scored-choice problem into a single record:

  1. a finite `candidates : Finset Cand`,
  2. a `score : Cand → Score` function, and
  3. a `decoder : Decoder Cand Score` mapping scored candidates to a
     probability distribution.

```
  Candidates  ──score──▶  Score   ──decoder──▶   P : Cand → ℝ
```

Every system exposes a single `predict` operation. Probability-preserving
decoders (`Decoder.IsProb`) yield non-negative predictions that sum to 1.

A closed-form `predict` and standard monotonicity / equiprobability /
sum-to-one lemmas for the `softmaxDecoder` specialisation also live here,
since they depend only on the record + `softmaxDecoder` from `Decoder.lean`
— no domain-specific score type is required.

Domain-specific instantiations (lex-min on integer cost vectors,
weighted-sum scoring, softmax over weighted sums, ...) live in the
consuming layer.
-/

namespace Core.Optimization

/-- A scored-choice system: candidate set + score function + decoder. -/
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

/-! ### Softmax-decoder specialisations

Closed-form / monotonicity / equiprobability lemmas for
`ConstraintSystem`s whose `decoder = softmaxDecoder α`. The hypothesis
`hd : s.decoder = softmaxDecoder α` is `rfl` for the explicit-record
construction pattern.
-/

namespace ConstraintSystem

variable {Cand : Type*} (s : ConstraintSystem Cand ℝ)

/-- For a system whose decoder is `softmaxDecoder α`, the predicted
    probability of an in-set candidate has the standard closed form
    `exp(α · score(c)) / Σ exp(α · score(c'))`. -/
theorem predict_softmax_of_mem {α : ℝ} (hd : s.decoder = softmaxDecoder α)
    {c : Cand} (hc : c ∈ s.candidates) :
    s.predict c =
      Real.exp (α * s.score c) / ∑ c' ∈ s.candidates, Real.exp (α * s.score c') := by
  classical
  show s.decoder.decode s.candidates s.score c = _
  rw [hd]
  simp only [softmaxDecoder, if_pos hc]

/-- Softmax monotonicity: for `α > 0`, the in-set candidate with strictly
    higher score gets strictly higher predicted probability. -/
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
    probability. -/
theorem predict_softmax_eq_of_score_eq {α : ℝ}
    (hd : s.decoder = softmaxDecoder α)
    {c1 c2 : Cand} (h1 : c1 ∈ s.candidates) (h2 : c2 ∈ s.candidates)
    (heq : s.score c1 = s.score c2) :
    s.predict c1 = s.predict c2 := by
  rw [predict_softmax_of_mem _ hd h1, predict_softmax_of_mem _ hd h2, heq]

/-- For a system whose decoder is `softmaxDecoder α`, predicted
    probabilities sum to 1 over the (non-empty) candidate set.
    Specialises `predict_sum_eq_one` so consumers needn't supply
    the `IsProb` instance argument explicitly. -/
theorem predict_softmax_isProb {α : ℝ}
    (hd : s.decoder = softmaxDecoder α) (hne : s.candidates.Nonempty) :
    ∑ c ∈ s.candidates, s.predict c = 1 := by
  show ∑ c ∈ s.candidates, s.decoder.decode s.candidates s.score c = 1
  rw [hd]
  exact (softmaxDecoder_isProb α).sum_eq_one hne _

end ConstraintSystem

end Core.Optimization
