import Linglib.Core.Agent.RationalAction

/-!
# Decoders — From Scored Candidates to Probability Distributions
@cite{mcfadden-1974}

A `Decoder` is the *choice* component of a constraint-based grammar.
Given a finite set of candidates, each carrying a score, a decoder
returns a probability distribution over those candidates:

```
  scored candidates  --[Decoder]-->  P : Cand → ℝ
```

Different constraint frameworks correspond to different decoders. This
table shows how the major OT/HG-family frameworks all instantiate the
same `Decoder` interface, varying only the score type and the choice rule:

| Framework         | Score type           | Decoder                       |
|-------------------|----------------------|-------------------------------|
| OT                | `LexProfile Nat n`   | argmin (uniform over winners) |
| HG                | `ℝ` (harmony)        | argmax (uniform over winners) |
| MaxEnt            | `ℝ` (harmony)        | softmax (Gumbel-noise argmax) |
| Normal MaxEnt     | `ℝ` (harmony)        | probit (Gaussian-noise argmax)|
| NHG               | `ℝ` (harmony)        | weight-perturbed argmax       |
| Stochastic OT     | `LexProfile Nat n`   | ranking-perturbed argmin      |

The unifying principle is McFadden's Random Utility Model
(@cite{mcfadden-1974}): every stochastic decoder is "argmax after a
noise kernel applied to the scores". The noise distribution determines
the choice rule (Gumbel ⇒ softmax, Gaussian ⇒ probit, point-mass ⇒
deterministic argmax). Noise-kernel-based decoders live in a sibling
file; here we just expose the `Decoder` interface and the three
foundational instances.

## Zero-temperature bridge

`softmaxDecoder α` interpolates between MaxEnt-style soft optimization
and OT-style hard optimization: as `α → ∞`, the softmax distribution
concentrates on the unique maximizer (when one exists), recovering
`argmaxDecoder`. This is the formal statement of the OT-as-MaxEnt-limit
correspondence and is captured by `softmax_argmax_limit` in
`Core.Agent.RationalAction`.

## Semiring connection (deferred)

For *deterministic* (point-mass noise) decoders, the resulting
algebraic structure on scores is a semiring:

  - `argmaxDecoder` over `ℝ`         ↔  max-plus semiring
  - `argminDecoder` over `Tropical R` ↔  min-plus (tropical) semiring
  - `softmaxDecoder` over `ℝ`         ↔  log-sum-exp ("warped") semiring

The zero-temperature limit `softmax → argmax` is precisely the semiring
homomorphism `log-sum-exp → max` in the limit `α → ∞`. A separate
`Semiring.lean` file will make these bridges precise.
-/

namespace Core.Constraint

open Finset

-- ============================================================================
-- § 1: The Decoder Interface
-- ============================================================================

/-- A decoder maps scored candidates to a probability distribution.

    `Decoder Cand Score` packages a single function:
    given a finite candidate set and a `Score`-valued evaluation, return
    a real-valued probability for each candidate.

    The structure does not enforce that outputs are non-negative or sum
    to 1 — those are *properties* of well-behaved decoders, captured by
    `IsProbDecoder` below. Keeping the structure plain makes it easy to
    define non-normalized scoring functions (e.g., raw `exp(score)` rather
    than full softmax) and prove their probabilistic properties separately. -/
structure Decoder (Cand : Type*) (Score : Type*) where
  /-- Decode a finite scored candidate set into a probability assignment. -/
  decode : Finset Cand → (Cand → Score) → Cand → ℝ

namespace Decoder

variable {Cand : Type*} {Score : Type*}

/-- A decoder is a *probability* decoder when its outputs are non-negative
    and sum to 1 over any non-empty candidate set. -/
class IsProb (d : Decoder Cand Score) : Prop where
  /-- All decoded probabilities are non-negative. -/
  nonneg : ∀ (cands : Finset Cand) (score : Cand → Score) (c : Cand),
    0 ≤ d.decode cands score c
  /-- Decoded probabilities sum to 1 over any non-empty candidate set. -/
  sum_eq_one : ∀ {cands : Finset Cand}, cands.Nonempty →
    ∀ (score : Cand → Score), ∑ c ∈ cands, d.decode cands score c = 1

end Decoder

-- ============================================================================
-- § 2: Softmax Decoder (MaxEnt)
-- ============================================================================

open scoped Classical in
/-- The MaxEnt decoder: softmax over real-valued scores at temperature `α`.

    `decode cands score c = exp(α · score(c)) / Σ_{c' ∈ cands} exp(α · score(c'))`
    when `c ∈ cands`, and `0` otherwise.

    Equivalent to `Core.softmax` from `RationalAction.lean` but generalised
    from `Fintype` to a finite subset `cands` of a possibly-infinite type. -/
noncomputable def softmaxDecoder {Cand : Type*} (α : ℝ) : Decoder Cand ℝ where
  decode cands score := fun c =>
    if c ∈ cands then
      Real.exp (α * score c) / ∑ c' ∈ cands, Real.exp (α * score c')
    else 0

-- ============================================================================
-- § 3: Argmax / Argmin Decoders (HG, OT)
-- ============================================================================

open scoped Classical in
/-- The HG-style decoder: uniform distribution over the maximizers of
    `score` on `cands`. Deterministic (Dirac on the unique winner) when
    the maximum is achieved by exactly one candidate.

    Used by deterministic HG (with `Score = ℝ` and `score = harmonyScoreR`)
    and is the `α → ∞` limit of `softmaxDecoder` (see `softmax_argmax_limit`). -/
noncomputable def argmaxDecoder {Cand : Type*} {Score : Type*} [LinearOrder Score] :
    Decoder Cand Score where
  decode cands score := fun c =>
    let winners := cands.filter (fun c' => ∀ c'' ∈ cands, score c'' ≤ score c')
    if c ∈ winners then (winners.card : ℝ)⁻¹ else 0

open scoped Classical in
/-- The OT-style decoder: uniform distribution over the minimizers of
    `score` on `cands`.

    For Optimality Theory, instantiate with `Score = LexProfile Nat n`,
    so that the lexicographic minimum on the violation-count profile
    selects the optimal candidate(s). With a strict total ranking and a
    single optimum, this is a Dirac on the OT winner. -/
noncomputable def argminDecoder {Cand : Type*} {Score : Type*} [LinearOrder Score] :
    Decoder Cand Score where
  decode cands score := fun c =>
    let winners := cands.filter (fun c' => ∀ c'' ∈ cands, score c' ≤ score c'')
    if c ∈ winners then (winners.card : ℝ)⁻¹ else 0

-- ============================================================================
-- § 4: Probability Properties
-- ============================================================================

open scoped Classical

/-- The softmax decoder is a proper probability decoder: outputs are
    non-negative and sum to 1 over any non-empty candidate set. -/
instance softmaxDecoder_isProb {Cand : Type*} (α : ℝ) :
    Decoder.IsProb (softmaxDecoder (Cand := Cand) α) where
  nonneg cands score c := by
    simp only [softmaxDecoder]
    split_ifs
    · exact div_nonneg (Real.exp_nonneg _)
        (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))
    · exact le_refl 0
  sum_eq_one := by
    intro cands hne score
    have hZ : 0 < ∑ c' ∈ cands, Real.exp (α * score c') :=
      Finset.sum_pos (fun c _ => Real.exp_pos _) hne
    show ∑ c ∈ cands, (softmaxDecoder α).decode cands score c = 1
    simp only [softmaxDecoder]
    rw [Finset.sum_congr rfl (fun c hc =>
      show (if c ∈ cands then Real.exp (α * score c) /
                ∑ c' ∈ cands, Real.exp (α * score c') else 0)
            = Real.exp (α * score c) / ∑ c' ∈ cands, Real.exp (α * score c')
        from if_pos hc)]
    rw [← Finset.sum_div, div_self (ne_of_gt hZ)]

/-- For a non-empty candidate set with a linearly ordered score, the
    set of maximizers is non-empty. (A standard `Finset.exists_max_image`
    result, packaged for the decoder proofs below.) -/
private lemma exists_argmax {Cand Score : Type*} [LinearOrder Score]
    {cands : Finset Cand} (hne : cands.Nonempty) (score : Cand → Score) :
    ∃ c ∈ cands, ∀ c' ∈ cands, score c' ≤ score c := by
  obtain ⟨c, hc, hmax⟩ := cands.exists_max_image score hne
  exact ⟨c, hc, hmax⟩

private lemma exists_argmin {Cand Score : Type*} [LinearOrder Score]
    {cands : Finset Cand} (hne : cands.Nonempty) (score : Cand → Score) :
    ∃ c ∈ cands, ∀ c' ∈ cands, score c ≤ score c' := by
  obtain ⟨c, hc, hmin⟩ := cands.exists_min_image score hne
  exact ⟨c, hc, hmin⟩

/-- Helper: the uniform-over-a-subset decoder pattern.
    `∑ c ∈ outer, (if c ∈ inner then n else 0) = (inner.card : ℝ) * n`
    when `inner ⊆ outer`. -/
private lemma sum_uniform_subset {Cand : Type*} (inner outer : Finset Cand)
    (h_sub : inner ⊆ outer) (n : ℝ) :
    ∑ c ∈ outer, (if c ∈ inner then n else 0) = (inner.card : ℝ) * n := by
  classical
  rw [Finset.sum_ite_mem, Finset.inter_comm, Finset.inter_eq_left.mpr h_sub,
      Finset.sum_const, nsmul_eq_mul]

/-- The argmax decoder is a proper probability decoder. The non-trivial part
    is that the set of winners is non-empty when `cands` is, so the uniform
    distribution `1/winners.card` makes sense. -/
instance argmaxDecoder_isProb {Cand Score : Type*} [LinearOrder Score] :
    Decoder.IsProb (argmaxDecoder (Cand := Cand) (Score := Score)) where
  nonneg cands score c := by
    simp only [argmaxDecoder]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_refl 0
  sum_eq_one := by
    intro cands hne score
    set winners := cands.filter (fun c' => ∀ c'' ∈ cands, score c'' ≤ score c')
      with hwinners
    have hwinners_ne : winners.Nonempty := by
      obtain ⟨c, hc, hmax⟩ := exists_argmax hne score
      exact ⟨c, by simpa [hwinners, Finset.mem_filter] using ⟨hc, hmax⟩⟩
    have hwinners_sub : winners ⊆ cands := Finset.filter_subset _ _
    have hcard_pos : 0 < winners.card := Finset.card_pos.mpr hwinners_ne
    have hcard_ne : (winners.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
    show ∑ c ∈ cands, (argmaxDecoder.decode cands score c) = 1
    simp only [argmaxDecoder, ← hwinners]
    rw [sum_uniform_subset winners cands hwinners_sub _]
    field_simp

/-- The argmin decoder is a proper probability decoder. Symmetric to the
    argmax case. -/
instance argminDecoder_isProb {Cand Score : Type*} [LinearOrder Score] :
    Decoder.IsProb (argminDecoder (Cand := Cand) (Score := Score)) where
  nonneg cands score c := by
    simp only [argminDecoder]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_refl 0
  sum_eq_one := by
    intro cands hne score
    set winners := cands.filter (fun c' => ∀ c'' ∈ cands, score c' ≤ score c'')
      with hwinners
    have hwinners_ne : winners.Nonempty := by
      obtain ⟨c, hc, hmin⟩ := exists_argmin hne score
      exact ⟨c, by simpa [hwinners, Finset.mem_filter] using ⟨hc, hmin⟩⟩
    have hwinners_sub : winners ⊆ cands := Finset.filter_subset _ _
    have hcard_pos : 0 < winners.card := Finset.card_pos.mpr hwinners_ne
    have hcard_ne : (winners.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
    show ∑ c ∈ cands, (argminDecoder.decode cands score c) = 1
    simp only [argminDecoder, ← hwinners]
    rw [sum_uniform_subset winners cands hwinners_sub _]
    field_simp

end Core.Constraint
