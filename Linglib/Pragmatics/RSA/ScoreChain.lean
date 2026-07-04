import Linglib.Core.Probability.Scores

/-!
# RSA score chains in ℚ≥0

Combinators for the exact-rational face of RSA models: literal listener,
exponentiated speaker with cost, joint pragmatic listener, marginals, and
stacked higher-order speakers. A study composes these into its chain and
wraps normalization sites with `PMF.ofScores`; predictions then reduce to
`ℚ≥0` comparisons closed by `decide +kernel` via the `PMF.ofScores_lt`
family.

`s1` applies `PMF.scoresWith` mid-tower, so a zero-mass utterance row takes
its declared fallback *inside* the ℚ≥0 values — downstream marginals are
total and the PMF bridges need no side conditions.

Scope: this face covers natural-`α`, rational-parameter models. Models with
transcendental ingredients state their chains on the `ℝ≥0∞`
`RSA.Canonical`/operator face with kernel-certified rational bounds on
named atoms.

## Main definitions

* `RSA.Score.l0` — literal listener from a Boolean meaning and a prior.
* `RSA.Score.s1` — speaker scores `l0^α · cost`, fallback-completed.
* `RSA.Score.l1Joint` — joint pragmatic-listener scores over `W × Lat`.
* `RSA.Score.worldMarginal` / `latentMarginal` — marginals of joint scores.
* `RSA.Score.s2` — stacked speaker over listener coordinates.

## Kernel hygiene

* Declare the full instance set on ℚ≥0-face sections:
  `[Fintype _] [DecidableEq _] [Nonempty _]`.
* Base tables are pattern matches or `Bool` tables — never propositional
  `if x = y` over a derived `DecidableEq`; one such `ite` anywhere in the
  chain blocks kernel reduction of every order comparison above it.
* Prefer strict-bound sandwiches over equalities with literals.
* Certify every numeric claim externally (exact fractions, mirroring the
  Lean definitions including fallback semantics) before proving.
-/

open scoped NNRat

namespace RSA.Score

variable {U W Lat : Type*} [Fintype U] [Fintype W] [Fintype Lat]

/-- Literal listener: prior conditioned on the meaning's truth, row-wise
(`÷0 = 0` on utterances true nowhere; speakers complete such rows via
their fallback). -/
def l0 (meaning : U → W → Bool) (prior : W → ℚ≥0) (u : U) (w : W) : ℚ≥0 :=
  (if meaning u w then prior w else 0) /
    ∑ w', if meaning u w' then prior w' else 0

/-- Speaker scores: `(l0 u w)^α · cost u`, normalized over utterances and
completed by `fb` on zero-mass rows. `α : ℕ` keeps the chain in ℚ≥0; `cost`
is the multiplicative cost factor (e.g. a rationalized `exp (−C)`). -/
def s1 (l0 : U → W → ℚ≥0) (α : ℕ) (cost : U → ℚ≥0) (fb : PMF.Fallback U)
    (w : W) : U → ℚ≥0 :=
  PMF.scoresWith fb (fun u => l0 u w ^ α * cost u)

/-- Joint pragmatic-listener scores over world × latent coordinates:
`prior p · s1 p u`. Wrap with `PMF.ofScores` for the joint listener PMF, or
marginalize first. -/
def l1Joint (prior : W × Lat → ℚ≥0) (s1 : W × Lat → U → ℚ≥0) (u : U)
    (p : W × Lat) : ℚ≥0 :=
  prior p * s1 p u

/-- World marginal of joint scores. -/
def worldMarginal (f : W × Lat → ℚ≥0) (w : W) : ℚ≥0 := ∑ l, f (w, l)

/-- Latent marginal of joint scores. -/
def latentMarginal (f : W × Lat → ℚ≥0) (l : Lat) : ℚ≥0 := ∑ w, f (w, l)

/-- Stacked speaker: scores over utterances from pragmatic-listener
coordinates `l1World^α · l1Lat^β · cost`, fallback-completed. Higher
levels iterate the same shape. -/
def s2 (l1World : U → W → ℚ≥0) (l1Lat : U → Lat → ℚ≥0) (α β : ℕ)
    (cost : U → ℚ≥0) (fb : PMF.Fallback U) (l : Lat) (w : W) : U → ℚ≥0 :=
  PMF.scoresWith fb (fun u => l1World u w ^ α * l1Lat u l ^ β * cost u)

/-! ### Basic lemmas -/

omit [Fintype U] in
theorem l0_le_one (meaning : U → W → Bool) (prior : W → ℚ≥0) (u : U) (w : W) :
    l0 meaning prior u w ≤ 1 := by
  unfold l0
  rcases eq_or_ne (∑ w', if meaning u w' then prior w' else 0) 0 with h | h
  · simp [h]
  · rw [div_le_one (pos_iff_ne_zero.mpr h)]
    exact Finset.single_le_sum (f := fun w' => if meaning u w' then prior w' else 0)
      (fun _ _ => zero_le) (Finset.mem_univ w)

omit [Fintype U] in
theorem l0_eq_zero_of_not_meaning {meaning : U → W → Bool} {u : U} {w : W}
    (h : ¬ meaning u w) (prior : W → ℚ≥0) : l0 meaning prior u w = 0 := by
  simp [l0, h]

omit [Fintype W] in
theorem s1_sum_eq_one (l0 : U → W → ℚ≥0) (α : ℕ) (cost : U → ℚ≥0)
    (fb : PMF.Fallback U) (w : W) : ∑ u, s1 l0 α cost fb w u = 1 :=
  PMF.scoresWith_sum_eq_one fb _

omit [Fintype U] in
theorem worldMarginal_l1Joint_total (prior : W × Lat → ℚ≥0)
    (s1 : W × Lat → U → ℚ≥0) (u : U) :
    ∑ w, worldMarginal (l1Joint prior s1 u) w = ∑ p, prior p * s1 p u := by
  simp [worldMarginal, l1Joint, Fintype.sum_prod_type]

end RSA.Score
