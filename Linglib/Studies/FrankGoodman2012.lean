import Linglib.Pragmatics.RSA.Gibbs

/-!
# [frank-goodman-2012] reference game (Measure/Kernel-native)
[frank-goodman-2012]

"Predicting Pragmatic Reasoning in Language Games", Science 336, 998.

The Rational Speech Act model of the paper, on the Measure/Kernel-native analytic
foundation of `Pragmatics/RSA/Gibbs.lean`. The informative speaker (the paper's
eq. 2) is a `MeasureTheory.Measure.tilted` Gibbs measure: `Measure.count`
restricted to the *applicable* utterances `W(r)`, tilted by the surprisal utility
`score w = log (1 / |w|)`. The closed form is exactly

  `S₁(w | r) ∝ |w|⁻¹`  over `w ∈ W(r)`,

[frank-goodman-2012]'s eq. (2). The architectural content — the speaker is a Gibbs
measure, monotone in utility, and the rational optimizer of expected-utility-minus-
KL (`RSA.Gibbs.speaker_isGreatest`) — is the substrate; here it is instantiated at
the paper's stimulus (Fig. 1A).

The pragmatic listener (eq. 1) is the Bayesian posterior of the speaker against the
salience prior, `RSA.Gibbs.listener`; its pragmatic inferences are driven by the
speaker asymmetries proved below (narrowing, unique reference). Empirical fit
(speaker `r = 0.98`, listener `r = 0.99`) is reported in the paper, not as a
theorem here.

## Main statements

* `prefers_informative` — the speaker prefers the uniquely-identifying `circle`
  over the ambiguous `blue` for the target (Fig. 1A); `prefers_informative_alpha`
  shows this holds at every rationality `α > 0` (consuming `RSA.Gibbs.speakerAlpha`).
* `size_principle` — generally, the speaker prefers the smaller-extension applicable
  utterance.
* `narrowing_blue` / `narrowing_square` — **pragmatic narrowing**: the speaker is
  less likely to use an ambiguous word at a referent that has a uniquely-identifying
  alternative; this asymmetry is what lets the listener narrow.
* `unique_green` / `unique_circle` — **unique reference**: a uniquely-applying word
  gets zero mass where it does not apply, so the listener recovers the referent.
-/

open MeasureTheory
open scoped ENNReal

namespace FrankGoodman2012

/-! ### Stimulus (Fig. 1A)

Three objects and four feature-words. Two features (`green`, `circle`) are uniquely
identifying; two (`blue`, `square`) are ambiguous between two objects each. -/

/-- The three objects in the reference context. -/
inductive Object
  | blueSquare | blueCircle | greenSquare
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The four feature-word utterances. -/
inductive Feature
  | blue | green | square | circle
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Feature := ⊤
instance : MeasurableSingletonClass Feature := ⟨fun _ => trivial⟩

/-- The denotation matrix: which feature applies to which object. -/
def appliesTo : Feature → Object → Bool
  | .blue,   .blueSquare  => true
  | .blue,   .blueCircle  => true
  | .green,  .greenSquare => true
  | .square, .blueSquare  => true
  | .square, .greenSquare => true
  | .circle, .blueCircle  => true
  | _, _ => false

/-- The applicable utterances at a referent — [frank-goodman-2012]'s `W(r)`, the
support over which the speaker normalizes. -/
def applicable (r : Object) : Finset Feature :=
  Finset.univ.filter (fun w => appliesTo w r)

/-- The extension size `|w|` — the number of objects the feature applies to. -/
def numApplies (w : Feature) : ℕ :=
  (Finset.univ.filter (fun o => appliesTo w o)).card

/-- Informativity utility (rationality `α = 1`, no cost): the surprisal
`score w = log (1 / |w|) = - log |w|`. Tilting by this realizes eq. (2)'s
`|w|⁻¹`. -/
noncomputable def score (w : Feature) : ℝ := -Real.log (numApplies w)

/-- The informative speaker (eq. 2): the Gibbs measure tilting `Measure.count`
restricted to the applicable utterances `W(r)` by the surprisal `score`. -/
noncomputable def speakerAt (r : Object) : Measure Feature :=
  RSA.Gibbs.speaker (Measure.count.restrict (↑(applicable r) : Set Feature)) score

/-! ### Speaker mass closed forms (eq. 2) -/

/-- At an applicable utterance, the speaker mass is the softmax over `W(r)`. -/
theorem speakerAt_apply (r : Object) (w : Feature) (h : w ∈ applicable r) :
    speakerAt r {w}
      = ENNReal.ofReal (Real.exp (score w) / ∑ x ∈ applicable r, Real.exp (score x)) :=
  RSA.Gibbs.speaker_countRestrict_singleton (applicable r) score w h

/-- A non-applicable utterance gets zero speaker mass. -/
theorem speakerAt_apply_zero (r : Object) (w : Feature) (h : w ∉ applicable r) :
    speakerAt r {w} = 0 :=
  RSA.Gibbs.speaker_countRestrict_singleton_of_not_mem (applicable r) score w h

/-! ### Numerical bookkeeping -/

private theorem expScore_blue   : Real.exp (score .blue)   = 1 / 2 := by
  rw [score, show numApplies Feature.blue = 2 from by decide, Nat.cast_ofNat,
    Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
private theorem expScore_green  : Real.exp (score .green)  = 1 := by
  rw [score, show numApplies Feature.green = 1 from by decide, Nat.cast_one,
    Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
private theorem expScore_square : Real.exp (score .square) = 1 / 2 := by
  rw [score, show numApplies Feature.square = 2 from by decide, Nat.cast_ofNat,
    Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
private theorem expScore_circle : Real.exp (score .circle) = 1 := by
  rw [score, show numApplies Feature.circle = 1 from by decide, Nat.cast_one,
    Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- Partition (total alternative weight) at each referent: `1` at `blueSquare`
(two ambiguous words), `3/2` at `blueCircle` and `greenSquare` (one ambiguous +
one uniquely-identifying word). -/
private theorem partition_blueSquare :
    ∑ x ∈ applicable .blueSquare, Real.exp (score x) = 1 := by
  rw [show applicable Object.blueSquare = {Feature.blue, Feature.square} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, expScore_blue, expScore_square]
  norm_num

private theorem partition_blueCircle :
    ∑ x ∈ applicable .blueCircle, Real.exp (score x) = 3 / 2 := by
  rw [show applicable Object.blueCircle = {Feature.blue, Feature.circle} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, expScore_blue, expScore_circle]
  norm_num

private theorem partition_greenSquare :
    ∑ x ∈ applicable .greenSquare, Real.exp (score x) = 3 / 2 := by
  rw [show applicable Object.greenSquare = {Feature.green, Feature.square} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, expScore_green, expScore_square]
  norm_num

/-! ### Predictions -/

/-- **The speaker prefers the uniquely-identifying description** (Fig. 1A): for the
target (`blueCircle`), `circle` (which uniquely identifies it) gets strictly more
mass than the ambiguous `blue`. Reduces via `speaker_countRestrict_lt_iff_score_lt`
to the surprisal comparison `score blue < score circle`. -/
theorem prefers_informative : speakerAt .blueCircle {.blue} < speakerAt .blueCircle {.circle} := by
  rw [speakerAt, RSA.Gibbs.speaker_countRestrict_lt_iff_score_lt _ score _ _ (by decide) (by decide),
    score, score, show numApplies Feature.blue = 2 from by decide,
    show numApplies Feature.circle = 1 from by decide, Nat.cast_ofNat, Nat.cast_one, Real.log_one]
  simp only [neg_zero, neg_lt_zero]
  exact Real.log_pos (by norm_num)

/-- **Robustness to rationality**: the informativeness preference holds at *every*
rationality level `α > 0`, not just the canonical `α = 1` (`prefers_informative`).
A consumer of the α-generalized speaker `RSA.Gibbs.speakerAlpha`. -/
theorem prefers_informative_alpha {α : ℝ} (hα : 0 < α) :
    RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑(applicable .blueCircle) : Set Feature))
        α score {.blue}
      < RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑(applicable .blueCircle) : Set Feature))
        α score {.circle} := by
  have hsc : score .blue < score .circle := by
    rw [score, score, show numApplies Feature.blue = 2 from by decide,
      show numApplies Feature.circle = 1 from by decide, Nat.cast_ofNat, Nat.cast_one, Real.log_one]
    simp only [neg_zero, neg_lt_zero]
    exact Real.log_pos (by norm_num)
  simp only [RSA.Gibbs.speakerAlpha]
  rw [RSA.Gibbs.speaker_countRestrict_lt_iff_score_lt _ _ _ _ (by decide) (by decide)]
  exact mul_lt_mul_of_pos_left hsc hα

/-- **Size principle**: among applicable utterances, the speaker prefers the one
with the smaller extension (lower `numApplies`). -/
theorem size_principle (r : Object) (w₁ w₂ : Feature) (h₁ : w₁ ∈ applicable r)
    (h₂ : w₂ ∈ applicable r) (h : numApplies w₂ < numApplies w₁) :
    speakerAt r {w₁} < speakerAt r {w₂} := by
  have hpos : 0 < numApplies w₂ :=
    Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, (Finset.mem_filter.mp h₂).2⟩⟩
  rw [speakerAt, RSA.Gibbs.speaker_countRestrict_lt_iff_score_lt _ score _ _ h₁ h₂, score, score,
    neg_lt_neg_iff]
  exact Real.log_lt_log (by exact_mod_cast hpos) (by exact_mod_cast h)

/-- **Pragmatic narrowing for "blue"**: the speaker assigns less mass to "blue" at
`blueCircle` (where "circle" uniquely identifies, raising the partition) than at
`blueSquare` (where the only alternative "square" is equally ambiguous). This
asymmetry — `S₁(blue | blueCircle) = 1/3 < 1/2 = S₁(blue | blueSquare)` — is what
lets a listener hearing "blue" narrow toward `blueSquare`. -/
theorem narrowing_blue : speakerAt .blueCircle {.blue} < speakerAt .blueSquare {.blue} := by
  rw [speakerAt_apply _ _ (by decide), speakerAt_apply _ _ (by decide),
    partition_blueCircle, partition_blueSquare, expScore_blue,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- **Pragmatic narrowing for "square"**: symmetrically, "square" is less likely at
`greenSquare` (where "green" uniquely identifies) than at `blueSquare`. -/
theorem narrowing_square : speakerAt .greenSquare {.square} < speakerAt .blueSquare {.square} := by
  rw [speakerAt_apply _ _ (by decide), speakerAt_apply _ _ (by decide),
    partition_greenSquare, partition_blueSquare, expScore_square,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- **Unique reference for "green"**: "green" applies only to `greenSquare`, so it
gets zero mass at `blueSquare` and positive mass at `greenSquare` — the listener
hearing "green" identifies `greenSquare`. -/
theorem unique_green : speakerAt .blueSquare {.green} < speakerAt .greenSquare {.green} := by
  rw [speakerAt_apply_zero _ _ (by decide), speakerAt_apply _ _ (by decide),
    partition_greenSquare, expScore_green]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- **Unique reference for "circle"**: "circle" applies only to `blueCircle`. -/
theorem unique_circle : speakerAt .blueSquare {.circle} < speakerAt .blueCircle {.circle} := by
  rw [speakerAt_apply_zero _ _ (by decide), speakerAt_apply _ _ (by decide),
    partition_blueCircle, expScore_circle]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

end FrankGoodman2012
