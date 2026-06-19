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
  shows this holds at every rationality `α > 0`, and `fully_rational_picks_circle`
  that the `α → ∞` speaker concentrates all its mass on `circle` (consuming
  `RSA.Gibbs.speakerAlpha` and its zero-temperature limit).
* `size_principle` — generally, the speaker prefers the smaller-extension applicable
  utterance.
* `narrowing_blue` / `narrowing_square` — **pragmatic narrowing**: the speaker is
  less likely to use an ambiguous word at a referent that has a uniquely-identifying
  alternative; this asymmetry is what lets the listener narrow.
* `unique_green` / `unique_circle` — **unique reference**: a uniquely-applying word
  gets zero mass where it does not apply, so the listener recovers the referent.
-/

open MeasureTheory
open scoped ENNReal Topology

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

/-! ### Speaker API at this stimulus

These wrappers carry `by decide` defaults for the applicability side-conditions, so
the concrete predictions below never spell out `w ∈ applicable r` proofs. -/

/-- At an applicable utterance, the speaker mass is the softmax over `W(r)`. -/
theorem speakerAt_apply (r : Object) (w : Feature) (h : w ∈ applicable r := by decide) :
    speakerAt r {w}
      = ENNReal.ofReal (Real.exp (score w) / ∑ x ∈ applicable r, Real.exp (score x)) :=
  RSA.Gibbs.speaker_countRestrict_singleton (applicable r) score w h

/-- A non-applicable utterance gets zero speaker mass. -/
theorem speakerAt_apply_zero (r : Object) (w : Feature) (h : w ∉ applicable r := by decide) :
    speakerAt r {w} = 0 :=
  RSA.Gibbs.speaker_countRestrict_singleton_of_not_mem (applicable r) score w h

/-- Speaker preference at a referent reduces to the surprisal comparison. -/
theorem speakerAt_lt_iff (r : Object) (w₁ w₂ : Feature)
    (h₁ : w₁ ∈ applicable r := by decide) (h₂ : w₂ ∈ applicable r := by decide) :
    speakerAt r {w₁} < speakerAt r {w₂} ↔ score w₁ < score w₂ :=
  RSA.Gibbs.speaker_countRestrict_lt_iff_score_lt (applicable r) score w₁ w₂ h₁ h₂

/-- α-speaker preference at a referent (`α > 0`) reduces to the surprisal comparison. -/
theorem speakerAtAlpha_lt_iff (r : Object) {α : ℝ} (hα : 0 < α) (w₁ w₂ : Feature)
    (h₁ : w₁ ∈ applicable r := by decide) (h₂ : w₂ ∈ applicable r := by decide) :
    RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑(applicable r) : Set Feature)) α score {w₁}
        < RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑(applicable r) : Set Feature)) α score {w₂}
      ↔ score w₁ < score w₂ :=
  RSA.Gibbs.speakerAlpha_countRestrict_lt_iff_score_lt (applicable r) hα score w₁ w₂ h₁ h₂

/-! ### Numerical bookkeeping -/

/-- Every feature applies to at least one object, so its extension is nonempty. -/
private theorem numApplies_pos (w : Feature) : 0 < numApplies w := by cases w <;> decide

/-- `exp (score w) = |w|⁻¹` — the literal-listener target probability the speaker
tilts by (the content of eq. 2). -/
private theorem expScore (w : Feature) : Real.exp (score w) = (numApplies w : ℝ)⁻¹ := by
  rw [score, Real.exp_neg, Real.exp_log (by exact_mod_cast numApplies_pos w)]

/-- Partition over a two-word applicable set, in closed form. -/
private theorem partition_pair (r : Object) (w₁ w₂ : Feature)
    (h : applicable r = {w₁, w₂}) (hne : w₁ ∉ ({w₂} : Finset Feature)) :
    ∑ x ∈ applicable r, Real.exp (score x) = (numApplies w₁ : ℝ)⁻¹ + (numApplies w₂ : ℝ)⁻¹ := by
  rw [h, Finset.sum_insert hne, Finset.sum_singleton, expScore, expScore]

/-- Partition (total alternative weight) at each referent: `1` at `blueSquare` (two
ambiguous words), `3/2` at `blueCircle` and `greenSquare` (one ambiguous + one
uniquely-identifying word). -/
private theorem partition_blueSquare :
    ∑ x ∈ applicable .blueSquare, Real.exp (score x) = 1 := by
  rw [partition_pair .blueSquare .blue .square (by decide) (by decide),
    show numApplies Feature.blue = 2 from by decide,
    show numApplies Feature.square = 2 from by decide]; norm_num

private theorem partition_blueCircle :
    ∑ x ∈ applicable .blueCircle, Real.exp (score x) = 3 / 2 := by
  rw [partition_pair .blueCircle .blue .circle (by decide) (by decide),
    show numApplies Feature.blue = 2 from by decide,
    show numApplies Feature.circle = 1 from by decide]; norm_num

private theorem partition_greenSquare :
    ∑ x ∈ applicable .greenSquare, Real.exp (score x) = 3 / 2 := by
  rw [partition_pair .greenSquare .green .square (by decide) (by decide),
    show numApplies Feature.green = 1 from by decide,
    show numApplies Feature.square = 2 from by decide]; norm_num

/-! ### Predictions -/

/-- `circle` is more informative than `blue`: `score blue < score circle`
(`= log(1/2) < log 1`). Shared by `prefers_informative` and its α-robust form. -/
private theorem score_blue_lt_circle : score .blue < score .circle := by
  rw [score, score, show numApplies Feature.blue = 2 from by decide,
    show numApplies Feature.circle = 1 from by decide, Nat.cast_ofNat, Nat.cast_one, Real.log_one]
  simp only [neg_zero, neg_lt_zero]
  exact Real.log_pos (by norm_num)

/-- **The speaker prefers the uniquely-identifying description** (Fig. 1A): for the
target (`blueCircle`), `circle` (which uniquely identifies it) gets strictly more
mass than the ambiguous `blue`. Reduces via `speaker_countRestrict_lt_iff_score_lt`
to the surprisal comparison `score blue < score circle`. -/
theorem prefers_informative : speakerAt .blueCircle {.blue} < speakerAt .blueCircle {.circle} :=
  (speakerAt_lt_iff .blueCircle .blue .circle).mpr score_blue_lt_circle

/-- **Robustness to rationality**: the informativeness preference holds at *every*
rationality level `α > 0`, not just the canonical `α = 1` (`prefers_informative`).
A consumer of the α-generalized speaker `RSA.Gibbs.speakerAlpha`. -/
theorem prefers_informative_alpha {α : ℝ} (hα : 0 < α) :
    RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑(applicable .blueCircle) : Set Feature))
        α score {.blue}
      < RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑(applicable .blueCircle) : Set Feature))
        α score {.circle} :=
  (speakerAtAlpha_lt_iff .blueCircle hα .blue .circle).mpr score_blue_lt_circle

/-- **The fully-rational speaker is deterministic** (`α → ∞`): at the target, the
speaker concentrates all its mass on the uniquely-identifying `circle`. The
zero-temperature limit of `prefers_informative`, via
`RSA.Gibbs.speakerAlpha_countRestrict_tendsto_one_of_isMax`. -/
theorem fully_rational_picks_circle :
    Filter.Tendsto (fun α => RSA.Gibbs.speakerAlpha
        (Measure.count.restrict (↑(applicable .blueCircle) : Set Feature)) α score {.circle})
      Filter.atTop (𝓝 1) := by
  refine RSA.Gibbs.speakerAlpha_countRestrict_tendsto_one_of_isMax _ score _ (by decide) ?_
  intro b hb hbne
  have hb' : b ∈ ({Feature.blue, Feature.circle} : Finset Feature) := by
    rwa [show applicable Object.blueCircle = {Feature.blue, Feature.circle} from by decide] at hb
  fin_cases hb'
  · exact score_blue_lt_circle
  · exact absurd rfl hbne

/-- **Size principle**: among applicable utterances, the speaker prefers the one
with the smaller extension (lower `numApplies`). -/
theorem size_principle (r : Object) (w₁ w₂ : Feature) (h₁ : w₁ ∈ applicable r)
    (h₂ : w₂ ∈ applicable r) (h : numApplies w₂ < numApplies w₁) :
    speakerAt r {w₁} < speakerAt r {w₂} := by
  refine (speakerAt_lt_iff r w₁ w₂ h₁ h₂).mpr ?_
  rw [score, score, neg_lt_neg_iff]
  exact Real.log_lt_log (by exact_mod_cast numApplies_pos w₂) (by exact_mod_cast h)

/-- **Pragmatic narrowing for "blue"**: the speaker assigns less mass to "blue" at
`blueCircle` (where "circle" uniquely identifies, raising the partition) than at
`blueSquare` (where the only alternative "square" is equally ambiguous). The
numerators are equal; the comparison is the partition comparison `3/2 > 1` — which
is what lets a listener hearing "blue" narrow toward `blueSquare`. -/
theorem narrowing_blue : speakerAt .blueCircle {.blue} < speakerAt .blueSquare {.blue} := by
  rw [speakerAt_apply .blueCircle .blue, speakerAt_apply .blueSquare .blue,
    partition_blueCircle, partition_blueSquare, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    div_one]
  exact div_lt_self (Real.exp_pos _) (by norm_num)

/-- **Pragmatic narrowing for "square"**: symmetrically, "square" is less likely at
`greenSquare` (where "green" uniquely identifies) than at `blueSquare`. -/
theorem narrowing_square : speakerAt .greenSquare {.square} < speakerAt .blueSquare {.square} := by
  rw [speakerAt_apply .greenSquare .square, speakerAt_apply .blueSquare .square,
    partition_greenSquare, partition_blueSquare, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    div_one]
  exact div_lt_self (Real.exp_pos _) (by norm_num)

/-- **Unique reference for "green"**: "green" applies only to `greenSquare`, so it
gets zero mass at `blueSquare` and positive mass at `greenSquare` — the listener
hearing "green" identifies `greenSquare`. -/
theorem unique_green : speakerAt .blueSquare {.green} < speakerAt .greenSquare {.green} := by
  rw [speakerAt_apply_zero .blueSquare .green, speakerAt_apply .greenSquare .green,
    partition_greenSquare]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- **Unique reference for "circle"**: "circle" applies only to `blueCircle`. -/
theorem unique_circle : speakerAt .blueSquare {.circle} < speakerAt .blueCircle {.circle} := by
  rw [speakerAt_apply_zero .blueSquare .circle, speakerAt_apply .blueCircle .circle,
    partition_blueCircle]
  exact ENNReal.ofReal_pos.mpr (by positivity)

end FrankGoodman2012
