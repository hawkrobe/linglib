import Linglib.Pragmatics.RSA.Gibbs

/-!
# Frank and Goodman (2012): Predicting Pragmatic Reasoning in Language Games

This file formalizes [frank-goodman-2012]'s rational speech act model at the paper's stimulus:
three objects, a blue square, a blue circle and a green square, described by the four words
*blue*, *green*, *square* and *circle*. A word applies to the objects it describes
(`Feature.AppliesTo`), and a speaker who wants to refer to an object chooses among the words
that apply to it in proportion to their specificity, the reciprocal of the number of objects
they apply to (the paper's second equation). The speaker is the Gibbs measure of
`RSA.Gibbs.speaker`, counting measure on the applicable words tilted by the surprisal of the
word, and inherits the substrate's characterization as the rational optimizer of expected
utility less divergence from the literal listener. At the stimulus the speaker prefers the
uniquely identifying *circle* to the ambiguous *blue* for the blue circle, at every rationality
and with all its mass in the limit (`prefers_informative`, `fully_rational_picks_circle`),
prefers the word with the smaller extension wherever both apply (`size_principle`), uses an
ambiguous word less at an object that a unique word identifies (`narrowing_blue`), and never
uses a word where it does not apply (`unique_green`). These asymmetries are what the paper's
listener, the Bayesian posterior of the speaker against the empirically measured salience prior
(its first equation), inverts; the paper reports the fit of speaker and listener bets to the
model's predictions.

## Implementation notes

* The rationality parameter is one and words are costless, as in the paper; the preference is
  restated at every positive rationality through `RSA.Gibbs.speakerAlpha`.
* The listener of the paper's first equation is `RSA.Gibbs.listener` against a salience prior;
  its predictions at the stimulus are not instantiated here.

## TODO

* The listener on hearing *blue*: its odds for the blue square against the blue circle are the
  prior odds times three halves, the ratio of the speaker's probabilities of *blue* at the two
  objects.

## References

* [frank-goodman-2012]
-/

open MeasureTheory
open scoped ENNReal Topology

namespace FrankGoodman2012

/-! ### The stimulus (Figure 1A) -/

/-- The three objects of the context. -/
inductive Object
  | blueSquare | blueCircle | greenSquare
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The four words. -/
inductive Feature
  | blue | green | square | circle
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Feature := ⊤
instance : MeasurableSingletonClass Feature := ⟨λ _ => trivial⟩

/-- The word describes the object. -/
def Feature.AppliesTo : Feature → Object → Prop
  | .blue, .blueSquare | .blue, .blueCircle | .green, .greenSquare
  | .square, .blueSquare | .square, .greenSquare | .circle, .blueCircle => True
  | _, _ => False

instance : DecidableRel Feature.AppliesTo := λ w o => by
  cases w <;> cases o <;> unfold Feature.AppliesTo <;> infer_instance

/-- The words that apply to a referent, the paper's `W(r)`: the support over which the speaker
normalizes. -/
def Object.applicable (r : Object) : Finset Feature := Finset.univ.filter (·.AppliesTo r)

/-- The extension of a word, the objects it applies to; its size is the paper's `|w|`. -/
def Feature.extension (w : Feature) : Finset Object := Finset.univ.filter w.AppliesTo

/-- The surprisal of a word, `-log |w|`: the informativity utility at rationality one and
without cost, whose Gibbs measure is proportional to `|w|⁻¹`. -/
noncomputable def score (w : Feature) : ℝ := -Real.log w.extension.card

/-- The informative speaker at a referent: counting measure on the applicable words, tilted by
the surprisal. -/
noncomputable def speakerAt (r : Object) : Measure Feature :=
  RSA.Gibbs.speaker (Measure.count.restrict (↑r.applicable : Set Feature)) score

/-! ### The speaker at the stimulus

The side conditions of applicability are discharged by `decide` by default, so the predictions
below never spell them out. -/

/-- At an applicable word the speaker's mass is the softmax over the applicable words. -/
theorem speakerAt_apply (r : Object) (w : Feature) (h : w ∈ r.applicable := by decide) :
    speakerAt r {w}
      = ENNReal.ofReal (Real.exp (score w) / ∑ x ∈ r.applicable, Real.exp (score x)) :=
  RSA.Gibbs.speaker_countRestrict_singleton r.applicable score w h

/-- A word that does not apply gets no mass. -/
theorem speakerAt_apply_zero (r : Object) (w : Feature) (h : w ∉ r.applicable := by decide) :
    speakerAt r {w} = 0 :=
  RSA.Gibbs.speaker_countRestrict_singleton_of_not_mem r.applicable score w h

/-- Speaker preference at a referent is the surprisal comparison. -/
theorem speakerAt_lt_iff (r : Object) (w₁ w₂ : Feature)
    (h₁ : w₁ ∈ r.applicable := by decide) (h₂ : w₂ ∈ r.applicable := by decide) :
    speakerAt r {w₁} < speakerAt r {w₂} ↔ score w₁ < score w₂ :=
  RSA.Gibbs.speaker_countRestrict_lt_iff_score_lt r.applicable score w₁ w₂ h₁ h₂

/-- At every positive rationality, speaker preference at a referent is the surprisal
comparison. -/
theorem speakerAtAlpha_lt_iff (r : Object) {α : ℝ} (hα : 0 < α) (w₁ w₂ : Feature)
    (h₁ : w₁ ∈ r.applicable := by decide) (h₂ : w₂ ∈ r.applicable := by decide) :
    RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑r.applicable : Set Feature)) α score {w₁}
        < RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑r.applicable : Set Feature)) α score {w₂}
      ↔ score w₁ < score w₂ :=
  RSA.Gibbs.speakerAlpha_countRestrict_lt_iff_score_lt r.applicable hα score w₁ w₂ h₁ h₂

/-! ### Partition functions -/

/-- Every word applies to some object. -/
private theorem extension_card_pos (w : Feature) : 0 < w.extension.card := by cases w <;> decide

/-- `exp (score w) = |w|⁻¹`, the literal listener's probability of the referent. -/
private theorem expScore (w : Feature) : Real.exp (score w) = (w.extension.card : ℝ)⁻¹ := by
  rw [score, Real.exp_neg, Real.exp_log (by exact_mod_cast extension_card_pos w)]

/-- The partition function over two applicable words. -/
private theorem partition_pair (r : Object) (w₁ w₂ : Feature)
    (h : r.applicable = {w₁, w₂}) (hne : w₁ ∉ ({w₂} : Finset Feature)) :
    ∑ x ∈ r.applicable, Real.exp (score x) =
      (w₁.extension.card : ℝ)⁻¹ + (w₂.extension.card : ℝ)⁻¹ := by
  rw [h, Finset.sum_insert hne, Finset.sum_singleton, expScore, expScore]

/-- The partition function is `1` at the blue square, whose two words are both ambiguous, and
`3/2` at the other objects, each described by one ambiguous and one unique word. -/
private theorem partition_blueSquare :
    ∑ x ∈ Object.blueSquare.applicable, Real.exp (score x) = 1 := by
  rw [partition_pair .blueSquare .blue .square (by decide) (by decide),
    show Feature.blue.extension.card = 2 from by decide,
    show Feature.square.extension.card = 2 from by decide]; norm_num

private theorem partition_blueCircle :
    ∑ x ∈ Object.blueCircle.applicable, Real.exp (score x) = 3 / 2 := by
  rw [partition_pair .blueCircle .blue .circle (by decide) (by decide),
    show Feature.blue.extension.card = 2 from by decide,
    show Feature.circle.extension.card = 1 from by decide]; norm_num

private theorem partition_greenSquare :
    ∑ x ∈ Object.greenSquare.applicable, Real.exp (score x) = 3 / 2 := by
  rw [partition_pair .greenSquare .green .square (by decide) (by decide),
    show Feature.green.extension.card = 1 from by decide,
    show Feature.square.extension.card = 2 from by decide]; norm_num

/-! ### Predictions -/

/-- *circle* is more informative than *blue*: `log (1/2) < log 1`. -/
private theorem score_blue_lt_circle : score .blue < score .circle := by
  rw [score, score, show Feature.blue.extension.card = 2 from by decide,
    show Feature.circle.extension.card = 1 from by decide, Nat.cast_ofNat, Nat.cast_one,
    Real.log_one]
  simp only [neg_zero, neg_lt_zero]
  exact Real.log_pos (by norm_num)

/-- For the blue circle the speaker prefers *circle*, which identifies it, to the ambiguous
*blue*. -/
theorem prefers_informative : speakerAt .blueCircle {.blue} < speakerAt .blueCircle {.circle} :=
  (speakerAt_lt_iff .blueCircle .blue .circle).mpr score_blue_lt_circle

/-- The preference holds at every positive rationality. -/
theorem prefers_informative_alpha {α : ℝ} (hα : 0 < α) :
    RSA.Gibbs.speakerAlpha (Measure.count.restrict (↑Object.blueCircle.applicable : Set Feature))
        α score {.blue}
      < RSA.Gibbs.speakerAlpha
          (Measure.count.restrict (↑Object.blueCircle.applicable : Set Feature)) α score
          {.circle} :=
  (speakerAtAlpha_lt_iff .blueCircle hα .blue .circle).mpr score_blue_lt_circle

/-- As rationality grows without bound the speaker puts all its mass on *circle*. -/
theorem fully_rational_picks_circle :
    Filter.Tendsto (λ α => RSA.Gibbs.speakerAlpha
        (Measure.count.restrict (↑Object.blueCircle.applicable : Set Feature)) α score {.circle})
      Filter.atTop (𝓝 1) := by
  refine RSA.Gibbs.speakerAlpha_countRestrict_tendsto_one_of_isMax _ score _ (by decide) ?_
  intro b hb hbne
  have hb' : b ∈ ({Feature.blue, Feature.circle} : Finset Feature) := by
    rwa [show Object.blueCircle.applicable = {Feature.blue, Feature.circle} from by decide] at hb
  fin_cases hb'
  · exact score_blue_lt_circle
  · exact absurd rfl hbne

/-- The size principle: of two applicable words the speaker prefers the one with the smaller
extension. -/
theorem size_principle (r : Object) (w₁ w₂ : Feature) (h₁ : w₁ ∈ r.applicable)
    (h₂ : w₂ ∈ r.applicable) (h : w₂.extension.card < w₁.extension.card) :
    speakerAt r {w₁} < speakerAt r {w₂} := by
  refine (speakerAt_lt_iff r w₁ w₂ h₁ h₂).mpr ?_
  rw [score, score, neg_lt_neg_iff]
  exact Real.log_lt_log (by exact_mod_cast extension_card_pos w₂) (by exact_mod_cast h)

/-- Narrowing: *blue* is used less for the blue circle, where *circle* competes, than for the
blue square, where the only competitor is as ambiguous; the numerators agree and the partition
functions differ. A listener hearing *blue* narrows toward the blue square. -/
theorem narrowing_blue : speakerAt .blueCircle {.blue} < speakerAt .blueSquare {.blue} := by
  rw [speakerAt_apply .blueCircle .blue, speakerAt_apply .blueSquare .blue,
    partition_blueCircle, partition_blueSquare, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    div_one]
  exact div_lt_self (Real.exp_pos _) (by norm_num)

/-- Narrowing for *square*: used less for the green square, which *green* identifies. -/
theorem narrowing_square : speakerAt .greenSquare {.square} < speakerAt .blueSquare {.square} := by
  rw [speakerAt_apply .greenSquare .square, speakerAt_apply .blueSquare .square,
    partition_greenSquare, partition_blueSquare, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    div_one]
  exact div_lt_self (Real.exp_pos _) (by norm_num)

/-- Unique reference: *green* gets no mass at the blue square and positive mass at the green
square, so a listener hearing it identifies the green square. -/
theorem unique_green : speakerAt .blueSquare {.green} < speakerAt .greenSquare {.green} := by
  rw [speakerAt_apply_zero .blueSquare .green, speakerAt_apply .greenSquare .green,
    partition_greenSquare]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- Unique reference for *circle*. -/
theorem unique_circle : speakerAt .blueSquare {.circle} < speakerAt .blueCircle {.circle} := by
  rw [speakerAt_apply_zero .blueSquare .circle, speakerAt_apply .blueCircle .circle,
    partition_blueCircle]
  exact ENNReal.ofReal_pos.mpr (by positivity)

end FrankGoodman2012
