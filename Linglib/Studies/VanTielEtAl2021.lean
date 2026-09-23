module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.VanTielEtAl2021
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# van Tiel, Franke and Sauerland (2021): Probabilistic Pragmatics Explains Gradience and Focality in Natural Language Quantification

This file formalizes the speaker models of [van-tiel-franke-sauerland-2021], which test two
semantic theories of quantity words against production data, the frame *— of the circles are
red* over displays of 432 circles. Production is gradient, without sharp boundaries, and focal,
peaking inside the range where a word is true. Generalized quantifier theory, [barwise-cooper-1981],
gives each word a threshold on the intersection set size, a lower bound for a monotone-increasing
word and an upper bound for a monotone-decreasing one, `gq`; prototype theory gives it a degree of
truth falling off with the distance from a prototype, `pt`. A literal speaker produces a word in
proportion to its salience and its truth value, `speakerLit`, and a pragmatic speaker in
proportion to its salience and the probability that a literal listener recovers the state from
it, `listenerLit` and `speakerPrag`, both with imprecise number representation added by
composing with a confusion kernel, `withConfusion`. The paper's finding is that the pragmatic
model over the threshold semantics explains the data as well as the prototype models: a literal
speaker never produces a false word, `speakerLit_apply_singleton_eq_zero`, and is indifferent
among true words of equal salience, `speakerLit_real_eq_of_eq`, so its productions are step
functions, whereas the pragmatic speaker prefers the true word with the smaller extension,
`speakerPrag_real_lt_of_card_lt`, which is where focality comes from, and it lets words
compete that stand in no entailment relation, *some* and *few*, `gq_no_entailment`. The
prototype semantics is gradient by itself, `pt_lt_pt_of_abs_lt`.

## Implementation notes

States are the intersection set sizes `Fin (n + 1)` and speakers are kernels from states to
words built with `Kernel.ofWeights`, the normalizing step of the RSA pipeline; the literal
listener has a uniform prior over states. Thresholds, prototypes, spreads and saliences are
parameters, not the fitted posterior values, and the Weber-fraction confusion kernel of
Experiment 3 is an arbitrary kernel on states. The monotonicity classification of Experiment 2,
the model comparison of Table 1, and the adequacy ratings of Experiment 4 are reported in the
paper and not formalized. The examples are the rows of `Data.Examples.VanTielEtAl2021`.

## References

* [van-tiel-franke-sauerland-2021]
* [barwise-cooper-1981]
* [frank-goodman-2012]
* [grice-1975]
* [sauerland-2004]
-/

@[expose] public section

namespace VanTielEtAl2021

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The states: the intersection set sizes of a display of `n` circles. -/
abbrev State (n : ℕ) := Fin (n + 1)

/-- The direction of a quantity word's threshold: a lower bound for a monotone-increasing word,
an upper bound for a monotone-decreasing one. -/
inductive Direction where
  | increasing
  | decreasing
  deriving DecidableEq, Repr

variable {n : ℕ} {M : Type*}

/-- A lexical meaning function: the truth value of a word at a state. -/
abbrev Lexicon (n : ℕ) (M : Type*) := M → State n → ℝ

/-- The generalized-quantifier lexicon: a word is true at the states on its side of its
threshold. -/
def gq (dir : M → Direction) (θ : M → ℕ) : Lexicon n M := λ m t =>
  match dir m with
  | .increasing => if θ m ≤ t.val then 1 else 0
  | .decreasing => if t.val ≤ θ m then 1 else 0

/-- The prototype lexicon: the degree of truth falls off with the distance from the
prototype `p`, scaled by the spread `d`. -/
noncomputable def pt (p d : M → ℝ) : Lexicon n M := λ m t =>
  Real.exp (-(((t.val : ℝ) - p m) / d m) ^ 2)

theorem gq_eq_one_or_zero (dir : M → Direction) (θ : M → ℕ) (m : M) (t : State n) :
    gq dir θ m t = 1 ∨ gq dir θ m t = 0 := by
  unfold gq
  split <;> split_ifs <;> simp

/-- *Some* and *few* stand in no entailment relation: with a lower bound for *some* and an upper
bound for *few* inside the range, *few* is true and *some* false of an empty intersection, and
the other way round of a full one. -/
theorem gq_no_entailment (dir : M → Direction) (θ : M → ℕ) {m m' : M}
    (hm : dir m = .increasing) (hθm : 1 ≤ θ m) (hθm' : θ m ≤ n) (hm' : dir m' = .decreasing)
    (hθ : θ m' < n) :
    gq dir θ m' (0 : State n) = 1 ∧ gq dir θ m (0 : State n) = 0 ∧
      gq dir θ m (Fin.last n) = 1 ∧ gq dir θ m' (Fin.last n) = 0 := by
  simp [gq, hm, hm', Fin.val_last]
  omega

theorem pt_pos (p d : M → ℝ) (m : M) (t : State n) : 0 < pt p d m t := Real.exp_pos _

theorem pt_le_one (p d : M → ℝ) (m : M) (t : State n) : pt p d m t ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg _))

/-- The prototype semantics is gradient by itself: a state closer to the prototype is truer. -/
theorem pt_lt_pt_of_abs_lt (p d : M → ℝ) (m : M) {t t' : State n} (hd : 0 < d m)
    (h : |(t.val : ℝ) - p m| < |(t'.val : ℝ) - p m|) : pt p d m t' < pt p d m t := by
  unfold pt
  rw [Real.exp_lt_exp, neg_lt_neg_iff, div_pow, div_pow]
  refine div_lt_div_of_pos_right ?_ (pow_pos hd 2)
  rw [← sq_abs ((t.val : ℝ) - p m), ← sq_abs ((t'.val : ℝ) - p m)]
  exact pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero

/-- The extension of a word: the states where it is true. -/
noncomputable def extension (n : ℕ) (dir : M → Direction) (θ : M → ℕ) (m : M) :
    Finset (State n) :=
  Finset.univ.filter λ t => gq dir θ m t = 1

theorem gq_nonneg (dir : M → Direction) (θ : M → ℕ) (m : M) (t : State n) :
    0 ≤ gq dir θ m t := by
  rcases gq_eq_one_or_zero dir θ m t with h | h <;> simp [h]

theorem sum_gq (dir : M → Direction) (θ : M → ℕ) (m : M) :
    ∑ t : State n, gq dir θ m t = (extension n dir θ m).card := by
  rw [extension, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl λ t _ => ?_
  rcases gq_eq_one_or_zero dir θ m t with h | h <;> simp [h]

/-! ### Speakers -/

/-- Production under imprecise number representation: the speaker rule at the state the
confusion kernel `cf` represents the true state as. -/
noncomputable def withConfusion [MeasurableSpace M] (S : Kernel (State n) M)
    (cf : Kernel (State n) (State n)) : Kernel (State n) M :=
  S ∘ₖ cf

/-- Exact number representation changes nothing. -/
theorem withConfusion_id [MeasurableSpace M] (S : Kernel (State n) M) :
    withConfusion S Kernel.id = S :=
  Kernel.comp_id S

variable [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]

/-- The literal speaker: a word in proportion to its salience and its truth value. -/
noncomputable def speakerLit (L : Lexicon n M) (sal : M → ℝ) : Kernel (State n) M :=
  Kernel.ofWeights λ t m => ENNReal.ofReal (sal m * L m t)

/-- The literal listener with a uniform prior over states: a state in proportion to the truth
value of the word there. -/
noncomputable def listenerLit (L : Lexicon n M) : Kernel M (State n) :=
  Kernel.ofWeights λ m t => ENNReal.ofReal (L m t)

/-- The pragmatic speaker with rationality `α`: a word in proportion to its salience and the
probability that the literal listener recovers the state from it. -/
noncomputable def speakerPrag (L : Lexicon n M) (sal : M → ℝ) (α : ℝ) : Kernel (State n) M :=
  Kernel.ofWeights λ t m => ENNReal.ofReal (sal m * ((listenerLit L m).real {t}) ^ α)

/-- A literal speaker never produces a false word. -/
theorem speakerLit_apply_singleton_eq_zero (L : Lexicon n M) (sal : M → ℝ) {m : M}
    {t : State n} (h : L m t = 0) : speakerLit L sal t {m} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by simp [h])

/-- A literal speaker is indifferent among words of equal salience and truth value: with a
threshold semantics its productions are step functions. -/
theorem speakerLit_real_eq_of_eq (L : Lexicon n M) (sal : M → ℝ) {m m' : M} {t : State n}
    (hL : L m t = L m' t) (hs : sal m = sal m') :
    (speakerLit L sal t).real {m} = (speakerLit L sal t).real {m'} := by
  rw [speakerLit, Kernel.ofWeights_real_singleton _ _ (λ _ => ENNReal.ofReal_ne_top),
    Kernel.ofWeights_real_singleton _ _ (λ _ => ENNReal.ofReal_ne_top), hL, hs]

/-- Under the threshold semantics the literal listener recovers a state from a word true there
with the reciprocal of the size of the word's extension. -/
theorem listenerLit_real_gq (dir : M → Direction) (θ : M → ℕ) {m : M} {t : State n}
    (h : gq dir θ m t = 1) :
    (listenerLit (gq dir θ) m).real {t} = 1 / (extension n dir θ m).card := by
  rw [listenerLit, Kernel.ofWeights_real_singleton _ _ (λ _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (gq_nonneg dir θ m t), h,
    Finset.sum_congr rfl (λ t' _ => ENNReal.toReal_ofReal (gq_nonneg dir θ m t')), sum_gq]

/-- Focality: among words true at a state and equally salient, the pragmatic speaker prefers the
one with the smaller extension, the more informative one. -/
theorem speakerPrag_real_lt_of_card_lt (dir : M → Direction) (θ : M → ℕ) {sal : M → ℝ}
    (hsal : ∀ m, 0 < sal m) {α : ℝ} (hα : 0 < α) {m m' : M} {t : State n}
    (hm : gq dir θ m t = 1) (hm' : gq dir θ m' t = 1) (hs : sal m = sal m')
    (hcard : (extension n dir θ m).card < (extension n dir θ m').card) :
    (speakerPrag (gq dir θ) sal α t).real {m'} < (speakerPrag (gq dir θ) sal α t).real {m} := by
  have hcm : 0 < (extension n dir θ m).card := Finset.card_pos.2 ⟨t, by simp [extension, hm]⟩
  have hwm : 0 < sal m * ((listenerLit (gq dir θ) m).real {t}) ^ α := by
    rw [listenerLit_real_gq dir θ hm]
    exact mul_pos (hsal m) (Real.rpow_pos_of_pos (by positivity) _)
  have h0 : (∑ m'', ENNReal.ofReal (sal m'' * ((listenerLit (gq dir θ) m'').real {t}) ^ α)) ≠ 0 :=
    λ h => (ENNReal.ofReal_pos.2 hwm).ne' ((Finset.sum_eq_zero_iff.1 h) m (Finset.mem_univ m))
  have htop : (∑ m'', ENNReal.ofReal (sal m'' * ((listenerLit (gq dir θ) m'').real {t}) ^ α)) ≠ ∞ :=
    ENNReal.sum_ne_top.2 λ _ _ => ENNReal.ofReal_ne_top
  rw [speakerPrag, Kernel.ofWeights_real_singleton_lt_iff _ h0 htop,
    ENNReal.ofReal_lt_ofReal_iff hwm, listenerLit_real_gq dir θ hm, listenerLit_real_gq dir θ hm',
    ← hs]
  refine mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (by positivity) ?_ hα) (hsal m)
  exact one_div_lt_one_div_of_lt (by exact_mod_cast hcm) (by exact_mod_cast hcard)

/-! ### The canonical quantity words -/

open English.Determiners

/-- The threshold direction of a quantity word is its monotonicity, with *half* counted as
increasing since the participants of Experiment 2 classified every word in the sample as
monotone. -/
def direction (w : QuantityWord) : Direction :=
  if w.entry.monotonicity = .decreasing then .decreasing else .increasing

/-- *Some* and *few* compete without entailment for any thresholds inside the range. -/
theorem some_few_no_entailment (θ : QuantityWord → ℕ) (hs : 1 ≤ θ .some_) (hs' : θ .some_ ≤ n)
    (hf : θ .few < n) :
    gq direction θ .few (0 : State n) = 1 ∧ gq direction θ .some_ (0 : State n) = 0 ∧
      gq direction θ .some_ (Fin.last n) = 1 ∧ gq direction θ .few (Fin.last n) = 0 :=
  gq_no_entailment direction θ rfl hs hs' rfl hf

end VanTielEtAl2021
