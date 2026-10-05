module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.VanTielEtAl2021
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# van Tiel, Franke and Sauerland (2021): Probabilistic Pragmatics Explains Gradience and Focality in Natural Language Quantification

Van Tiel, Franke and Sauerland compare two semantics of quantity words on production data, the
frame *— of the circles are red* over displays of 432 circles, where production is gradient and
peaks inside the range in which a word is true. Generalized quantifier theory gives a word a
threshold on the intersection set size, a lower bound for a monotone-increasing word and an upper
bound for a monotone-decreasing one; prototype theory gives it a degree of truth that falls off
with the distance from a prototype. Each semantics is embedded in a literal and a pragmatic
speaker, and the pragmatic speaker over thresholds explains the data as well as the prototype
models, since it prefers the true word with the smaller extension.

## Main definitions

* `gq`, `pt`: the threshold and the prototype lexicon.
* `speakerLit`, `listenerLit`, `speakerPrag`: the literal speaker, the literal listener and the
  pragmatic speaker.
* `withConfusion`: production under imprecise number representation.
* `direction`: the threshold direction of an English quantity word, read off its reading.

## Main results

* `speakerLit_apply_singleton_eq_zero`, `speakerLit_real_eq_of_eq`: a literal speaker never
  produces a false word and is indifferent among true words of equal salience.
* `speakerPrag_real_lt_of_card_lt`: the pragmatic speaker prefers the true word with the smaller
  extension, which is where focality comes from.
* `gq_no_entailment`, `some_few_no_entailment`: *some* and *few* compete without entailment.
* `monotone_gq`, `antitone_gq`: a word with a lower bound is monotone in the intersection set
  size, and a word with an upper bound antitone.
* `pt_lt_pt_of_abs_lt`: the prototype semantics is gradient by itself.

## Implementation notes

States are the intersection set sizes `Fin (n + 1)` and speakers are kernels from states to
words built with `Kernel.ofWeights`; the literal listener has a uniform prior over states.
Thresholds, prototypes, spreads and saliences are parameters, not the fitted posterior values,
and the Weber-fraction confusion kernel of Experiment 3 is an arbitrary kernel on states. The
paper takes the monotonicity of each word from the judgments of Experiment 2. Here the direction
of an English quantity word is derived from whether its reading in
`Fragments/English/Determiners.lean` is antitone in its scope, which on the six scale words gives
the experiment's classification, the non-monotone *half* included. The model comparison of
Table 1 and the ratings of Experiment 4 are not formalized. The examples are the rows of
`Data.Examples.VanTielEtAl2021`.

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

/-- The states are the intersection set sizes of a display of `n` circles. -/
abbrev State (n : ℕ) := Fin (n + 1)

/-- A quantity word's threshold is a lower bound for a monotone-increasing word and an upper
bound for a monotone-decreasing one. -/
inductive Direction where
  | increasing
  | decreasing
  deriving DecidableEq, Repr

variable {n : ℕ} {M : Type*}

/-- A lexical meaning function gives the truth value of a word at a state. -/
abbrev Lexicon (n : ℕ) (M : Type*) := M → State n → ℝ

/-- In the generalized-quantifier lexicon a word is true at the states on its side of its
threshold. -/
def gq (dir : M → Direction) (θ : M → ℕ) : Lexicon n M := fun m t ↦
  match dir m with
  | .increasing => if θ m ≤ t.val then 1 else 0
  | .decreasing => if t.val ≤ θ m then 1 else 0

/-- In the prototype lexicon the degree of truth falls off with the distance from the
prototype `p`, scaled by the spread `d`. -/
noncomputable def pt (p d : M → ℝ) : Lexicon n M := fun m t ↦
  Real.exp (-(((t.val : ℝ) - p m) / d m) ^ 2)

theorem gq_eq_one_or_zero (dir : M → Direction) (θ : M → ℕ) (m : M) (t : State n) :
    gq dir θ m t = 1 ∨ gq dir θ m t = 0 := by
  unfold gq
  split <;> split_ifs <;> simp

/-- *Some* and *few* stand in no entailment relation. With a lower bound for *some* and an upper
bound for *few* inside the range, *few* is true and *some* false of an empty intersection, and
the other way round of a full one. -/
theorem gq_no_entailment (dir : M → Direction) (θ : M → ℕ) {m m' : M}
    (hm : dir m = .increasing) (hθm : 1 ≤ θ m) (hθm' : θ m ≤ n) (hm' : dir m' = .decreasing)
    (hθ : θ m' < n) :
    gq dir θ m' (0 : State n) = 1 ∧ gq dir θ m (0 : State n) = 0 ∧
      gq dir θ m (Fin.last n) = 1 ∧ gq dir θ m' (Fin.last n) = 0 := by
  simp [gq, hm, hm', Fin.val_last]
  omega

/-- A word with a lower bound is true at more states as the intersection grows. -/
theorem monotone_gq (dir : M → Direction) (θ : M → ℕ) {m : M} (h : dir m = .increasing) :
    Monotone (gq (n := n) dir θ m) := fun t t' (htt' : t.val ≤ t'.val) ↦ by
  simp only [gq, h]
  split_ifs with h₁ h₂
  exacts [le_rfl, absurd (h₁.trans htt') h₂, zero_le_one, le_rfl]

/-- A word with an upper bound is true at fewer states as the intersection grows. -/
theorem antitone_gq (dir : M → Direction) (θ : M → ℕ) {m : M} (h : dir m = .decreasing) :
    Antitone (gq (n := n) dir θ m) := fun t t' (htt' : t.val ≤ t'.val) ↦ by
  simp only [gq, h]
  split_ifs with h₁ h₂
  exacts [le_rfl, absurd (htt'.trans h₁) h₂, zero_le_one, le_rfl]

theorem pt_pos (p d : M → ℝ) (m : M) (t : State n) : 0 < pt p d m t := Real.exp_pos _

theorem pt_le_one (p d : M → ℝ) (m : M) (t : State n) : pt p d m t ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg _))

/-- The prototype semantics is gradient by itself, a state closer to the prototype being truer. -/
theorem pt_lt_pt_of_abs_lt (p d : M → ℝ) (m : M) {t t' : State n} (hd : 0 < d m)
    (h : |(t.val : ℝ) - p m| < |(t'.val : ℝ) - p m|) : pt p d m t' < pt p d m t := by
  unfold pt
  rw [Real.exp_lt_exp, neg_lt_neg_iff, div_pow, div_pow]
  refine div_lt_div_of_pos_right ?_ (pow_pos hd 2)
  rw [← sq_abs ((t.val : ℝ) - p m), ← sq_abs ((t'.val : ℝ) - p m)]
  exact pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero

/-- The extension of a word is the set of states where it is true. -/
noncomputable def extension (n : ℕ) (dir : M → Direction) (θ : M → ℕ) (m : M) :
    Finset (State n) :=
  Finset.univ.filter fun t ↦ gq dir θ m t = 1

theorem gq_nonneg (dir : M → Direction) (θ : M → ℕ) (m : M) (t : State n) :
    0 ≤ gq dir θ m t := by
  rcases gq_eq_one_or_zero dir θ m t with h | h <;> simp [h]

theorem sum_gq (dir : M → Direction) (θ : M → ℕ) (m : M) :
    ∑ t : State n, gq dir θ m t = (extension n dir θ m).card := by
  rw [extension, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rcases gq_eq_one_or_zero dir θ m t with h | h <;> simp [h]

/-! ### Speakers -/

/-- Under imprecise number representation a speaker applies its rule at the state the confusion
kernel `cf` represents the true state as. -/
noncomputable def withConfusion [MeasurableSpace M] (S : Kernel (State n) M)
    (cf : Kernel (State n) (State n)) : Kernel (State n) M :=
  S ∘ₖ cf

/-- Exact number representation changes nothing. -/
theorem withConfusion_id [MeasurableSpace M] (S : Kernel (State n) M) :
    withConfusion S Kernel.id = S :=
  Kernel.comp_id S

variable [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]

/-- The literal speaker produces a word in proportion to its salience and its truth value. -/
noncomputable def speakerLit (L : Lexicon n M) (sal : M → ℝ) : Kernel (State n) M :=
  Kernel.ofWeights fun t m ↦ ENNReal.ofReal (sal m * L m t)

/-- The literal listener, with a uniform prior over states, infers a state in proportion to the
truth value of the word there. -/
noncomputable def listenerLit (L : Lexicon n M) : Kernel M (State n) :=
  Kernel.ofWeights fun m t ↦ ENNReal.ofReal (L m t)

/-- The pragmatic speaker with rationality `α` produces a word in proportion to its salience and
the probability that the literal listener recovers the state from it. -/
noncomputable def speakerPrag (L : Lexicon n M) (sal : M → ℝ) (α : ℝ) : Kernel (State n) M :=
  Kernel.ofWeights fun t m ↦ ENNReal.ofReal (sal m * ((listenerLit L m).real {t}) ^ α)

/-- A literal speaker never produces a false word. -/
theorem speakerLit_apply_singleton_eq_zero (L : Lexicon n M) (sal : M → ℝ) {m : M}
    {t : State n} (h : L m t = 0) : speakerLit L sal t {m} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by simp [h])

/-- A literal speaker is indifferent among words of equal salience and truth value, so that with a
threshold semantics its productions are step functions. -/
theorem speakerLit_real_eq_of_eq (L : Lexicon n M) (sal : M → ℝ) {m m' : M} {t : State n}
    (hL : L m t = L m' t) (hs : sal m = sal m') :
    (speakerLit L sal t).real {m} = (speakerLit L sal t).real {m'} := by
  rw [speakerLit, Kernel.ofWeights_real_singleton _ _ (fun _ ↦ ENNReal.ofReal_ne_top),
    Kernel.ofWeights_real_singleton _ _ (fun _ ↦ ENNReal.ofReal_ne_top), hL, hs]

/-- Under the threshold semantics the literal listener recovers a state from a word true there
with the reciprocal of the size of the word's extension. -/
theorem listenerLit_real_gq (dir : M → Direction) (θ : M → ℕ) {m : M} {t : State n}
    (h : gq dir θ m t = 1) :
    (listenerLit (gq dir θ) m).real {t} = 1 / (extension n dir θ m).card := by
  rw [listenerLit, Kernel.ofWeights_real_singleton _ _ (fun _ ↦ ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (gq_nonneg dir θ m t), h,
    Finset.sum_congr rfl (fun t' _ ↦ ENNReal.toReal_ofReal (gq_nonneg dir θ m t')), sum_gq]

/-- Among words true at a state and equally salient, the pragmatic speaker prefers the one with
the smaller extension, the more informative one, which is focality. -/
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
    fun h ↦ (ENNReal.ofReal_pos.2 hwm).ne' ((Finset.sum_eq_zero_iff.1 h) m (Finset.mem_univ m))
  have htop : (∑ m'', ENNReal.ofReal (sal m'' * ((listenerLit (gq dir θ) m'').real {t}) ^ α)) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top
  rw [speakerPrag, Kernel.ofWeights_real_singleton_lt_iff _ h0 htop,
    ENNReal.ofReal_lt_ofReal_iff hwm, listenerLit_real_gq dir θ hm, listenerLit_real_gq dir θ hm',
    ← hs]
  refine mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (by positivity) ?_ hα) (hsal m)
  exact one_div_lt_one_div_of_lt (by exact_mod_cast hcm) (by exact_mod_cast hcard)

/-! ### The canonical quantity words -/

open English.Determiners Quantifier GQ
open scoped Semantics

open Classical in
/-- A quantity word sets an upper bound when it has a reading antitone in its scope on every
finite domain, and a lower bound otherwise. -/
noncomputable def direction (w : QuantityWord) : Direction :=
  if ∃ d ∈ (⟦w⟧ : Set Family.{0}), ∀ (α : Type) [Fintype α], ScopeAntitone (d α) then .decreasing
  else .increasing

open Classical in
theorem direction_few : direction .few = .decreasing := by
  rw [direction, ite_eq_left_iff]
  exact fun h ↦ absurd ⟨_, rfl, fun _ _ ↦ scopeAntitone_few⟩ h

open Classical in
theorem direction_some : direction .some_ = .increasing := by
  rw [direction, ite_eq_right_iff]
  exact fun ⟨_, (hd : _ = Family.some), h⟩ ↦ absurd (hd ▸ h PUnit) not_scopeAntitone_some

/-- *Some* and *few* compete without entailment for any thresholds inside the range. -/
theorem some_few_no_entailment (θ : QuantityWord → ℕ) (hs : 1 ≤ θ .some_) (hs' : θ .some_ ≤ n)
    (hf : θ .few < n) :
    gq direction θ .few (0 : State n) = 1 ∧ gq direction θ .some_ (0 : State n) = 0 ∧
      gq direction θ .some_ (Fin.last n) = 1 ∧ gq direction θ .few (Fin.last n) = 0 :=
  gq_no_entailment direction θ direction_some hs hs' direction_few hf

end VanTielEtAl2021
