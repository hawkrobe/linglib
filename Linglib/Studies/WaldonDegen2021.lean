module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Pragmatics.RSA.Incremental
public import Linglib.Data.Examples.WaldonDegen2021

/-!
# Waldon & Degen (2021): Modeling Cross-Linguistic Production of Referring Expressions

This file formalizes Waldon and Degen's continuous-incremental Rational Speech Act model (CI-RSA) of
redundant modification. The model joins the word-by-word production of Cohn-Gordon, Goodman and
Potts with the noisy adjective semantics of Degen and colleagues: a word is true of a referent with
its semantic value and false with the complement, an utterance's value is the product over its
words, and the literal listener interprets a prefix by the average value of its grammatical
completions among the utterances true of some referent in the scene (`prefixMeaning`). The
incremental speaker is the softmax of the listener's mass on the referent against the word's cost,
so a trajectory's probability is the product of its steps (`stepSpeaker`, `trajectory`). Where the
standard, continuous and incremental models predict symmetric or language-blind rates, the paper
reports that CI-RSA predicts the English color/size asymmetry, less redundant color in a postnominal
Spanish, and its reversal there.

The paper's Figure 3 locates the difference at the node where the redundant adjective is
chosen after the informative one: in English, after *small* in the size-sufficient scene, the
speaker chooses between the redundant *blue* and the noun; in postnominal Spanish, after
*pin blue* in the color-sufficient scene, between the redundant *small* and stopping. The
literal listener's odds at the two nodes are `v_color (2 − v_size) / (v_color v_size + 1 −
v_size)` and its mirror image, so for every rationality and adjective cost the two steps are
equally likely under the incremental model's Boolean semantics and the English redundant color
step is the likelier exactly when color is the more reliable adjective
(`english_color_step_gt_spanish_size_step`).

## Implementation notes

Referents are pairs of a size and a color, scenes are finsets of them, and the two languages
are the utterance lists of Figure 1 closed by a stop token. Semantic values, the rationality and
the per-adjective cost are free real parameters with the bounds the paper's values
satisfy, in place of the simulated `v_size = 0.8`, `v_color = 0.95`, `α = 7` and cost `0.1`;
the whole-trajectory and cross-scene comparisons of Figures 2 and 4 are reported from the
paper's simulations and not proved. The paper's Spanish examples are the rows of
`Data.Examples.WaldonDegen2021`.

## References

* [waldon-degen-2021]
* [cohn-gordon-goodman-potts-2019]
* [degen-etal-2020]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace WaldonDegen2021

/-! ### Words, referents and semantics -/

/-- The words of the reference game, with an explicit stop token closing an utterance. -/
inductive Word
  | blue | red | big | small | pin | stop
  deriving DecidableEq, Fintype

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨λ _ => trivial⟩

/-- A referent is big or small and blue or red. -/
abbrev Referent := Bool × Bool

/-- The target of every prediction, the small blue pin. -/
abbrev smallBlue : Referent := (false, true)

/-- Boolean truth of a word of a referent. -/
def applies : Word → Referent → Bool
  | .blue, r => r.2
  | .red, r => !r.2
  | .big, r => r.1
  | .small, r => !r.1
  | .pin, _ => true
  | .stop, _ => true

/-- In the continuous lexicon of [degen-etal-2020] a color word is worth `vc` where true and
`1 − vc` where false, a size word likewise with `vs`, and the noun and the stop token are worth
one. -/
def lexicon (vc vs : ℝ) : Word → Referent → ℝ
  | .blue, r => if r.2 then vc else 1 - vc
  | .red, r => if r.2 then 1 - vc else vc
  | .big, r => if r.1 then vs else 1 - vs
  | .small, r => if r.1 then 1 - vs else vs
  | .pin, _ => 1
  | .stop, _ => 1

variable {vc vs : ℝ}

theorem lexicon_nonneg (hc : vc ≤ 1) (hc0 : 0 ≤ vc) (hs : vs ≤ 1) (hs0 : 0 ≤ vs) (w : Word)
    (r : Referent) : 0 ≤ lexicon vc vs w r := by
  cases w <;> simp only [lexicon] <;> first | (split_ifs <;> linarith) | norm_num

/-! ### Languages and scenes (Figure 1) -/

/-- English utterances put size then color before the noun, closed by the stop. -/
def english : List (List Word) :=
  [[.blue, .pin, .stop], [.red, .pin, .stop], [.big, .pin, .stop], [.small, .pin, .stop],
   [.small, .blue, .pin, .stop], [.small, .red, .pin, .stop],
   [.big, .blue, .pin, .stop], [.big, .red, .pin, .stop]]

/-- Postnominal Spanish utterances put the noun first, then color then size, closed by the
stop. -/
def spanish : List (List Word) :=
  [[.pin, .blue, .stop], [.pin, .red, .stop], [.pin, .big, .stop], [.pin, .small, .stop],
   [.pin, .blue, .small, .stop], [.pin, .red, .small, .stop],
   [.pin, .blue, .big, .stop], [.pin, .red, .big, .stop]]

/-- In the size-sufficient scene the target is the only small pin. -/
def ss : Finset Referent := {(true, true), (true, false), (false, true)}

/-- In the color-sufficient scene the target is the only blue pin. -/
def cs : Finset Referent := {(false, false), (true, false), (false, true)}

/-- The utterances of a language true of some referent of the scene. -/
def inScene (L : List (List Word)) (scene : Finset Referent) : List (List Word) :=
  L.filter λ u => decide (∃ r ∈ scene, ∀ w ∈ u, applies w r)

/-- The grammatical completions of a prefix. -/
def continuations (L : List (List Word)) (scene : Finset Referent) (pfx : List Word) :
    List (List Word) :=
  (inScene L scene).filter (pfx.isPrefixOf ·)

/-! ### The literal listener and the incremental speaker -/

/-- The continuous meaning of a prefix is the average utterance value over its
completions. -/
noncomputable def prefixMeaning (vc vs : ℝ) (L : List (List Word)) (scene : Finset Referent)
    (pfx : List Word) (r : Referent) : ℝ :=
  ((continuations L scene pfx).map (prodMeaning (lexicon vc vs) · r)).sum /
    (continuations L scene pfx).length

theorem prefixMeaning_nonneg (hc : vc ≤ 1) (hc0 : 0 ≤ vc) (hs : vs ≤ 1) (hs0 : 0 ≤ vs)
    (L : List (List Word)) (scene : Finset Referent) (pfx : List Word) (r : Referent) :
    0 ≤ prefixMeaning vc vs L scene pfx r :=
  div_nonneg (List.sum_nonneg λ x hx => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
      exact prodMeaning_nonneg (λ w r => lexicon_nonneg hc hc0 hs hs0 w r) u r)
    (Nat.cast_nonneg _)

/-- A prefix with no completion has meaning zero. -/
theorem prefixMeaning_eq_zero {L : List (List Word)} {scene : Finset Referent}
    {pfx : List Word} (h : continuations L scene pfx = []) (r : Referent) :
    prefixMeaning vc vs L scene pfx r = 0 := by
  simp [prefixMeaning, h]

/-- The listener weighs a referent of the scene by the prefix meaning. -/
noncomputable def listenerWeight (vc vs : ℝ) (L : List (List Word)) (scene : Finset Referent)
    (pfx : List Word) (r : Referent) : ℝ≥0∞ :=
  if r ∈ scene then ENNReal.ofReal (prefixMeaning vc vs L scene pfx r) else 0

/-- Given the next word, the literal listener at a context is a distribution over the scene's
referents proportional to the prefix meaning. -/
noncomputable def listener (vc vs : ℝ) (L : List (List Word)) (scene : Finset Referent)
    (ctx : List Word) : Kernel Word Referent :=
  Kernel.ofWeights λ w r => listenerWeight vc vs L scene (ctx ++ [w]) r

instance (L : List (List Word)) (scene : Finset Referent) (ctx : List Word) :
    IsFiniteKernel (listener vc vs L scene ctx) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The incremental speaker at a context is the RSA speaker of rationality `α`, against the word
costs, over the literal listener at that context. -/
noncomputable def stepSpeaker (α : ℝ) (cost : Word → ℝ) (vc vs : ℝ) (L : List (List Word))
    (scene : Finset Referent) (ctx : List Word) : Kernel Referent Word :=
  speaker α cost (listener vc vs L scene ctx)

/-- The probability of an utterance is the product of its steps, the chain rule. -/
noncomputable def trajectory (α : ℝ) (cost : Word → ℝ) (vc vs : ℝ) (L : List (List Word))
    (scene : Finset Referent) (r : Referent) (u : List Word) : ℝ :=
  ((List.range u.length).map λ k =>
    (stepSpeaker α cost vc vs L scene (u.take k) r).real {u.getD k .stop}).prod

/-! ### The listener at the redundancy nodes -/

private theorem sum_referent (f : Referent → ℝ) :
    ∑ r, f r = f (false, false) + f (false, true) + f (true, false) + f (true, true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

section Nodes

variable (hc : vc < 1) (hc0 : 0 < vc) (hs : vs < 1) (hs0 : 0 < vs)
include hc hc0 hs hs0

/-- The listener's real mass on a referent, as a ratio of prefix meanings over the scene. -/
private theorem listener_real (L : List (List Word)) (scene : Finset Referent) (ctx : List Word)
    (w : Word) (r : Referent) :
    (listener vc vs L scene ctx w).real {r} =
      (if r ∈ scene then prefixMeaning vc vs L scene (ctx ++ [w]) r else 0) /
        ∑ r', if r' ∈ scene then prefixMeaning vc vs L scene (ctx ++ [w]) r' else 0 := by
  have hnn := prefixMeaning_nonneg hc.le hc0.le hs.le hs0.le L scene (ctx ++ [w])
  simp only [listener]
  rw [Kernel.ofWeights_real_singleton _ _
    (λ _ => by simp only [listenerWeight]; split_ifs <;> simp)]
  congr 1
  · simp only [listenerWeight]; split_ifs <;> simp [ENNReal.toReal_ofReal (hnn _)]
  · exact Finset.sum_congr rfl λ r' _ => by
      simp only [listenerWeight]; split_ifs <;> simp [ENNReal.toReal_ofReal (hnn _)]

/-- After *small* in the size-sufficient scene, the listener's mass on the target under the
redundant *blue*. -/
theorem listener_ss_small_blue :
    (listener vc vs english ss [.small] .blue).real {smallBlue} =
      vs * vc / (vs * vc + (1 - vs)) := by
  rw [listener_real hc hc0 hs hs0, sum_referent]
  have h : continuations english ss [.small, .blue] = [[.small, .blue, .pin, .stop]] := by
    decide
  simp only [List.cons_append, List.nil_append, prefixMeaning, h]
  simp [lexicon, ss, smallBlue]
  congr 1
  ring

/-- After *small* in the size-sufficient scene, the listener's mass on the target under the
noun. -/
theorem listener_ss_small_pin :
    (listener vc vs english ss [.small] .pin).real {smallBlue} = vs / (2 - vs) := by
  rw [listener_real hc hc0 hs hs0, sum_referent]
  have h : continuations english ss [.small, .pin] = [[.small, .pin, .stop]] := by decide
  simp only [List.cons_append, List.nil_append, prefixMeaning, h]
  simp [lexicon, ss, smallBlue]
  congr 1
  ring

/-- After *pin blue* in the color-sufficient scene, the Spanish listener's mass on the target
under the redundant *small*. -/
theorem listener_cs_pin_blue_small :
    (listener vc vs spanish cs [.pin, .blue] .small).real {smallBlue} =
      vc * vs / (vc * vs + (1 - vc)) := by
  rw [listener_real hc hc0 hs hs0, sum_referent]
  have h : continuations spanish cs [.pin, .blue, .small] = [[.pin, .blue, .small, .stop]] := by
    decide
  simp only [List.cons_append, List.nil_append, prefixMeaning, h]
  simp [lexicon, cs, smallBlue]
  congr 1
  ring

/-- After *pin blue* in the color-sufficient scene, the Spanish listener's mass on the target
under stopping. -/
theorem listener_cs_pin_blue_stop :
    (listener vc vs spanish cs [.pin, .blue] .stop).real {smallBlue} = vc / (2 - vc) := by
  rw [listener_real hc hc0 hs hs0, sum_referent]
  have h : continuations spanish cs [.pin, .blue, .stop] = [[.pin, .blue, .stop]] := by decide
  simp only [List.cons_append, List.nil_append, prefixMeaning, h]
  simp [lexicon, cs, smallBlue]
  congr 1
  ring

end Nodes

/-! ### The incremental speaker at the redundancy nodes -/

section Speaker

variable {α : ℝ} {cost : Word → ℝ} {L : List (List Word)} {scene : Finset Referent}
  {ctx : List Word}

/-- A next word with no completion receives no listener mass. -/
theorem listener_apply_eq_zero {w : Word} (h : continuations L scene (ctx ++ [w]) = [])
    (r : Referent) : listener vc vs L scene ctx w {r} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by simp [listenerWeight, prefixMeaning_eq_zero h])

/-- At a node with two applicable words the speaker's share of one is its weight against the
other's, the weight being the listener's mass raised to the rationality, discounted by the cost. -/
theorem stepSpeaker_real_pair (hα : 0 < α) {u u' : Word} (huu' : u ≠ u')
    (hsupp : ∀ w, w ≠ u → w ≠ u' → continuations L scene (ctx ++ [w]) = []) (r : Referent) :
    (stepSpeaker α cost vc vs L scene ctx r).real {u} =
      (listener vc vs L scene ctx u).real {r} ^ α * Real.exp (-(α * cost u)) /
        ((listener vc vs L scene ctx u).real {r} ^ α * Real.exp (-(α * cost u)) +
          (listener vc vs L scene ctx u').real {r} ^ α * Real.exp (-(α * cost u'))) := by
  rw [stepSpeaker, speaker_eq_ofWeights, Kernel.ofWeights_real_singleton_of_pair r huu'
      (λ w => ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
        ENNReal.ofReal_ne_top)
      (λ w hw => by
        by_contra hne
        push Not at hne
        exact hw (by rw [listener_apply_eq_zero (hsupp w hne.1 hne.2), ENNReal.zero_rpow_of_pos hα,
          zero_mul]))]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, measureReal_def,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- At the paper's Figure 3 nodes, with a common cost for the two adjectives and none for the
noun and the stop, the English redundant color step after *small* in the size-sufficient scene
is likelier than the Spanish redundant size step after *pin blue* in the color-sufficient scene
exactly when color is the more reliable adjective, at every rationality. -/
theorem english_color_step_gt_spanish_size_step (hα : 0 < α) (hadj : cost .small = cost .blue)
    (hpin : cost .pin = 0) (hstop : cost .stop = 0) (hc : vc < 1) (hc0 : 0 < vc) (hs : vs < 1)
    (hs0 : 0 < vs)
    (h : vs < vc) :
    (stepSpeaker α cost vc vs spanish cs [.pin, .blue] smallBlue).real {.small} <
      (stepSpeaker α cost vc vs english ss [.small] smallBlue).real {.blue} := by
  rw [stepSpeaker_real_pair hα (u := .small) (u' := .stop) (by decide)
      (λ w h1 h2 => by cases w <;> first | decide | exact absurd rfl h1 | exact absurd rfl h2),
    stepSpeaker_real_pair hα (u := .blue) (u' := .pin) (by decide)
      (λ w h1 h2 => by cases w <;> first | decide | exact absurd rfl h1 | exact absurd rfl h2),
    listener_cs_pin_blue_small hc hc0 hs hs0, listener_cs_pin_blue_stop hc hc0 hs hs0,
    listener_ss_small_blue hc hc0 hs hs0, listener_ss_small_pin hc hc0 hs hs0, hadj, hpin, hstop,
    mul_zero, neg_zero, Real.exp_zero, mul_one]
  have hcpos : 0 < Real.exp (-(α * cost .blue)) := Real.exp_pos _
  have hD : 0 < vs * vc + (1 - vs) := by nlinarith
  have hD' : 0 < vc * vs + (1 - vc) := by nlinarith
  have hA : 0 < vs * vc / (vs * vc + (1 - vs)) := div_pos (by positivity) hD
  have hA' : 0 < vc * vs / (vc * vs + (1 - vc)) := div_pos (by positivity) hD'
  have hB : 0 < vs / (2 - vs) := div_pos hs0 (by linarith)
  have hB' : 0 < vc / (2 - vc) := div_pos hc0 (by linarith)
  have hkey : vc * vs / (vc * vs + (1 - vc)) * (vs / (2 - vs)) <
      vs * vc / (vs * vc + (1 - vs)) * (vc / (2 - vc)) := by
    rw [div_mul_div_comm, div_mul_div_comm,
      div_lt_div_iff₀ (mul_pos hD' (by linarith)) (mul_pos hD (by linarith))]
    have e : vs * vc * vc * ((vc * vs + (1 - vc)) * (2 - vs)) -
        vc * vs * vs * ((vs * vc + (1 - vs)) * (2 - vc)) =
        vc * vs * ((vc - vs) * (2 * (1 - vc) * (1 - vs) + vc * vs)) := by ring
    nlinarith [mul_pos (mul_pos hc0 hs0) (mul_pos (sub_pos.2 h)
      (by nlinarith : 0 < 2 * (1 - vc) * (1 - vs) + vc * vs))]
  have hpow := Real.rpow_lt_rpow (by positivity) hkey hα
  rw [Real.mul_rpow hA'.le hB.le, Real.mul_rpow hA.le hB'.le] at hpow
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left hpow hcpos, Real.rpow_pos_of_pos hA α,
    Real.rpow_pos_of_pos hA' α, Real.rpow_pos_of_pos hB α, Real.rpow_pos_of_pos hB' α]

/-- With equally reliable adjectives, the Boolean case of the incremental model, the two steps
are equally likely, the symmetry the paper's Figure 3 reports for I-RSA. -/
theorem english_color_step_eq_spanish_size_step (hα : 0 < α) (hadj : cost .small = cost .blue)
    (hpin : cost .pin = 0) (hstop : cost .stop = 0)
    (hc : vc < 1) (hc0 : 0 < vc) (hs : vs < 1) (hs0 : 0 < vs) (h : vs = vc) :
    (stepSpeaker α cost vc vs spanish cs [.pin, .blue] smallBlue).real {.small} =
      (stepSpeaker α cost vc vs english ss [.small] smallBlue).real {.blue} := by
  rw [stepSpeaker_real_pair hα (u := .small) (u' := .stop) (by decide)
      (λ w h1 h2 => by cases w <;> first | decide | exact absurd rfl h1 | exact absurd rfl h2),
    stepSpeaker_real_pair hα (u := .blue) (u' := .pin) (by decide)
      (λ w h1 h2 => by cases w <;> first | decide | exact absurd rfl h1 | exact absurd rfl h2),
    listener_cs_pin_blue_small hc hc0 hs hs0, listener_cs_pin_blue_stop hc hc0 hs hs0,
    listener_ss_small_blue hc hc0 hs hs0, listener_ss_small_pin hc hc0 hs hs0, hadj, hpin, hstop,
    h, mul_comm vc vc]

end Speaker

end WaldonDegen2021
