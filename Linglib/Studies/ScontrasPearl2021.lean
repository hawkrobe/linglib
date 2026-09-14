import Linglib.Pragmatics.RSA.QUD
import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Core.Probability.Distributions.Binomial
import Linglib.Core.Probability.Kernel.Posterior

/-!
# Scontras and Pearl (2021): When Pragmatics Matters More for Truth-Value Judgments

This file formalizes the paper's Rational Speech Act model of utterance endorsement in the
truth-value judgment task, for the scopally ambiguous *every horse didn't jump* (§3) and *two
horses didn't jump* (§4), on the RSA kernel pipeline. A world is the number of horses that
jumped. The test sentence is true on its surface reading when the determiner holds of the
non-jumpers and on its inverse reading when it fails of the jumpers (`ext`); the literal listener
is uniform on the extension (fn. 6); a question projects the worlds onto its answer (`project`);
the speaker `S1` is the best response to the literal listener of its scope interpretation
projected by its question; the pragmatic listener `L1` inverts the speaker jointly over worlds,
interpretations and questions; and the endorsing speaker `S2`, who sees only the world, chooses
between the sentence and silence by the world marginal of `L1`, so that a truth-value judgment is
a production decision.

The endorsement probability has a closed form (`S2_real_amb`): writing `m` for the probability
that a speaker at the observed world produces the sentence, averaged over interpretations and
questions, and `z` for its expectation under the world prior, the sentence is endorsed with
probability `m (1 - z) / (m (1 - z) + z (1 - m))`, hence more often than not exactly when it is
produced at the observed world more often than on average (`one_half_lt_S2_real_amb_iff`). The
paper's mechanisms follow. Under the question *all?* the two scope interpretations produce alike
at every world (`S1_all_scope`), so with that question settled the scope prior does not affect
endorsement (`S2_real_amb_all`, Figure 3); at the not-all world of the two-horse scenario *all?*
maximizes and *none?* minimizes the production of the sentence under either interpretation
(`share_le_share_all`, `share_none_le_share`, Figure 2); production falls with the number of
jumpers (`share_antitone`), so a higher success base rate in the binomial world prior raises
endorsement at every world (`S2_real_amb_mono_baseRate`, Figure 2). With two horses the two-not
sentence has the extension of the every-not sentence on both interpretations under either
numeral reading, so the two models coincide (`S2_twoExact_two`, `S2_twoAtLeast_two`, §4.2.1).
With four horses and two jumpers the exact reading makes the surface interpretation true at that
world alone (`ext_twoExact_surface`), so the surface speaker produces the sentence at least as
often as under the at-least reading whatever the question (`share_twoAtLeast_le_share_twoExact`),
while the inverse interpretation under *all?* favors the at-least reading
(`share_twoExact_lt_share_twoAtLeast`), which is why the 2-of-4 fit needs a low prior on inverse
scope (Figure 7).

## Implementation notes

* The rationality of `S1` and the priors on worlds, interpretations and questions are
  parameters. The numerical predictions of Figures 2, 3, 6 and 7, at unit rationality and the
  paper's grid of priors, are not restated, and the endorsement rates of the experiments the
  paper reviews are not data of this file.
* A determiner is a relation between the number of restrictor members outside its scope and the
  number inside it, so *every* is `every` and *two* is `Numerals.bareMeaning 2` or
  `Numerals.atLeastMeaning 2` of the inside count; (2) and (6) are the resulting truth conditions
  at two and at four horses.
* Both models share the five questions of (7): the every-not model is the case of a question
  prior carried by the first three, and with two horses the numeral questions partition the
  worlds as *all?* does (`cell_exactlyTwo_two`, `cell_atLeastTwo_two`).
* Utterances are costless (fn. 8) and the literal listener carries no world prior (fn. 6),
  following [qing-franke-2015]; the projected listener is that of [kao-etal-2014-hyperbole].

## References

* [scontras-pearl-2021]
* [musolino-lidz-2003]
* [kao-etal-2014-hyperbole]
* [qing-franke-2015]
* [goodman-frank-2016]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal unitInterval Fin.NatCast

namespace ScontrasPearl2021

/-- The utterances of (2): the null utterance, which says nothing, and the scopally ambiguous
test sentence. -/
inductive Utt
  | null | amb
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utt := ⊤
instance : DiscreteMeasurableSpace Utt := ⟨λ _ => trivial⟩

/-- The scope interpretations of the test sentence: the determiner over negation, or negation
over the determiner. -/
inductive Scope
  | surface | inverse
  deriving DecidableEq, Fintype

instance : MeasurableSpace Scope := ⊤
instance : DiscreteMeasurableSpace Scope := ⟨λ _ => trivial⟩
instance : Nonempty Scope := ⟨.surface⟩

/-- The questions under discussion of (3) and (7): how many horses jumped, and whether all, none,
exactly two or at least two did. -/
inductive QUD
  | howMany | all | none | exactlyTwo | atLeastTwo
  deriving DecidableEq, Fintype

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨λ _ => trivial⟩
instance : Nonempty QUD := ⟨.howMany⟩

/-- A world: the number of horses, out of `n`, that jumped. -/
abbrev World (n : ℕ) := Fin (n + 1)

/-! ### Semantics -/

/-- The determiner *every* on counts: no restrictor member lies outside its scope. -/
def every (outside _inside : ℕ) : Prop := outside = 0

instance : DecidableRel every := λ _ _ => inferInstanceAs (Decidable (_ = 0))

/-- The numeral *two* on counts, on its exact reading. -/
def twoExact (_outside inside : ℕ) : Prop := Numerals.bareMeaning 2 inside

instance : DecidableRel twoExact := λ _ k => inferInstanceAs (Decidable (Numerals.bareMeaning 2 k))

/-- The numeral *two* on counts, on its at-least reading. -/
def twoAtLeast (_outside inside : ℕ) : Prop := Numerals.atLeastMeaning 2 inside

instance : DecidableRel twoAtLeast :=
  λ _ k => inferInstanceAs (Decidable (Numerals.atLeastMeaning 2 k))

/-- The extension of an utterance under a scope interpretation ((2), (6)) among `n` horses. The
null utterance is true everywhere; *D horses didn't jump* is true at `w` on its surface reading
when `D` holds with the `w` jumpers outside its scope and the `n - w` non-jumpers inside, and on
its inverse reading when `D` fails with the `n - w` non-jumpers outside and the `w` jumpers
inside. -/
def ext (D : ℕ → ℕ → Prop) [DecidableRel D] (n : ℕ) : Scope → Utt → Finset (World n)
  | _, .null => Finset.univ
  | .surface, .amb => Finset.univ.filter λ w => D w (n - w)
  | .inverse, .amb => Finset.univ.filter λ w => ¬ D (n - w) w

/-- With two horses, *two horses didn't jump* on its exact reading is true exactly where *every
horse didn't jump* is, on both interpretations (§4.2.1). -/
theorem ext_twoExact_two (i : Scope) (u : Utt) : ext twoExact 2 i u = ext every 2 i u := by
  cases i <;> cases u <;> decide

/-- With two horses, *two horses didn't jump* on its at-least reading is true exactly where *every
horse didn't jump* is, on both interpretations (§4.2.1). -/
theorem ext_twoAtLeast_two (i : Scope) (u : Utt) : ext twoAtLeast 2 i u = ext every 2 i u := by
  cases i <;> cases u <;> decide

/-- With four horses, the surface reading of *two horses didn't jump* on the exact reading of the
numeral is true only where exactly two jumped ((6), Figure 5). -/
theorem ext_twoExact_surface : ext twoExact 4 .surface .amb = {2} := by decide

theorem mem_ext_every_surface {n : ℕ} {w : World n} :
    w ∈ ext every n .surface .amb ↔ w = 0 := by
  rw [ext, Finset.mem_filter, every, Fin.ext_iff, Fin.val_zero]
  simp only [Finset.mem_univ, true_and]

theorem mem_ext_every_inverse {n : ℕ} {w : World n} :
    w ∈ ext every n .inverse .amb ↔ w ≠ Fin.last n := by
  rw [ext, Finset.mem_filter, every, Ne, Fin.ext_iff, Fin.val_last]
  simp only [Finset.mem_univ, true_and]
  omega

/-- The projection of a question ((3), (7)) sends a world to its answer: the number of jumpers
for *how many?*, and for the polar questions whether all, none, exactly two or at least two
jumped. -/
def project (n : ℕ) : QUD → World n → World n ⊕ Bool
  | .howMany, w => .inl w
  | .all, w => .inr (decide (w = Fin.last n))
  | .none, w => .inr (decide (w = 0))
  | .exactlyTwo, w => .inr (decide ((w : ℕ) = 2))
  | .atLeastTwo, w => .inr (decide (2 ≤ (w : ℕ)))

/-- The cell of a world under a question: the worlds sharing its answer. -/
def cell (n : ℕ) (q : QUD) (w : World n) : Finset (World n) :=
  Finset.univ.filter λ w' => project n q w' = project n q w

theorem mem_cell {n : ℕ} {q : QUD} {w w' : World n} :
    w' ∈ cell n q w ↔ project n q w' = project n q w := by
  simp [cell]

theorem mem_cell_self {n : ℕ} (q : QUD) (w : World n) : w ∈ cell n q w := mem_cell.mpr rfl

theorem mem_cell_all {n : ℕ} {w w' : World n} :
    w' ∈ cell n .all w ↔ (w' = Fin.last n ↔ w = Fin.last n) := by
  simp [mem_cell, project]

/-- With two horses, *exactly two?* asks whether all jumped. -/
theorem cell_exactlyTwo_two (w : World 2) : cell 2 .exactlyTwo w = cell 2 .all w := by
  revert w; decide

/-- With two horses, *at least two?* asks whether all jumped. -/
theorem cell_atLeastTwo_two (w : World 2) : cell 2 .atLeastTwo w = cell 2 .all w := by
  revert w; decide

/-! ### The model -/

section Model

variable (D : ℕ → ℕ → Prop) [DecidableRel D] (n : ℕ)

/-- The literal listener: uniform on the extension of the utterance under the scope
interpretation, with no world prior (fn. 6). -/
noncomputable def L0 (i : Scope) : Kernel Utt (World n) :=
  literalListener (uniformOn Set.univ) λ u => (↑(ext D n i u) : Set (World n)).indicator 1

theorem L0_apply (i : Scope) (u : Utt) : L0 D n i u = uniformOn ↑(ext D n i u) := by
  rw [L0, literalListener_indicator, Kernel.ofFunOfCountable_apply, uniformOn, uniformOn,
    cond_cond_eq_cond_inter' MeasurableSet.univ (Finset.measurableSet _) (by simp),
    Set.univ_inter]

theorem L0_apply_le_one (i : Scope) (u : Utt) (s : Set (World n)) : L0 D n i u s ≤ 1 :=
  literalListener_apply_le_one _ _ u s

/-- The literal listener of a scope interpretation projected by a question puts on a world the
fraction of the extension lying in the world's cell. -/
theorem projListener_L0_apply (i : Scope) (q : QUD) (u : Utt) (w : World n) :
    projListener (project n) (L0 D n i) q u {w}
      = uniformOn ↑(ext D n i u) (↑(cell n q w) : Set (World n)) := by
  rw [projListener_apply_singleton, L0_apply]
  congr 1
  ext w'
  simp [cell]

variable (α : ℝ)

/-- The speaker (§3.1): at a world, a scope interpretation and a question, the best response at
rationality `α` to the literal listener of the interpretation projected by the question; the
utterances are costless (fn. 8). -/
noncomputable def S1 : Kernel (World n × (Scope × QUD)) Utt :=
  familySpeaker (λ l => projListener (project n) (L0 D n l.1) l.2) α 1

theorem S1_apply (w : World n) (l : Scope × QUD) :
    S1 D n α (w, l) = speaker α 1 (projListener (project n) (L0 D n l.1) l.2) w := rfl

instance : IsFiniteKernel (S1 D n α) := inferInstanceAs (IsFiniteKernel (familySpeaker _ α 1))

theorem isMarkovKernel_S1 (hα : 0 ≤ α) : IsMarkovKernel (S1 D n α) := by
  refine ⟨λ p => ?_⟩
  obtain ⟨w, l⟩ := p
  rw [S1_apply]
  have := isMarkovKernel_speaker hα (λ _ => one_ne_zero) (λ _ => ENNReal.one_ne_top)
    (projListener (project n) (L0 D n l.1) l.2)
    (λ u w => projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one D n l.1))
    (λ w => ⟨.null, by
      rw [projListener_L0_apply, Ne, uniformOn_eq_zero_iff (Finset.finite_toSet _)]
      exact Set.nonempty_iff_ne_empty.mp
        ⟨w, Finset.mem_coe.mpr (Finset.mem_univ w), Finset.mem_coe.mpr (mem_cell_self l.2 w)⟩⟩)
  exact IsMarkovKernel.isProbabilityMeasure w

variable (μ : Measure (World n)) [IsFiniteMeasure μ] (ν : Measure (Scope × QUD)) [IsFiniteMeasure ν]

/-- The pragmatic listener (§3.1): the Bayesian inverse of the speaker over worlds,
interpretations and questions, against the product of the world prior and a prior on
interpretations and questions (the paper's `P(i) P(q)`). -/
noncomputable def L1 : Kernel Utt (World n × (Scope × QUD)) :=
  familyListener (λ l => projListener (project n) (L0 D n l.1) l.2) α 1 (μ.prod ν)

/-- The endorsing speaker (§3.1): at the observed world, the best response at unit rationality to
the world marginal of the pragmatic listener. -/
noncomputable def S2 : Kernel (World n) Utt := speaker 1 1 (Kernel.fst (L1 D n α μ ν))

/-- With two horses the two-not model on the exact reading is the every-not model (§4.2.1). -/
theorem S2_twoExact_two (μ : Measure (World 2)) [IsFiniteMeasure μ] :
    S2 twoExact 2 α μ ν = S2 every 2 α μ ν := by
  simp only [S2, L1, L0, ext_twoExact_two]

/-- With two horses the two-not model on the at-least reading is the every-not model (§4.2.1). -/
theorem S2_twoAtLeast_two (μ : Measure (World 2)) [IsFiniteMeasure μ] :
    S2 twoAtLeast 2 α μ ν = S2 every 2 α μ ν := by
  simp only [S2, L1, L0, ext_twoAtLeast_two]

end Model

/-! ### Production shares -/

section Share

variable (D : ℕ → ℕ → Prop) [DecidableRel D] (n : ℕ) (α : ℝ)

/-- The fraction of the extension of an utterance under a scope interpretation that lies in the
cell of a world under a question: the projected literal listener's mass on the world. -/
noncomputable def cellMass (l : Scope × QUD) (u : Utt) (w : World n) : ℝ :=
  (projListener (project n) (L0 D n l.1) l.2 u).real {w}

theorem cellMass_eq (l : Scope × QUD) (u : Utt) (w : World n) :
    cellMass D n l u w = ((ext D n l.1 u ∩ cell n l.2 w).card : ℝ) / (ext D n l.1 u).card := by
  rw [cellMass, measureReal_def, projListener_L0_apply, uniformOn_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

theorem cellMass_nonneg (l : Scope × QUD) (u : Utt) (w : World n) : 0 ≤ cellMass D n l u w :=
  measureReal_nonneg

theorem cellMass_null_pos (l : Scope × QUD) (w : World n) : 0 < cellMass D n l .null w := by
  rw [cellMass_eq]
  refine div_pos ?_ (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_univ w⟩))
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr
    ⟨Finset.mem_univ w, mem_cell_self l.2 w⟩⟩)

/-- The probability that the speaker produces the test sentence at a world under a scope
interpretation and a question. -/
noncomputable def share (l : Scope × QUD) (w : World n) : ℝ := (S1 D n α (w, l)).real {.amb}

theorem share_eq (hα : 0 ≤ α) (l : Scope × QUD) (w : World n) :
    share D n α l w
      = cellMass D n l .amb w ^ α / (cellMass D n l .amb w ^ α + cellMass D n l .null w ^ α) := by
  rw [share, S1_apply, speaker, Kernel.ofWeights_real_singleton_of_pair _ (b := Utt.amb)
    (b' := Utt.null) (by decide)
    (λ u => ENNReal.mul_ne_top (weight_rpow_ne_top hα
      (projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one D n l.1))) ENNReal.one_ne_top)
    (λ u _ => by cases u <;> simp)]
  simp only [Pi.one_apply, mul_one, cellMass, measureReal_def, ← ENNReal.toReal_rpow]

theorem share_nonneg (l : Scope × QUD) (w : World n) : 0 ≤ share D n α l w := measureReal_nonneg

theorem share_le_one (l : Scope × QUD) (w : World n) : share D n α l w ≤ 1 := by
  rw [share, S1_apply]
  exact speaker_real_singleton_le_one _ _ _ _ _

theorem share_lt_one (hα : 0 ≤ α) (l : Scope × QUD) (w : World n) : share D n α l w < 1 := by
  rw [share_eq D n α hα]
  have hy := Real.rpow_pos_of_pos (cellMass_null_pos D n l w) α
  have hx := Real.rpow_nonneg (cellMass_nonneg D n l .amb w) α
  rw [div_lt_one (add_pos_of_nonneg_of_pos hx hy)]
  linarith

/-- The test sentence is produced at a world at which it is true. -/
theorem share_pos (hα : 0 ≤ α) {l : Scope × QUD} {w : World n} (h : w ∈ ext D n l.1 .amb) :
    0 < share D n α l w := by
  rw [share_eq D n α hα]
  have hy := Real.rpow_pos_of_pos (cellMass_null_pos D n l w) α
  refine div_pos (Real.rpow_pos_of_pos ?_ α)
    (add_pos_of_nonneg_of_pos (Real.rpow_nonneg (cellMass_nonneg _ _ _ _ _) α) hy)
  rw [cellMass_eq]
  refine div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr
    ⟨h, mem_cell_self l.2 w⟩⟩)) (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, h⟩))

private theorem sum_utt (f : Utt → ℝ) : ∑ u, f u = f .amb + f .null :=
  Fintype.sum_eq_add Utt.amb Utt.null (by decide) (λ u h => by cases u <;> simp at h)

/-- The null utterance takes the rest of the speaker's mass. -/
theorem S1_real_null (hα : 0 ≤ α) (l : Scope × QUD) (w : World n) :
    (S1 D n α (w, l)).real {.null} = 1 - share D n α l w := by
  have := isMarkovKernel_S1 D n α hα
  have h := probReal_univ (μ := S1 D n α (w, l))
  rw [← Finset.coe_univ, ← sum_measureReal_singleton, sum_utt] at h
  rw [share]
  linarith

/-- The number of worlds in the cell of `w` under the question of `l` at which `u` is true under
the interpretation of `l`. -/
def cellCount (l : Scope × QUD) (u : Utt) (w : World n) : ℕ := (ext D n l.1 u ∩ cell n l.2 w).card

private theorem cellMass_mul_cellMass_le_iff {D' : ℕ → ℕ → Prop} [DecidableRel D']
    {l l' : Scope × QUD} {w w' : World n} (hS : 0 < (ext D n l.1 .amb).card)
    (hS' : 0 < (ext D' n l'.1 .amb).card) :
    cellMass D n l .amb w * cellMass D' n l' .null w'
        ≤ cellMass D' n l' .amb w' * cellMass D n l .null w
      ↔ cellCount D n l .amb w * cellCount D' n l' .null w' * (ext D' n l'.1 .amb).card
        ≤ cellCount D' n l' .amb w' * cellCount D n l .null w * (ext D n l.1 .amb).card := by
  simp only [cellMass_eq, cellCount]
  have hN : (0 : ℝ) < (ext D' n l'.1 .null).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w', Finset.mem_univ _⟩)
  have hN' : (ext D n l.1 .null).card = (ext D' n l'.1 .null).card := rfl
  rw [hN', div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity), ← mul_assoc, ← mul_assoc]
  exact ⟨λ h => by exact_mod_cast le_of_mul_le_mul_right h hN,
    λ h => mul_le_mul_of_nonneg_right (by exact_mod_cast h) hN.le⟩

/-- Comparing production probabilities across worlds, interpretations, questions and
determiners: the rationality cancels, leaving a comparison of the odds of the test sentence
against silence, each the fraction of the sentence's extension in the world's cell over the
fraction of all worlds in it. -/
theorem share_le_share_iff (hα : 0 < α) {D' : ℕ → ℕ → Prop} [DecidableRel D']
    {l l' : Scope × QUD} {w w' : World n} (hS : 0 < (ext D n l.1 .amb).card)
    (hS' : 0 < (ext D' n l'.1 .amb).card) :
    share D n α l w ≤ share D' n α l' w'
      ↔ cellCount D n l .amb w * cellCount D' n l' .null w' * (ext D' n l'.1 .amb).card
        ≤ cellCount D' n l' .amb w' * cellCount D n l .null w * (ext D n l.1 .amb).card := by
  rw [share_eq D n α hα.le, share_eq D' n α hα.le, ← cellMass_mul_cellMass_le_iff D n hS hS']
  have hx := Real.rpow_nonneg (cellMass_nonneg D n l .amb w) α
  have hx' := Real.rpow_nonneg (cellMass_nonneg D' n l' .amb w') α
  have hy := Real.rpow_pos_of_pos (cellMass_null_pos D n l w) α
  have hy' := Real.rpow_pos_of_pos (cellMass_null_pos D' n l' w') α
  rw [div_le_div_iff₀ (by linarith) (by linarith), ← Real.rpow_le_rpow_iff (z := α)
    (mul_nonneg (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _))
    (mul_nonneg (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _)) hα,
    Real.mul_rpow (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _),
    Real.mul_rpow (cellMass_nonneg _ _ _ _ _) (cellMass_nonneg _ _ _ _ _)]
  constructor <;> intro h <;> nlinarith

theorem share_lt_share_iff (hα : 0 < α) {D' : ℕ → ℕ → Prop} [DecidableRel D']
    {l l' : Scope × QUD} {w w' : World n} (hS : 0 < (ext D n l.1 .amb).card)
    (hS' : 0 < (ext D' n l'.1 .amb).card) :
    share D n α l w < share D' n α l' w'
      ↔ cellCount D n l .amb w * cellCount D' n l' .null w' * (ext D' n l'.1 .amb).card
        < cellCount D' n l' .amb w' * cellCount D n l .null w * (ext D n l.1 .amb).card := by
  rw [← not_le, share_le_share_iff D' n α hα hS' hS, not_le]

end Share

/-! ### Endorsement -/

section Endorsement

variable (D : ℕ → ℕ → Prop) [DecidableRel D] (n : ℕ) (α : ℝ) (μ : Measure (World n))
  (ν : Measure (Scope × QUD))

/-- The probability that the test sentence is produced at a world, the interpretation and the
question drawn from `ν`. -/
noncomputable def production (w : World n) : ℝ := ∑ l, ν.real {l} * share D n α l w

/-- The prior probability that the test sentence is produced: the observation marginal of the
speaker. -/
noncomputable def expectedProduction : ℝ := (S1 D n α ∘ₘ μ.prod ν).real {.amb}

theorem production_nonneg (w : World n) : 0 ≤ production D n α ν w :=
  Finset.sum_nonneg λ l _ => mul_nonneg measureReal_nonneg (share_nonneg D n α l w)

private theorem sum_real_singleton_eq_one {X : Type*} [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X] (ρ : Measure X) [IsProbabilityMeasure ρ] :
    ∑ x, ρ.real {x} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

instance : IsMarkovKernel (L1 D n α μ ν) :=
  inferInstanceAs (IsMarkovKernel ((familySpeaker _ α 1)†(μ.prod ν)))

theorem expectedProduction_eq_sum :
    expectedProduction D n α μ ν = ∑ w, μ.real {w} * production D n α ν w := by
  rw [expectedProduction, Measure.comp_real_singleton, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl λ w _ => ?_
  rw [production, Finset.mul_sum]
  exact Finset.sum_congr rfl λ l _ => by rw [Measure.prod_real_singleton, share, mul_assoc]

theorem production_le_one (w : World n) : production D n α ν w ≤ 1 :=
  (Finset.sum_le_sum λ l _ =>
    mul_le_of_le_one_right measureReal_nonneg (share_le_one D n α l w)).trans_eq
    (sum_real_singleton_eq_one ν)

theorem production_lt_one (hα : 0 ≤ α) (w : World n) : production D n α ν w < 1 := by
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((sum_real_singleton_eq_one ν).trans_ne one_ne_zero)
  refine (Finset.sum_lt_sum (λ l _ => mul_le_of_le_one_right measureReal_nonneg
    (share_le_one D n α l w)) ⟨l, Finset.mem_univ l, ?_⟩).trans_eq (sum_real_singleton_eq_one ν)
  exact mul_lt_of_lt_one_right (lt_of_le_of_ne measureReal_nonneg (Ne.symm hl))
    (share_lt_one D n α hα l w)

/-- The test sentence is produced with positive probability at a world at which it is true on
both interpretations. -/
theorem production_pos (hα : 0 ≤ α) {w : World n} (h : ∀ l : Scope × QUD, w ∈ ext D n l.1 .amb) :
    0 < production D n α ν w := by
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((sum_real_singleton_eq_one ν).trans_ne one_ne_zero)
  exact Finset.sum_pos' (λ l _ => mul_nonneg measureReal_nonneg (share_nonneg D n α l w))
    ⟨l, Finset.mem_univ l, mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hl))
      (share_pos D n α hα (h l))⟩

theorem expectedProduction_lt_one (hα : 0 ≤ α) : expectedProduction D n α μ ν < 1 := by
  rw [expectedProduction_eq_sum]
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((sum_real_singleton_eq_one μ).trans_ne one_ne_zero)
  refine (Finset.sum_lt_sum (λ w _ => mul_le_of_le_one_right measureReal_nonneg
    (production_le_one D n α ν w)) ⟨w, Finset.mem_univ w, ?_⟩).trans_eq
    (sum_real_singleton_eq_one μ)
  exact mul_lt_of_lt_one_right (lt_of_le_of_ne measureReal_nonneg (Ne.symm hw))
    (production_lt_one D n α ν hα w)

theorem expectedProduction_pos (hα : 0 ≤ α) {w : World n} (hμ : μ {w} ≠ 0)
    (h : ∀ l : Scope × QUD, w ∈ ext D n l.1 .amb) : 0 < expectedProduction D n α μ ν := by
  rw [expectedProduction_eq_sum]
  exact Finset.sum_pos' (λ w _ => mul_nonneg measureReal_nonneg (production_nonneg D n α ν w))
    ⟨w, Finset.mem_univ w, mul_pos (ENNReal.toReal_pos hμ (measure_ne_top _ _))
      (production_pos D n α ν hα h)⟩

/-- The endorsement probability as a function of the production probability `m` at the observed
world and its expectation `z` under the world prior. -/
noncomputable def endorse (m z : ℝ) : ℝ := m * (1 - z) / (m * (1 - z) + z * (1 - m))

section Endorse

variable {m m' z z' : ℝ}

theorem endorse_denom_pos (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < m * (1 - z) + z * (1 - m) := by
  rcases hm1.lt_or_eq with hm | rfl
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hm0 (by linarith)) (mul_pos hz0 (by linarith))
  · rw [one_mul, sub_self, mul_zero, add_zero]
    linarith

/-- Endorsement rises with the production probability at the observed world. -/
theorem endorse_le_endorse (hm0 : 0 ≤ m) (hm1 : m' ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (h : m ≤ m') : endorse m z ≤ endorse m' z := by
  unfold endorse
  rw [div_le_div_iff₀ (endorse_denom_pos hm0 (h.trans hm1) hz0 hz1)
    (endorse_denom_pos (hm0.trans h) hm1 hz0 hz1)]
  nlinarith [mul_nonneg (mul_nonneg hz0.le (sub_nonneg.2 hz1.le)) (sub_nonneg.2 h)]

/-- Endorsement falls with the expected production probability. -/
theorem endorse_antitone (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hz0 : 0 < z) (hz1 : z' < 1)
    (h : z ≤ z') : endorse m z' ≤ endorse m z := by
  unfold endorse
  rw [div_le_div_iff₀ (endorse_denom_pos hm0 hm1 (hz0.trans_le h) hz1)
    (endorse_denom_pos hm0 hm1 hz0 (h.trans_lt hz1))]
  nlinarith [mul_nonneg (mul_nonneg hm0 (sub_nonneg.2 hm1)) (sub_nonneg.2 h)]

/-- The sentence is endorsed more often than not exactly when it is produced at the observed
world more often than on average. -/
theorem one_half_lt_endorse_iff (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    1 / 2 < endorse m z ↔ z < m := by
  unfold endorse
  rw [div_lt_div_iff₀ two_pos (endorse_denom_pos hm0 hm1 hz0 hz1)]
  constructor <;> intro h <;> nlinarith

end Endorse

/-- The endorsement probability at a world of positive prior (§3.1): the production probability
at the world played against its expectation under the world prior. -/
theorem S2_real_amb (hα : 0 < α) {w : World n} (hμ : μ {w} ≠ 0)
    (hz0 : 0 < expectedProduction D n α μ ν) (hz1 : expectedProduction D n α μ ν < 1) :
    (S2 D n α μ ν w).real {.amb}
      = endorse (production D n α ν w) (expectedProduction D n α μ ν) := by
  have := isMarkovKernel_S1 D n α hα.le
  set m := production D n α ν w with hm
  set z := expectedProduction D n α μ ν with hz
  set a := μ.real {w} with ha
  have hZ : (S1 D n α ∘ₘ μ.prod ν).real {.null} = 1 - z := by
    have h := probReal_univ (μ := S1 D n α ∘ₘ μ.prod ν)
    rw [← Finset.coe_univ, ← sum_measureReal_singleton, sum_utt] at h
    have : (S1 D n α ∘ₘ μ.prod ν).real {.amb} = z := rfl
    linarith
  have hZamb : (S1 D n α ∘ₘ μ.prod ν) {.amb} ≠ 0 :=
    (measureReal_ne_zero_iff (measure_ne_top _ _)).mp hz0.ne'
  have hZnull : (S1 D n α ∘ₘ μ.prod ν) {.null} ≠ 0 := by
    rw [← measureReal_ne_zero_iff (measure_ne_top _ _), hZ]
    linarith
  have hnull : ∑ l, ν.real {l} * (S1 D n α (w, l)).real {.null} = 1 - m := by
    simp only [S1_real_null D n α hα.le, mul_sub, mul_one, Finset.sum_sub_distrib,
      sum_real_singleton_eq_one ν]
    rfl
  have hFamb : (Kernel.fst (L1 D n α μ ν) .amb).real {w} = a * m / z :=
    familyListener_fst_real_singleton _ α 1 μ ν hZamb w
  have hFnull : (Kernel.fst (L1 D n α μ ν) .null).real {w}
      = a * (∑ l, ν.real {l} * (S1 D n α (w, l)).real {.null})
        / (S1 D n α ∘ₘ μ.prod ν).real {.null} :=
    familyListener_fst_real_singleton _ α 1 μ ν hZnull w
  rw [hnull, hZ] at hFnull
  rw [S2, speaker_real_singleton (cost := 1) (L := Kernel.fst (L1 D n α μ ν)) (w := w)
    zero_le_one (λ _ => ENNReal.one_ne_top) (λ _ => prob_le_one)]
  simp only [ENNReal.rpow_one, Pi.one_apply, ENNReal.toReal_one, mul_one, ← measureReal_def]
  rw [sum_utt, hFamb, hFnull, endorse]
  have ha0 : 0 < a := ENNReal.toReal_pos hμ (measure_ne_top _ _)
  have hm0 : 0 ≤ m := production_nonneg D n α ν w
  have hm1 : m ≤ 1 := production_le_one D n α ν w
  have hden := endorse_denom_pos hm0 hm1 hz0 hz1
  have hz0' : z ≠ 0 := hz0.ne'
  have h1z : 1 - z ≠ 0 := (sub_pos.2 hz1).ne'
  have hAB : 0 < a * m / z + a * (1 - m) / (1 - z) := by
    rcases hm0.lt_or_eq with hm | hm
    · exact add_pos_of_pos_of_nonneg (div_pos (mul_pos ha0 hm) hz0)
        (div_nonneg (mul_nonneg ha0.le (sub_nonneg.2 hm1)) (sub_pos.2 hz1).le)
    · rw [← hm, mul_zero, zero_div, zero_add, sub_zero, mul_one]
      exact div_pos ha0 (sub_pos.2 hz1)
  rw [div_eq_div_iff hAB.ne' hden.ne']
  field_simp

/-- The sentence is endorsed more often than not exactly when it is produced at the observed
world more often than on average under the world prior (§5.1). -/
theorem one_half_lt_S2_real_amb_iff (hα : 0 < α) {w : World n} (hμ : μ {w} ≠ 0)
    (hz0 : 0 < expectedProduction D n α μ ν) (hz1 : expectedProduction D n α μ ν < 1) :
    1 / 2 < (S2 D n α μ ν w).real {.amb} ↔ expectedProduction D n α μ ν < production D n α ν w := by
  rw [S2_real_amb D n α μ ν hα hμ hz0 hz1,
    one_half_lt_endorse_iff (production_nonneg D n α ν w) (production_le_one D n α ν w) hz0 hz1]

end Endorsement

/-! ### The every-not model (§3) -/

section EveryNot

variable (α : ℝ) {n : ℕ}

private theorem zero_ne_last (hn : 0 < n) : (0 : World n) ≠ Fin.last n := λ h =>
  hn.ne (by simpa [Fin.ext_iff] using h)

/-- The sentence *every horse didn't jump* is true at the no-success world on both
interpretations. -/
theorem zero_mem_ext_every (hn : 0 < n) (i : Scope) : (0 : World n) ∈ ext every n i .amb := by
  cases i
  · exact mem_ext_every_surface.mpr rfl
  · exact mem_ext_every_inverse.mpr (zero_ne_last hn)

theorem ext_every_amb_card_pos (hn : 0 < n) (i : Scope) : 0 < (ext every n i .amb).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_ext_every hn i⟩

/-- Under the question *all?* the sentence *every horse didn't jump* fully resolves the question
in the negative on either interpretation: its projected literal listener is certain of every
world short of total success. -/
theorem projListener_L0_every_all (hn : 0 < n) (i : Scope) (w : World n) :
    projListener (project n) (L0 every n i) .all .amb {w} = if w = Fin.last n then 0 else 1 := by
  rw [projListener_L0_apply]
  have hcell : ∀ w', w' ∈ cell n .all w ↔ (w' = Fin.last n ↔ w = Fin.last n) := λ _ => mem_cell_all
  have hext : ∀ w', w' ∈ ext every n i .amb → w' ≠ Fin.last n := λ w' h => by
    cases i
    · exact (mem_ext_every_surface.mp h) ▸ zero_ne_last hn
    · exact mem_ext_every_inverse.mp h
  split_ifs with hw
  · rw [uniformOn_eq_zero_iff (Finset.finite_toSet _), Set.eq_empty_iff_forall_notMem]
    rintro w' ⟨h1, h2⟩
    exact hext w' (Finset.mem_coe.mp h1) (((hcell w').mp (Finset.mem_coe.mp h2)).mpr hw)
  · exact uniformOn_eq_one_of (Finset.finite_toSet _)
      ⟨0, Finset.mem_coe.mpr (zero_mem_ext_every hn i)⟩ λ w' h =>
      Finset.mem_coe.mpr ((hcell w').mpr (iff_of_false (hext w' (Finset.mem_coe.mp h)) hw))

/-- Under the question *all?* the two scope interpretations of *every horse didn't jump* produce
alike at every world: the sentence answers the question in the negative on either reading
(§3.2, §5.1). -/
theorem S1_all_scope (hn : 0 < n) (w : World n) :
    S1 every n α (w, (.surface, .all)) = S1 every n α (w, (.inverse, .all)) := by
  rw [S1_apply, S1_apply, speaker, speaker]
  have key : ∀ u, projListener (project n) (L0 every n .surface) .all u {w}
      = projListener (project n) (L0 every n .inverse) .all u {w} := by
    intro u
    cases u
    · rw [projListener_L0_apply, projListener_L0_apply]
      rfl
    · rw [projListener_L0_every_all hn, projListener_L0_every_all hn]
  exact Measure.ext_of_singleton λ u => by simp only [Kernel.ofWeights_apply_singleton, key]

theorem share_all_scope (hn : 0 < n) (w : World n) :
    share every n α (.surface, .all) w = share every n α (.inverse, .all) w := by
  simp only [share, S1_all_scope α hn w]

private theorem dirac_real_singleton (a q : QUD) :
    (Measure.dirac a).real {q} = if q = a then 1 else 0 := by
  rcases eq_or_ne q a with rfl | h
  · rw [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_singleton q), ENNReal.toReal_one,
      if_pos rfl]
  · rw [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton q),
      Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr (Ne.symm h)), ENNReal.toReal_zero,
      if_neg h]

variable (ρ : Measure Scope) [IsProbabilityMeasure ρ]

/-- With the question settled as *all?*, the production of the sentence at a world does not
depend on the scope prior. -/
theorem production_all (hn : 0 < n) (w : World n) :
    production every n α (ρ.prod (Measure.dirac .all)) w = share every n α (.surface, .all) w := by
  rw [production, Fintype.sum_prod_type]
  simp only [Measure.prod_real_singleton, dirac_real_singleton, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hscope : ∀ f : Scope → ℝ, ∑ i, f i = f .surface + f .inverse := λ f =>
    Fintype.sum_eq_add Scope.surface Scope.inverse (by decide) (λ i h => by cases i <;> simp at h)
  have hsum := sum_real_singleton_eq_one ρ
  rw [hscope] at hsum
  rw [hscope, ← share_all_scope α hn w, ← add_mul, hsum, one_mul]

theorem expectedProduction_all (hn : 0 < n) (μ : Measure (World n)) [IsProbabilityMeasure μ] :
    expectedProduction every n α μ (ρ.prod (Measure.dirac .all))
      = ∑ w, μ.real {w} * share every n α (.surface, .all) w := by
  rw [expectedProduction_eq_sum]
  simp only [production_all α ρ hn]

/-- With the question settled as *all?*, endorsement does not depend on the scope prior: the
scope prior matters only through questions the two interpretations answer differently (§3.2,
Figure 3). -/
theorem S2_real_amb_all (hα : 0 < α) (hn : 0 < n) (μ : Measure (World n)) [IsProbabilityMeasure μ]
    (ρ' : Measure Scope) [IsProbabilityMeasure ρ'] {w : World n} (hμ : μ {w} ≠ 0)
    (hz0 : 0 < expectedProduction every n α μ (ρ.prod (Measure.dirac .all)))
    (hz1 : expectedProduction every n α μ (ρ.prod (Measure.dirac .all)) < 1) :
    (S2 every n α μ (ρ.prod (Measure.dirac .all)) w).real {.amb}
      = (S2 every n α μ (ρ'.prod (Measure.dirac .all)) w).real {.amb} := by
  have hz0' := hz0
  have hz1' := hz1
  rw [expectedProduction_all α ρ hn μ, ← expectedProduction_all α ρ' hn μ] at hz0' hz1'
  rw [S2_real_amb _ _ _ _ _ hα hμ hz0 hz1, S2_real_amb _ _ _ _ _ hα hμ hz0' hz1',
    production_all α ρ hn w, production_all α ρ' hn w, expectedProduction_all α ρ hn μ,
    expectedProduction_all α ρ' hn μ]

/-! #### Two horses (§3.2) -/

private theorem ext_every_two (l : Scope × QUD) : 0 < (ext every 2 l.1 .amb).card :=
  ext_every_amb_card_pos two_pos l.1

/-- At the not-all world of the two-horse scenario, the question *all?* maximizes the production of
the sentence under either interpretation: the sentence answers it fully on either reading
(§3.2, Figure 2). -/
theorem share_le_share_all (hα : 0 < α) (i : Scope) (q : QUD) :
    share every 2 α (i, q) 1 ≤ share every 2 α (i, .all) 1 :=
  (share_le_share_iff every 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by revert i q; decide)

/-- At the not-all world, the question *none?* minimizes the production of the sentence under
either interpretation (§3.2, Figure 2). -/
theorem share_none_le_share (hα : 0 < α) (i : Scope) (q : QUD) :
    share every 2 α (i, .none) 1 ≤ share every 2 α (i, q) 1 :=
  (share_le_share_iff every 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by revert i q; decide)

/-- On the surface interpretation the sentence is false at the not-all world, so *how many?* has
it produced less often than *all?*, under which it is nonetheless a full answer. -/
theorem share_howMany_lt_share_all (hα : 0 < α) :
    share every 2 α (.surface, .howMany) 1 < share every 2 α (.surface, .all) 1 :=
  (share_lt_share_iff every 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by decide)

/-- On the inverse interpretation, *none?* has the sentence produced less often than
*how many?*: the sentence, *not all jumped*, leaves *none?* open. -/
theorem share_none_lt_share_howMany (hα : 0 < α) :
    share every 2 α (.inverse, .none) 1 < share every 2 α (.inverse, .howMany) 1 :=
  (share_lt_share_iff every 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by decide)

/-- Production of the sentence falls with the number of jumpers, under every interpretation and
question. -/
theorem share_antitone (hα : 0 < α) (l : Scope × QUD) :
    share every 2 α l 1 ≤ share every 2 α l 0 ∧ share every 2 α l 2 ≤ share every 2 α l 1 :=
  ⟨(share_le_share_iff every 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by revert l; decide),
    (share_le_share_iff every 2 α hα (ext_every_two _) (ext_every_two _)).mpr (by revert l; decide)⟩

theorem production_antitone (hα : 0 < α) (ν : Measure (Scope × QUD)) :
    production every 2 α ν 1 ≤ production every 2 α ν 0 ∧
      production every 2 α ν 2 ≤ production every 2 α ν 1 :=
  ⟨Finset.sum_le_sum λ l _ =>
      mul_le_mul_of_nonneg_left (share_antitone α hα l).1 measureReal_nonneg,
    Finset.sum_le_sum λ l _ =>
      mul_le_mul_of_nonneg_left (share_antitone α hα l).2 measureReal_nonneg⟩

variable (ν : Measure (Scope × QUD)) [IsProbabilityMeasure ν]

/-- Raising the success base rate of the binomial world prior raises endorsement at every world
(§3.2, Figure 2): the more success is expected, the more the sentence, on either reading, rules
out. -/
theorem S2_real_amb_mono_baseRate (hα : 0 < α) {p p' : I} (hp : 0 < (p : ℝ))
    (hpp' : (p : ℝ) ≤ p') (hp' : (p' : ℝ) < 1) (w : World 2) :
    (S2 every 2 α Bin(World 2, 2, p) ν w).real {.amb}
      ≤ (S2 every 2 α Bin(World 2, 2, p') ν w).real {.amb} := by
  have hpos : ∀ (q : I), 0 < (q : ℝ) → (q : ℝ) < 1 → ∀ w : World 2, Bin(World 2, 2, q) {w} ≠ 0 :=
    λ q hq hq1 w => (measureReal_ne_zero_iff (measure_ne_top _ _)).mp (by
      rw [map_cast_binomial_fin_real_singleton]
      exact (mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos w.is_le)) (pow_pos hq _))
        (pow_pos (sub_pos.2 hq1) _)).ne')
  have hp1 : (p : ℝ) < 1 := hpp'.trans_lt hp'
  have hp'0 : 0 < (p' : ℝ) := hp.trans_le hpp'
  have hz0 : ∀ (q : I), 0 < (q : ℝ) → (q : ℝ) < 1 →
      0 < expectedProduction every 2 α Bin(World 2, 2, q) ν := λ q hq hq1 =>
    expectedProduction_pos _ _ _ _ _ hα.le (hpos q hq hq1 0) λ l => zero_mem_ext_every two_pos l.1
  rw [S2_real_amb _ _ _ _ _ hα (hpos p hp hp1 w) (hz0 p hp hp1)
      (expectedProduction_lt_one _ _ _ _ _ hα.le),
    S2_real_amb _ _ _ _ _ hα (hpos p' hp'0 hp' w) (hz0 p' hp'0 hp')
      (expectedProduction_lt_one _ _ _ _ _ hα.le)]
  refine endorse_antitone (production_nonneg _ _ _ _ _) (production_le_one _ _ _ _ _)
    (hz0 p' hp'0 hp') (expectedProduction_lt_one _ _ _ _ _ hα.le) ?_
  rw [expectedProduction_eq_sum, expectedProduction_eq_sum, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [map_cast_binomial_fin_real_singleton, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one, Nat.cast_ofNat,
    pow_zero, Nat.sub_zero, Nat.sub_self, Nat.reduceSub, one_mul, mul_one, pow_one]
  obtain ⟨h10, h21⟩ := production_antitone α hα ν
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hpp') (by linarith : (0 : ℝ) ≤ 2 - p - p'))
      (sub_nonneg.2 h10),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hpp') (by linarith : (0 : ℝ) ≤ p + p'))
      (sub_nonneg.2 h21)]

end EveryNot

/-! ### The two-not model (§4) -/

section TwoNot

variable (α : ℝ)

/-- With four horses, the inverse reading of *two horses didn't jump* on the exact reading of the
numeral is true wherever the number of jumpers is not two ((6), Figure 5). -/
theorem ext_twoExact_inverse : ext twoExact 4 .inverse .amb = {0, 1, 3, 4} := by decide

/-- With four horses and two jumpers, the surface interpretation of the sentence is produced at
least as often on the exact reading of the numeral as on the at-least reading, whatever the
question: the exact reading makes the sentence true at that world alone (§4.2.2, Figure 7). -/
theorem share_twoAtLeast_le_share_twoExact (hα : 0 < α) (q : QUD) :
    share twoAtLeast 4 α (.surface, q) 2 ≤ share twoExact 4 α (.surface, q) 2 :=
  (share_le_share_iff twoAtLeast 4 α hα
    (show 0 < (ext twoAtLeast 4 .surface .amb).card by decide)
    (show 0 < (ext twoExact 4 .surface .amb).card by decide)).mpr (by revert q; decide)

/-- The advantage of the exact reading is strict under every question but *all?*, which the
surface interpretation answers fully on either reading. -/
theorem share_twoAtLeast_lt_share_twoExact (hα : 0 < α) {q : QUD} (hq : q ≠ .all) :
    share twoAtLeast 4 α (.surface, q) 2 < share twoExact 4 α (.surface, q) 2 :=
  (share_lt_share_iff twoAtLeast 4 α hα
    (show 0 < (ext twoAtLeast 4 .surface .amb).card by decide)
    (show 0 < (ext twoExact 4 .surface .amb).card by decide)).mpr (by revert q hq; decide)

/-- Under the inverse interpretation and the question *all?* the at-least reading is produced
more often at that world: *not exactly two jumped* is compatible with all four having jumped and
so leaves *all?* open, while *not at least two jumped* settles it. This is why the paper's 2-of-4
fit needs a low prior on inverse scope (§4.2.2, Figure 7). -/
theorem share_twoExact_lt_share_twoAtLeast (hα : 0 < α) :
    share twoExact 4 α (.inverse, .all) 2 < share twoAtLeast 4 α (.inverse, .all) 2 :=
  (share_lt_share_iff twoExact 4 α hα (by decide) (by decide)).mpr (by decide)

end TwoNot

end ScontrasPearl2021
