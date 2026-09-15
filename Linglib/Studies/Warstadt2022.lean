import Linglib.Pragmatics.RSA.QUD
import Linglib.Data.Examples.Warstadt2022

/-!
# Warstadt (2022): Presupposition Triggering Reflects Pragmatic Reasoning About Utterance Utility

This file formalizes [warstadt-2022]'s account of soft presupposition triggers as a listener's
inference about the common ground the speaker assumed. The model is
[qing-goodman-lassiter-2016]'s: the literal listener within a context set answers the question
under discussion (`L0`), the speaker best-responds to it and never says what is false at the
world (`speaker`), and the pragmatic listener inverts the speaker jointly over worlds and
context sets, weighting a world within a context set by its prior and every context set
equally (`listener`). [abusch-2002]'s genus-species presupposition follows: with the question
whether Tom needs a visa, *Tom doesn't have a green card* makes the listener favour the world
in which Tom is a non-US citizen over the one in which he is a US citizen, at every rationality
(`needVisa_nonUS_lt`), because within a context set that already settles that Tom is not a US
citizen the utterance answers the question while at the US-citizen world it never does better
than its competitors. Under the question whether Tom gets a free drink the utterance is an
exhaustive answer in every context set (`freeDrink_exhaustive`), so no context set can make it
more useful than another; the model still favours the non-US world (`freeDrink_nonUS_lt`),
though by a narrower margin. The family-genus-species example makes the strength of the
inference depend on the prior: at the non-athlete world in the universe, *not an Olympic
sprinter* is barely more informative than silence and less than *not a runner*
(`other_share_lt`), and it answers the question at the runner world only within context sets
that exclude both the athlete and the non-athlete world (`notSprinter_exhaustive_iff`).

## Implementation notes

Utterances carry no cost, and the honesty correction of the paper's footnote is the literal
listener's restriction to the utterance's extension, so a false utterance has weight zero in
the speaker's softmax. Shares are evaluated cell by cell from the tables of weights behind the
literal listener, certified by `decide`, and the listener comparisons are prior-weighted sums
over the eight context sets. The paper reports the free-drink posteriors of Figure 2 as nearly
equal; under the model as written the non-US world is favoured under both questions, and the
family-genus-species listener of Figure 3 is not formalized.

## References

* [warstadt-2022]
* [qing-goodman-lassiter-2016]
* [abusch-2002]
* [frank-goodman-2012]
* [stalnaker-1978]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace Warstadt2022

/-! ### The model (3) -/

section Model

variable {W U Q : Type} [DecidableEq W]

/-- The weights behind the literal listener: those of the context-set worlds that make the
utterance true and share the world's answer, over those that make it true; a false utterance
counts as `0` over `1`. -/
def l0 (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (C : Finset W) (q : Q) (u : U) (w : W) : ℕ × ℕ :=
  if w ∈ sem u then
    (∑ v ∈ (C.filter (· ∈ sem u)).filter (λ v => cell q v = cell q w), P v,
      ∑ v ∈ C.filter (· ∈ sem u), P v)
  else (0, 1)

theorem l0_fst_le_snd (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (C : Finset W) (q : Q) (u : U) (w : W) :
    (l0 P cell sem C q u w).1 ≤ (l0 P cell sem C q u w).2 := by
  unfold l0
  split_ifs
  · exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  · exact zero_le_one

section Prior

variable [MeasurableSpace W] [MeasurableSingletonClass W] [MeasurableSpace (Finset W)]
  [MeasurableSingletonClass (Finset W)]

/-- The prior over pairs of a world and a context set (3d): within a context set a world's
weight is its prior share of the set, and context sets are equally likely. -/
noncomputable def pairPrior (P : W → ℕ) : Measure (W × Finset W) :=
  Measure.count.withDensity λ p =>
    if p.1 ∈ p.2 then (P p.1 : ℝ≥0∞) / ∑ v ∈ p.2, (P v : ℝ≥0∞) else 0

theorem pairPrior_singleton (P : W → ℕ) (w : W) (C : Finset W) :
    pairPrior P {(w, C)}
      = if w ∈ C then (P w : ℝ≥0∞) / ∑ v ∈ C, (P v : ℝ≥0∞) else 0 := by
  rw [pairPrior, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    Measure.count_singleton, mul_one]

theorem pairPrior_singleton_le_one (P : W → ℕ) (w : W) (C : Finset W) :
    pairPrior P {(w, C)} ≤ 1 := by
  rw [pairPrior_singleton]
  split_ifs with h
  · exact ENNReal.div_le_of_le_mul (by
      rw [one_mul]
      exact Finset.single_le_sum (f := λ v => (P v : ℝ≥0∞)) (λ _ _ => zero_le) h)
  · exact zero_le_one

theorem pairPrior_real (P : W → ℕ) (w : W) (C : Finset W) :
    (pairPrior P).real {(w, C)}
      = if w ∈ C then (P w : ℝ) / ∑ v ∈ C, (P v : ℝ) else 0 := by
  rw [measureReal_def, pairPrior_singleton]
  split_ifs
  · rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_sum λ _ _ => ENNReal.natCast_ne_top _]
    simp only [ENNReal.toReal_natCast]
  · exact ENNReal.toReal_zero

variable [Fintype W]

instance (P : W → ℕ) : IsFiniteMeasure (pairPrior P) :=
  ⟨by
    rw [pairPrior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
      tsum_fintype]
    exact ENNReal.sum_lt_top.mpr λ p _ =>
      lt_of_le_of_lt (by rw [← pairPrior_singleton]; exact pairPrior_singleton_le_one P p.1 p.2)
        ENNReal.one_lt_top⟩

end Prior

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype U]
  [MeasurableSpace U] [MeasurableSingletonClass U]

/-- The literal listener within a context set (3a), gated by literal truth: the worlds of the
context set weighted by the prior, conditioned on the utterance and projected onto the cells of
the question, with no mass at a world where the utterance is false. -/
noncomputable def L0 (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W)
    (C : Finset W) (q : Q) : Kernel U W :=
  Kernel.ofFunOfCountable λ u =>
    (projListener cell (literalListener ((priorOfWeights P).restrict ↑C) λ u =>
      (sem u).indicator 1) q u).restrict (sem u)

variable (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W)
  [∀ u, DecidablePred (· ∈ sem u)] (C : Finset W) (q : Q) (u : U) (w : W)

theorem L0_apply [DiscreteMeasurableSpace W] :
    L0 P cell sem C q u {w}
      = ((l0 P cell sem C q u w).1 : ℝ≥0∞) / (l0 P cell sem C q u w).2 := by
  rw [L0, Kernel.ofFunOfCountable_apply, Measure.restrict_apply (measurableSet_singleton w)]
  by_cases h : w ∈ sem u
  · rw [Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr h),
      projListener_literalListener_restrict_apply_singleton]
    simp only [l0, ite_eq_left h, Nat.cast_sum]
  · rw [Set.singleton_inter_eq_empty.mpr h, measure_empty]
    simp [l0, ite_eq_right h]

theorem L0_le_one [DiscreteMeasurableSpace W] : L0 P cell sem C q u {w} ≤ 1 := by
  rw [L0_apply]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast l0_fst_le_snd P cell sem C q u w)

/-- The speaker within a context set (3b), with no cost. -/
noncomputable def speaker (α : ℝ) : Kernel W U := RSA.speaker α (λ _ => 1) (L0 P cell sem C q)

/-- The share of an utterance at a world within a context set, on reals. -/
noncomputable def share (α : ℝ) : ℝ := (speaker P cell sem C q α w).real {u}

variable {P cell sem C q u w}

theorem speaker_apply_singleton_ne_zero [DiscreteMeasurableSpace W] {α : ℝ} (hα : 0 < α)
    (h : w ∈ sem u) (hC : w ∈ C) (hP : P w ≠ 0) : speaker P cell sem C q α w {u} ≠ 0 :=
  RSA.speaker_apply_singleton_ne_zero hα.le (λ _ => one_ne_zero) (λ _ => ENNReal.one_ne_top)
    (L0_le_one P cell sem C q · w) (by
      rw [L0_apply, ne_eq, ENNReal.div_eq_zero_iff, not_or]
      refine ⟨?_, ENNReal.natCast_ne_top _⟩
      simp only [l0, ite_eq_left h, Nat.cast_eq_zero]
      exact Finset.sum_eq_zero_iff.not.mpr λ hz =>
        hP (hz w (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hC, h⟩, rfl⟩)))

variable [MeasurableSpace (Finset W)] [MeasurableSingletonClass (Finset W)]
  [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace (Finset W)]

/-- The pragmatic listener (3d): the Bayesian inverse of the speaker jointly over worlds and
context sets, given the question. -/
noncomputable def listener (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W) (q : Q)
    (α : ℝ) : Kernel U (W × Finset W) :=
  familyListener (λ C => L0 P cell sem C q) α (λ _ => 1) (pairPrior P)

/-- The pairs whose world is `w`. -/
def worldEvent (w : W) : Finset (W × Finset W) := Finset.univ.image λ C => (w, C)

/-- The listener's preference between two worlds, marginalizing the context set, is the
comparison of prior-weighted speaker shares summed over context sets. -/
theorem listener_worldEvent_lt_iff (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (q : Q) {α : ℝ} {u : U}
    (hu : (familySpeaker (λ C => L0 P cell sem C q) α (λ _ => 1) ∘ₘ pairPrior P) {u} ≠ 0)
    (w₁ w₂ : W) :
    (listener P cell sem q α u).real ↑(worldEvent w₁)
        < (listener P cell sem q α u).real ↑(worldEvent w₂)
      ↔ (∑ C, (pairPrior P).real {(w₁, C)} * share P cell sem C q u w₁ α)
        < ∑ C, (pairPrior P).real {(w₂, C)} * share P cell sem C q u w₂ α := by
  unfold listener worldEvent
  rw [familyListener_real_lt_iff _ _ _ hu,
    Finset.sum_image λ _ _ _ _ h => (Prod.mk.inj h).2,
    Finset.sum_image λ _ _ _ _ h => (Prod.mk.inj h).2]
  rfl

end Model

private theorem toReal_frac_rpow (n m : ℕ) (α : ℝ) :
    (((n : ℝ≥0∞) / m) ^ α).toReal = ((n : ℝ) / m) ^ α := by
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-! ### The green card scenario (Table 1) -/

/-- Tom is a US citizen, a green card holder, or a non-US citizen without a green card. -/
inductive World
  | usCitizen | gcHolder | nonUS
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass World := DiscreteMeasurableSpace.toMeasurableSingletonClass
instance : MeasurableSpace (Finset World) := ⊤
instance : DiscreteMeasurableSpace (Finset World) := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass (Finset World) :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Silence, *US citizen*, *not US citizen*, *green card*, *not green card*. -/
inductive Utterance
  | silence | us | notUS | gc | notGC
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass Utterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The truth conditions of Table 1: a negation is the complement. -/
def Utterance.sem : Utterance → Set World
  | .silence => Set.univ
  | .us => {w | w = .usCitizen}
  | .notUS => {w | w ≠ .usCitizen}
  | .gc => {w | w = .gcHolder}
  | .notGC => {w | w ≠ .gcHolder}

instance : ∀ u : Utterance, DecidablePred (· ∈ u.sem)
  | .silence, _ => inferInstanceAs (Decidable True)
  | .us, w => inferInstanceAs (Decidable (w = _))
  | .notUS, w => inferInstanceAs (Decidable (w ≠ _))
  | .gc, w => inferInstanceAs (Decidable (w = _))
  | .notGC, w => inferInstanceAs (Decidable (w ≠ _))

/-- Does Tom need a visa? Can Tom get a free drink? -/
inductive QUD
  | needVisa | freeDrink
  deriving DecidableEq, Repr

/-- The answer of a world to a question. -/
def QUD.answer : QUD → World → Bool
  | .needVisa, w => decide (w = .nonUS)
  | .freeDrink, w => decide (w = .gcHolder)

/-- The cell of a world: the worlds with the same answer. -/
def QUD.cell (q : QUD) (w : World) : Finset World := Finset.univ.filter (q.answer · = q.answer w)

/-- The context sets containing the non-US world, and those containing the US-citizen world. -/
def nonUSSets : List (Finset World) :=
  [{.nonUS}, {.usCitizen, .nonUS}, {.gcHolder, .nonUS}, {.usCitizen, .gcHolder, .nonUS}]

def usSets : List (Finset World) :=
  [{.usCitizen}, {.usCitizen, .gcHolder}, {.usCitizen, .nonUS}, {.usCitizen, .gcHolder, .nonUS}]

/-- The uniform world prior. -/
def uniform : World → ℕ := λ _ => 1

/-- *Not green card* is an exhaustive answer to the free-drink question in every context set:
its literal-listener weight at a world where it is true is the whole weight. -/
theorem freeDrink_exhaustive :
    ∀ (C : Finset World) (w : World), w ∈ C → w ∈ Utterance.notGC.sem →
      (l0 uniform QUD.cell Utterance.sem C .freeDrink .notGC w).1
        = (l0 uniform QUD.cell Utterance.sem C .freeDrink .notGC w).2 := by
  decide

/-- Under the visa question it is not: in the universe at the US-citizen world it leaves half
the answer open, while within the context set that Tom is not a US citizen it settles it. -/
theorem needVisa_not_exhaustive :
    l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .needVisa .notGC
        .usCitizen = (1, 2) ∧
      l0 uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} .needVisa .notGC .nonUS = (1, 1) := by
  decide

/-! #### Shares -/

private theorem sum_utterance {M : Type*} [AddCommMonoid M] (f : Utterance → M) :
    ∑ u, f u = f .silence + f .us + f .notUS + f .gc + f .notGC := by
  rw [show (Finset.univ : Finset Utterance) = {.silence, .us, .notUS, .gc, .notGC} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]

/-- The share of *not green card* at a cell, expanded over the utterances. -/
private theorem share_expand (C : Finset World) (q : QUD) (w : World) {α : ℝ} (hα : 0 < α)
    (tbl : Utterance → ℕ × ℕ)
    (htbl : ∀ u, l0 uniform QUD.cell Utterance.sem C q u w = tbl u) :
    share uniform QUD.cell Utterance.sem C q .notGC w α =
      (((tbl .notGC).1 : ℝ) / (tbl .notGC).2) ^ α /
        (((tbl .silence).1 / (tbl .silence).2) ^ α + ((tbl .us).1 / (tbl .us).2) ^ α
          + ((tbl .notUS).1 / (tbl .notUS).2) ^ α + ((tbl .gc).1 / (tbl .gc).2) ^ α
          + ((tbl .notGC).1 / (tbl .notGC).2) ^ α) := by
  rw [share, speaker, speaker_real_singleton hα.le (λ _ => ENNReal.one_ne_top)
    (L0_le_one uniform QUD.cell Utterance.sem C q · w), sum_utterance]
  simp only [L0_apply, htbl, toReal_frac_rpow, ENNReal.toReal_one, mul_one]

section Tables

/-- Weights at the non-US world within its singleton context set, both questions. -/
private def tblN1 : Utterance → ℕ × ℕ
  | .silence => (1, 1) | .us => (0, 1) | .notUS => (1, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem l0_N1 (q : QUD) : ∀ u, l0 uniform QUD.cell Utterance.sem {.nonUS} q u .nonUS
    = tblN1 u := by
  cases q <;> decide

/-- Weights at the non-US world within `{usCitizen, nonUS}`, visa question. -/
private def tblN2 : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (0, 1) | .notUS => (1, 1) | .gc => (0, 1) | .notGC => (1, 2)

private theorem l0_N2 : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa u
    .nonUS = tblN2 u := by
  decide

/-- Weights at the non-US world within `{gcHolder, nonUS}`, both questions. -/
private def tblN3 : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (0, 1) | .notUS => (1, 2) | .gc => (0, 1) | .notGC => (1, 1)

private theorem l0_N3 (q : QUD) : ∀ u, l0 uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} q u
    .nonUS = tblN3 u := by
  cases q <;> decide

/-- Weights at the non-US world in the universe, visa question. -/
private def tblN4 : Utterance → ℕ × ℕ
  | .silence => (1, 3) | .us => (0, 1) | .notUS => (1, 2) | .gc => (0, 1) | .notGC => (1, 2)

private theorem l0_N4 : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .needVisa u .nonUS = tblN4 u := by
  decide

/-- Weights at the US-citizen world within its singleton context set, both questions. -/
private def tblU1 : Utterance → ℕ × ℕ
  | .silence => (1, 1) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem l0_U1 (q : QUD) : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen} q u
    .usCitizen = tblU1 u := by
  cases q <;> decide

/-- Weights at the US-citizen world within `{usCitizen, gcHolder}`, visa question. -/
private def tblU2 : Utterance → ℕ × ℕ
  | .silence => (2, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem l0_U2 : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder} .needVisa
    u .usCitizen = tblU2 u := by
  decide

/-- Weights at the US-citizen world within `{usCitizen, nonUS}`, visa question. -/
private def tblU3 : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 2)

private theorem l0_U3 : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa u
    .usCitizen = tblU3 u := by
  decide

/-- Weights at the US-citizen world in the universe, visa question. -/
private def tblU4 : Utterance → ℕ × ℕ
  | .silence => (2, 3) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 2)

private theorem l0_U4 : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .needVisa u .usCitizen = tblU4 u := by
  decide

/-- Weights at the non-US world within `{usCitizen, nonUS}`, free-drink question. -/
private def tblN2' : Utterance → ℕ × ℕ
  | .silence => (2, 2) | .us => (0, 1) | .notUS => (1, 1) | .gc => (0, 1) | .notGC => (2, 2)

private theorem l0_N2' : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink
    u .nonUS = tblN2' u := by
  decide

/-- Weights at the non-US world in the universe, free-drink question. -/
private def tblN4' : Utterance → ℕ × ℕ
  | .silence => (2, 3) | .us => (0, 1) | .notUS => (1, 2) | .gc => (0, 1) | .notGC => (2, 2)

private theorem l0_N4' : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .freeDrink u .nonUS = tblN4' u := by
  decide

/-- Weights at the US-citizen world within `{usCitizen, gcHolder}`, free-drink question. -/
private def tblU2' : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem l0_U2' : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder} .freeDrink
    u .usCitizen = tblU2' u := by
  decide

/-- Weights at the US-citizen world within `{usCitizen, nonUS}`, free-drink question. -/
private def tblU3' : Utterance → ℕ × ℕ
  | .silence => (2, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (2, 2)

private theorem l0_U3' : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink u
    .usCitizen = tblU3' u := by
  decide

/-- Weights at the US-citizen world in the universe, free-drink question. -/
private def tblU4' : Utterance → ℕ × ℕ
  | .silence => (2, 3) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (2, 2)

private theorem l0_U4' : ∀ u, l0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .freeDrink u .usCitizen = tblU4' u := by
  decide

end Tables

section Cells

variable {α : ℝ} (hα : 0 < α)
include hα

private theorem share_N1 (q : QUD) : share uniform QUD.cell Utterance.sem {.nonUS} q .notGC
    .nonUS α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblN1 (l0_N1 q)]
  dsimp only [tblN1]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_N2 : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa
    .notGC .nonUS α = (1 / 2 : ℝ) ^ α / (1 + 2 * (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN2 l0_N2]
  dsimp only [tblN2]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_N3 (q : QUD) : share uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} q
    .notGC .nonUS α = 1 / (1 + 2 * (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN3 (l0_N3 q)]
  dsimp only [tblN3]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_N4 : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .needVisa .notGC .nonUS α
      = (1 / 2 : ℝ) ^ α / (2 * (1 / 2 : ℝ) ^ α + (1 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN4 l0_N4]
  dsimp only [tblN4]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U1 (q : QUD) : share uniform QUD.cell Utterance.sem {.usCitizen} q .notGC
    .usCitizen α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblU1 (l0_U1 q)]
  dsimp only [tblU1]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_U2 : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder} .needVisa
    .notGC .usCitizen α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblU2 l0_U2]
  dsimp only [tblU2]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_U3 : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa
    .notGC .usCitizen α = (1 / 2 : ℝ) ^ α / (1 + 2 * (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU3 l0_U3]
  dsimp only [tblU3]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U4 : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .needVisa .notGC .usCitizen α
      = (1 / 2 : ℝ) ^ α / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU4 l0_U4]
  dsimp only [tblU4]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_N2' : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink
    .notGC .nonUS α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblN2' l0_N2']
  dsimp only [tblN2']
  norm_num [Real.zero_rpow hα.ne']

private theorem share_N4' : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .freeDrink .notGC .nonUS α = 1 / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN4' l0_N4']
  dsimp only [tblN4']
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U2' : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder}
    .freeDrink .notGC .usCitizen α = 1 / (2 + (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU2' l0_U2']
  dsimp only [tblU2']
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U3' : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink
    .notGC .usCitizen α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblU3' l0_U3']
  dsimp only [tblU3']
  norm_num [Real.zero_rpow hα.ne']

private theorem share_U4' : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .freeDrink .notGC .usCitizen α = 1 / (2 + (2 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU4' l0_U4']
  dsimp only [tblU4']
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

end Cells

/-! #### The listener over worlds -/

/-- The joint listener of the green card scenario. -/
noncomputable def gcListener (q : QUD) (α : ℝ) : Kernel Utterance (World × Finset World) :=
  listener uniform QUD.cell Utterance.sem q α

private theorem sum_ctx {M : Type*} [AddCommMonoid M] (f : Finset World → M) :
    ∑ C, f C = f ∅ + f {.usCitizen} + f {.gcHolder} + f {.nonUS} + f {.usCitizen, .gcHolder}
      + f {.usCitizen, .nonUS} + f {.gcHolder, .nonUS} + f {.usCitizen, .gcHolder, .nonUS} := by
  rw [show (Finset.univ : Finset (Finset World)) = {∅, {.usCitizen}, {.gcHolder}, {.nonUS},
      {.usCitizen, .gcHolder}, {.usCitizen, .nonUS}, {.gcHolder, .nonUS},
      {.usCitizen, .gcHolder, .nonUS}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]

private theorem pairPrior_uniform_real (w : World) (C : Finset World) :
    (pairPrior uniform).real {(w, C)} = if w ∈ C then 1 / (C.card : ℝ) else 0 := by
  rw [pairPrior_real]
  simp [uniform]

private theorem card_two {a b : World} (h : a ≠ b) : ({a, b} : Finset World).card = 2 := by
  rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr h), Finset.card_singleton]

private theorem card_three : ({.usCitizen, .gcHolder, .nonUS} : Finset World).card = 3 := by
  decide

private theorem comp_ne_zero (q : QUD) {α : ℝ} (hα : 0 < α) :
    (familySpeaker (λ C => L0 uniform QUD.cell Utterance.sem C q) α (λ _ => 1)
      ∘ₘ pairPrior uniform) {.notGC} ≠ 0 :=
  comp_familySpeaker_ne_zero (w := .nonUS) (l := {.nonUS})
    (by rw [pairPrior_singleton, ite_eq_left (by decide)]; simp [uniform])
    (speaker_apply_singleton_ne_zero hα (by decide) (by decide) one_ne_zero)

private theorem half_rpow_lt_one {α : ℝ} (hα : 0 < α) : (1 / 2 : ℝ) ^ α < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hα

/-- With the question whether Tom needs a visa, *not green card* makes the listener favour the
non-US world over the US-citizen world at every rationality: within the context set that Tom is
not a US citizen the utterance answers the question, whereas at the US-citizen world *US
citizen* always answers it at least as well (Figure 1). -/
theorem needVisa_nonUS_lt {α : ℝ} (hα : 0 < α) :
    (gcListener .needVisa α .notGC).real ↑(worldEvent World.usCitizen)
      < (gcListener .needVisa α .notGC).real ↑(worldEvent World.nonUS) := by
  rw [gcListener, listener_worldEvent_lt_iff _ _ _ _ (comp_ne_zero _ hα), sum_ctx, sum_ctx]
  simp (config := { decide := true }) only [pairPrior_uniform_real, ite_true, ite_false]
  rw [card_two (by decide), card_two (by decide), card_two (by decide), card_three]
  norm_num
  rw [share_N1 hα, share_N2 hα, share_N3 hα, share_N4 hα, share_U1 hα, share_U2 hα,
    share_U3 hα, share_U4 hα]
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hy0 : (0 : ℝ) < (1 / 3 : ℝ) ^ α := by positivity
  have hyz : (1 / 3 : ℝ) ^ α < (2 / 3 : ℝ) ^ α :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hα
  have h1 : (1 : ℝ) / 3 < 1 / (1 + 2 * (1 / 2 : ℝ) ^ α) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h2 : (1 / 2 : ℝ) ^ α / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α)
      < (1 / 2 : ℝ) ^ α / (2 * (1 / 2 : ℝ) ^ α + (1 / 3 : ℝ) ^ α) :=
    div_lt_div_of_pos_left hx0 (by positivity) (by linarith)
  linarith

/-- With the question whether Tom gets a free drink, *not green card* is an exhaustive answer
in every context set, yet the listener still favours the non-US world: at the US-citizen world
*US citizen* is an equally good answer, so the utterance's share there never exceeds a half
(Figure 2 reports the two posteriors as nearly equal). -/
theorem freeDrink_nonUS_lt {α : ℝ} (hα : 0 < α) :
    (gcListener .freeDrink α .notGC).real ↑(worldEvent World.usCitizen)
      < (gcListener .freeDrink α .notGC).real ↑(worldEvent World.nonUS) := by
  rw [gcListener, listener_worldEvent_lt_iff _ _ _ _ (comp_ne_zero _ hα), sum_ctx, sum_ctx]
  simp (config := { decide := true }) only [pairPrior_uniform_real, ite_true, ite_false]
  rw [card_two (by decide), card_two (by decide), card_two (by decide), card_three]
  norm_num
  rw [share_N1 hα, share_N2' hα, share_N3 hα, share_N4' hα, share_U1 hα, share_U2' hα,
    share_U3' hα, share_U4' hα]
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hz0 : (0 : ℝ) < (2 / 3 : ℝ) ^ α := by positivity
  have h1 : (1 : ℝ) / (2 + (1 / 2 : ℝ) ^ α) < 1 / (1 + 2 * (1 / 2 : ℝ) ^ α) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h2 : (1 : ℝ) / (2 + (2 / 3 : ℝ) ^ α)
      < 1 / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-! ### The family-genus-species scenario (Table 2) -/

/-- Tom is an Olympic sprinter, another runner, another athlete, or none of these. -/
inductive Hobby
  | sprinter | runner | athlete | other
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Hobby := ⊤
instance : DiscreteMeasurableSpace Hobby := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass Hobby := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The three predicates, affirmed or negated, and silence. -/
inductive HobbyUtterance
  | silence | sprinter | notSprinter | runner | notRunner | athlete | notAthlete
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace HobbyUtterance := ⊤
instance : DiscreteMeasurableSpace HobbyUtterance := ⟨λ _ => trivial⟩
instance : MeasurableSingletonClass HobbyUtterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The truth conditions of Table 2, respecting the hierarchy of the predicates. -/
def HobbyUtterance.sem : HobbyUtterance → Set Hobby
  | .silence => Set.univ
  | .sprinter => {w | w = .sprinter}
  | .notSprinter => {w | w ≠ .sprinter}
  | .runner => {w | w = .sprinter ∨ w = .runner}
  | .notRunner => {w | ¬ (w = .sprinter ∨ w = .runner)}
  | .athlete => {w | w ≠ .other}
  | .notAthlete => {w | w = .other}

instance : ∀ u : HobbyUtterance, DecidablePred (· ∈ u.sem)
  | .silence, _ => inferInstanceAs (Decidable True)
  | .sprinter, w => inferInstanceAs (Decidable (w = _))
  | .notSprinter, w => inferInstanceAs (Decidable (w ≠ _))
  | .runner, w => inferInstanceAs (Decidable (w = _ ∨ w = _))
  | .notRunner, w => inferInstanceAs (Decidable (¬ (w = _ ∨ w = _)))
  | .athlete, w => inferInstanceAs (Decidable (w ≠ _))
  | .notAthlete, w => inferInstanceAs (Decidable (w = _))

/-- The prior of Table 2, in percent. -/
def hobbyWeight : Hobby → ℕ
  | .sprinter => 1
  | .runner => 5
  | .athlete => 10
  | .other => 84

/-- The question which world it is: every cell is a singleton. -/
def which (_ : Unit) (w : Hobby) : Finset Hobby := {w}

/-- The universe of hobbies. -/
def hobbies : Finset Hobby := {.sprinter, .runner, .athlete, .other}

/-- *Not an Olympic sprinter* answers the question at the runner world exactly within context
sets that exclude the athlete and the non-athlete world: the accommodation the paper describes
is of a common ground in which Tom is a runner or a sprinter. -/
theorem notSprinter_exhaustive_iff :
    ∀ C : Finset Hobby, .runner ∈ C →
      ((l0 hobbyWeight which HobbyUtterance.sem C () .notSprinter .runner).1
          = (l0 hobbyWeight which HobbyUtterance.sem C () .notSprinter .runner).2
        ↔ .athlete ∉ C ∧ .other ∉ C) := by
  decide

/-- *Not a runner* answers the question at the athlete world exactly within context sets that
exclude the non-athlete world. -/
theorem notRunner_exhaustive_iff :
    ∀ C : Finset Hobby, .athlete ∈ C →
      ((l0 hobbyWeight which HobbyUtterance.sem C () .notRunner .athlete).1
          = (l0 hobbyWeight which HobbyUtterance.sem C () .notRunner .athlete).2
        ↔ .other ∉ C) := by
  decide

private theorem sum_hobbyUtterance {M : Type*} [AddCommMonoid M] (f : HobbyUtterance → M) :
    ∑ u, f u = f .silence + f .sprinter + f .notSprinter + f .runner + f .notRunner + f .athlete
      + f .notAthlete := by
  rw [show (Finset.univ : Finset HobbyUtterance) = {.silence, .sprinter, .notSprinter, .runner,
      .notRunner, .athlete, .notAthlete} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

/-- Weights at the non-athlete world in the universe. -/
private def tblO : HobbyUtterance → ℕ × ℕ
  | .silence => (84, 100) | .sprinter => (0, 1) | .notSprinter => (84, 99) | .runner => (0, 1)
  | .notRunner => (84, 94) | .athlete => (0, 1) | .notAthlete => (84, 84)

private theorem l0_O : ∀ u, l0 hobbyWeight which HobbyUtterance.sem hobbies () u .other
    = tblO u := by
  decide

/-- The share of an utterance at the non-athlete world in the universe, expanded. -/
private theorem share_other {α : ℝ} (hα : 0 < α) (u : HobbyUtterance) :
    share hobbyWeight which HobbyUtterance.sem hobbies () u .other α =
      (((tblO u).1 : ℝ) / (tblO u).2) ^ α /
        (((tblO .silence).1 / (tblO .silence).2) ^ α
          + ((tblO .sprinter).1 / (tblO .sprinter).2) ^ α
          + ((tblO .notSprinter).1 / (tblO .notSprinter).2) ^ α
          + ((tblO .runner).1 / (tblO .runner).2) ^ α
          + ((tblO .notRunner).1 / (tblO .notRunner).2) ^ α
          + ((tblO .athlete).1 / (tblO .athlete).2) ^ α
          + ((tblO .notAthlete).1 / (tblO .notAthlete).2) ^ α) := by
  rw [share, speaker, speaker_real_singleton hα.le (λ _ => ENNReal.one_ne_top)
    (L0_le_one hobbyWeight which HobbyUtterance.sem hobbies () · .other), sum_hobbyUtterance]
  simp only [L0_apply, l0_O, toReal_frac_rpow, ENNReal.toReal_one, mul_one]

/-- At the non-athlete world in the universe, *not an Olympic sprinter* is produced more often
than silence but less often than *not a runner*, which loses to *not an athlete*: Olympic
sprinters are rare, so denying that Tom is one says little (4). -/
theorem other_share_lt {α : ℝ} (hα : 0 < α) :
    share hobbyWeight which HobbyUtterance.sem hobbies () .silence .other α
        < share hobbyWeight which HobbyUtterance.sem hobbies () .notSprinter .other α ∧
      share hobbyWeight which HobbyUtterance.sem hobbies () .notSprinter .other α
        < share hobbyWeight which HobbyUtterance.sem hobbies () .notRunner .other α ∧
      share hobbyWeight which HobbyUtterance.sem hobbies () .notRunner .other α
        < share hobbyWeight which HobbyUtterance.sem hobbies () .notAthlete .other α := by
  simp only [share_other hα]
  dsimp only [tblO]
  refine ⟨?_, ?_, ?_⟩ <;>
    exact div_lt_div_of_pos_right (Real.rpow_lt_rpow (by norm_num) (by norm_num) hα)
      (by positivity)

end Warstadt2022
