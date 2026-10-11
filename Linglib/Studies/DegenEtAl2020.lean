module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Reference.Distinguishing
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Degen, Hawkins, Graf, Kreiss and Goodman (2020): When Redundancy Is Useful: A Bayesian Approach to "Overinformative" Referring Expressions

Degen and colleagues' rational speech act model with a continuous semantics. A referring
expression holds of an object to a degree in the unit interval. An adjective of semantic value `x`
holds to degree `x` of the objects in its Boolean extension and to degree `1 − x` of the others,
and an expression of two adjectives multiplies their degrees. The literal listener normalizes the
degrees over the objects of the context, and the speaker chooses an expression in proportion to
the exponential of its utility, the log of the listener's probability of the intended object less
the cost of the expression. An adjective that the Boolean semantics makes redundant then adds
information, and adds more the less noisy it is.

## Main statements

* `overmodification_odds_lt_iff`: among the three pins of the paper's first figure the speaker
  adds a redundant colour to a sufficient size more readily than a redundant size to a sufficient
  colour exactly when size is the noisier of the two, at every positive rationality and when the
  two redundant adjectives cost the same.
* `color_overmodification_iff`, `size_overmodification_iff`: without cost the redundant
  expression is preferred to the sufficient one exactly when the semantic value of the redundant
  adjective exceeds one half.
* `boolean_no_preference`: with Boolean values the redundant adjective adds nothing.

## Implementation notes

* `S1` is `RSA.speaker`, whose rationality `α` scales the whole utility. The paper weights
  informativeness and cost separately and notes that the two parameterizations are equivalent.
* The listener and the speaker take any graded meaning, so the typicality semantics of the
  paper's third experiment is the same model at another meaning, and `S1_real_lt_iff` is its
  preference for the term of greater utility.

## TODO

* Tables 2 and 3 do not follow from Equation (1) at the stated values x_size = .8 and
  x_colour = .99. Their values match a listener proportional to the exponential of the meaning.
  The theorems follow the equations.
* The regression coefficients and the fitted parameters of the three experiments are not encoded.

## References

* [degen-etal-2020]
* [frank-goodman-2012]
-/

@[expose] public section

namespace DegenEtAl2020

open MeasureTheory ProbabilityTheory RSA

/-! ### Continuous semantics -/

/-- An adjective of semantic value `x` holds to degree `x` of an object in its Boolean extension
and to degree `1 − x` of any other, (6). -/
def noisy (x : ℝ) (p : Prop) [Decidable p] : ℝ := if p then x else 1 - x

theorem noisy_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (p : Prop) [Decidable p] :
    0 ≤ noisy x p := by
  unfold noisy; split_ifs <;> linarith

/-! ### Listener and speaker -/

section Model

variable {E U : Type*} [Fintype E]

private theorem sum_pos_of_pos {m : U → E → ℝ} {u : U} {o : E} (hm : ∀ v o', 0 ≤ m v o')
    (h : 0 < m u o) : 0 < ∑ o', m u o' :=
  Finset.sum_pos' (fun o' _ ↦ hm u o') ⟨o, Finset.mem_univ o, h⟩

variable [Nonempty E] [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype U]
  [MeasurableSpace U] [MeasurableSingletonClass U]

/-- The literal listener (1) normalizes the meaning of an expression over the objects at a
uniform prior. -/
noncomputable def L0 (m : U → E → ℝ) : Kernel U E :=
  Kernel.ofDensity (uniformOn Set.univ) fun u o ↦ ENNReal.ofReal (m u o)

instance (m : U → E → ℝ) : IsFiniteKernel (L0 m) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

/-- The speaker of (3) and (4) at rationality `α` chooses an expression in proportion to the
exponential of `α` times its utility, the log of the listener's probability of the object less
the cost `C`. -/
noncomputable def S1 (α : ℝ) (C : U → ℝ) (m : U → E → ℝ) : Kernel E U :=
  speaker α C (L0 m) Measure.dirac

instance (α : ℝ) (C : U → ℝ) (m : U → E → ℝ) : IsFiniteKernel (S1 α C m) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

variable {m : U → E → ℝ} {α : ℝ} {C : U → ℝ} {u u' : U} {o : E}

/-- The listener's probability of an object is the share of its degree in the row. -/
theorem L0_apply (hm : ∀ o', 0 ≤ m u o') (hpos : 0 < ∑ o', m u o') (o : E) :
    L0 m u {o} = ENNReal.ofReal (m u o / ∑ o', m u o') :=
  Kernel.ofDensity_uniformOn_ofReal_apply_singleton _ u o hm hpos

theorem L0_real_singleton (hm : ∀ o', 0 ≤ m u o') (hpos : 0 < ∑ o', m u o') (o : E) :
    (L0 m u).real {o} = m u o / ∑ o', m u o' := by
  rw [measureReal_def, L0_apply hm hpos, ENNReal.toReal_ofReal (div_nonneg (hm o) hpos.le)]

private theorem L0_ne_zero (hm : ∀ v o', 0 ≤ m v o') (h : 0 < m u o) : L0 m u {o} ≠ 0 := by
  rw [L0_apply (hm u) (sum_pos_of_pos hm h)]
  exact (ENNReal.ofReal_pos.2 (div_pos h (sum_pos_of_pos hm h))).ne'

/-- The odds of one expression against another for an object are the ratio of the listener's
probabilities of the object to the power `α`, discounted by the difference in cost. -/
theorem S1_real_div (hα : 0 ≤ α) (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o) (hu' : 0 < m u' o) :
    (S1 α C m o).real {u'} / (S1 α C m o).real {u} =
      ((m u' o / ∑ o', m u' o') / (m u o / ∑ o', m u o')) ^ α *
        Real.exp (-(α * (C u' - C u))) := by
  rw [S1, speaker_dirac_real_singleton_div hα (L0_ne_zero hm hu), ← measureReal_def,
    ← measureReal_def, L0_real_singleton (hm u) (sum_pos_of_pos hm hu),
    L0_real_singleton (hm u') (sum_pos_of_pos hm hu')]

/-- The speaker prefers the expression of greater utility. -/
theorem S1_real_lt_iff (hα : 0 < α) (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o)
    (hu' : 0 < m u' o) :
    (S1 α C m o).real {u} < (S1 α C m o).real {u'} ↔
      Real.log (m u o / ∑ o', m u o') - C u < Real.log (m u' o / ∑ o', m u' o') - C u' := by
  have hr := div_pos hu (sum_pos_of_pos hm hu)
  have hr' := div_pos hu' (sum_pos_of_pos hm hu')
  have hp : 0 < (S1 α C m o).real {u} := ENNReal.toReal_pos
    (speaker_dirac_apply_singleton_ne_zero hα.le (L0_ne_zero hm hu)) (measure_ne_top _ _)
  rw [← one_lt_div hp, S1_real_div hα.le hm hu hu', Real.rpow_def_of_pos (div_pos hr' hr),
    ← Real.exp_add, Real.one_lt_exp_iff, Real.log_div hr'.ne' hr.ne']
  constructor <;> intro h <;> nlinarith

/-- With two expressions the probability of one is the logistic function of its advantage in
utility over the other, scaled by the rationality. -/
theorem S1_real_of_pair (hα : 0 ≤ α) (huu' : u ≠ u') (hall : ∀ v, v = u ∨ v = u')
    (hm : ∀ v o', 0 ≤ m v o') (hu : 0 < m u o) (hu' : 0 < m u' o) :
    (S1 α C m o).real {u'} = Real.sigmoid (α * (Real.log
      ((m u' o / ∑ o', m u' o') / (m u o / ∑ o', m u o')) - (C u' - C u))) := by
  rw [S1, speaker_dirac_real_singleton_of_pair hα huu' hall (L0_ne_zero hm hu)
      (L0_ne_zero hm hu'), ← measureReal_def, ← measureReal_def,
    L0_real_singleton (hm u) (sum_pos_of_pos hm hu),
    L0_real_singleton (hm u') (sum_pos_of_pos hm hu')]

/-- A description distinguishes an object under the literal listener, so that the object is the
listener's best guess, exactly when it does under the meaning. -/
theorem distinguishes_L0_iff (hm : ∀ o', 0 ≤ m u o') (hpos : 0 < ∑ o', m u o') (D : Finset E)
    (r : E) :
    Reference.Distinguishes (fun u o ↦ L0 m u {o}) D r u ↔ Reference.Distinguishes m D r u :=
  forall₂_congr fun c _ ↦ by
    change L0 m u {c} < L0 m u {r} ↔ _
    rw [L0_apply hm hpos, L0_apply hm hpos,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (div_nonneg (hm c) hpos.le),
      div_lt_div_iff_of_pos_right hpos]

end Model

/-! ### The pins of the first figure -/

/-- The sizes of the pins. -/
inductive Size where
  | big
  | small
  deriving DecidableEq, Repr

/-- The colours of the pins. -/
inductive Color where
  | blue
  | red
  deriving DecidableEq, Repr

/-- The size-sufficient context has three pins, the target small blue pin, a big blue one and
a big red one. -/
inductive Pin where
  | bigBlue
  | bigRed
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Pin := ⊤
instance : DiscreteMeasurableSpace Pin := ⟨fun _ ↦ trivial⟩

/-- The size of a pin. -/
def Pin.size : Pin → Size
  | .bigBlue | .bigRed => .big
  | .smallBlue => .small

/-- The colour of a pin. -/
def Pin.color : Pin → Color
  | .bigBlue | .smallBlue => .blue
  | .bigRed => .red

/-- The seven referring expressions name a size, a colour, or both, each followed by
*pin*. -/
inductive Utterance where
  | big
  | small
  | blue
  | red
  | bigBlue
  | bigRed
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- The size an expression names, if any. -/
def Utterance.size : Utterance → Option Size
  | .big | .bigBlue | .bigRed => some .big
  | .small | .smallBlue => some .small
  | .blue | .red => none

/-- The colour an expression names, if any. -/
def Utterance.color : Utterance → Option Color
  | .blue | .bigBlue | .smallBlue => some .blue
  | .red | .bigRed => some .red
  | .big | .small => none

/-- The meaning of an expression is the product, over the adjectives it contains, of the degree
to which each holds of the pin, (5) and (6), with semantic value `xs` for size and `xc` for
colour. -/
def meaning (xs xc : ℝ) (u : Utterance) (o : Pin) : ℝ :=
  (u.size.elim 1 fun s ↦ noisy xs (o.size = s)) * (u.color.elim 1 fun c ↦ noisy xc (o.color = c))

section Overmodification

variable {xs xc α : ℝ} {C : Utterance → ℝ}

theorem meaning_nonneg (hs0 : 0 ≤ xs) (hs1 : xs ≤ 1) (hc0 : 0 ≤ xc) (hc1 : xc ≤ 1)
    (u : Utterance) (o : Pin) : 0 ≤ meaning xs xc u o := by
  refine mul_nonneg ?_ ?_
  · cases u.size <;> [exact zero_le_one; exact noisy_nonneg hs0 hs1 _]
  · cases u.color <;> [exact zero_le_one; exact noisy_nonneg hc0 hc1 _]

private theorem sum_pin (f : Pin → ℝ) : ∑ o, f o = f .bigBlue + f .bigRed + f .smallBlue := by
  rw [show (Finset.univ : Finset Pin) = {.bigBlue, .bigRed, .smallBlue} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

private theorem row_small : ∑ o, meaning xs xc .small o = 2 - xs := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size]
  ring

private theorem row_smallBlue : ∑ o, meaning xs xc .smallBlue o = (1 - xs) + xs * xc := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]
  ring

private theorem row_red : ∑ o, meaning xs xc .red o = 2 - xc := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.color]
  ring

private theorem row_bigRed : ∑ o, meaning xs xc .bigRed o = xs + (1 - xs) * (1 - xc) := by
  rw [sum_pin]; simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]
  ring

private theorem meaning_small : meaning xs xc .small .smallBlue = xs := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size]

private theorem meaning_smallBlue : meaning xs xc .smallBlue .smallBlue = xs * xc := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]

private theorem meaning_red : meaning xs xc .red .bigRed = xc := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.color]

private theorem meaning_bigRed : meaning xs xc .bigRed .bigRed = xs * xc := by
  simp [meaning, noisy, Utterance.size, Utterance.color, Pin.size, Pin.color]

/-- For the small blue pin and without cost, the redundant *small blue* is preferred to the
sufficient *small* exactly when the semantic value of colour exceeds one half, whatever that of
size short of Boolean. -/
theorem color_overmodification_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs < 1) (hc0 : 0 < xc)
    (hc1 : xc ≤ 1) :
    (S1 α 0 (meaning xs xc) .smallBlue).real {.small} <
      (S1 α 0 (meaning xs xc) .smallBlue).real {.smallBlue} ↔ 1/2 < xc := by
  have hsum : 0 < (1 - xs) + xs * xc := by nlinarith
  rw [S1_real_lt_iff hα (meaning_nonneg hs0.le hs1.le hc0.le hc1) (by rwa [meaning_small])
      (by rw [meaning_smallBlue]; positivity), row_small, row_smallBlue, meaning_small,
    meaning_smallBlue, Pi.zero_apply, Pi.zero_apply, sub_zero, sub_zero,
    Real.log_lt_log_iff (div_pos hs0 (by linarith)) (div_pos (by positivity) hsum),
    div_lt_div_iff₀ (by linarith) hsum]
  have hk : 0 < xs * (1 - xs) := mul_pos hs0 (by linarith)
  constructor <;> intro h <;> nlinarith

/-- For the big red pin and without cost, the redundant *big red* is preferred to the sufficient
*red* exactly when the semantic value of size exceeds one half, whatever that of colour short of
Boolean. -/
theorem size_overmodification_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hc0 : 0 < xc)
    (hc1 : xc < 1) :
    (S1 α 0 (meaning xs xc) .bigRed).real {.red} <
      (S1 α 0 (meaning xs xc) .bigRed).real {.bigRed} ↔ 1/2 < xs := by
  have hsum : 0 < xs + (1 - xs) * (1 - xc) := by nlinarith
  rw [S1_real_lt_iff hα (meaning_nonneg hs0.le hs1 hc0.le hc1.le) (by rwa [meaning_red])
      (by rw [meaning_bigRed]; positivity), row_red, row_bigRed, meaning_red, meaning_bigRed,
    Pi.zero_apply, Pi.zero_apply, sub_zero, sub_zero,
    Real.log_lt_log_iff (div_pos hc0 (by linarith)) (div_pos (by positivity) hsum),
    div_lt_div_iff₀ (by linarith) hsum]
  have hk : 0 < xc * (1 - xc) := mul_pos hc0 (by linarith)
  constructor <;> intro h <;> nlinarith

/-- The odds of the redundant *small blue* against *small* for the small blue pin exceed the odds
of the redundant *big red* against *red* for the big red pin exactly when size is noisier than
colour, at every positive rationality and when the two redundant adjectives cost the same. This is
the paper's asymmetry, more redundant use of colour than of size. -/
theorem overmodification_odds_lt_iff (hα : 0 < α) (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hc0 : 0 < xc)
    (hc1 : xc ≤ 1) (hC : C .smallBlue - C .small = C .bigRed - C .red) :
    (S1 α C (meaning xs xc) .bigRed).real {.bigRed} /
        (S1 α C (meaning xs xc) .bigRed).real {.red} <
      (S1 α C (meaning xs xc) .smallBlue).real {.smallBlue} /
        (S1 α C (meaning xs xc) .smallBlue).real {.small} ↔ xs < xc := by
  have hnn := meaning_nonneg hs0.le hs1 hc0.le hc1
  have hsB : 0 < (1 - xs) + xs * xc := by nlinarith
  have hbR : 0 < xs + (1 - xs) * (1 - xc) := by nlinarith
  have hs2 : 0 < 2 - xs := by linarith
  have hc2 : 0 < 2 - xc := by linarith
  have hsc : 0 < xs * xc := mul_pos hs0 hc0
  have hk : 0 < xs * xc + 2 * ((1 - xs) * (1 - xc)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hc1)]
  rw [S1_real_div hα.le hnn (by rwa [meaning_red]) (by rwa [meaning_bigRed]),
    S1_real_div hα.le hnn (by rwa [meaning_small]) (by rwa [meaning_smallBlue]), hC,
    mul_lt_mul_iff_left₀ (Real.exp_pos _), row_red, row_bigRed, row_small, row_smallBlue,
    meaning_red, meaning_bigRed, meaning_small, meaning_smallBlue,
    Real.rpow_lt_rpow_iff (by positivity) (by positivity) hα,
    div_lt_div_iff₀ (by positivity) (by positivity), div_mul_div_comm, div_mul_div_comm,
    div_lt_div_iff₀ (by positivity) (by positivity), ← sub_pos,
    show xs * xc * xc * ((xs + (1 - xs) * (1 - xc)) * (2 - xs)) -
        xs * xc * xs * ((1 - xs + xs * xc) * (2 - xc)) =
      (xc - xs) * (xs * xc * (xs * xc + 2 * ((1 - xs) * (1 - xc)))) by ring,
    mul_pos_iff_of_pos_right (mul_pos hsc hk), sub_pos]

/-- The sufficient *small* distinguishes the small blue pin from the big ones, so that the
listener's best guess is the target, exactly when the semantic value of size beats chance. -/
theorem small_distinguishes_iff :
    Reference.Distinguishes (meaning xs xc) {.bigBlue, .bigRed} .smallBlue .small ↔ 1/2 < xs := by
  simp [Reference.Distinguishes, meaning, noisy, Utterance.size, Utterance.color, Pin.size]
  constructor <;> intro h <;> linarith

/-- The redundant *small blue* distinguishes the pin exactly when the semantic value of size
beats chance and the two values together exceed one, so a noisy colour can cost the
identification that the sufficient description had. With Boolean values both descriptions
distinguish. -/
theorem smallBlue_distinguishes_iff (hc : 0 < xc) :
    Reference.Distinguishes (meaning xs xc) {.bigBlue, .bigRed} .smallBlue .smallBlue ↔
      1/2 < xs ∧ 1 < xs + xc := by
  simp [Reference.Distinguishes, meaning, noisy, Utterance.size, Utterance.color, Pin.size,
    Pin.color]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- With Boolean values the redundant modifier adds nothing, since *small* and *small blue* both
identify the small blue pin with certainty and are produced alike. -/
theorem boolean_no_preference (α : ℝ) :
    (S1 α 0 (meaning 1 1) .smallBlue).real {.small} =
      (S1 α 0 (meaning 1 1) .smallBlue).real {.smallBlue} := by
  have hnn := meaning_nonneg (xs := 1) (xc := 1) zero_le_one le_rfl zero_le_one le_rfl
  have h1 := L0_apply (hnn .small) (by rw [row_small]; norm_num) Pin.smallBlue
  have h2 := L0_apply (hnn .smallBlue) (by rw [row_smallBlue]; norm_num) Pin.smallBlue
  rw [row_small, meaning_small] at h1
  rw [row_smallBlue, meaning_smallBlue] at h2
  norm_num at h1 h2
  simp only [S1, measureReal_def, speaker_dirac_zero_apply_singleton, h1, h2]

end Overmodification

end DegenEtAl2020
