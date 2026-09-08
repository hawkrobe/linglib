import Linglib.Pragmatics.RSA.Uniform
import Mathlib.Algebra.Order.Field.Basic

/-!
# Degen, Hawkins, Graf, Kreiss and Goodman (2020): When Redundancy Is Useful

This file formalizes the continuous-semantics rational speech act model of [degen-etal-2020].
A referring expression's meaning is a value in the unit interval rather than a truth value:
each mentioned adjective is a noise channel, a size or colour predicate holding of an object
to degree x_size or x_colour when it matches and to degree 1 − x when it does not, and a
two-adjective expression multiplies its channels, (5) and (6). The literal listener of (1)
normalizes the meaning over the objects at a uniform prior, and the speaker of (3) and (4),
here with unit informativeness weight and no cost as in [frank-goodman-2012], chooses an
expression in proportion to the listener's probability of the intended object. A redundant
modifier then adds information: for the small blue pin among a big blue and a big red one,
the speaker prefers the redundant *small blue* to the sufficient *small* exactly when the
colour channel exceeds one half, and for the big red pin prefers *big red* to *red* exactly
when the size channel does; with Boolean channels, both values one, there is no preference
either way. The same mechanism with a typicality meaning gives the choice of taxonomic level
of Experiment 3: the subordinate term is preferred to the basic-level term exactly when it is
the more informative of the two about the target, typicality replacing the noise channel.

## TODO

* Tables 2 and 3 do not follow from Equation (1) at the stated values x_size = .8 and
  x_colour = .99: Equation (1) gives the literal listener 0.67 for *small* and 0.80 for *small
  blue* at the small blue pin, where the table has .48 and .50, and gives the redundant *big
  red* a larger value than *red* at the big red pin, where the table has .52 against .57; the
  table's values match a listener proportional to the exponential of the meaning. The theorems
  follow the equations, on which the colour–size asymmetry is the regime x_size ≤ 1/2 < x_colour
  rather than the stated values.
* The regression coefficients and the fitted noise parameters of the three experiments are not
  encoded.

## References

* [degen-etal-2020]
* [frank-goodman-2012]
-/

namespace DegenEtAl2020

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### The scene of Figure 1a -/

/-- The three pins of the size-sufficient context: the target small blue pin, a big blue and
a big red one. -/
inductive World where
  | bigBlue
  | bigRed
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨λ _ => trivial⟩

/-- Whether a pin is big. -/
def World.big : World → Bool
  | .bigBlue | .bigRed => true
  | .smallBlue => false

/-- Whether a pin is blue. -/
def World.blue : World → Bool
  | .bigBlue | .smallBlue => true
  | .bigRed => false

/-- The seven referring expressions: a size, a colour, or both, each followed by *pin*. -/
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
instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩

/-- The size an expression mentions, `true` for big. -/
def Utterance.size : Utterance → Option Bool
  | .big | .bigBlue | .bigRed => some true
  | .small | .smallBlue => some false
  | .blue | .red => none

/-- The colour an expression mentions, `true` for blue. -/
def Utterance.color : Utterance → Option Bool
  | .blue | .bigBlue | .smallBlue => some true
  | .red | .bigRed => some false
  | .big | .small => none

/-- The demonstration value x_size = .8 of Tables 2 and 3, footnote 14. -/
def sizeMatch : ℚ := 8/10

/-- The mismatch degree 1 − x_size. -/
def sizeMismatch : ℚ := 2/10

/-- The demonstration value x_colour = .99. -/
def colorMatch : ℚ := 99/100

/-- The mismatch degree 1 − x_colour. -/
def colorMismatch : ℚ := 1/100

/-! ### Continuous semantics -/

/-- A noise channel: a mentioned feature holds of an object to degree `x` when it matches and
`1 − x` when it does not, and an unmentioned feature contributes nothing. -/
def channel (x : ℝ) : Option Bool → Bool → ℝ
  | none, _ => 1
  | some b, a => if b = a then x else 1 - x

/-- The continuous meaning, (5) and (6): the product of the size and colour channels. -/
def meaning (xs xc : ℝ) (u : Utterance) (w : World) : ℝ :=
  channel xs u.size w.big * channel xc u.color w.blue

section Model

variable {xs xc : ℝ}

theorem channel_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (o : Option Bool) (a : Bool) :
    0 ≤ channel x o a := by
  cases o with
  | none => exact zero_le_one
  | some b => simp only [channel]; split_ifs <;> linarith

theorem meaning_nonneg (hs0 : 0 ≤ xs) (hs1 : xs ≤ 1) (hc0 : 0 ≤ xc) (hc1 : xc ≤ 1)
    (u : Utterance) (w : World) : 0 ≤ meaning xs xc u w :=
  mul_nonneg (channel_nonneg hs0 hs1 _ _) (channel_nonneg hc0 hc1 _ _)

/-- The literal listener, (1): the meaning normalized over the pins at a uniform prior. -/
noncomputable def L0 (xs xc : ℝ) : Kernel Utterance World :=
  literalListener (uniformOn Set.univ) λ u w => ENNReal.ofReal (meaning xs xc u w)

/-- The speaker, (3) and (4), with unit informativeness weight and no cost. -/
noncomputable def S1 (xs xc : ℝ) : Kernel World Utterance := speaker 1 1 (L0 xs xc)

private theorem sum_world (f : World → ℝ) : ∑ w, f w = f .bigBlue + f .bigRed + f .smallBlue := by
  rw [show (Finset.univ : Finset World) = {.bigBlue, .bigRed, .smallBlue} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-- The listener's value of an expression at a pin is the share of its row. -/
theorem L0_apply (hs0 : 0 ≤ xs) (hs1 : xs ≤ 1) (hc0 : 0 ≤ xc) (hc1 : xc ≤ 1) (u : Utterance)
    (w : World) (hpos : 0 < ∑ w', meaning xs xc u w') :
    L0 xs xc u {w} = ENNReal.ofReal (meaning xs xc u w / ∑ w', meaning xs xc u w') :=
  literalListener_uniformOn_ofReal_apply_singleton _ u w
    (λ w' => meaning_nonneg hs0 hs1 hc0 hc1 u w') hpos

/-- The speaker prefers `u'` to `u` for a pin exactly when the listener finds the pin likelier
under `u'`; the normalization cancels. -/
theorem S1_real_lt_iff (w : World) (u u' : Utterance) (h : L0 xs xc u' {w} ≠ 0) :
    (S1 xs xc w).real {u} < (S1 xs xc w).real {u'} ↔ L0 xs xc u {w} < L0 xs xc u' {w} := by
  rw [S1]
  refine (speaker_real_singleton_lt_iff (cost := 1) (L := L0 xs xc) (w := w) zero_le_one
    (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one _ _ u _) ⟨u', ?_⟩).trans ?_
  · simpa only [ENNReal.rpow_one, Pi.one_apply, mul_one] using h
  · simp only [ENNReal.rpow_one, Pi.one_apply, mul_one]

end Model

/-! ### Overmodification -/

section Overmodification

variable {xs xc : ℝ}

private theorem row_small : ∑ w, meaning xs xc .small w = 2 - xs := by
  rw [sum_world]; simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]
  ring

private theorem row_smallBlue : ∑ w, meaning xs xc .smallBlue w = (1 - xs) + xs * xc := by
  rw [sum_world]; simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]
  ring

private theorem row_red : ∑ w, meaning xs xc .red w = 2 - xc := by
  rw [sum_world]; simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]
  ring

private theorem row_bigRed : ∑ w, meaning xs xc .bigRed w = xs + (1 - xs) * (1 - xc) := by
  rw [sum_world]; simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]
  ring

/-- Colour overmodification: for the small blue pin the redundant *small blue* is preferred
to the sufficient *small* exactly when the colour channel exceeds one half, whatever the size
channel short of Boolean. -/
theorem color_overmodification_iff (hs0 : 0 < xs) (hs1 : xs < 1) (hc0 : 0 < xc) (hc1 : xc ≤ 1) :
    (S1 xs xc .smallBlue).real {.small} < (S1 xs xc .smallBlue).real {.smallBlue} ↔ 1/2 < xc := by
  have hsum : 0 < (1 - xs) + xs * xc := by nlinarith
  have hsum' : 0 < 2 - xs := by linarith
  have h1 := L0_apply hs0.le hs1.le hc0.le hc1 .small World.smallBlue
    (by rw [row_small]; exact hsum')
  have h2 := L0_apply hs0.le hs1.le hc0.le hc1 .smallBlue World.smallBlue
    (by rw [row_smallBlue]; exact hsum)
  rw [S1_real_lt_iff _ _ _ (by rw [h2]; exact (ENNReal.ofReal_pos.mpr (div_pos (by
      simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]; positivity)
      (by rw [row_smallBlue]; exact hsum))).ne'), h1, h2, row_small, row_smallBlue,
    ENNReal.ofReal_lt_ofReal_iff (div_pos (by
      simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]; positivity)
      hsum)]
  simp only [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]
  simp only [↓reduceIte, mul_one]
  rw [div_lt_div_iff₀ hsum' hsum]
  have hk : 0 < xs * (1 - xs) := mul_pos hs0 (by linarith)
  constructor <;> intro h <;> nlinarith [hk]

/-- Size overmodification: for the big red pin the redundant *big red* is preferred to the
sufficient *red* exactly when the size channel exceeds one half, whatever the colour channel
short of Boolean. The asymmetry of the paper is thus the regime of a size channel at most one
half and a colour channel above it. -/
theorem size_overmodification_iff (hs0 : 0 < xs) (hs1 : xs ≤ 1) (hc0 : 0 < xc) (hc1 : xc < 1) :
    (S1 xs xc .bigRed).real {.red} < (S1 xs xc .bigRed).real {.bigRed} ↔ 1/2 < xs := by
  have hsum : 0 < xs + (1 - xs) * (1 - xc) := by nlinarith
  have hsum' : 0 < 2 - xc := by linarith
  have h1 := L0_apply hs0.le hs1 hc0.le hc1.le .red World.bigRed (by rw [row_red]; exact hsum')
  have h2 := L0_apply hs0.le hs1 hc0.le hc1.le .bigRed World.bigRed (by rw [row_bigRed]; exact hsum)
  rw [S1_real_lt_iff _ _ _ (by rw [h2]; exact (ENNReal.ofReal_pos.mpr (div_pos (by
      simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]; positivity)
      (by rw [row_bigRed]; exact hsum))).ne'), h1, h2, row_red, row_bigRed,
    ENNReal.ofReal_lt_ofReal_iff (div_pos (by
      simp [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]; positivity)
      hsum)]
  simp only [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue]
  simp only [↓reduceIte, one_mul]
  rw [div_lt_div_iff₀ hsum' hsum]
  have hk : 0 < xc * (1 - xc) := mul_pos hc0 (by linarith)
  constructor <;> intro h <;> nlinarith [hk]

/-- With Boolean channels the redundant modifier adds nothing: *small* and *small blue* both
identify the small blue pin with certainty and are produced alike. -/
theorem boolean_no_preference :
    (S1 1 1 .smallBlue).real {.small} = (S1 1 1 .smallBlue).real {.smallBlue} := by
  have h1 := L0_apply (xs := 1) (xc := 1) zero_le_one le_rfl zero_le_one le_rfl .small
    World.smallBlue (by rw [row_small]; norm_num)
  have h2 := L0_apply (xs := 1) (xc := 1) zero_le_one le_rfl zero_le_one le_rfl .smallBlue
    World.smallBlue (by rw [row_smallBlue]; norm_num)
  rw [row_small] at h1
  rw [row_smallBlue] at h2
  simp only [meaning, channel, Utterance.size, Utterance.color, World.big, World.blue,
    ↓reduceIte] at h1 h2
  norm_num at h1 h2
  simp only [S1, measureReal_def, speaker_apply_singleton, h1, h2, Pi.one_apply]

end Overmodification

/-! ### Taxonomic level, Experiment 3 -/

/-- The target dalmatian among a cat and a bird, where the basic-level *dog* suffices. -/
inductive NomWorld where
  | dalmatian
  | cat
  | bird
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NomWorld := ⊤
instance : DiscreteMeasurableSpace NomWorld := ⟨λ _ => trivial⟩

/-- The nouns at the three taxonomic levels: *dalmatian*, *dog*, *animal*. -/
inductive NomUtterance where
  | sub
  | basic
  | super
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NomUtterance := ⊤
instance : DiscreteMeasurableSpace NomUtterance := ⟨λ _ => trivial⟩

section Nominal

variable (typ : NomUtterance → NomWorld → ℝ)

/-- The literal listener with the typicality of each object for each noun as its meaning. -/
noncomputable def nomL0 : Kernel NomUtterance NomWorld :=
  literalListener (uniformOn Set.univ) λ u w => ENNReal.ofReal (typ u w)

/-- The nominal speaker with unit informativeness weight and no cost. -/
noncomputable def nomS1 : Kernel NomWorld NomUtterance := speaker 1 1 (nomL0 typ)

/-- The subordinate term is preferred to the basic-level one for the target exactly when it is
the more informative about it: its typicality for the target, relative to its typicality over
the scene, exceeds the basic term's. -/
theorem subordinate_preferred_iff (hnn : ∀ u w, 0 ≤ typ u w) (hsub : 0 < typ .sub .dalmatian)
    (hbasic : 0 < typ .basic .dalmatian) :
    (nomS1 typ .dalmatian).real {.basic} < (nomS1 typ .dalmatian).real {.sub} ↔
      typ .basic .dalmatian * ∑ w, typ .sub w < typ .sub .dalmatian * ∑ w, typ .basic w := by
  have hsum : ∀ u, 0 < typ u .dalmatian → 0 < ∑ w, typ u w := λ u h =>
    h.trans_le (Finset.single_le_sum (λ w _ => hnn u w) (Finset.mem_univ _))
  have h1 := literalListener_uniformOn_ofReal_apply_singleton typ .basic NomWorld.dalmatian
    (hnn .basic) (hsum _ hbasic)
  have h2 := literalListener_uniformOn_ofReal_apply_singleton typ .sub NomWorld.dalmatian
    (hnn .sub) (hsum _ hsub)
  rw [nomS1]
  refine (speaker_real_singleton_lt_iff (cost := 1) (L := nomL0 typ) (w := NomWorld.dalmatian)
    zero_le_one (λ _ => ENNReal.one_ne_top) (λ u => literalListener_apply_le_one _ _ u _)
    ⟨.sub, ?_⟩).trans ?_
  · rw [ENNReal.rpow_one, Pi.one_apply, mul_one, nomL0, h2]
    exact (ENNReal.ofReal_pos.mpr (div_pos hsub (hsum _ hsub))).ne'
  · simp only [ENNReal.rpow_one, Pi.one_apply, mul_one, nomL0]
    rw [h1, h2, ENNReal.ofReal_lt_ofReal_iff (div_pos hsub (hsum _ hsub)),
      div_lt_div_iff₀ (hsum _ hbasic) (hsum _ hsub)]

end Nominal

end DegenEtAl2020
