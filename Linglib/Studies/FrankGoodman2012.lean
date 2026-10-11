module

public import Linglib.Core.Order.Bundle
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Semantics.Denotation

/-!
# Frank and Goodman (2012): Predicting Pragmatic Reasoning in Language Games

Frank and Goodman's rational speech act model, at the paper's stimulus. The model `M` has three
objects in its domain, a blue square, a blue circle and a green square, and gives each its colour
and its shape. The lexicon has four one-place predicates, *blue*, *green*, *square* and *circle*,
and the extension `⟦w⟧ᴹ` of a word is the set of objects whose colour or shape is the one the word
names, so a word is true of an object that lies in its extension. The literal listener hears a
word as the uniform distribution over its extension, and a speaker who wants to refer to an
object chooses a word in proportion to the literal listener's probability of the object, the
reciprocal of the size of the word's extension. The paper's listener inverts that speaker
against a salience prior, and the paper reports the fit of speaker and listener bets to the
model.

## Main statements

* `size_principle`, `prefers_informative`: of two words true of an object the speaker prefers the
  one with the smaller extension, so for the blue circle it prefers *circle* to *blue*.
* `narrowing_blue`, `narrowing_square`: the speaker uses an ambiguous word less for an object
  that another word identifies.
* `unique_green`, `unique_circle`: the speaker never uses a word for an object it is false of.

## Implementation notes

* The model records the colour and the shape of each object, and a word is the pair of an
  attribute and the value it names, so the lexical entries are one clause and no table of words
  against objects is given.
* The paper's speaker has rationality one and costless words. The findings are stated at every
  positive rationality.
* The literal listener conditions the counting measure, the uniform prior over the objects, on
  the extension of the word.

## TODO

* The listener on hearing *blue*: its odds for the blue square against the blue circle are the
  prior odds times three halves, the ratio of the speaker's probabilities of *blue* at the two
  objects.

## References

* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Semantics
open scoped ENNReal Topology Semantics.Superscript

namespace FrankGoodman2012

universe u

/-! ### The stimulus (Figure 1A) -/

/-- The two attributes of an object. -/
inductive Attribute
  | colour | shape
  deriving DecidableEq, Fintype, Repr

/-- The colours. -/
inductive Colour
  | blue | green
  deriving DecidableEq, Fintype, Repr

/-- The shapes. -/
inductive Shape
  | square | circle
  deriving DecidableEq, Fintype, Repr

/-- The values an attribute takes. -/
abbrev Attribute.Value : Attribute → Type
  | .colour => Colour
  | .shape => Shape

instance (a : Attribute) : DecidableEq a.Value := by cases a <;> exact inferInstance

instance (a : Attribute) : Fintype a.Value := by cases a <;> exact inferInstance

/-- The three objects of the context, the domain of the model. -/
inductive Object
  | blueSquare | blueCircle | greenSquare
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The model `M` gives each object of its domain its colour and its shape. -/
def M : Object → Bundle Attribute Attribute.Value
  | .blueSquare, .colour => some Colour.blue
  | .blueSquare, .shape => some Shape.square
  | .blueCircle, .colour => some Colour.blue
  | .blueCircle, .shape => some Shape.circle
  | .greenSquare, .colour => some Colour.green
  | .greenSquare, .shape => some Shape.square

/-- A word is a one-place predicate that names a colour or a shape. -/
abbrev Word := Σ a : Attribute, a.Value

namespace Word

/-- The word *blue*. -/
abbrev blue : Word := ⟨.colour, Colour.blue⟩

/-- The word *green*. -/
abbrev green : Word := ⟨.colour, Colour.green⟩

/-- The word *square*. -/
abbrev square : Word := ⟨.shape, Shape.square⟩

/-- The word *circle*. -/
abbrev circle : Word := ⟨.shape, Shape.circle⟩

end Word

instance : MeasurableSpace Object := ⊤
instance : DiscreteMeasurableSpace Object := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The lexical entries. The extension of a word in a model is the set of objects whose colour or
shape in the model is the one the word names, so `⟦blue⟧ᴹ` is the set of objects that are blue
in `M`. -/
instance : Denotes Word ({E : Type u} → (E → Bundle Attribute Attribute.Value) → Set E) where
  denote w _ M := {x | M x w.1 = some w.2}

instance {E : Type u} (M : E → Bundle Attribute Attribute.Value) (w : Word) :
    DecidablePred (· ∈ ⟦w⟧ M) := fun x ↦ inferInstanceAs (Decidable (M x w.1 = some w.2))

/-- On hearing a word, the literal listener is uniform over its extension. -/
noncomputable def literal : Kernel Word Object :=
  RSA.listener Measure.count (RSA.truthful fun w : Word ↦ ⟦w⟧ᴹ)

instance : IsFiniteKernel literal :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ (RSA.truthful _)))

/-- The speaker at rationality `α` and no cost is `S₁(w | r) ∝ L₀(r | w) ^ α`, the paper's
second equation at `α = 1`. -/
noncomputable def speaker (α : ℝ) : Kernel Object Word := RSA.speaker α 0 literal Measure.dirac

theorem count_denote (w : Word) :
    Measure.count ⟦w⟧ᴹ = ⟦w⟧ᴹ.toFinset.card := by
  rw [← Measure.count_apply_finset, Set.coe_toFinset]

/-- The literal listener gives an object in the extension of a word the reciprocal of the size
of the extension, the paper's `|w|`. -/
theorem literal_apply_singleton (w : Word) (r : Object) :
    literal w {r} =
      if r ∈ ⟦w⟧ᴹ then (⟦w⟧ᴹ.toFinset.card : ℝ≥0∞)⁻¹ else 0 := by
  split_ifs with h
  · rw [literal, RSA.listener_truthful_apply_singleton Measure.count
      (fun w : Word ↦ ⟦w⟧ᴹ) h, count_denote, Measure.count_singleton, mul_one]
  · exact RSA.listener_truthful_apply_singleton_of_notMem Measure.count
      (fun w : Word ↦ ⟦w⟧ᴹ) h

/-! ### Predictions -/

/-- By the size principle, of two words that apply to an object the speaker prefers the one with
the smaller extension. -/
theorem size_principle {α : ℝ} (hα : 0 < α) {r : Object} {w₁ w₂ : Word}
    (h₁ : r ∈ ⟦w₁⟧ᴹ) (h₂ : r ∈ ⟦w₂⟧ᴹ) :
    (speaker α r).real {w₁} < (speaker α r).real {w₂} ↔
      ⟦w₂⟧ᴹ.toFinset.card < ⟦w₁⟧ᴹ.toFinset.card := by
  refine (RSA.speaker_listener_truthful_dirac_real_singleton_lt_iff hα 0 Measure.count
    (fun w : Word ↦ ⟦w⟧ᴹ) (by simp) h₁ h₂).trans ?_
  simp only [count_denote, Nat.cast_lt]

/-- For the blue circle the speaker prefers *circle*, which identifies it, to the ambiguous
*blue*. -/
theorem prefers_informative {α : ℝ} (hα : 0 < α) :
    (speaker α .blueCircle).real {.blue} < (speaker α .blueCircle).real {.circle} :=
  (size_principle hα (by decide) (by decide)).2 (by decide)

/-- As rationality grows without bound the speaker puts all its mass on *circle*. -/
theorem fully_rational_picks_circle :
    Filter.Tendsto (fun α ↦ (speaker α .blueCircle).real {.circle}) Filter.atTop (𝓝 1) := by
  refine RSA.tendsto_speaker_dirac_real_singleton_atTop ?_ fun u hu ↦ ?_
  · rw [literal_apply_singleton, ite_eq_left (by decide)]
    simp [show ⟦Word.circle⟧ᴹ.toFinset.card = 1 from by decide]
  · simp only [Pi.zero_apply, neg_zero, Real.exp_zero, mul_one]
    rw [literal_apply_singleton, literal_apply_singleton,
      ite_eq_left (by decide : Object.blueCircle ∈ ⟦Word.circle⟧ᴹ),
      show ⟦Word.circle⟧ᴹ.toFinset.card = 1 from by decide]
    obtain ⟨a, v⟩ := u
    cases a <;> cases v
    · rw [ite_eq_left (by decide), show ⟦Word.blue⟧ᴹ.toFinset.card = 2 from by decide]
      norm_num
    · rw [ite_eq_right (by decide)]; norm_num
    · rw [ite_eq_right (by decide)]; norm_num
    · exact absurd rfl hu

/-- On reals, the speaker's probability of a word at an object is the literal listener's
probability raised to the rationality, over its total across the words. -/
theorem speaker_real_singleton {α : ℝ} (hα : 0 ≤ α) (r : Object) (w : Word) :
    (speaker α r).real {w} = (literal w {r} ^ α).toReal / ∑ v, (literal v {r} ^ α).toReal :=
  RSA.speaker_dirac_zero_real_singleton hα w

private theorem sum_word (f : Word → ℝ) :
    ∑ w, f w = f .blue + f .green + f .square + f .circle := by
  rw [show (Finset.univ : Finset Word) = {.blue, .green, .square, .circle} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  ring

/-- *Blue* is used less for the blue circle, where *circle* competes, than for the blue square,
where the only competitor is as ambiguous, so a listener hearing *blue* narrows toward the blue
square. -/
theorem narrowing_blue {α : ℝ} (hα : 0 < α) :
    (speaker α .blueCircle).real {.blue} < (speaker α .blueSquare).real {.blue} := by
  set x : ℝ := ((2 : ℝ≥0∞)⁻¹ ^ α).toReal
  have hx0 : 0 < x := ENNReal.toReal_pos (by simp) (ENNReal.rpow_ne_top_of_nonneg hα.le (by simp))
  have hx1 : x < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top
      (ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) hα)
  have h2 : ⟦Word.blue⟧ᴹ.toFinset.card = 2 := by decide
  have h2' : ⟦Word.square⟧ᴹ.toFinset.card = 2 := by decide
  have h1 : ⟦Word.circle⟧ᴹ.toFinset.card = 1 := by decide
  rw [speaker_real_singleton hα.le, speaker_real_singleton hα.le, sum_word, sum_word]
  simp only [literal_apply_singleton, h1, h2, h2']
  simp (decide := true) [ENNReal.zero_rpow_of_pos hα]
  rw [div_lt_div_iff_of_pos_left hx0 (by positivity) (by positivity)]
  linarith

/-- *Square* is likewise used less for the green square, which *green* identifies. -/
theorem narrowing_square {α : ℝ} (hα : 0 < α) :
    (speaker α .greenSquare).real {.square} < (speaker α .blueSquare).real {.square} := by
  set x : ℝ := ((2 : ℝ≥0∞)⁻¹ ^ α).toReal
  have hx0 : 0 < x := ENNReal.toReal_pos (by simp) (ENNReal.rpow_ne_top_of_nonneg hα.le (by simp))
  have hx1 : x < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top
      (ENNReal.rpow_lt_one (ENNReal.inv_lt_one.2 (by norm_num)) hα)
  have h2 : ⟦Word.blue⟧ᴹ.toFinset.card = 2 := by decide
  have h2' : ⟦Word.square⟧ᴹ.toFinset.card = 2 := by decide
  have h1 : ⟦Word.green⟧ᴹ.toFinset.card = 1 := by decide
  rw [speaker_real_singleton hα.le, speaker_real_singleton hα.le, sum_word, sum_word]
  simp only [literal_apply_singleton, h1, h2, h2']
  simp (decide := true) [ENNReal.zero_rpow_of_pos hα]
  rw [div_lt_div_iff_of_pos_left hx0 (by positivity) (by positivity)]
  linarith

/-- A word that does not apply is never used, and one that does is used with positive
probability. -/
private theorem unique {α : ℝ} (hα : 0 < α) {w : Word} {r r' : Object}
    (hr : r ∉ ⟦w⟧ᴹ) (hr' : r' ∈ ⟦w⟧ᴹ) :
    (speaker α r).real {w} < (speaker α r').real {w} := by
  rw [measureReal_def, measureReal_def, speaker,
    RSA.speaker_dirac_apply_singleton_eq_zero hα
      (by rw [literal_apply_singleton, ite_eq_right hr]),
    ENNReal.toReal_zero]
  refine ENNReal.toReal_pos (RSA.speaker_dirac_apply_singleton_ne_zero hα.le ?_)
    (measure_ne_top _ _)
  rw [literal_apply_singleton, ite_eq_left hr']
  simp

/-- *Green* is never used for the blue square and is used for the green square, so a listener
hearing it identifies the green square. -/
theorem unique_green {α : ℝ} (hα : 0 < α) :
    (speaker α .blueSquare).real {.green} < (speaker α .greenSquare).real {.green} :=
  unique hα (by decide) (by decide)

/-- Unique reference for *circle*. -/
theorem unique_circle {α : ℝ} (hα : 0 < α) :
    (speaker α .blueSquare).real {.circle} < (speaker α .blueCircle).real {.circle} :=
  unique hα (by decide) (by decide)

end FrankGoodman2012
