module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Linglib.Pragmatics.Efficiency
public import Linglib.Data.Examples.XuEtAl2024

/-!
# Xu, Kemp, Frermann & Xu (2024): Word Reuse and Combination Support Efficient Communication

This file formalizes the efficient-communication account of lexicalization in [xu-etal-2024].
A novel concept enters the lexicon by reusing an existing form or by combining existing forms
into a compound, and both strategies are shaped by a tradeoff between speaker effort, the
expected length of the form, and information loss, the expected surprisal of the intended
concept under the listener's distribution (`costs`). The speaker produces from the expanded
lexicon while the listener, who has not yet acquired the new pairs, interprets each form as
the label of a category with a prototype, assigning concepts probability by a similarity
choice rule (`listener`), so the listener's distribution is positive, normalized, and
decreasing in the distance to the prototype (`listener_pos`, `sum_listener`, `listener_anti`).
The combined objective weights the two costs by a tradeoff parameter and, with need held
fixed, decomposes into an item-level objective, so an encoding that is optimal concept by
concept is optimal overall (`weightedCost_costs`, `weightedCost_le_of_forall`). Along the
frontier the optimal encodings trade length for informativeness as the parameter grows
(`Pragmatics.Efficiency.frontier_antitone`), and a compound is longer than the constituent it
reuses (`length_compound`), the length half of the tradeoff the paper reports between the two
strategies. An item is literal when the intended concept is a hyponym of an existing sense of
the reused form or of the compound's head (`Literal`), and the model predicts that a form
whose prototype lies closer to the intended concept incurs less information loss
(`surprisal_anti`).

## Implementation notes

The speaker's distribution is a point mass on the intended concept, so the expected
Kullback–Leibler divergence of the paper is the expected surprisal. Need probabilities and
the production policy enter through one weight per concept over a deterministic encoding, the
case under which the paper computes its frontier. The corpus results, the fitted sensitivity
parameter, the sentence-encoder prototypes, and the baseline encodings are not restated; the
attested items of the paper's first table and the near-synonyms of its second are recorded
as examples.

## References

* [xu-etal-2024]
* [kemp-regier-2012]
* [zaslavsky-kemp-regier-tishby-2018]
* [regier-kemp-kay-2015]
-/

@[expose] public section

namespace XuEtAl2024

open Pragmatics.Efficiency Finset

/-- Surprisal in bits. -/
noncomputable def surprisal (x : ℝ) : ℝ := -Real.logb 2 x

/-- Surprisal decreases as probability grows. -/
theorem surprisal_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : surprisal y ≤ surprisal x :=
  neg_le_neg (Real.logb_le_logb_of_le (by norm_num) hx hxy)

/-! ### The listener -/

section Listener

variable {C W Q : Type*} [Fintype C]

/-- The similarity choice listener: the probability of a concept given a form falls off
exponentially, at rate `γ`, with the concept's distance from the form's prototype. -/
noncomputable def listener (γ : ℝ) (d : C → Q → ℝ) (q : W → Q) (w : W) (c : C) : ℝ :=
  Real.exp (-γ * d c (q w)) / ∑ c', Real.exp (-γ * d c' (q w))

variable (γ : ℝ) (d : C → Q → ℝ) (q : W → Q) (w : W)

/-- The listener never assigns zero probability. -/
theorem listener_pos [Nonempty C] (c : C) : 0 < listener γ d q w c :=
  div_pos (Real.exp_pos _) (sum_pos (λ _ _ => Real.exp_pos _) univ_nonempty)

/-- The listener's distribution is normalized. -/
theorem sum_listener [Nonempty C] : ∑ c, listener γ d q w c = 1 := by
  unfold listener
  rw [← sum_div, div_self (sum_pos (λ _ _ => Real.exp_pos _) univ_nonempty).ne']

/-- A concept closer to the prototype is more probable. -/
theorem listener_anti (hγ : 0 ≤ γ) {c c' : C} (h : d c (q w) ≤ d c' (q w)) :
    listener γ d q w c' ≤ listener γ d q w c :=
  div_le_div_of_nonneg_right
    (Real.exp_le_exp.2 (by nlinarith)) (sum_nonneg λ _ _ => (Real.exp_pos _).le)

/-- With no sensitivity the listener is uniform. -/
theorem listener_zero (c : C) : listener 0 d q w c = 1 / Fintype.card C := by
  simp [listener]

end Listener

/-! ### Communicative costs -/

section Costs

variable {C W : Type*} [Fintype C]

/-- The costs of an encoding `f` of the emerging concepts under need `p`, form length `l`,
and listener `m`: expected length and expected surprisal of the intended concept. -/
noncomputable def costs (p : C → ℝ) (l : W → ℝ) (m : W → C → ℝ) (f : C → W) :
    CostPair :=
  ⟨∑ c, p c * l (f c), ∑ c, p c * surprisal (m (f c) c)⟩

/-- The item-level objective: the surprisal of the concept under the form, plus the weighted
length of the form. -/
noncomputable def itemObjective (l : W → ℝ) (m : W → C → ℝ) (β : ℝ) (c : C) (w : W) :
    ℝ :=
  surprisal (m w c) + β * l w

/-- The combined objective is the need-weighted sum of the item-level objectives. -/
theorem weightedCost_costs (p : C → ℝ) (l : W → ℝ) (m : W → C → ℝ) (f : C → W)
    (β : ℝ) :
    weightedCost (costs p l m f) β = ∑ c, p c * itemObjective l m β c (f c) := by
  simp only [weightedCost, costs, itemObjective, mul_add, sum_add_distrib, mul_sum]
  congr 1
  exact sum_congr rfl λ _ _ => by ring

/-- An encoding that is optimal for every concept is optimal overall. -/
theorem weightedCost_le_of_forall {p : C → ℝ} (hp : ∀ c, 0 ≤ p c) (l : W → ℝ)
    (m : W → C → ℝ) {f g : C → W} (β : ℝ)
    (h : ∀ c, itemObjective l m β c (f c) ≤ itemObjective l m β c (g c)) :
    weightedCost (costs p l m f) β ≤ weightedCost (costs p l m g) β := by
  rw [weightedCost_costs, weightedCost_costs]
  exact sum_le_sum λ c _ => mul_le_mul_of_nonneg_left (h c) (hp c)

end Costs

/-! ### Reuse and combination -/

section Forms

variable {A C Q : Type*}

/-- A compound concatenates two existing forms. -/
def compound (w₁ w₂ : List A) : List A := w₁ ++ w₂

/-- A compound is longer than a constituent it could have reused. -/
theorem length_compound (w₁ : List A) {w₂ : List A} (h : w₂ ≠ []) :
    w₁.length < (compound w₁ w₂).length := by
  simp [compound, List.length_pos_iff_ne_nil.2 h]

/-- The prototype of a compound is the sum of its constituents' prototypes. -/
def compoundPrototype [Add Q] (q : List A → Q) (w₁ w₂ : List A) : Q := q w₁ + q w₂

/-- An item is literal when its concept is a hyponym of an existing sense of the form that
carries it: the reused form, or the head of a compound. -/
def Literal (Hypo : C → C → Prop) (senses : List A → Set C) (carrier : List A) (c : C) :
    Prop :=
  ∃ c' ∈ senses carrier, Hypo c c'

end Forms

end XuEtAl2024
