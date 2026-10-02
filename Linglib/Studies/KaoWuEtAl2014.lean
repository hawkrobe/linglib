module

public import Linglib.Pragmatics.RSA.QUD
public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Data.Rat.Floor

/-!
# Kao, Wu, Bergen and Goodman (2014): Nonliteral Understanding of Number Words

Kao, Wu, Bergen and Goodman model hyperbole on the RSA kernel pipeline. A meaning pairs a price
state with the speaker's affect; the literal listener conditions the prior on the price named, a
speaker with a communicative goal is informative about the goal's projection of the meaning and
pays a higher cost for sharp numbers, and the pragmatic listener marginalizes the goal.

## Main results

* `KaoWuEtAl2014.listener_ne_zero_iff`: a meaning receives positive posterior mass exactly when
  some goal of positive prior projects it into the cell of a meaning at which the utterance is
  literally true.
* `KaoWuEtAl2014.hyperbole`: a low price with affect is available under the affect goal.
* `KaoWuEtAl2014.literal_of_price_goals`, `KaoWuEtAl2014.halo_of_price_goals`: the comparison
  models of Fig. 2B.
* `KaoWuEtAl2014.approximate_prefers_round`: the halo effect of Fig. 3B rests on the cost.

## Implementation notes

Priors are arguments: the price prior and the conditional affect prior of Experiments 3a and 3b
enter as one probability measure on meanings, and the goal prior as a probability measure on
goals, uniform in the paper. The model's numerical fits (Figs. 2 to 5) rest on the raw priors
published as data rather than in the paper, and are not stated. The goals are the paper's, a
precision projection composed with a relevance projection, the two affect-only goals coinciding
(`project_affect`).

## References

* [kao-etal-2014-hyperbole]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoWuEtAl2014

/-- The precision of a goal is exact, the paper's `f_e`, or approximate, `f_a`, which rounds the
price to the nearest multiple of ten. -/
inductive Precision
  | exact | approximate
  deriving DecidableEq, Repr, Fintype

/-- The price states of Materials and Methods are five round prices and their sharp neighbours. -/
inductive Price
  | p50 | p51 | p500 | p501 | p1000 | p1001 | p5000 | p5001 | p10000 | p10001
  deriving DecidableEq, Repr, Fintype

namespace Price

/-- The price in dollars. -/
def value : Price → ℕ
  | .p50 => 50 | .p51 => 51 | .p500 => 500 | .p501 => 501 | .p1000 => 1000
  | .p1001 => 1001 | .p5000 => 5000 | .p5001 => 5001 | .p10000 => 10000 | .p10001 => 10001

/-- A round price is divisible by ten. -/
def IsRound (p : Price) : Prop := 10 ∣ p.value

instance : DecidablePred IsRound := fun _ ↦ inferInstanceAs (Decidable (_ ∣ _))

/-- The nearest round price, the paper's `Round`. -/
def round : Price → Price
  | .p50 | .p51 => .p50 | .p500 | .p501 => .p500 | .p1000 | .p1001 => .p1000
  | .p5000 | .p5001 => .p5000 | .p10000 | .p10001 => .p10000

theorem isRound_round (p : Price) : p.round.IsRound := by cases p <;> decide

@[simp] theorem round_round (p : Price) : p.round.round = p.round := by cases p <;> rfl

/-- `round` is the substrate rounding to the nearest multiple of ten. -/
theorem value_round (p : Price) :
    (p.round.value : ℚ) = Degree.Granularity.representative 10 (p.value : ℚ) := by
  cases p <;> norm_num [round, value, Degree.Granularity.representative]

/-- The precision projection `f` of a goal keeps the price exact or rounds it. -/
def project : Precision → Price → Price
  | .exact, p => p
  | .approximate, p => p.round

instance : MeasurableSpace Price := ⊤
instance : DiscreteMeasurableSpace Price := ⟨fun _ ↦ trivial⟩
instance : Nonempty Price := ⟨.p50⟩

end Price

/-- A meaning pairs the price state with whether the speaker has an affect about it, the paper's
`M = S × A` with `A = {0, 1}`. -/
abbrev Meaning := Price × Bool

/-- The relevance projection `r` of a goal keeps the price, the affect, or both. -/
inductive Relevance
  | price | affect | both
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Relevance := ⊤
instance : DiscreteMeasurableSpace Relevance := ⟨fun _ ↦ trivial⟩
instance : Nonempty Relevance := ⟨.price⟩
instance : MeasurableSpace Precision := ⊤
instance : DiscreteMeasurableSpace Precision := ⟨fun _ ↦ trivial⟩
instance : Nonempty Precision := ⟨.exact⟩

/-- A goal composes a precision projection with a relevance projection, `g(s, a) = r(f(s), a)`. -/
abbrev Goal := Precision × Relevance

/-- The projection of a goal keeps the price component, exact or rounded, and the affect component,
each when it is relevant. -/
def project (g : Goal) (m : Meaning) : Option Price × Option Bool :=
  (if g.2 = .affect then none else some (Price.project g.1 m.1),
    if g.2 = .price then none else some m.2)

/-- The two affect-only goals coincide, as the paper notes. -/
theorem project_affect (f f' : Precision) : project (f, .affect) = project (f', .affect) :=
  rfl

/-- An utterance is true of a meaning when the price it names is the price state. -/
def sem (u : Price) : Set Meaning := {m | m.1 = u}

theorem mem_sem {u : Price} {m : Meaning} : m ∈ sem u ↔ m.1 = u := Iff.rfl

/-- The literal listener conditions the prior on the price named, eq. 9. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Price Meaning :=
  literalListener μ fun u ↦ (sem u).indicator 1

theorem L0_apply (μ : Measure Meaning) (u : Price) : L0 μ u = μ[|sem u] := by
  rw [L0, literalListener_indicator, Kernel.ofFunOfCountable_apply]

theorem L0_apply_le_one (μ : Measure Meaning) (u : Price) (s : Set Meaning) : L0 μ u s ≤ 1 :=
  literalListener_apply_le_one μ _ u s

/-- The literal listener gives a meaning mass exactly when the utterance names its price and
the prior gives it mass. -/
theorem L0_apply_singleton_ne_zero_iff (μ : Measure Meaning) [IsFiniteMeasure μ] (u : Price)
    (m : Meaning) : L0 μ u {m} ≠ 0 ↔ m.1 = u ∧ μ {m} ≠ 0 := by
  by_cases h : m ∈ sem u
  · rw [L0, literalListener_indicator_apply_singleton μ sem h]
    exact ⟨fun h' ↦ ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      fun h' ↦ mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [L0, literalListener_indicator_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (fun h' ↦ h' rfl) (fun h' ↦ h h'.1)

/-- The cost factor `e^{-C(u)}` of eq. 7 takes `C(u) = 1` at a round price and the fitted parameter
`c` at a sharp one. -/
noncomputable def cost (c : ℝ) (u : Price) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(if u.IsRound then 1 else c)))

theorem cost_ne_zero (c : ℝ) (u : Price) : cost c u ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem cost_ne_top (c : ℝ) (u : Price) : cost c u ≠ ∞ := ENNReal.ofReal_ne_top

/-- The goal-indexed speaker, eqs. 5 to 8, is the best response to the projected literal listener of
the goal, at unit rationality, weighted by the cost factor. -/
noncomputable def S1 (μ : Measure Meaning) (c : ℝ) : Kernel (Meaning × Goal) Price :=
  familySpeaker (projListener project (L0 μ)) 1 (cost c)

/-- The pragmatic listener over meaning and goal, eq. 10, is the family listener over the product of
the meaning prior and the goal prior; its first marginal is the meaning listener. -/
noncomputable def L1 (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
    [IsProbabilityMeasure ν] (c : ℝ) : Kernel Price (Meaning × Goal) :=
  familyListener (projListener project (L0 μ)) 1 (cost c) (μ.prod ν)

section Support

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
  [IsProbabilityMeasure ν] (c : ℝ)

/-- A goal's speaker produces an utterance at a meaning exactly when the meaning's cell holds
a meaning of positive prior at which the utterance is literally true. -/
theorem S1_apply_singleton_ne_zero_iff (g : Goal) (m : Meaning) (u : Price) :
    S1 μ c (m, g) {u} ≠ 0 ↔ ∃ m', project g m' = project g m ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [S1, familySpeaker_apply]
  constructor
  · intro h
    have hL : projListener project (L0 μ) g u {m} ≠ 0 := fun h' ↦
      h (speaker_apply_singleton_eq_zero one_pos h')
    rw [projListener_apply_singleton_ne_zero_iff] at hL
    obtain ⟨m', hm', h0⟩ := hL
    exact ⟨m', hm', (L0_apply_singleton_ne_zero_iff μ u m').mp h0⟩
  · rintro ⟨m', hm', hu, hμ⟩
    exact speaker_apply_singleton_ne_zero zero_le_one (cost_ne_zero c) (cost_ne_top c)
      (fun u' ↦ projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one μ))
      ((projListener_apply_singleton_ne_zero_iff _ _ _ _ _).mpr
        ⟨m', hm', (L0_apply_singleton_ne_zero_iff μ u m').mpr ⟨hu, hμ⟩⟩)

/-- An utterance naming a price of positive prior has a positive marginal. -/
theorem comp_S1_ne_zero {u : Price} (h : ∃ m : Meaning, m.1 = u ∧ μ {m} ≠ 0) :
    (S1 μ c ∘ₘ μ.prod ν) {u} ≠ 0 := by
  obtain ⟨m, hm, hμ⟩ := h
  obtain ⟨g, -, hg⟩ : ∃ g ∈ (Finset.univ : Finset Goal), ν {g} ≠ 0 := by
    refine Finset.exists_ne_zero_of_sum_ne_zero ?_
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    exact one_ne_zero
  refine comp_familySpeaker_ne_zero (w := m) (l := g) ?_ ?_
  · rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    exact mul_ne_zero hμ hg
  · exact (S1_apply_singleton_ne_zero_iff μ c g m u).mpr ⟨m, rfl, hm, hμ⟩

/-- A meaning is in the support of the meaning listener at an utterance exactly when it has positive
prior and some goal of positive prior projects it into the cell of a meaning of positive prior at
which the utterance is literally true. -/
theorem listener_ne_zero_iff {u : Price} (hu : (S1 μ c ∘ₘ μ.prod ν) {u} ≠ 0) (m : Meaning) :
    (L1 μ ν c u).fst {m} ≠ 0
      ↔ μ {m} ≠ 0 ∧ ∃ g, ν {g} ≠ 0 ∧ ∃ m', project g m' = project g m ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [L1, familyListener_fst_apply_singleton_ne_zero_iff _ _ _ hu]
  simp only [← S1_apply_singleton_ne_zero_iff μ c, S1, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff]
  exact ⟨fun ⟨g, ⟨hm, hg⟩, hs⟩ ↦ ⟨hm, g, hg, hs⟩, fun ⟨hm, g, hg, hs⟩ ↦ ⟨g, ⟨hm, hg⟩, hs⟩⟩

/-- A low price with affect is a possible meaning of a high price under the affect goal whenever the
prior gives mass to both meanings with affect, which is hyperbole. -/
theorem hyperbole (hν : ν {(.exact, .affect)} ≠ 0) (h50 : μ {(.p50, true)} ≠ 0)
    (h10k : μ {(.p10000, true)} ≠ 0) : (L1 μ ν c .p10000).fst {(.p50, true)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν c (comp_S1_ne_zero μ ν c ⟨_, rfl, h10k⟩)]
  exact ⟨h50, (.exact, .affect), hν, (.p10000, true), rfl, rfl, h10k⟩

/-- A listener entertaining only the exact price goal, the first comparison model of Fig. 2B,
interprets every utterance literally. -/
theorem literal_of_price_goals (hν : ∀ g, ν {g} ≠ 0 → g = (.exact, .price)) {u : Price}
    (hu : (S1 μ c ∘ₘ μ.prod ν) {u} ≠ 0) {m : Meaning} (h : (L1 μ ν c u).fst {m} ≠ 0) :
    m.1 = u := by
  obtain ⟨-, g, hg, m', hm', hu', -⟩ := (listener_ne_zero_iff μ ν c hu m).mp h
  obtain rfl := hν g hg
  subst hu'
  have : m'.1 = m.1 := by simpa [project, Price.project] using hm'
  exact this.symm

/-- A listener entertaining the price goals, exact or approximate, the second comparison model
of Fig. 2B, reaches only the prices rounding to the utterance. -/
theorem halo_of_price_goals (hν : ∀ g, ν {g} ≠ 0 → g.2 = .price) {u : Price}
    (hu : (S1 μ c ∘ₘ μ.prod ν) {u} ≠ 0) {m : Meaning} (h : (L1 μ ν c u).fst {m} ≠ 0) :
    m.1.round = u.round := by
  obtain ⟨-, ⟨f, r⟩, hg, m', hm', hu', -⟩ := (listener_ne_zero_iff μ ν c hu m).mp h
  obtain rfl : r = .price := hν _ hg
  subst hu'
  cases f
  · have : m'.1 = m.1 := by simpa [project, Price.project] using hm'
    rw [this]
  · have : m'.1.round = m.1.round := by simpa [project, Price.project] using hm'
    rw [this]

end Support

section Halo

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (c : ℝ)

/-- At an approximate price goal, an utterance naming a price with positive prior puts all its
projected mass on every meaning of the same round price. -/
theorem projListener_approximate {u p : Price} (hμ : μ (sem u) ≠ 0) (hp : u.round = p.round)
    (a : Bool) : projListener project (L0 μ) (.approximate, .price) u {(p, a)} = 1 := by
  rw [projListener_apply_singleton, L0_apply, cond_apply .of_discrete,
    Set.inter_eq_self_of_subset_left (fun m hm ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, project, Price.project, mem_sem.mp hm, hp]
      rfl),
    ENNReal.inv_mul_cancel hμ (measure_ne_top _ _)]

/-- At an approximate price goal a sharp price projects with its round neighbour, so the speaker
prefers the round utterance exactly when sharp numbers cost more, the cost mechanism of the halo
effect (Fig. 3B). -/
theorem approximate_prefers_round {p : Price} (hp : ¬ p.IsRound) (h₁ : μ (sem p) ≠ 0)
    (h₂ : μ (sem p.round) ≠ 0) (a : Bool) :
    (S1 μ c ((p, a), (.approximate, .price))).real {p}
        < (S1 μ c ((p, a), (.approximate, .price))).real {p.round} ↔ 1 < c := by
  have hle : ∀ u, projListener project (L0 μ) (.approximate, .price) u {(p, a)} ≤ 1 :=
    fun u ↦ projListener_apply_singleton_le_one _ _ _ _ _ (L0_apply_le_one μ)
  rw [S1, familySpeaker_apply, speaker_real_singleton_lt_iff zero_le_one (cost_ne_top c) hle
    ⟨p, by rw [projListener_approximate μ h₁ rfl]; simp [cost_ne_zero]⟩,
    projListener_approximate μ h₁ rfl, projListener_approximate μ h₂ (Price.round_round p),
    ENNReal.one_rpow, one_mul, one_mul, cost, cost, ite_eq_right hp,
    ite_eq_left (Price.isRound_round p),
    ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp, neg_lt_neg_iff]

end Halo

end KaoWuEtAl2014
