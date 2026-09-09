import Mathlib.Data.Fintype.Vector
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Linglib.Processing.Expectation.InformationValue

/-!
# Giulianelli, Wallbridge, Cotterell and Fernández (2026): Incremental Alternative Sampling as a Lens into the Temporal and Representational Resolution of Linguistic Prediction

This file formalizes the incremental alternative sampling (IAS) family of [giulianelli-etal-2026]:
a comprehender samples continuations of the context from a language model over a forecast horizon
of `h` symbols (`gram`), and the generalised surprisal of the next unit is a warping of the expected
score of the target against those alternatives (`genSurprisalH`, the horizon-`h` form of
[giulianelli-opedal-cotterell-2024]'s definition in `Processing/Expectation/InformationValue.lean`).
Standard surprisal is the member with the negative logarithm and the prefix indicator at every
horizon, because the alternatives' first symbol is distributed as the model's next symbol
(`map_head_gram`, `sum_prefixIndicator`, `genSurprisalH_indicator`); it thus evaluates alternatives
by lexical identity alone, and the discrete distance shows what this conflates, since information
value with it is the probability of error (`informationValue1_discrete`). Incremental information
value replaces the indicator by a representational distance between each alternative and the
observed unit followed by the alternatives sampled after it, the double expectation of the paper's
definition (`iiv`), whose horizon-one case is the information value of the substrate (`iiv_zero`).

## Implementation notes

* Alternatives are `h`-grams of `Option Voc`, `none` standing for end of string and padding the
  continuation after it, so that expectations are finite sums over a `Fintype`.
* The alternative-set reformulation with mean, minimum and maximum summary statistics, and its
  reduction to the single-alternative definition under the mean, are not formalized; nor are the
  representation functions, which the paper takes from a Transformer's layers and which enter
  here only through the distance.
* The paper's regression results, which horizon and layer best predict cloze probability, the
  N400 and P600, and eye-tracked and self-paced reading times, are empirical fits and stay in
  prose: explicit predictability peaks at horizon one and lexical representations, the ERP
  components at horizon two, and self-paced reading of multi-sentence stimuli at longer horizons.

## References

* [giulianelli-etal-2026]
* [giulianelli-opedal-cotterell-2024]
* [levy-2008]
-/

namespace GiulianelliEtAl2026

open Processing.PredictiveUncertainty Processing.LanguageModel Finset

variable {Voc : Type*}

/-! ### Sampling alternatives over a forecast horizon -/

/-- The alternatives of horizon `h`: `h` symbols sampled autoregressively from the model, `none`
for end of string and padding the continuation after it. -/
noncomputable def gram (lm : LangModel Voc) : List Voc → (h : ℕ) → PMF (List.Vector (Option Voc) h)
  | _, 0 => PMF.pure List.Vector.nil
  | c, h + 1 => (lm.next c).bind λ
    | none => PMF.pure (List.Vector.replicate (h + 1) none)
    | some w => (gram lm (c ++ [w]) h).map (List.Vector.cons (some w))

/-- The first symbol of an alternative is distributed as the model's next symbol. -/
theorem map_head_gram (lm : LangModel Voc) (c : List Voc) (h : ℕ) :
    (gram lm c (h + 1)).map List.Vector.head = lm.next c := by
  simp only [gram, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (lm.next c)]
  congr 1
  funext o
  cases o with
  | none => simp [PMF.pure_map, List.Vector.replicate_succ]
  | some w =>
    rw [PMF.map_comp]
    have hc : (List.Vector.head ∘ List.Vector.cons (some w) :
        List.Vector (Option Voc) h → Option Voc) = Function.const _ (some w) :=
      funext λ v => List.Vector.head_cons _ v
    rw [hc, PMF.map_const]

/-- Alternatives of horizon one are the model's next symbols. -/
theorem gram_one (lm : LangModel Voc) (c : List Voc) :
    gram lm c 1 = (lm.next c).map (λ o => List.Vector.cons o List.Vector.nil) := by
  rw [gram, ← PMF.bind_pure_comp]
  congr 1
  funext o
  cases o with
  | none => rfl
  | some w => simp [gram, PMF.pure_map]

variable [Fintype Voc] [DecidableEq Voc]

/-- Generalised surprisal at horizon `h`: a warping of the expected score of the target against
the sampled alternatives. -/
noncomputable def genSurprisalH (lm : LangModel Voc) (h : ℕ) (warp : ℝ → ℝ)
    (score : List.Vector (Option Voc) h → Voc → List Voc → ℝ) (c : List Voc) (w : Voc) : ℝ :=
  warp (∑ a, (gram lm c h a).toReal * score a w c)

/-- The prefix indicator of surprisal's scoring function: `1` when the alternative starts with the
target. -/
def prefixIndicator {h : ℕ} (w : Voc) (a : List.Vector (Option Voc) (h + 1)) : ℝ :=
  if a.head = some w then 1 else 0

/-- The expected prefix indicator is the next-symbol probability, at every horizon. -/
theorem sum_prefixIndicator (lm : LangModel Voc) (c : List Voc) (h : ℕ) (w : Voc) :
    ∑ a, (gram lm c (h + 1) a).toReal * prefixIndicator w a = (lm.nextProb c w).toReal := by
  have key : ∀ a : List.Vector (Option Voc) (h + 1),
      (gram lm c (h + 1) a).toReal * prefixIndicator w a =
        (if some w = a.head then gram lm c (h + 1) a else 0).toReal := by
    intro a
    unfold prefixIndicator
    by_cases ha : a.head = some w
    · simp [ha]
    · simp [ha, Ne.symm ha]
  simp_rw [key]
  rw [← ENNReal.toReal_sum (λ a _ => by split_ifs <;> simp [PMF.apply_ne_top])]
  congr 1
  rw [LangModel.nextProb, ← map_head_gram lm c h, PMF.map_apply, tsum_fintype]
  exact Finset.sum_congr rfl λ a _ => by congr

/-- Standard surprisal is the generalised surprisal with the negative logarithm and the prefix
indicator, at every horizon. -/
theorem genSurprisalH_indicator (lm : LangModel Voc) (c : List Voc) (h : ℕ) (w : Voc) :
    genSurprisalH lm (h + 1) (λ x => -Real.log x) (λ a w _ => prefixIndicator w a) c w =
      lm.surprisal c w := by
  unfold genSurprisalH LangModel.surprisal
  rw [sum_prefixIndicator]

/-! ### What the indicator conflates -/

/-- The discrete distance on next symbols: an alternative is accurate only when identical to the
target. -/
def discrete (o : Option Voc) (w : Voc) : ℝ := if o = some w then 0 else 1

/-- Information value with the discrete distance is the probability of error, `1 − p(w | c)`: the
alternatives' similarity to the target counts for nothing, as under surprisal. -/
theorem informationValue1_discrete (lm : LangModel Voc) (c : List Voc) (w : Voc) :
    informationValue1 lm discrete c w = 1 - (lm.nextProb c w).toReal := by
  unfold informationValue1 discrete
  have h1 : ∑ o : Option Voc, ((lm.next c) o).toReal = 1 := by
    have h := (lm.next c).tsum_coe
    rw [tsum_fintype] at h
    rw [← ENNReal.toReal_sum (λ _ _ => PMF.apply_ne_top _ _), h, ENNReal.toReal_one]
  have h2 : ∀ o : Option Voc, ((lm.next c) o).toReal * (if o = some w then 0 else 1) =
      ((lm.next c) o).toReal - (if o = some w then ((lm.next c) o).toReal else 0) := by
    intro o
    split_ifs <;> ring
  simp_rw [h2, Finset.sum_sub_distrib, h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-! ### Incremental information value -/

/-- Incremental information value at horizon `h + 1`: the expected representational distance
between an alternative sampled before the target and the target followed by an alternative
sampled after it, the paper's double expectation. -/
noncomputable def iiv (lm : LangModel Voc) (h : ℕ)
    (d : List.Vector (Option Voc) (h + 1) → List.Vector (Option Voc) (h + 1) → ℝ)
    (c : List Voc) (w : Voc) : ℝ :=
  ∑ a, (gram lm c (h + 1) a).toReal *
    ∑ a', (gram lm (c ++ [w]) h a').toReal * d a (List.Vector.cons (some w) a')

/-- Next symbols and alternatives of horizon one correspond. -/
def singletonEquiv : Option Voc ≃ List.Vector (Option Voc) 1 where
  toFun o := List.Vector.cons o List.Vector.nil
  invFun a := a.head
  left_inv o := List.Vector.head_cons o List.Vector.nil
  right_inv a := by
    symm
    rw [List.Vector.eq_cons_iff]
    exact ⟨rfl, List.Vector.singleton_tail a⟩

/-- At horizon one, incremental information value is the information value of the substrate,
with the distance read on the single symbols. -/
theorem iiv_zero (lm : LangModel Voc)
    (d : List.Vector (Option Voc) 1 → List.Vector (Option Voc) 1 → ℝ) (c : List Voc) (w : Voc) :
    iiv lm 0 d c w = informationValue1 lm (λ o w' => d (singletonEquiv o) (singletonEquiv (some w')))
      c w := by
  unfold iiv informationValue1
  show ∑ a : List.Vector (Option Voc) 1, (gram lm c 1 a).toReal *
      ∑ a' : List.Vector (Option Voc) 0, (gram lm (c ++ [w]) 0 a').toReal *
        d a (List.Vector.cons (some w) a') = _
  have inner : ∀ a : List.Vector (Option Voc) 1,
      ∑ a' : List.Vector (Option Voc) 0, (gram lm (c ++ [w]) 0 a').toReal *
        d a (List.Vector.cons (some w) a') = d a (singletonEquiv (some w)) := by
    intro a
    rw [Fintype.sum_eq_single List.Vector.nil (λ a' ha' => absurd (Subsingleton.elim a' _) ha')]
    show ((PMF.pure List.Vector.nil : PMF (List.Vector (Option Voc) 0)) List.Vector.nil).toReal *
      _ = _
    rw [PMF.pure_apply_self, ENNReal.toReal_one, one_mul]
    rfl
  simp_rw [inner, gram_one]
  rw [← singletonEquiv.sum_comp]
  refine Finset.sum_congr rfl λ o _ => ?_
  congr 2
  rw [PMF.map_apply, tsum_fintype]
  simp [singletonEquiv, List.Vector.eq_cons_iff, List.Vector.head_cons, Finset.sum_ite_eq]

end GiulianelliEtAl2026
