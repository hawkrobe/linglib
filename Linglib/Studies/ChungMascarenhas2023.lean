import Linglib.Core.Probability.Confirmation
import Linglib.Semantics.Conditionals.Probabilistic
import Linglib.Data.Examples.ChungMascarenhas2023
import Mathlib.Probability.Distributions.Uniform

/-!
# Chung & Mascarenhas 2023: Modality, expected utility, and hypothesis testing

A single core semantics for necessity modals over a family `R` of relevant
propositions ([chung-mascarenhas-2023] (6)):

  ⟦must φ⟧^w = (E_w[μ_R ∣ φ] > θ) ∧ ∀ψ ∈ Alt(φ). (E_w[μ_R ∣ ψ] ≤ θ)

with `μ_R` counting the relevant propositions true at a world ((7)/(11), substrate
`countMeasure`). Read deontically (`R` = rules/ideals), `E[μ_R ∣ φ]` is the expected
utility of `φ`; read epistemically (`R` = relevant known facts), it is the
*explanatory value* of `φ`, the sum of likelihoods `Σ_i P(e_i ∣ φ)` ((12), substrate
`condExpect_countMeasure`). *ought* ((17)) is the best-good-enough variant: above `θ`
and strictly better than every alternative — the paper's rendering of the weak
necessity literature it cites ([vonfintel-iatridou-2005]; [sloman-1970]).

* **Miners** (§3.1, [kolodny-macfarlane-2010]): six worlds = action × location,
  `idealsRD` = the ten cumulative ideals of (18) (borrowed from
  [cariani-kaufmann-kaufmann-2013]), so `μ_R` counts miners saved
  (`Miners.countMeasure_idealsRD`). The paper's expected utilities (19)–(21) and (23)
  are derived (`ev_*`: block-neither 9, block-A/B 5; conditionalized on
  miners-in-A: block-A 10, block-neither 9, block-B 0), giving *ought* (22)/(24) and
  *must* for `5 ≤ θ < 9` ((26)'s "threshold θ between 5 and 9"). The conditional
  *must* (25b) instead needs `9 ≤ θ < 10`; `must_thresholds_incompatible` is the
  paper's observation that the two requirements "are of course incompatible" — a
  shift of the standard `θ` is forced.
* **Modal Linda** (§3.2, [tversky-kahneman-1983]): the stipulated likelihoods
  (30)/(31) give explanatory values 0.5 (teller) vs 1.5 (feminist teller)
  ((32)/(33)); for any `θ` in `[0.5, 1.5)`, (34) makes *Linda must be a feminist
  bank teller* true and *Linda must be a bank teller* false
  (`modal_conjunction_fallacy`).
* **Modal Lawyers** (§3.3, [kahneman-tversky-1973]): likelihoods (37)/(38) give
  explanatory values 1.33 (engineer) vs 0.63 (lawyer) ((39)/(40)); for `θ` in
  `[0.63, 1.33)`, (41) makes *Jack must be an engineer* true irrespective of the
  prior split (`base_rate_neglect`).
* **Korean conditional evaluatives** (§4): `cip-ey iss-eya toy-n-ta` decomposes as
  the evaluative predicate *toy* (= `μ_R`), the conditional ((44), `condIf`),
  Lassiter's thresholding Θ ((46)/(47)), and the *-(e)ya* exhaustifier negating each
  alternative. `koreanConditionalEvaluative_iff_mustCM` is (48): the composition is
  exactly `mustCM`, via the (45) ≡ (12) identity `condExpect_countMeasure`.
* **§5**: the plausibility patch — *must φ* additionally requires a reasonably high
  prior for `φ` — kept as the separate `mustCMWithPlausibility`, since the paper
  presents it as an add-on whose derivation from the core is left open.

The Linda and Lawyers scenarios stay at the level of the paper's stipulated
conditional probabilities (ℚ values): the joint distributions over
hypothesis-and-evidence are not pinned down by the text, so no PMF is constructed.

The paper's fn. 17 comparison: Lassiter's *ought* compares the prejacent only to a
threshold, and his *must* requires alternatives to fall below the utility of
indifference — both differ from (6)/(17), which compare alternatives to `θ` and to
the prejacent respectively.

## Main results

* `mustCM` / `oughtCM` / `mustCMWithPlausibility` — (6), (17), and the §5 patch
* `Miners.countMeasure_idealsRD` — `μ_{R_D}` counts miners saved
* `Miners.ev_blockNeither` … `Miners.ev_inA_blockB` — the paper's expected-utility
  computations (19)–(21), (23)
* `Miners.ought_blockNeither` / `Miners.ought_if_inA_blockA` — (22), (24)
* `Miners.must_blockNeither` / `Miners.must_if_inA_blockA` — the *must* variants
  (26)/(25b) with their θ-ranges
* `Miners.must_thresholds_incompatible` — no single `θ` verifies both
* `ModalLinda.modal_conjunction_fallacy` — (34) over `θ ∈ [1/2, 3/2)`
* `ModalLawyers.base_rate_neglect` — (41) over `θ ∈ [63/100, 133/100)`
* `koreanConditionalEvaluative_iff_mustCM` — (48)

## References

* [W. Chung, S. Mascarenhas, *Modality, expected utility, and hypothesis
  testing* (2023)][chung-mascarenhas-2023]
* [N. Kolodny, J. MacFarlane, *Ifs and oughts* (2010)][kolodny-macfarlane-2010]
* [F. Cariani, M. Kaufmann, S. Kaufmann, *Deliberative modality under epistemic
  uncertainty* (2013)][cariani-kaufmann-kaufmann-2013]
* [A. Tversky, D. Kahneman, *Extensional versus intuitive reasoning: The
  conjunction fallacy in probability judgment* (1983)][tversky-kahneman-1983]
* [D. Kahneman, A. Tversky, *On the psychology of prediction*
  (1973)][kahneman-tversky-1973]
-/

namespace ChungMascarenhas2023

open PMF PMF.Confirmation Conditionals.Probabilistic
open scoped ENNReal
open BigOperators

variable {W : Type*} [Fintype W] {ι : Type*} [Fintype ι]

/-! ### The operators -/

/-- [chung-mascarenhas-2023] (6): `must φ` iff `E_w[μ_R ∣ φ]` exceeds the
contextual threshold `θ` AND no alternative does — `φ` is the only good-enough
option/explanation. -/
def mustCM (p : PMF W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W))
    (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ ∧ ∀ ψ ∈ alts, sumLikelihoods p R ψ ≤ θ

/-- [chung-mascarenhas-2023] (17): `ought φ` iff `φ` is the *best* good-enough
option — above `θ` and of strictly greater expected value than every
alternative. "This is the semantics for 'must φ', minus the requirement that φ
be the only good-enough alternative"; the paper motivates it from the weak
necessity literature ([vonfintel-iatridou-2005]; [sloman-1970]). -/
def oughtCM (p : PMF W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W))
    (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ ∧
    ∀ ψ ∈ alts, sumLikelihoods p R ψ < sumLikelihoods p R φ

/-- [chung-mascarenhas-2023] §5: `mustCM` plus the plausibility requirement —
a reasonably high prior for the prejacent. Kept as a separate `def`: the paper
presents the requirement as an add-on whose derivation from the core semantics
is left open. -/
def mustCMWithPlausibility (p : PMF W) (R : ι → Set W) (φ : Set W)
    (alts : Set (Set W)) (θ θplaus : ℝ≥0∞) : Prop :=
  mustCM p R φ alts θ ∧ θplaus ≤ p.probOfSet φ

/-! ### Korean conditional evaluatives (§4) -/

/-- [chung-mascarenhas-2023] (48), left-hand side: the compositional semantics
of `cip-ey iss-eya toy-n-ta` — Lassiter's thresholding Θ ((46), [lassiter-2017])
applied to the conditional `if φ, then eval` ((45), `condIf` over `μ_R`), plus
the *-(e)ya* 'only if' exhaustifier negating each alternative's thresholded
conditional. -/
def koreanConditionalEvaluative (p : PMF W) (R : ι → Set W) (φ : Set W)
    (alts : Set (Set W)) (θ : ℝ≥0∞) : Prop :=
  condIf p φ (countMeasure R) > θ ∧
    ∀ ψ ∈ alts, ¬(condIf p ψ (countMeasure R) > θ)

/-- [chung-mascarenhas-2023] (48): the Korean conditional evaluative composition
is exactly the `must` semantics (6). The content is the (45) ≡ (12) identity
`condExpect_countMeasure` — the conditional's expected value of `μ_R` *is* the
sum of likelihoods. -/
theorem koreanConditionalEvaluative_iff_mustCM (p : PMF W) (R : ι → Set W)
    (φ : Set W) (alts : Set (Set W)) (θ : ℝ≥0∞) :
    koreanConditionalEvaluative p R φ alts θ ↔ mustCM p R φ alts θ := by
  simp only [koreanConditionalEvaluative, mustCM, condIf,
    condExpect_countMeasure, not_lt]

/-! ### The miners puzzle (§3.1, [kolodny-macfarlane-2010])

Six worlds = (block-action) × (miners-location), Table 1:
`w0` block-A ∧ in-A (all 10 saved), `w1` block-A ∧ in-B (0), `w2` block-B ∧ in-A
(0), `w3` block-B ∧ in-B (10), `w4`/`w5` block-neither (9 each, "one drowned").
Uniform prior: the paper takes the locations equiprobable and independent of the
action. -/

namespace Miners

/-- World type: six (action × miners-location) combinations. -/
abbrev World := Fin 6

/-- Block shaft A. -/
def blockA : Set World := {w | w.val = 0 ∨ w.val = 1}
/-- Block shaft B. -/
def blockB : Set World := {w | w.val = 2 ∨ w.val = 3}
/-- Block neither shaft. -/
def blockNeither : Set World := {w | w.val = 4 ∨ w.val = 5}
/-- The miners are in shaft A. -/
def minersInA : Set World := {w | w.val = 0 ∨ w.val = 2 ∨ w.val = 4}
/-- The miners are in shaft B. -/
def minersInB : Set World := {w | w.val = 1 ∨ w.val = 3 ∨ w.val = 5}

/-- Miners saved at each world (Table 1). -/
def minersSaved : World → ℕ := fun w =>
  match w.val with
  | 0 => 10 | 1 => 0 | 2 => 0 | 3 => 10 | 4 => 9 | 5 => 9 | _ => 0

/-- Uniform prior over the six worlds. -/
noncomputable def prior : PMF World := PMF.uniformOfFintype World

/-- [chung-mascarenhas-2023] (18), borrowed from
[cariani-kaufmann-kaufmann-2013]: `R_D` = {1 miner saved, …, 10 miners saved},
as an indexed family — the ten ideals are distinct rules even where their
world-extensions coincide on this six-world space. -/
def idealsRD : Fin 10 → Set World := fun k => {w | k.val < minersSaved w}

instance : DecidablePred (· ∈ blockA) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))
instance : DecidablePred (· ∈ blockB) :=
  fun w => inferInstanceAs (Decidable (w.val = 2 ∨ w.val = 3))
instance : DecidablePred (· ∈ blockNeither) :=
  fun w => inferInstanceAs (Decidable (w.val = 4 ∨ w.val = 5))
instance : DecidablePred (· ∈ minersInA) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 2 ∨ w.val = 4))
instance : DecidablePred (· ∈ minersInB) :=
  fun w => inferInstanceAs (Decidable (w.val = 1 ∨ w.val = 3 ∨ w.val = 5))
instance (k : Fin 10) : DecidablePred (· ∈ idealsRD k) :=
  fun w => inferInstanceAs (Decidable (k.val < minersSaved w))

private instance {α : Type*} {s t : Set α} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : DecidablePred (· ∈ (s ∩ t)) :=
  fun a => inferInstanceAs (Decidable (a ∈ s ∧ a ∈ t))

/-- `μ_{R_D}` counts miners saved: each world abides by exactly
`minersSaved w` of the ten cumulative ideals. -/
theorem countMeasure_idealsRD (w : World) :
    countMeasure idealsRD w = minersSaved w := by
  rw [countMeasure_apply, Nat.cast_inj]
  revert w; decide

private theorem ev_eval {φ : Set World} [DecidablePred (· ∈ φ)]
    [∀ i : Fin 10, DecidablePred (· ∈ (φ ∩ idealsRD i))] {m n : ℕ}
    (hm : (∑ i : Fin 10,
      (Finset.univ.filter (· ∈ φ ∩ idealsRD i)).card) = m)
    (hn : (Finset.univ.filter (· ∈ φ)).card = n) :
    sumLikelihoods prior idealsRD φ = (m : ℝ≥0∞) / n := by
  rw [prior, sumLikelihoods_uniformOfFintype, ← Nat.cast_sum, hm, hn]

/-- (19): the expected utility of block-neither is 9. -/
theorem ev_blockNeither : sumLikelihoods prior idealsRD blockNeither = 9 := by
  rw [ev_eval (by decide : _ = 18) (by decide : _ = 2),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (20): the expected utility of block-A is 5. -/
theorem ev_blockA : sumLikelihoods prior idealsRD blockA = 5 := by
  rw [ev_eval (by decide : _ = 10) (by decide : _ = 2),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (21): the expected utility of block-B is 5. -/
theorem ev_blockB : sumLikelihoods prior idealsRD blockB = 5 := by
  rw [ev_eval (by decide : _ = 10) (by decide : _ = 2),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (23): conditionalized on miners-in-A, the expected utility of block-A
is 10. -/
theorem ev_inA_blockA :
    sumLikelihoods prior idealsRD (minersInA ∩ blockA) = 10 := by
  rw [ev_eval (by decide : _ = 10) (by decide : _ = 1),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- Conditionalized on miners-in-A, the expected utility of block-neither is
still 9 ("exactly one miner will drown irrespective of the location"). -/
theorem ev_inA_blockNeither :
    sumLikelihoods prior idealsRD (minersInA ∩ blockNeither) = 9 := by
  rw [ev_eval (by decide : _ = 9) (by decide : _ = 1),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- Conditionalized on miners-in-A, the expected utility of block-B is 0. -/
theorem ev_inA_blockB :
    sumLikelihoods prior idealsRD (minersInA ∩ blockB) = 0 := by
  rw [ev_eval (by decide : _ = 0) (by decide : _ = 1),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (22): *we ought to block neither shaft* — true for any `θ < 9`:
block-neither is the best good-enough option. -/
theorem ought_blockNeither {θ : ℝ≥0∞} (hθ : θ < 9) :
    oughtCM prior idealsRD blockNeither {blockA, blockB} θ := by
  refine ⟨ev_blockNeither ▸ hθ, ?_⟩
  rintro ψ (rfl | rfl)
  · rw [ev_blockA, ev_blockNeither]; norm_num
  · rw [ev_blockB, ev_blockNeither]; norm_num
/-- (24): *if the miners are in shaft A, we ought to block shaft A* — the
if-clause conditionalizes every expected utility on the antecedent (following
Lassiter, fn. 16 via Import-Export). True for any `θ < 10`. -/
theorem ought_if_inA_blockA {θ : ℝ≥0∞} (hθ : θ < 10) :
    oughtCM prior idealsRD (minersInA ∩ blockA)
      {minersInA ∩ blockNeither, minersInA ∩ blockB} θ := by
  refine ⟨ev_inA_blockA ▸ hθ, ?_⟩
  rintro ψ (rfl | rfl)
  · rw [ev_inA_blockNeither, ev_inA_blockA]; norm_num
  · rw [ev_inA_blockB, ev_inA_blockA]; norm_num
/-- (26): *we must block neither shaft* — block-neither is the *only*
good-enough option for any `θ` with `5 ≤ θ < 9` ("it will therefore be trivial
to find a threshold θ between 5 and 9"). -/
theorem must_blockNeither {θ : ℝ≥0∞} (h5 : 5 ≤ θ) (h9 : θ < 9) :
    mustCM prior idealsRD blockNeither {blockA, blockB} θ := by
  refine ⟨ev_blockNeither ▸ h9, ?_⟩
  rintro ψ (rfl | rfl)
  · exact ev_blockA ▸ h5
  · exact ev_blockB ▸ h5

/-- (25b) as *must*: conditionalized on miners-in-A, block-A is the only
good-enough option for any `θ` with `9 ≤ θ < 10` — the alternative
block-neither sits at 9, so the paper's "10 > θ ≥ 9" is forced. -/
theorem must_if_inA_blockA {θ : ℝ≥0∞} (h9 : 9 ≤ θ) (h10 : θ < 10) :
    mustCM prior idealsRD (minersInA ∩ blockA)
      {minersInA ∩ blockNeither, minersInA ∩ blockB} θ := by
  refine ⟨ev_inA_blockA ▸ h10, ?_⟩
  rintro ψ (rfl | rfl)
  · exact ev_inA_blockNeither ▸ h9
  · exact ev_inA_blockB ▸ bot_le

/-- The paper's tension: (26) needs `θ < 9` while the conditional (25b) needs
`9 ≤ θ` — "these two requirements are of course incompatible". No single
standard of evaluation verifies both *must*-claims; a `θ`-shift is forced. -/
theorem must_thresholds_incompatible :
    ¬ ∃ θ, mustCM prior idealsRD blockNeither {blockA, blockB} θ ∧
      mustCM prior idealsRD (minersInA ∩ blockA)
        {minersInA ∩ blockNeither, minersInA ∩ blockB} θ := by
  rintro ⟨θ, ⟨h9, -⟩, ⟨-, halts⟩⟩
  have h := halts _ (Set.mem_insert _ _)
  rw [ev_inA_blockNeither] at h
  rw [ev_blockNeither] at h9
  exact absurd (lt_of_le_of_lt h h9) (lt_irrefl _)

end Miners

/-! ### Modal Linda (§3.2, [tversky-kahneman-1983])

The salient evidence from the Linda description projects to two propositions —
concern with social justice and anti-nuclear-protest participation — with the
stipulated likelihoods (30)/(31). The joint distribution over
hypothesis-and-evidence is not pinned down by the paper, so the scenario stays
at the ℚ level of the paper's own computations. -/

namespace ModalLinda

/-- `P(social-justice ∣ teller) = 0.3` per (30). -/
def prSocialJusticeGivenTeller : ℚ := 3 / 10
/-- `P(anti-nuclear-protests ∣ teller) = 0.2` per (30). -/
def prAntiNuclearGivenTeller : ℚ := 2 / 10
/-- `P(social-justice ∣ feminist-teller) = 0.8` per (31). -/
def prSocialJusticeGivenFeministTeller : ℚ := 8 / 10
/-- `P(anti-nuclear-protests ∣ feminist-teller) = 0.7` per (31). -/
def prAntiNuclearGivenFeministTeller : ℚ := 7 / 10

/-- `E[μ_R ∣ teller] = 0.5` per (32). -/
def explanatoryValueTeller : ℚ :=
  prSocialJusticeGivenTeller + prAntiNuclearGivenTeller

/-- `E[μ_R ∣ feminist-teller] = 1.5` per (33). -/
def explanatoryValueFeministTeller : ℚ :=
  prSocialJusticeGivenFeministTeller + prAntiNuclearGivenFeministTeller

/-- (34), the modal conjunction fallacy: for any threshold in `[1/2, 3/2)`,
*Linda must be a feminist bank teller* is true — the conjunctive hypothesis is
the only good-enough explanation — while *Linda must be a bank teller* is
false. -/
theorem modal_conjunction_fallacy {θ : ℚ} (h₀ : 1 / 2 ≤ θ) (h₁ : θ < 3 / 2) :
    explanatoryValueFeministTeller > θ ∧ explanatoryValueTeller ≤ θ :=
  ⟨by show (8 : ℚ) / 10 + 7 / 10 > θ; linarith,
   by show (3 : ℚ) / 10 + 2 / 10 ≤ θ; linarith⟩

end ModalLinda

/-! ### Modal Lawyers and Engineers (§3.3, [kahneman-tversky-1973])

Two evidence pieces from the Jack description — no interest in political and
social issues, enjoyment of mathematical puzzles — with the likelihoods
(37)/(38). Same ℚ-level caveat as Modal Linda. -/

namespace ModalLawyers

/-- `P(not-political-social ∣ engineer) = 0.78` per (37). -/
def prNotPoliticalGivenEngineer : ℚ := 78 / 100
/-- `P(enjoys-mathematical-puzzles ∣ engineer) = 0.55` per (37). -/
def prMathGivenEngineer : ℚ := 55 / 100
/-- `P(not-political-social ∣ lawyer) = 0.35` per (38). -/
def prNotPoliticalGivenLawyer : ℚ := 35 / 100
/-- `P(enjoys-mathematical-puzzles ∣ lawyer) = 0.28` per (38). -/
def prMathGivenLawyer : ℚ := 28 / 100

/-- `E[μ_R ∣ engineer] = 1.33` per (39). -/
def explanatoryValueEngineer : ℚ :=
  prNotPoliticalGivenEngineer + prMathGivenEngineer

/-- `E[μ_R ∣ lawyer] = 0.63` per (40). -/
def explanatoryValueLawyer : ℚ :=
  prNotPoliticalGivenLawyer + prMathGivenLawyer

/-- (41), base-rate neglect at the modal level: for any threshold in
`[0.63, 1.33)`, *Jack must be an engineer* is true — irrespective of the prior
split between lawyers and engineers, since explanatory value conditions only on
the hypotheses. -/
theorem base_rate_neglect {θ : ℚ} (h₀ : 63 / 100 ≤ θ) (h₁ : θ < 133 / 100) :
    explanatoryValueEngineer > θ ∧ explanatoryValueLawyer ≤ θ :=
  ⟨by show (78 : ℚ) / 100 + 55 / 100 > θ; linarith,
   by show (35 : ℚ) / 100 + 28 / 100 ≤ θ; linarith⟩

end ModalLawyers

end ChungMascarenhas2023
